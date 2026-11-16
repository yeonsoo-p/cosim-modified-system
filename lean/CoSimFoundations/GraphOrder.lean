/-
The coupling graph and the order of execution (the paper, Corollary 5.6), in the one-step form
with explicit remainders of `ForcedBlock` and `ForcedParts`.

A pair of subsystems `s ≠ t` that are not partners is "forced into dissipation" if
`Σ_k (ς_sk + ς_tk) A_sk A_kt ≠ 0`; in entries, for states `p` of `s` and `q` of `t`, the sum is
`Σ_r (ς(s, sub r) + ς(t, sub r)) A p r A r q`.

(i) **Jacobi mode** (all stages equal). All signs are `-1`, the sum is `-2 (A²) p q`
    (`jacobi_sum`). Moreover a Jacobi scheme moves nothing between `s` and `t`, so the statement
    needs no consistency: for `U = exp (H • A)`, `H ≥ 0`, `c₃ = ‖A‖³/6 · e^{H‖A‖}`,
      `|⟪x, (X - U) y⟫ + ½H² ⟪x, A² y⟫| ≤ c₃ H³ ‖x‖ ‖y‖`                       (`jacobi_block`),
      `|⟪x, (X - U) y⟫ + ⟪y, (X - U) x⟫ + H² ⟪x, A² y⟫| ≤ 2 c₃ H³ ‖x‖ ‖y‖`     (`jacobi_sym`),
      `H² |⟪x, A² y⟫| - 2 c₃ H³ ≤ (‖D‖ - 1) + ‖D - 1‖ (1 + η)`                 (`jacobi_pair_gain`),
    the last for unit `x`, `y` and `X = D * U`: Proposition 5.4, eq. (pair), with the remainder of
    `u = H² ⟪x, A² y⟫ + O(H³)` made explicit.

(ii) **A branch point.** In every order of execution, among three subsystems two lie on the same
    side of a fourth, `k`: both after it or both not (`exists_pair_same_side`). If `k` is the only
    common partner of that pair, the sum is `±2 A p k A k q` (`exists_pair_sum`), and for a
    consistent scheme
      `H² |A p k A k q| - 2 C H³ ≤ |(X - U) p q + (X - U) q p|`              (`exists_pair_forced`),
      `H² |A p k A k q| - 2 C H³ ≤ (‖D‖ - 1) + ‖D - 1‖ (1 + 2 ‖A‖ e^{H‖A‖} H)` (`exists_pair_gain`).
    For subsystems with several states the pair is forced only if the product `A_pk A_kq` of the
    two coupling blocks is not zero, which partnership alone does not give (for scalar stores it
    does); the statement here is in terms of the entries.

(iii) **A path executed from end to end.** If every common partner of `s` and `t` runs between them
    (before exactly one of the two), the sum vanishes (`sum_eq_zero_of_between`) and
      `|(X - U) p q + (X - U) q p| ≤ 2 C H³`                                   (`sym_of_between`).
    On a path (`partner s t ↔ s + 1 = t ∨ t + 1 = s` on `Fin m`) with strictly monotone or
    strictly antitone stages this holds for every pair (`path_between`, `path_sym`).

The Gauss–Seidel scheme of scalar stores of `GaussSeidel` is a `HeldScheme` (`ScalarNet.gsHeld`),
so the statements apply to the step matrix derived from the differential equations of the stores;
`ScalarNet.gs_path_sym` is (iii) for it.
-/
import CoSimFoundations.ForcedParts
import CoSimFoundations.GaussSeidel

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

namespace HeldScheme

variable {n : ℕ} {κ : Type*} {S : HeldScheme n κ}

/-! ### (i) Jacobi mode -/

/-- In Jacobi mode all signs are `-1`. -/
theorem sg_of_jacobi (hJ : ∀ s t, S.stage s = S.stage t) (s k : κ) : S.sg s k = -1 := by
  have h : ¬ S.stage k < S.stage s := by rw [hJ k s]; exact lt_irrefl _
  simp [sg, h]

/-- **Jacobi mode: the sum of Corollary 5.6 (i).** All signs are `-1`, so the sum that decides
whether a pair is forced into dissipation is `-2 (A²) p q`: the pair is forced iff
`(A²) p q ≠ 0`. -/
theorem jacobi_sum (hJ : ∀ s t, S.stage s = S.stage t) (A : Matrix (Fin n) (Fin n) ℝ)
    (s t : κ) (p q : Fin n) :
    ∑ r, (S.sg s (S.sub r) + S.sg t (S.sub r)) * A p r * A r q = -2 * (A * A) p q := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sg_of_jacobi hJ, sg_of_jacobi hJ]
  ring

/-- A Jacobi scheme uses no new samples. -/
theorem N_eq_zero_of_jacobi (hJ : ∀ s t, S.stage s = S.stage t) : S.N = 0 := by
  ext p q
  exact S.hN p q fun h => absurd h.2 (by rw [hJ]; exact lt_irrefl _)

/-- A Jacobi scheme moves nothing between different subsystems that are not partners. -/
theorem X_eq_zero_of_jacobi (hJ : ∀ s t, S.stage s = S.stage t) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q)) : S.X p q = 0 := by
  have h := congrFun (congrFun S.hX p) q
  rw [N_eq_zero_of_jacobi hJ, Matrix.zero_mul, add_zero, Matrix.add_apply, S.hF p q hne,
    S.hM p q (fun h => hnp h.1), add_zero] at h
  exact h

/-- **Jacobi mode, the forced block without a consistency assumption.** For every Jacobi scheme
with one held sample, `U = exp (H • A)`, `H ≥ 0`, `x` supported on a subsystem `s` and `y` on a
subsystem `t ≠ s` that is not a partner of `s`:
`|⟪x, (X - U) y⟫ + ½H² ⟪x, A² y⟫| ≤ ‖A‖³/6 · e^{H‖A‖} H³ ‖x‖ ‖y‖`. -/
theorem jacobi_block (hJ : ∀ s t, S.stage s = S.stage t) {A U : Matrix (Fin n) (Fin n) ℝ}
    {H : ℝ} (hH : 0 ≤ H) (hU : U = NormedSpace.exp (H • A))
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ + H ^ 2 / 2 * ⟪x, opE (A * A) y⟫| ≤
      ‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖) * H ^ 3 * (‖x‖ * ‖y‖) := by
  set R : Matrix (Fin n) (Fin n) ℝ := U - (1 + H • A + (H ^ 2 / 2) • (A * A)) with hR
  have key : ∀ p q, S.sub p = s → S.sub q = t →
      (S.X - U + (H ^ 2 / 2) • (A * A)) p q = (-R) p q := by
    intro p q hp hq
    have hne : S.sub p ≠ S.sub q := by rw [hp, hq]; exact hst
    have hnp' : ¬ S.partner (S.sub p) (S.sub q) := by rw [hp, hq]; exact hnp
    have hpq : p ≠ q := fun h => hne (h ▸ rfl)
    simp only [hR, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.one_apply_ne hpq, smul_eq_mul, hA p q hne hnp', X_eq_zero_of_jacobi hJ hne hnp']
    ring
  have hin : ⟪x, opE (S.X - U) y⟫ + H ^ 2 / 2 * ⟪x, opE (A * A) y⟫ =
      ⟪x, opE (S.X - U + (H ^ 2 / 2) • (A * A)) y⟫ := by
    rw [inner_opE_add, opE_smul, FunLike.coe_smul, Pi.smul_apply, inner_smul_right]
  have hRn : ‖opE (-R)‖ ≤ ‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖) * H ^ 3 := by
    have e : opE (-R) = -opE R := map_neg _ R
    rw [e, norm_neg, hR, hU]
    exact norm_opE_exp_sub_quadratic_le A hH
  rw [hin, inner_opE_congr hx hy key]
  exact (abs_inner_opE_le (-R) x y).trans (mul_le_mul_of_nonneg_right hRn (by positivity))

/-- With skew coupling the matrix element of `A²` between two different subsystems that are not
partners may be read in either direction. -/
theorem inner_sq_swap {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    ⟪y, opE (A * A) x⟫ = ⟪x, opE (A * A) y⟫ := by
  rw [inner_opE_transpose]
  refine inner_opE_congr hx hy fun p q hp hq => ?_
  have h := skew_entry hA hskew (fun _ => (1 : ℝ)) (p := p) (q := q) (by rw [hp, hq]; exact hst)
    (by rw [hp, hq]; exact hnp) (by rw [hp, hq]; exact hnp')
  rw [Matrix.diagonal_one, Matrix.mul_one] at h
  rw [Matrix.transpose_apply]
  exact h

/-- **Jacobi mode, the symmetric combination** (Corollary 5.6 (i) with Corollary 5.1): with skew
coupling, `|⟪x, (X - U) y⟫ + ⟪y, (X - U) x⟫ + H² ⟪x, A² y⟫| ≤ 2 · ‖A‖³/6 · e^{H‖A‖} H³ ‖x‖ ‖y‖`:
every pair with `⟪x, A² y⟫ ≠ 0` is forced into dissipation, with this remainder. -/
theorem jacobi_sym (hJ : ∀ s t, S.stage s = S.stage t) {A U : Matrix (Fin n) (Fin n) ℝ}
    {H : ℝ} (hH : 0 ≤ H) (hU : U = NormedSpace.exp (H • A))
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫ + H ^ 2 * ⟪x, opE (A * A) y⟫| ≤
      2 * (‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖)) * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := abs_le.1 (jacobi_block hJ hH hU hA hst hnp hx hy)
  have h2 := abs_le.1 (jacobi_block hJ hH hU hA hst.symm hnp' hy hx)
  rw [inner_sq_swap hA hskew hst hnp hnp' hx hy, mul_comm ‖y‖ ‖x‖] at h2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Jacobi mode, what the pair costs** (Proposition 5.4, eq. (pair), with the remainder of
`u = H² ⟪x, A² y⟫ + O(H³)` explicit). For a Jacobi scheme with skew coupling and `X = D * U`,
unit vectors `x` on `s`, `y` on `t`:
`H² |⟪x, A² y⟫| - 2 · ‖A‖³/6 · e^{H‖A‖} H³ ≤ (‖D‖ - 1) + ‖D - 1‖ (1 + ‖U x - x‖ + ‖U y - y‖)`. -/
theorem jacobi_pair_gain (hJ : ∀ s t, S.stage s = S.stage t) {A U D : Matrix (Fin n) (Fin n) ℝ}
    {H : ℝ} (hH : 0 ≤ H) (hU : U = NormedSpace.exp (H • A))
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hD : S.X = D * U) {s t : κ}
    (hst : s ≠ t) (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    H ^ 2 * |⟪x, opE (A * A) y⟫| - 2 * (‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖)) * H ^ 3 ≤
      (‖opE D‖ - 1) + ‖opE D - 1‖ * (1 + (‖opE U x - x‖ + ‖opE U y - y‖)) := by
  have h1 := jacobi_sym hJ hH hU hA hskew hst hnp hnp' hx hy
  rw [hx1, hy1, mul_one, mul_one] at h1
  have h2 := pair_gain (opE D) (opE U) hx1 hy1 (inner_eq_zero_of_support hst hx hy)
  rw [inner_defect_eq hD, inner_defect_eq hD, ← neg_add, abs_neg] at h2
  have h3 : H ^ 2 * |⟪x, opE (A * A) y⟫| = |H ^ 2 * ⟪x, opE (A * A) y⟫| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ H ^ 2)]
  rw [h3]
  have h4 := abs_sub_abs_le_abs_sub (H ^ 2 * ⟪x, opE (A * A) y⟫)
    (-(⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫))
  have h5 : H ^ 2 * ⟪x, opE (A * A) y⟫ - -(⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫) =
      ⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫ + H ^ 2 * ⟪x, opE (A * A) y⟫ := by ring
  rw [abs_neg, h5] at h4
  linarith

/-! ### (ii) A branch point -/

/-- **Pigeonhole for the order of execution.** Among three subsystems `f 0`, `f 1`, `f 2`, two
lie on the same side of any subsystem `k`: both run after `k`, or both do not. -/
theorem exists_pair_same_side (S : HeldScheme n κ) (k : κ) (f : Fin 3 → κ) :
    ∃ i j, i ≠ j ∧ S.sg (f i) k = S.sg (f j) k := by
  obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin 3 => decide (S.stage k < S.stage (f i))) (by simp)
  refine ⟨i, j, hij, ?_⟩
  have h' : S.stage k < S.stage (f i) ↔ S.stage k < S.stage (f j) := by
    simpa using h
  by_cases hi : S.stage k < S.stage (f i)
  · simp [sg, hi, h'.1 hi]
  · have hj : ¬ S.stage k < S.stage (f j) := fun hj => hi (h'.2 hj)
    simp [sg, hi, hj]

/-- The square of a sign is one. -/
theorem abs_sg (S : HeldScheme n κ) (s k : κ) : |S.sg s k| = 1 := by
  by_cases h : S.stage k < S.stage s <;> simp [sg, h]

/-- **Corollary 5.6 (ii), the sum.** Let `p 0`, `p 1`, `p 2` be three states and `k` a state such
that, for each two of the three, `k` is the only state through which they interact
(`A (p i) r * A r (p j) = 0` for `r ≠ k`). Then in every order of execution there is a pair for
which the sum that decides the numerical dissipation is `±2 A (p i) k A k (p j)`: the pair is
forced into dissipation iff `A (p i) k * A k (p j) ≠ 0`. -/
theorem exists_pair_sum (S : HeldScheme n κ) (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin 3 → Fin n)
    (k : Fin n) (honly : ∀ i j, i ≠ j → ∀ r, r ≠ k → A (p i) r * A r (p j) = 0) :
    ∃ i j, i ≠ j ∧ |∑ r, (S.sg (S.sub (p i)) (S.sub r) + S.sg (S.sub (p j)) (S.sub r)) *
      A (p i) r * A r (p j)| = 2 * |A (p i) k * A k (p j)| := by
  obtain ⟨i, j, hij, h⟩ := S.exists_pair_same_side (S.sub k) (fun i => S.sub (p i))
  refine ⟨i, j, hij, ?_⟩
  rw [Finset.sum_eq_single k (fun r _ hr => by rw [mul_assoc, honly i j hij r hr, mul_zero])
    (fun hk => absurd (Finset.mem_univ k) hk), h, mul_assoc, abs_mul, ← two_mul, abs_mul,
    S.abs_sg, mul_one, abs_two]

section Consistent

variable {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- **Corollary 5.6 (ii), one-step form.** For a consistent scheme with skew coupling, three
states `p 0`, `p 1`, `p 2` in different subsystems that are pairwise not partners, and a state `k`
that is the only one through which any two of them interact: in every order of execution there is
a pair with `H² |A (p i) k A k (p j)| - 2 C H³ ≤ |(X - U) (p i) (p j) + (X - U) (p j) (p i)|`. -/
theorem Consistent.exists_pair_forced (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (p : Fin 3 → Fin n) (k : Fin n)
    (hne : ∀ i j, i ≠ j → S.sub (p i) ≠ S.sub (p j))
    (hnp : ∀ i j, i ≠ j → ¬ S.partner (S.sub (p i)) (S.sub (p j)))
    (honly : ∀ i j, i ≠ j → ∀ r, r ≠ k → A (p i) r * A r (p j) = 0) :
    ∃ i j, i ≠ j ∧ H ^ 2 * |A (p i) k * A k (p j)| - 2 * forcedC a b c ‖opE A‖ H * H ^ 3 ≤
      |(S.X - U) (p i) (p j) + (S.X - U) (p j) (p i)| := by
  obtain ⟨i, j, hij, hs⟩ := S.exists_pair_sum A p k honly
  refine ⟨i, j, hij, ?_⟩
  have h1 := h.forced_sym_entry hskew (hne i j hij) (hnp i j hij) (hnp j i hij.symm)
  have h2 := abs_sub_abs_le_abs_sub
    (H ^ 2 / 2 * ∑ r, (S.sg (S.sub (p i)) (S.sub r) + S.sg (S.sub (p j)) (S.sub r)) *
      A (p i) r * A r (p j)) ((S.X - U) (p i) (p j) + (S.X - U) (p j) (p i))
  rw [abs_sub_comm, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ H ^ 2 / 2), hs] at h2
  linarith

/-- **Corollary 5.6 (ii) with the cost.** In the situation of `exists_pair_forced`, with
`X = D * U`: in every order of execution there is a pair with
`H² |A (p i) k A k (p j)| - 2 C H³ ≤ (‖D‖ - 1) + ‖D - 1‖ (1 + 2 ‖A‖ e^{H‖A‖} H)`:
a network with a branch point cannot be executed without this choice. -/
theorem Consistent.exists_pair_gain (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : S.X = D * U) (p : Fin 3 → Fin n) (k : Fin n)
    (hne : ∀ i j, i ≠ j → S.sub (p i) ≠ S.sub (p j))
    (hnp : ∀ i j, i ≠ j → ¬ S.partner (S.sub (p i)) (S.sub (p j)))
    (honly : ∀ i j, i ≠ j → ∀ r, r ≠ k → A (p i) r * A r (p j) = 0) :
    ∃ i j, i ≠ j ∧ H ^ 2 * |A (p i) k * A k (p j)| - 2 * forcedC a b c ‖opE A‖ H * H ^ 3 ≤
      (‖opE D‖ - 1) + ‖opE D - 1‖ * (1 + 2 * (‖opE A‖ * Real.exp (H * ‖opE A‖) * H)) := by
  obtain ⟨i, j, hij, hs⟩ := S.exists_pair_sum A p k honly
  refine ⟨i, j, hij, ?_⟩
  have h1 := h.pair_gain_forced_explicit hskew hD (hne i j hij) (hnp i j hij)
    (hnp j i hij.symm)
  rw [hs] at h1
  linarith

/-! ### (iii) Common partners that run between -/

/-- **Corollary 5.6 (iii), the sum.** If every common partner of `s` and `t` runs between them
(before exactly one of the two), then for states `p` of `s` and `q` of `t` (different subsystems
that are not partners) the sum that decides the numerical dissipation vanishes. -/
theorem sum_eq_zero_of_between {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {p q : Fin n} (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hbetween : ∀ k, S.partner (S.sub p) k → S.partner k (S.sub q) →
      (S.stage k < S.stage (S.sub p) ↔ ¬ S.stage k < S.stage (S.sub q))) :
    ∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q = 0 := by
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hrp : S.sub r = S.sub p
  · rw [hA r q (by rw [hrp]; exact hne) (by rw [hrp]; exact hnp), mul_zero]
  · by_cases hrq : S.sub r = S.sub q
    · rw [hA p r (fun h => hrp h.symm) (by rw [hrq]; exact hnp), mul_zero, zero_mul]
    · by_cases h1 : S.partner (S.sub p) (S.sub r)
      · by_cases h2 : S.partner (S.sub r) (S.sub q)
        · have hk := hbetween (S.sub r) h1 h2
          have h0 : S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r) = 0 := by
            by_cases hkq : S.stage (S.sub r) < S.stage (S.sub q)
            · have hkp : ¬ S.stage (S.sub r) < S.stage (S.sub p) := fun h' => (hk.1 h') hkq
              simp [sg, hkp, hkq]
            · have hkp : S.stage (S.sub r) < S.stage (S.sub p) := hk.2 hkq
              simp [sg, hkp, hkq]
          rw [h0, zero_mul, zero_mul]
        · rw [hA r q hrq h2, mul_zero]
      · rw [hA p r (fun h => hrp h.symm) h1, mul_zero, zero_mul]

/-- **Corollary 5.6 (iii), one-step form.** For a consistent scheme with skew coupling, if every
common partner of the subsystems of `p` and `q` runs between them, the symmetric combination of
the one-step error is of third order: `|(X - U) p q + (X - U) q p| ≤ 2 C H³`. The pair is not
forced into dissipation. -/
theorem Consistent.sym_of_between (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p))
    (hbetween : ∀ k, S.partner (S.sub p) k → S.partner k (S.sub q) →
      (S.stage k < S.stage (S.sub p) ↔ ¬ S.stage k < S.stage (S.sub q))) :
    |(S.X - U) p q + (S.X - U) q p| ≤ 2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_sym_entry hskew hne hnp hnp'
  rwa [sum_eq_zero_of_between h.hA hne hnp hbetween, mul_zero, sub_zero] at h1

end Consistent

end HeldScheme

/-- **On a path executed from end to end, a common partner runs between.** Subsystems `Fin m`
with `s`, `t` partners iff they are neighbours, stages strictly monotone or strictly antitone:
for `s ≠ t` that are not partners, a common partner `k` runs before exactly one of them. -/
theorem path_between {m : ℕ} {stage : Fin m → ℕ} (hstage : StrictMono stage ∨ StrictAnti stage)
    {s t k : Fin m} (hsk : s.val + 1 = k.val ∨ k.val + 1 = s.val)
    (hkt : k.val + 1 = t.val ∨ t.val + 1 = k.val) (hst : s ≠ t) :
    stage k < stage s ↔ ¬ stage k < stage t := by
  have hst' : s.val ≠ t.val := fun h => hst (Fin.ext h)
  rcases hstage with hm | ha
  · rw [hm.lt_iff_lt, hm.lt_iff_lt, Fin.lt_def, Fin.lt_def]
    omega
  · rw [ha.lt_iff_gt, ha.lt_iff_gt, Fin.lt_def, Fin.lt_def]
    omega

namespace HeldScheme

variable {n m : ℕ} {S : HeldScheme n (Fin m)} {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- **Corollary 5.6 (iii) for a path.** If the coupling graph is a path and the subsystems are
executed from one of its ends to the other, then for a consistent scheme with skew coupling no
pair is forced into dissipation: for states `p`, `q` of different subsystems that are not
partners, `Σ_r (ς(sub p, sub r) + ς(sub q, sub r)) A p r A r q = 0` and
`|(X - U) p q + (X - U) q p| ≤ 2 C H³`. -/
theorem Consistent.path_sym (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hpath : ∀ s t, S.partner s t ↔ (s.val + 1 = t.val ∨ t.val + 1 = s.val))
    (hstage : StrictMono S.stage ∨ StrictAnti S.stage) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q)) :
    ∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q = 0 ∧
      |(S.X - U) p q + (S.X - U) q p| ≤ 2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have hnp' : ¬ S.partner (S.sub q) (S.sub p) := by
    rw [hpath] at hnp ⊢
    omega
  have hb : ∀ k, S.partner (S.sub p) k → S.partner k (S.sub q) →
      (S.stage k < S.stage (S.sub p) ↔ ¬ S.stage k < S.stage (S.sub q)) :=
    fun k h1 h2 => path_between hstage ((hpath _ _).1 h1) ((hpath _ _).1 h2) hne
  exact ⟨sum_eq_zero_of_between h.hA hne hnp hb, h.sym_of_between hskew hne hnp hnp' hb⟩

end HeldScheme

/-! ### The Gauss–Seidel scheme of scalar stores is such a scheme -/

namespace ScalarNet

variable {n : ℕ} (N : ScalarNet n)

/-- The use of new samples in the Gauss–Seidel scheme of `GaussSeidel`. -/
noncomputable def gsNew (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j < i then N.inGain H k i * w i j * N.c j else 0

/-- The use of old samples in the Gauss–Seidel scheme of `GaussSeidel`. -/
noncomputable def gsOld (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i < j then N.inGain H k i * w i j * N.c j else 0

/-- **The Gauss–Seidel scheme of scalar stores** (`GaussSeidel`: store `i` runs at stage `i`, with
gains `k` and weights `w` on the coupling graph) **is a scheme with one held sample** in the sense
of `HeldScheme`, with one-step map `gsStep`. So `ForcedBlock`, `ForcedParts` and this module apply
to the step matrix derived from the differential equations of the stores. -/
noncomputable def gsHeld (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ i j, ¬ N.partner i j → w i j = 0) : HeldScheme n (Fin n) where
  sub := id
  partner := N.partner
  stage := fun i => i.val
  F := Matrix.diagonal fun i => Real.exp (N.rate k i * H)
  N := N.gsNew H k w
  M := N.gsOld H k w
  X := N.gsStep H k w
  hF := fun _ _ h => Matrix.diagonal_apply_ne _ h
  hN := fun p q h => by
    by_cases hlt : q < p
    · have hp : ¬ N.partner p q := fun hp => h ⟨hp, hlt⟩
      simp [gsNew, hw p q hp]
    · simp [gsNew, hlt]
  hM := fun p q h => by
    by_cases hlt : p < q
    · have hp : ¬ N.partner p q := fun hp => h ⟨hp, fun h' => lt_asymm hlt h'⟩
      simp [gsOld, hw p q hp]
    · simp [gsOld, hlt]
  hX := by
    have h := N.gsLo_mul_gsStep H k w
    have hLo : N.gsLo H k w = 1 - N.gsNew H k w := by
      ext i j
      simp [gsLo, gsNew, Matrix.one_apply]
    have hR : N.gsR H k w =
        Matrix.diagonal (fun i => Real.exp (N.rate k i * H)) + N.gsOld H k w := by
      ext i j
      simp [gsR, gsOld, Matrix.diagonal_apply]
    rw [hLo, hR, Matrix.sub_mul, Matrix.one_mul] at h
    exact eq_add_of_sub_eq h

/-- **A chain of scalar stores in Gauss–Seidel mode from end to end** (Corollary 5.6 (iii), end to
end from the scheme): if the stores are partners exactly when they are neighbours, and the scheme
is consistent with the monolithic step, then for stores `p`, `q` that are not partners the
symmetric combination of the one-step error is of third order,
`|(X - U) p q + (X - U) q p| ≤ 2 C H³`, with `X` the Gauss–Seidel step matrix. -/
theorem gs_path_sym {H : ℝ} (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ i j, ¬ N.partner i j → w i j = 0)
    (hpath : ∀ s t, N.partner s t ↔ (s.val + 1 = t.val ∨ t.val + 1 = s.val))
    {A U : Matrix (Fin n) (Fin n) ℝ} {a b c : ℝ}
    (h : (N.gsHeld H k w hw).Consistent A U H a b c)
    (hskew : ∀ p q : Fin n, p ≠ q → A q p = -A p q) {p q : Fin n} (hne : p ≠ q)
    (hnp : ¬ N.partner p q) :
    |(N.gsStep H k w - U) p q + (N.gsStep H k w - U) q p| ≤
      2 * HeldScheme.forcedC a b c ‖opE A‖ H * H ^ 3 :=
  (h.path_sym hskew hpath (Or.inl Fin.val_strictMono) hne hnp).2

end ScalarNet

end CoSimFoundations
