/-
The two parts of the unavoidable error, and what the symmetric part costs, at one macro step with
explicit remainders (the paper, Corollary 5.1 and the one-step counterpart of Corollary 5.3; the
paper states both "to leading order").

Setting of `ForcedBlock`: a scheme with one held sample `S`, consistent with the monolithic step
`U = exp (H • A)` with constants `a`, `b`, `c` (`S.Consistent A U H a b c`), and
`C = forcedC a b c ‖A‖ H`. In addition the coupling is skew in energy coordinates:
`A q p = -A p q` for states `p`, `q` of different subsystems (`A_ij = -A_jiᵀ`, eq. (2)).
Let `s ≠ t` be subsystems that are not partners, `x` supported on `s`, `y` on `t`.

* **Symmetric and antisymmetric combination** (`forced_sym`, `forced_antisym`):
    `|⟪x, (X - U) y⟫ + ⟪y, (X - U) x⟫ - ½H² ⟪x, A (ς_s + ς_t) A y⟫| ≤ 2 C H³ ‖x‖ ‖y‖`,
    `|⟪x, (X - U) y⟫ - ⟪y, (X - U) x⟫ - ½H² ⟪x, A (ς_s - ς_t) A y⟫| ≤ 2 C H³ ‖x‖ ‖y‖`.
  Proof: `ForcedBlock` for `(s, t)` and for `(t, s)`, and `(A D A) q p = (A D A) p q` on the block
  for every diagonal `D`, by the skew symmetry. In entries: `forced_sym_entry`,
  `forced_antisym_entry` with `Σ_r (ς(sub p, sub r) ± ς(sub q, sub r)) A p r A r q`.

* **A single common partner `k`** (`A p r * A r q = 0` for `r ≠ k`): the symmetric combination is
  within `2 C H³` of `-H² A p k A k q` if `k` runs at no earlier stage than either (as in Jacobi
  mode), of `+H² A p k A k q` if `k` runs before both, and of `0` if `k` runs between them; in the
  last case the antisymmetric combination is within `2 C H³` of `H² A p k A k q`
  (`sym_after_both`, `sym_before_both`, `sym_between`, `antisym_between`). In the paper's terms
  (`Δ ≈ (X - U)/H`, `Δ_R = -sym Δ`) these are the contributions `+½H A A`, `-½H A A` to the
  numerical dissipation and `±½H A A` to the numerical interconnection: the signs agree.

* **What the symmetric part costs** (`pair_gain_forced`, `pair_gain_forced_entry`,
  `pair_tradeoff_forced`). For `X = D * U`, unit `x`, `y`, `α = ‖D - 1‖`,
  `η = ‖U x - x‖ + ‖U y - y‖`:
    `½H² |⟪x, A (ς_s + ς_t) A y⟫| - 2 C H³ ≤ (‖D‖ - 1) + α (1 + η)`,
    `½H² |⟪x, A (ς_s + ς_t) A y⟫| - 2 C H³ - α (η + α/2) ≤ (‖D‖² - m²)/2`
  (`m` a lower bound of the least stretch of `D`), from `pair_gain` and `pair_tradeoff`, which
  hold for every scheme. This is Proposition 5.4, eq. (pair), for every order of execution, and
  the one-step counterpart of Corollary 5.3: the amount is an inequality at the given macro step.
  `η ≤ 2 ‖A‖ e^{H‖A‖} H` (`norm_exp_apply_sub_le`).

* **The difference form** (the statements as the paper has them, for `Δ = Ã - A` with
  `X = exp (H • Ã)`, `H > 0`). In a Banach algebra, `‖a‖, ‖b‖ ≤ m` give
  `‖exp a - exp b - (a - b)‖ ≤ ‖a - b‖ m e^m` (series; `‖aᵏ - bᵏ‖ ≤ k ‖a - b‖ mᵏ⁻¹`), hence
  `|(X - U) p q - H Δ p q| ≤ H² ‖Δ‖ m e^{Hm}` for `‖Ã‖, ‖A‖ ≤ m`. With
  `ρ = C H² + H ‖Δ‖ m e^{Hm}`:
    `|Δ p q - ½H Σ_r ς(sub p, sub r) A p r A r q| ≤ ρ`       (`difference_entry`),
    `|Δ p q + Δ q p - ½H Σ_r (ς + ς) A p r A r q| ≤ 2 ρ`     (`difference_sym_entry`),
    `|Δ p q - Δ q p - ½H Σ_r (ς - ς) A p r A r q| ≤ 2 ρ`     (`difference_antisym_entry`),
    `½H |Σ_r (ς + ς) A p r A r q| - 2 ρ ≤ n lam - tr Δ`      (`amount`, with `triple_law`),
  for `xᵀ Δ x ≤ lam xᵀ x`: Corollary 5.3, `ν + n ι ≥ ½H |Σ| - 2 ρ`. The remainder `ρ` contains
  `‖Δ‖` and `‖Ã‖` of the scheme itself (`‖Δ‖ = O(H)` for a consistent family): it is explicit
  but not a priori.
-/
import CoSimFoundations.ForcedBlock
import CoSimFoundations.PairLaws
import CoSimFoundations.PairTradeOff
import CoSimFoundations.TripleLaw

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

variable {n : ℕ}

/-- `⟪y, T x⟫ = ⟪x, Tᵀ y⟫`. -/
theorem inner_opE_transpose (T : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, opE T x⟫ = ⟪x, opE Tᵀ y⟫ := by
  rw [inner_opE_eq_sum, inner_opE_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.transpose_apply]
  ring

/-- `⟪x, (T + T') y⟫ = ⟪x, T y⟫ + ⟪x, T' y⟫`. -/
theorem inner_opE_add (T T' : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (T + T') y⟫ = ⟪x, opE T y⟫ + ⟪x, opE T' y⟫ := by
  rw [opE_add, FunLike.coe_add, Pi.add_apply, inner_add_right]

/-- `⟪x, (T - T') y⟫ = ⟪x, T y⟫ - ⟪x, T' y⟫`. -/
theorem inner_opE_sub (T T' : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (T - T') y⟫ = ⟪x, opE T y⟫ - ⟪x, opE T' y⟫ := by
  rw [opE_sub, FunLike.coe_sub, Pi.sub_apply, inner_sub_right]

/-- Vectors supported on two different subsystems are orthogonal. -/
theorem inner_eq_zero_of_support {κ : Type*} {sub : Fin n → κ} {s t : κ} (hst : s ≠ t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, sub p ≠ s → x p = 0)
    (hy : ∀ q, sub q ≠ t → y q = 0) : ⟪x, y⟫ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : sub i = s
  · rw [hy i (fun h => hst (hi.symm.trans h)), inner_zero_right]
  · rw [hx i hi, inner_zero_left]

/-- `‖U x - x‖ ≤ ‖A‖ e^{H‖A‖} H ‖x‖` for `U = exp (H • A)`, `H ≥ 0`. -/
theorem norm_exp_apply_sub_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖opE (NormedSpace.exp (H • A)) x - x‖ ≤ ‖opE A‖ * Real.exp (H * ‖opE A‖) * H * ‖x‖ := by
  have h := norm_opE_exp_sub_one_le A hH
  have e : opE (NormedSpace.exp (H • A)) x - x = opE (NormedSpace.exp (H • A) - 1) x := by
    rw [opE_sub, opE_one, FunLike.coe_sub, Pi.sub_apply, one_apply_eq_self]
  rw [e]
  exact ((opE _).le_opNorm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

section ExpDiff

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `‖a^(k+1) - b^(k+1)‖ ≤ (k + 1) ‖a - b‖ m^k` if `‖a‖ ≤ m` and `‖b‖ ≤ m`. -/
theorem norm_pow_succ_sub_pow_succ_le (a b : 𝔸) {m : ℝ} (ha : ‖a‖ ≤ m) (hb : ‖b‖ ≤ m) (k : ℕ) :
    ‖a ^ (k + 1) - b ^ (k + 1)‖ ≤ (k + 1) * ‖a - b‖ * m ^ k := by
  have hm : 0 ≤ m := (norm_nonneg a).trans ha
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) =
        a ^ (k + 1) * (a - b) + (a ^ (k + 1) - b ^ (k + 1)) * b := by
      rw [pow_succ a (k + 1), pow_succ b (k + 1)]
      noncomm_ring
    have h1 : ‖a ^ (k + 1)‖ ≤ m ^ (k + 1) :=
      (norm_pow_le' a (Nat.succ_pos k)).trans (pow_le_pow_left₀ (norm_nonneg a) ha _)
    have h2 : ‖a ^ (k + 1) * (a - b)‖ ≤ m ^ (k + 1) * ‖a - b‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    have h3 : ‖(a ^ (k + 1) - b ^ (k + 1)) * b‖ ≤ (k + 1) * ‖a - b‖ * m ^ k * m :=
      (norm_mul_le _ _).trans (mul_le_mul ih hb (norm_nonneg _) (by positivity))
    rw [e]
    refine (norm_add_le _ _).trans ?_
    push_cast
    calc ‖a ^ (k + 1) * (a - b)‖ + ‖(a ^ (k + 1) - b ^ (k + 1)) * b‖
        ≤ m ^ (k + 1) * ‖a - b‖ + (k + 1) * ‖a - b‖ * m ^ k * m := add_le_add h2 h3
      _ = ((k : ℝ) + 1 + 1) * ‖a - b‖ * m ^ (k + 1) := by ring

/-- **The exponential against its linear part, for two arguments:** if `‖a‖ ≤ m` and `‖b‖ ≤ m`,
then `‖exp a - exp b - (a - b)‖ ≤ ‖a - b‖ m e^m`. -/
theorem norm_exp_sub_exp_sub_le (a b : 𝔸) {m : ℝ} (ha : ‖a‖ ≤ m) (hb : ‖b‖ ≤ m) :
    ‖NormedSpace.exp a - NormedSpace.exp b - (a - b)‖ ≤ ‖a - b‖ * m * Real.exp m := by
  have hm : 0 ≤ m := (norm_nonneg a).trans ha
  have hfa : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • a ^ k) (NormedSpace.exp a) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a
  have hfb : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • b ^ k) (NormedSpace.exp b) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) b
  have htail := (hasSum_nat_add_iff' 2).2 (hfa.sub hfb)
  have hsum : ∑ k ∈ Finset.range 2,
      (((k.factorial : ℝ)⁻¹) • a ^ k - ((k.factorial : ℝ)⁻¹) • b ^ k) = a - b := by
    simp [Finset.sum_range_succ]
  rw [hsum] at htail
  have hg : HasSum (fun i : ℕ => ‖a - b‖ * m * (m ^ i / (i.factorial : ℝ)))
      (‖a - b‖ * m * Real.exp m) := by
    have h : HasSum (fun i : ℕ => m ^ i / (i.factorial : ℝ)) (Real.exp m) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp m
    exact h.mul_left _
  refine htail.norm_le_of_bounded hg (fun i => ?_)
  rw [← smul_sub, norm_smul, norm_inv, Real.norm_natCast]
  have hpow := norm_pow_succ_sub_pow_succ_le a b ha hb (i + 1)
  push_cast at hpow
  have hF : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfact : ((i + 2).factorial : ℝ) = ((i : ℝ) + 2) * (((i : ℝ) + 1) * (i.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hfpos : (0 : ℝ) < ((i + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (i + 2)
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hY : 0 ≤ ‖a - b‖ * m ^ (i + 1) := by positivity
  have hR : ((i + 2).factorial : ℝ) * (‖a - b‖ * m * (m ^ i / (i.factorial : ℝ))) =
      ((i : ℝ) + 2) * ((i : ℝ) + 1) * (‖a - b‖ * m ^ (i + 1)) := by
    rw [hfact, pow_succ]
    field_simp
  rw [inv_mul_le_iff₀ hfpos, hR]
  refine hpow.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (i : ℝ) + 2) hi0) hY]

/-- **Two steps against their generators:** for `H ≥ 0`, `‖Ã‖ ≤ m`, `‖A‖ ≤ m`,
`‖exp (H Ã) - exp (H A) - H (Ã - A)‖ ≤ H² ‖Ã - A‖ m e^{Hm}`. -/
theorem norm_exp_smul_sub_exp_smul_sub_le (At A : 𝔸) {H m : ℝ} (hH : 0 ≤ H) (hAt : ‖At‖ ≤ m)
    (hA : ‖A‖ ≤ m) :
    ‖NormedSpace.exp (H • At) - NormedSpace.exp (H • A) - H • (At - A)‖ ≤
      H ^ 2 * ‖At - A‖ * m * Real.exp (H * m) := by
  have h := norm_exp_sub_exp_sub_le (H • At) (H • A) (m := H * m)
    (by rw [norm_smul, Real.norm_of_nonneg hH]; exact mul_le_mul_of_nonneg_left hAt hH)
    (by rw [norm_smul, Real.norm_of_nonneg hH]; exact mul_le_mul_of_nonneg_left hA hH)
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hH] at h
  calc ‖NormedSpace.exp (H • At) - NormedSpace.exp (H • A) - H • (At - A)‖
      ≤ H * ‖At - A‖ * (H * m) * Real.exp (H * m) := h
    _ = H ^ 2 * ‖At - A‖ * m * Real.exp (H * m) := by ring

end ExpDiff

/-- **The one-step error against the difference of the generators:** for `H ≥ 0`, `‖Ã‖ ≤ m`,
`‖A‖ ≤ m`: `|⟪x, (e^{HÃ} - e^{HA}) y⟫ - H ⟪x, (Ã - A) y⟫| ≤ H² ‖Ã - A‖ m e^{Hm} ‖x‖ ‖y‖`. -/
theorem abs_inner_step_sub_difference_le {At A : Matrix (Fin n) (Fin n) ℝ} {H m : ℝ}
    (hH : 0 ≤ H) (hAt : ‖opE At‖ ≤ m) (hA : ‖opE A‖ ≤ m) (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (NormedSpace.exp (H • At) - NormedSpace.exp (H • A)) y⟫ -
        H * ⟪x, opE (At - A) y⟫| ≤
      H ^ 2 * ‖opE (At - A)‖ * m * Real.exp (H * m) * (‖x‖ * ‖y‖) := by
  have e : ⟪x, opE (NormedSpace.exp (H • At) - NormedSpace.exp (H • A) - H • (At - A)) y⟫ =
      ⟪x, opE (NormedSpace.exp (H • At) - NormedSpace.exp (H • A)) y⟫ -
        H * ⟪x, opE (At - A) y⟫ := by
    rw [inner_opE_sub (NormedSpace.exp (H • At) - NormedSpace.exp (H • A)), opE_smul,
      FunLike.coe_smul, Pi.smul_apply, inner_smul_right]
  have hn : ‖opE (NormedSpace.exp (H • At) - NormedSpace.exp (H • A) - H • (At - A))‖ ≤
      H ^ 2 * ‖opE (At - A)‖ * m * Real.exp (H * m) := by
    rw [opE_sub, opE_sub, opE_exp, opE_exp, opE_smul, opE_smul, opE_smul, opE_sub]
    exact norm_exp_smul_sub_exp_smul_sub_le (opE At) (opE A) hH hAt hA
  rw [← e]
  exact (abs_inner_opE_le _ x y).trans (mul_le_mul_of_nonneg_right hn (by positivity))

end OneStep

open OneStep

namespace HeldScheme

variable {n : ℕ} {κ : Type*} {S : HeldScheme n κ}

/-- With skew coupling, the block of `A D A` between two different subsystems that are not
partners is symmetric, for every diagonal `D`: `(A D A) q p = (A D A) p q`. -/
theorem skew_entry {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (v : Fin n → ℝ) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    (A * diagonal v * A) q p = (A * diagonal v * A) p q := by
  rw [mul_diagonal_mul_apply, mul_diagonal_mul_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hrp : S.sub r = S.sub p
  · have h1 : A q r = 0 := hA q r (by rw [hrp]; exact hne.symm) (by rw [hrp]; exact hnp')
    have h2 : A r q = 0 := hA r q (by rw [hrp]; exact hne) (by rw [hrp]; exact hnp)
    rw [h1, h2]
    ring
  · by_cases hrq : S.sub r = S.sub q
    · have h1 : A r p = 0 := hA r p hrp (by rw [hrq]; exact hnp')
      have h2 : A p r = 0 := hA p r (fun h => hrp h.symm) (by rw [hrq]; exact hnp)
      rw [h1, h2]
      ring
    · rw [hskew r q hrq, hskew p r (fun h => hrp h.symm)]
      ring

/-- The entry of `A (ς_s + ς_t) A`. -/
theorem sgn_add_entry (S : HeldScheme n κ) (A : Matrix (Fin n) (Fin n) ℝ) (s t : κ)
    (p q : Fin n) : (A * (S.sgn s + S.sgn t) * A) p q =
      ∑ r, (S.sg s (S.sub r) + S.sg t (S.sub r)) * A p r * A r q := by
  rw [sgn, sgn, Matrix.diagonal_add, mul_diagonal_mul_apply]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- The entry of `A (ς_s - ς_t) A`. -/
theorem sgn_sub_entry (S : HeldScheme n κ) (A : Matrix (Fin n) (Fin n) ℝ) (s t : κ)
    (p q : Fin n) : (A * (S.sgn s - S.sgn t) * A) p q =
      ∑ r, (S.sg s (S.sub r) - S.sg t (S.sub r)) * A p r * A r q := by
  rw [sgn, sgn, Matrix.diagonal_sub, mul_diagonal_mul_apply]
  exact Finset.sum_congr rfl fun r _ => by ring

section Parts

variable {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- The matrix element of `A ς_t A` between `s` and `t` may be read in either direction. -/
theorem Consistent.inner_sgn_swap (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s) (u : κ) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    ⟪y, opE (A * S.sgn u * A) x⟫ = ⟪x, opE (A * S.sgn u * A) y⟫ := by
  rw [inner_opE_transpose]
  refine inner_opE_congr hx hy fun p q hp hq => ?_
  rw [Matrix.transpose_apply]
  exact skew_entry h.hA hskew _ (by rw [hp, hq]; exact hst) (by rw [hp, hq]; exact hnp)
    (by rw [hp, hq]; exact hnp')

/-- **The symmetric combination** (Corollary 5.1, one-step form, numerical dissipation). For a
consistent scheme with skew coupling, subsystems `s ≠ t` that are not partners, `x` supported on
`s` and `y` on `t`:
`|⟪x, (X - U) y⟫ + ⟪y, (X - U) x⟫ - ½H² ⟪x, A (ς_s + ς_t) A y⟫| ≤ 2 C H³ ‖x‖ ‖y‖`. -/
theorem Consistent.forced_sym (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫ -
        H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := abs_le.1 (h.forced_block hst hnp hx hy)
  have h2 := abs_le.1 (h.forced_block hst.symm hnp' hy hx)
  rw [h.inner_sgn_swap hskew hst hnp hnp' t hx hy, mul_comm ‖y‖ ‖x‖] at h2
  rw [Matrix.mul_add, Matrix.add_mul, inner_opE_add, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The antisymmetric combination** (Corollary 5.1, one-step form, numerical interconnection):
`|⟪x, (X - U) y⟫ - ⟪y, (X - U) x⟫ - ½H² ⟪x, A (ς_s - ς_t) A y⟫| ≤ 2 C H³ ‖x‖ ‖y‖`. -/
theorem Consistent.forced_antisym (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - ⟪y, opE (S.X - U) x⟫ -
        H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s - S.sgn t) * A) y⟫| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := abs_le.1 (h.forced_block hst hnp hx hy)
  have h2 := abs_le.1 (h.forced_block hst.symm hnp' hy hx)
  rw [h.inner_sgn_swap hskew hst hnp hnp' t hx hy, mul_comm ‖y‖ ‖x‖] at h2
  rw [Matrix.mul_sub, Matrix.sub_mul, inner_opE_sub (A * S.sgn s * A), abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The symmetric combination, in entries** (for scalar stores `sub = id`). For states `p`, `q`
of different subsystems that are not partners:
`|(X - U) p q + (X - U) q p - ½H² Σ_r (ς(sub p, sub r) + ς(sub q, sub r)) A p r A r q| ≤ 2 C H³`. -/
theorem Consistent.forced_sym_entry (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    |(S.X - U) p q + (S.X - U) q p - H ^ 2 / 2 *
        ∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_sym hskew hne hnp hnp' (S.unitE_support p) (S.unitE_support q)
  rwa [inner_unitE_opE, inner_unitE_opE, inner_unitE_opE, norm_unitE, norm_unitE, mul_one,
    mul_one, S.sgn_add_entry] at h1

/-- **The antisymmetric combination, in entries**:
`|(X - U) p q - (X - U) q p - ½H² Σ_r (ς(sub p, sub r) - ς(sub q, sub r)) A p r A r q| ≤ 2 C H³`. -/
theorem Consistent.forced_antisym_entry (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    |(S.X - U) p q - (S.X - U) q p - H ^ 2 / 2 *
        ∑ r, (S.sg (S.sub p) (S.sub r) - S.sg (S.sub q) (S.sub r)) * A p r * A r q| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_antisym hskew hne hnp hnp' (S.unitE_support p) (S.unitE_support q)
  rwa [inner_unitE_opE, inner_unitE_opE, inner_unitE_opE, norm_unitE, norm_unitE, mul_one,
    mul_one, S.sgn_sub_entry] at h1

/-- **A single common partner at no earlier stage than either** (as in Jacobi mode): the
symmetric combination is within `2 C H³` of `-H² A p k A k q` (numerical dissipation
`+½H A A` in the paper's terms). `k` is the only state with `A p k A k q ≠ 0`. -/
theorem Consistent.sym_after_both (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {p q k : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) (honly : ∀ r, r ≠ k → A p r * A r q = 0)
    (hkp : ¬ S.stage (S.sub k) < S.stage (S.sub p))
    (hkq : ¬ S.stage (S.sub k) < S.stage (S.sub q)) :
    |(S.X - U) p q + (S.X - U) q p + H ^ 2 * (A p k * A k q)| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_sym_entry hskew hne hnp hnp'
  rw [Finset.sum_eq_single k (fun r _ hr => by rw [mul_assoc, honly r hr, mul_zero])
    (fun hk => absurd (Finset.mem_univ k) hk)] at h1
  simp only [sg, hkp, hkq, ↓reduceIte] at h1
  convert h1 using 2
  ring

/-- **A single common partner that runs before both**: the symmetric combination is within
`2 C H³` of `+H² A p k A k q` (numerical dissipation `-½H A A` in the paper's terms). -/
theorem Consistent.sym_before_both (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {p q k : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) (honly : ∀ r, r ≠ k → A p r * A r q = 0)
    (hkp : S.stage (S.sub k) < S.stage (S.sub p))
    (hkq : S.stage (S.sub k) < S.stage (S.sub q)) :
    |(S.X - U) p q + (S.X - U) q p - H ^ 2 * (A p k * A k q)| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_sym_entry hskew hne hnp hnp'
  rw [Finset.sum_eq_single k (fun r _ hr => by rw [mul_assoc, honly r hr, mul_zero])
    (fun hk => absurd (Finset.mem_univ k) hk)] at h1
  simp only [sg, hkp, hkq, ↓reduceIte] at h1
  convert h1 using 2
  ring

/-- **A single common partner that runs between the two** (before exactly one of them): the
symmetric combination is within `2 C H³` of zero. -/
theorem Consistent.sym_between (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {p q k : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) (honly : ∀ r, r ≠ k → A p r * A r q = 0)
    (hk : S.stage (S.sub k) < S.stage (S.sub p) ↔ ¬ S.stage (S.sub k) < S.stage (S.sub q)) :
    |(S.X - U) p q + (S.X - U) q p| ≤ 2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_sym_entry hskew hne hnp hnp'
  rw [Finset.sum_eq_single k (fun r _ hr => by rw [mul_assoc, honly r hr, mul_zero])
    (fun hk => absurd (Finset.mem_univ k) hk)] at h1
  have h0 : S.sg (S.sub p) (S.sub k) + S.sg (S.sub q) (S.sub k) = 0 := by
    by_cases hkq : S.stage (S.sub k) < S.stage (S.sub q)
    · have hkp : ¬ S.stage (S.sub k) < S.stage (S.sub p) := fun h' => (hk.1 h') hkq
      simp [sg, hkp, hkq]
    · have hkp : S.stage (S.sub k) < S.stage (S.sub p) := hk.2 hkq
      simp [sg, hkp, hkq]
  rwa [h0, zero_mul, zero_mul, mul_zero, sub_zero] at h1

/-- **A single common partner that runs before `p` and not before `q`**: the antisymmetric
combination is within `2 C H³` of `H² A p k A k q` (a numerical interconnection `±½H A A` in the
paper's terms): the later of the two receives twice the amount, the earlier one nothing. -/
theorem Consistent.antisym_between (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {p q k : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) (honly : ∀ r, r ≠ k → A p r * A r q = 0)
    (hkp : S.stage (S.sub k) < S.stage (S.sub p))
    (hkq : ¬ S.stage (S.sub k) < S.stage (S.sub q)) :
    |(S.X - U) p q - (S.X - U) q p - H ^ 2 * (A p k * A k q)| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_antisym_entry hskew hne hnp hnp'
  rw [Finset.sum_eq_single k (fun r _ hr => by rw [mul_assoc, honly r hr, mul_zero])
    (fun hk => absurd (Finset.mem_univ k) hk)] at h1
  simp only [sg, hkp, hkq, ↓reduceIte] at h1
  convert h1 using 2
  ring

/-- What the scheme fails to move, in terms of the defect: `⟪x, U y - D (U y)⟫ = -⟪x, (X - U) y⟫`
for `X = D * U`. -/
theorem inner_defect_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : S.X = D * U)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE U y - opE D (opE U y)⟫ = -⟪x, opE (S.X - U) y⟫ := by
  rw [inner_opE_sub, hD, opE_mul_apply, inner_sub_right]
  ring

/-- **What the symmetric part costs** (Proposition 5.4, eq. (pair), for every order of execution;
one-step counterpart of Corollary 5.3). For a consistent scheme with skew coupling and one-step
map `X = D * U`, subsystems `s ≠ t` that are not partners and unit vectors `x` on `s`, `y` on `t`:
`½H² |⟪x, A (ς_s + ς_t) A y⟫| - 2 C H³ ≤ (‖D‖ - 1) + ‖D - 1‖ (1 + ‖U x - x‖ + ‖U y - y‖)`. -/
theorem Consistent.pair_gain_forced (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : S.X = D * U) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) :
    H ^ 2 / 2 * |⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| -
        2 * forcedC a b c ‖opE A‖ H * H ^ 3 ≤
      (‖opE D‖ - 1) + ‖opE D - 1‖ * (1 + (‖opE U x - x‖ + ‖opE U y - y‖)) := by
  have h1 := h.forced_sym hskew hst hnp hnp' hx hy
  rw [hx1, hy1, mul_one, mul_one] at h1
  have h2 := pair_gain (opE D) (opE U) hx1 hy1 (inner_eq_zero_of_support hst hx hy)
  rw [inner_defect_eq hD, inner_defect_eq hD, ← neg_add, abs_neg] at h2
  have h3 : H ^ 2 / 2 * |⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| =
      |H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ H ^ 2 / 2)]
  rw [h3]
  have h4 := abs_sub_abs_le_abs_sub (H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫)
    (⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫)
  rw [abs_sub_comm] at h4
  linarith

/-- **What the symmetric part costs, in entries** (for scalar stores `sub = id`), with
`e_p`, `e_q` the unit vectors of the states `p`, `q`:
`½H² |Σ_r (ς(sub p, sub r) + ς(sub q, sub r)) A p r A r q| - 2 C H³ ≤
(‖D‖ - 1) + ‖D - 1‖ (1 + ‖U e_p - e_p‖ + ‖U e_q - e_q‖)`. -/
theorem Consistent.pair_gain_forced_entry (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : S.X = D * U) {p q : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    H ^ 2 / 2 * |∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q| -
        2 * forcedC a b c ‖opE A‖ H * H ^ 3 ≤
      (‖opE D‖ - 1) + ‖opE D - 1‖ *
        (1 + (‖opE U (unitE p) - unitE p‖ + ‖opE U (unitE q) - unitE q‖)) := by
  have h1 := h.pair_gain_forced hskew hD hne hnp hnp' (S.unitE_support p) (S.unitE_support q)
    (norm_unitE p) (norm_unitE q)
  rwa [inner_unitE_opE, S.sgn_add_entry] at h1

/-- **What the symmetric part costs, fully explicit**: with `η ≤ 2 ‖A‖ e^{H‖A‖} H`,
`½H² |Σ_r (ς(sub p, sub r) + ς(sub q, sub r)) A p r A r q| - 2 C H³ ≤
(‖D‖ - 1) + ‖D - 1‖ (1 + 2 ‖A‖ e^{H‖A‖} H)`. In particular a scheme that adds no energy in any
state, `‖D‖ ≤ 1`, has a one-step error `‖D - 1‖` of at least the left side divided by
`1 + 2 ‖A‖ e^{H‖A‖} H`. -/
theorem Consistent.pair_gain_forced_explicit (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : S.X = D * U) {p q : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    H ^ 2 / 2 * |∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q| -
        2 * forcedC a b c ‖opE A‖ H * H ^ 3 ≤
      (‖opE D‖ - 1) + ‖opE D - 1‖ * (1 + 2 * (‖opE A‖ * Real.exp (H * ‖opE A‖) * H)) := by
  have h1 := h.pair_gain_forced_entry hskew hD hne hnp hnp'
  have hp := norm_exp_apply_sub_le A h.hH (unitE p)
  have hq := norm_exp_apply_sub_le A h.hH (unitE q)
  rw [← h.hU, norm_unitE, mul_one] at hp hq
  have h2 : ‖opE D - 1‖ * (1 + (‖opE U (unitE p) - unitE p‖ + ‖opE U (unitE q) - unitE q‖)) ≤
      ‖opE D - 1‖ * (1 + 2 * (‖opE A‖ * Real.exp (H * ‖opE A‖) * H)) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  linarith

/-- **The symmetric part against the spread of the stretches** (from `pair_tradeoff`): if
`m ‖v‖ ≤ ‖D v‖` for all `v`, then
`½H² |⟪x, A (ς_s + ς_t) A y⟫| - 2 C H³ - α (η + α/2) ≤ (‖D‖² - m²)/2`, `α = ‖D - 1‖`,
`η = ‖U x - x‖ + ‖U y - y‖`. A defect that keeps the energy of every state (`‖D‖ = m = 1`) has
`α (η + α/2) ≥ ½H² |⟪x, A (ς_s + ς_t) A y⟫| - 2 C H³`. -/
theorem Consistent.pair_tradeoff_forced (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : S.X = D * U) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {m : ℝ} (hm0 : 0 ≤ m) (hmD : ∀ v, m * ‖v‖ ≤ ‖opE D v‖) :
    H ^ 2 / 2 * |⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| -
        2 * forcedC a b c ‖opE A‖ H * H ^ 3 -
        ‖opE D - 1‖ * ((‖opE U x - x‖ + ‖opE U y - y‖) + ‖opE D - 1‖ / 2) ≤
      (‖opE D‖ ^ 2 - m ^ 2) / 2 := by
  have h1 := h.forced_sym hskew hst hnp hnp' hx hy
  rw [hx1, hy1, mul_one, mul_one] at h1
  have h2 := pair_tradeoff (opE D) (opE U) hx1 hy1 (inner_eq_zero_of_support hst hx hy) hm0 hmD
  rw [inner_defect_eq hD, inner_defect_eq hD, ← neg_add, abs_neg] at h2
  have h3 : H ^ 2 / 2 * |⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| =
      |H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ H ^ 2 / 2)]
  rw [h3]
  have h4 := abs_sub_abs_le_abs_sub (H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫)
    (⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫)
  rw [abs_sub_comm] at h4
  linarith

/-! ### The difference form: Proposition 4.4, Corollary 5.1 and Corollary 5.3 as stated -/

/-- The entry of the one-step error against the entry of the difference `Δ = Ã - A`, for a scheme
with a modified system, `X = exp (H • Ã)`: `|(X - U) p q - H Δ p q| ≤ H² ‖Δ‖ m e^{Hm}`. -/
theorem Consistent.abs_step_entry_sub_le (h : S.Consistent A U H a b c)
    {At : Matrix (Fin n) (Fin n) ℝ} (hX : S.X = NormedSpace.exp (H • At)) {m : ℝ}
    (hAt : ‖opE At‖ ≤ m) (hA : ‖opE A‖ ≤ m) (p q : Fin n) :
    |(S.X - U) p q - H * (At - A) p q| ≤ H ^ 2 * ‖opE (At - A)‖ * m * Real.exp (H * m) := by
  have h1 := abs_inner_step_sub_difference_le h.hH hAt hA (unitE p) (unitE q)
  rwa [← hX, ← h.hU, inner_unitE_opE, inner_unitE_opE, norm_unitE, norm_unitE, mul_one,
    mul_one] at h1

/-- **The forced block of the difference** (Proposition 4.4, second statement, with its
remainder). For a consistent scheme with a modified system `Ã`, `X = exp (H • Ã)`, `H > 0`,
`Δ = Ã - A`, `‖Ã‖ ≤ m`, `‖A‖ ≤ m`, and states `p`, `q` of different subsystems that are not
partners: `|Δ p q - ½H Σ_r ς(sub p, sub r) A p r A r q| ≤ C H² + H ‖Δ‖ m e^{Hm}`. -/
theorem Consistent.difference_entry (h : S.Consistent A U H a b c)
    {At : Matrix (Fin n) (Fin n) ℝ} (hX : S.X = NormedSpace.exp (H • At)) (hH : 0 < H) {m : ℝ}
    (hAt : ‖opE At‖ ≤ m) (hA : ‖opE A‖ ≤ m) {p q : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) :
    |(At - A) p q - H / 2 * ∑ r, S.sg (S.sub p) (S.sub r) * A p r * A r q| ≤
      forcedC a b c ‖opE A‖ H * H ^ 2 + H * ‖opE (At - A)‖ * m * Real.exp (H * m) := by
  have h1 := abs_le.1 (h.forced_entry hne hnp)
  have h2 := abs_le.1 (h.abs_step_entry_sub_le hX hAt hA p q)
  rw [Matrix.sub_apply] at h2
  refine le_of_mul_le_mul_left ?_ hH
  rw [← abs_of_pos hH, ← abs_mul, abs_of_pos hH, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **The symmetric part of the difference** (Corollary 5.1 as stated, numerical dissipation
`[Δ_R]_pq = -½ (Δ p q + Δ q p)`, with its remainder):
`|Δ p q + Δ q p - ½H Σ_r (ς(sub p, sub r) + ς(sub q, sub r)) A p r A r q| ≤
2 (C H² + H ‖Δ‖ m e^{Hm})`. -/
theorem Consistent.difference_sym_entry (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {At : Matrix (Fin n) (Fin n) ℝ} (hX : S.X = NormedSpace.exp (H • At)) (hH : 0 < H) {m : ℝ}
    (hAt : ‖opE At‖ ≤ m) (hA : ‖opE A‖ ≤ m) {p q : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    |(At - A) p q + (At - A) q p - H / 2 *
        ∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q| ≤
      2 * (forcedC a b c ‖opE A‖ H * H ^ 2 + H * ‖opE (At - A)‖ * m * Real.exp (H * m)) := by
  have h1 := abs_le.1 (h.forced_sym_entry hskew hne hnp hnp')
  have h2 := abs_le.1 (h.abs_step_entry_sub_le hX hAt hA p q)
  have h3 := abs_le.1 (h.abs_step_entry_sub_le hX hAt hA q p)
  refine le_of_mul_le_mul_left ?_ hH
  rw [← abs_of_pos hH, ← abs_mul, abs_of_pos hH, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The antisymmetric part of the difference** (Corollary 5.1 as stated, numerical
interconnection `[Δ_J]_pq = ½ (Δ p q - Δ q p)`, with its remainder):
`|Δ p q - Δ q p - ½H Σ_r (ς(sub p, sub r) - ς(sub q, sub r)) A p r A r q| ≤
2 (C H² + H ‖Δ‖ m e^{Hm})`. -/
theorem Consistent.difference_antisym_entry (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {At : Matrix (Fin n) (Fin n) ℝ} (hX : S.X = NormedSpace.exp (H • At)) (hH : 0 < H) {m : ℝ}
    (hAt : ‖opE At‖ ≤ m) (hA : ‖opE A‖ ≤ m) {p q : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    |(At - A) p q - (At - A) q p - H / 2 *
        ∑ r, (S.sg (S.sub p) (S.sub r) - S.sg (S.sub q) (S.sub r)) * A p r * A r q| ≤
      2 * (forcedC a b c ‖opE A‖ H * H ^ 2 + H * ‖opE (At - A)‖ * m * Real.exp (H * m)) := by
  have h1 := abs_le.1 (h.forced_antisym_entry hskew hne hnp hnp')
  have h2 := abs_le.1 (h.abs_step_entry_sub_le hX hAt hA p q)
  have h3 := abs_le.1 (h.abs_step_entry_sub_le hX hAt hA q p)
  refine le_of_mul_le_mul_left ?_ hH
  rw [← abs_of_pos hH, ← abs_mul, abs_of_pos hH, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The amount** (Corollary 5.3 as stated, with its remainder; coordinate directions). For a
consistent scheme with skew coupling and a modified system `Ã`, `Δ = Ã - A`, numerical damping
`ν = -tr Δ` and any bound `lam` of the injection rate (`xᵀ Δ x ≤ lam xᵀ x` for all `x`), and
states `p`, `q` of different subsystems that are not partners:
`½H |Σ_r (ς(sub p, sub r) + ς(sub q, sub r)) A p r A r q| - 2 (C H² + H ‖Δ‖ m e^{Hm}) ≤
n lam - tr Δ`, that is `ν + n ι ≥ ½H |Σ_k (ς_ik + ς_jk) A_ik A_kj| - O(H²)` with the `O(H²)`
explicit (`‖Δ‖ = O(H)` for a consistent family). -/
theorem Consistent.amount (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {At : Matrix (Fin n) (Fin n) ℝ} (hX : S.X = NormedSpace.exp (H • At)) (hH : 0 < H) {m : ℝ}
    (hAt : ‖opE At‖ ≤ m) (hA : ‖opE A‖ ≤ m) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, x ⬝ᵥ ((At - A) *ᵥ x) ≤ lam * (x ⬝ᵥ x)) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q))
    (hnp' : ¬ S.partner (S.sub q) (S.sub p)) :
    H / 2 * |∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q| -
        2 * (forcedC a b c ‖opE A‖ H * H ^ 2 + H * ‖opE (At - A)‖ * m * Real.exp (H * m)) ≤
      n * lam - (At - A).trace := by
  have hpq : p ≠ q := fun h' => hne (h' ▸ rfl)
  have h1 := h.difference_sym_entry hskew hX hH hAt hA hne hnp hnp'
  have h2 := triple_law (At - A) hlam hpq
  have h3 : H / 2 *
      |∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q| =
      |H / 2 * ∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < H / 2)]
  rw [h3]
  have h4 := abs_sub_abs_le_abs_sub
    (H / 2 * ∑ r, (S.sg (S.sub p) (S.sub r) + S.sg (S.sub q) (S.sub r)) * A p r * A r q)
    ((At - A) p q + (At - A) q p)
  rw [abs_sub_comm] at h4
  linarith

end Parts

end HeldScheme

end CoSimFoundations
