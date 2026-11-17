/-
The unavoidable error of a scheme with one held sample, with an explicit remainder
(the paper, Proposition 4.4, one-step form: the paper proves it "to leading order in `H`").

Setting. States `Fin n`, grouped into subsystems by `sub : Fin n → κ` (scalar stores: `sub = id`).
A scheme with one held sample is given by matrices `F` (zero between different subsystems), `N`
(the use of new samples: `N p q = 0` unless `sub q` is a partner of `sub p` that runs at an earlier
stage) and `M` (the use of old samples: `M p q = 0` unless `sub q` is a partner of `sub p` that does
not run at an earlier stage), and its one-step map `X` obeys `X = F + M + N * X`, that is
`X = (1 - N)⁻¹ (F + M)`, the one-step map of Section 2.2. `U = exp (H • A)` is the monolithic
step; `A` vanishes between different subsystems that are not partners. All norms are spectral
norms, `‖opE ·‖`.

1. **Exact remainder of the scheme** (`entry_eq_mul`). For `p`, `q` in different subsystems that
   are not partners,
     `X p q = (N * (M + N)) p q + (N * N * (X - 1)) p q`,
   because `F`, `M`, `N` and `N * F` vanish there. No expansion of the inverse is needed.

2. **Coupling coefficients** (`coupling_eq`). With `E = X - 1 - H • A - N * (X - 1)`:
     `M p q + N p q = H * A p q + E p q`   for `p`, `q` in different subsystems,
   exactly, and `‖E‖ ≤ ‖X - U‖ + ‖U - 1 - H A‖ + ‖N‖ ‖X - 1‖`. This is the paper's
   "consistency gives `M_ik + N_ik = H A_ik + O(H²)`", with the constant.

3. **Expansion with the mask of the early stages** (`entry_expand`). For any `E` as in 2, with
   `early s` the diagonal `0/1` matrix of the states whose subsystem runs before `s`:
     `X p q = H² (A early A) p q + H (E early A) p q + (N E) p q + (N N (X - 1)) p q`.

4. **The forced block** (`forced_block_of_coupling`, `forced_block`, `forced_entry`). If
   `‖N‖ ≤ a H`, `‖X - 1‖ ≤ b H`, `‖E‖ ≤ d H²`, `H ≥ 0`, then for `x` supported on a subsystem `s`
   and `y` on a subsystem `t ≠ s` that is not a partner of `s`,
     `|⟪x, (X - U) y⟫ - ½H² ⟪x, A ς_s A y⟫| ≤ (a² b + d (a + ‖A‖) + ‖A‖³/6 · e^{H‖A‖}) H³ ‖x‖ ‖y‖`,
   `ς_s = diag(±1)`: `+1` on the states whose subsystem runs before `s`, `-1` elsewhere. For a
   scheme with `‖X - U‖ ≤ c H²` (the paper's consistency) `d = c + a b + ‖A‖²/2 · e^{H‖A‖}`.
   In entries: `|X p q - U p q - ½H² Σ_r ς(sub p, sub r) A p r A r q| ≤ C H³`.

Neither `F = 1 + O(H)` nor a bound on `M` is used; subsystems that share a stage, and subsystems
with several states, are covered.
-/
import CoSimFoundations.OrderBarrier
import CoSimFoundations.FloorMatrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

section Taylor

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Taylor remainder of the exponential, order one: `‖exp Z - 1‖ ≤ ‖Z‖ e^{‖Z‖}`. -/
theorem norm_exp_sub_one_le (Z : 𝔸) :
    ‖NormedSpace.exp Z - 1‖ ≤ ‖Z‖ * Real.exp ‖Z‖ := by
  have h := norm_exp_sub_sum_le Z (b := 1) (by norm_num)
  simpa [Finset.sum_range_succ, Nat.factorial] using h

/-- Taylor remainder of the exponential, order two: `‖exp Z - (1 + Z)‖ ≤ ‖Z‖²/2 · e^{‖Z‖}`. -/
theorem norm_exp_sub_linear_le (Z : 𝔸) :
    ‖NormedSpace.exp Z - (1 + Z)‖ ≤ ‖Z‖ ^ 2 / 2 * Real.exp ‖Z‖ := by
  have h := norm_exp_sub_sum_le Z (b := 2) (by norm_num)
  simpa [Finset.sum_range_succ, Nat.factorial] using h

/-- Taylor remainder of the exponential, order three:
`‖exp Z - (1 + Z + ½ Z²)‖ ≤ ‖Z‖³/6 · e^{‖Z‖}`. -/
theorem norm_exp_sub_quadratic_le (Z : 𝔸) :
    ‖NormedSpace.exp Z - (1 + Z + (2 : ℝ)⁻¹ • Z ^ 2)‖ ≤ ‖Z‖ ^ 3 / 6 * Real.exp ‖Z‖ := by
  have h := norm_exp_sub_sum_le Z (b := 3) (by norm_num)
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  simpa [Finset.sum_range_succ, Nat.factorial] using h

/-- `‖exp (H T) - 1‖ ≤ ‖T‖ e^{H‖T‖} · H` for `H ≥ 0`. -/
theorem norm_exp_smul_sub_one_le (T : 𝔸) {H : ℝ} (hH : 0 ≤ H) :
    ‖NormedSpace.exp (H • T) - 1‖ ≤ ‖T‖ * Real.exp (H * ‖T‖) * H := by
  have h := norm_exp_sub_one_le (H • T)
  rw [norm_smul, Real.norm_of_nonneg hH] at h
  linarith

/-- `‖exp (H T) - (1 + H T)‖ ≤ ‖T‖²/2 · e^{H‖T‖} · H²` for `H ≥ 0`. -/
theorem norm_exp_smul_sub_linear_le (T : 𝔸) {H : ℝ} (hH : 0 ≤ H) :
    ‖NormedSpace.exp (H • T) - (1 + H • T)‖ ≤ ‖T‖ ^ 2 / 2 * Real.exp (H * ‖T‖) * H ^ 2 := by
  have h := norm_exp_sub_linear_le (H • T)
  rw [norm_smul, Real.norm_of_nonneg hH] at h
  linarith

/-- `‖exp (H T) - (1 + H T + ½H² T²)‖ ≤ ‖T‖³/6 · e^{H‖T‖} · H³` for `H ≥ 0`. -/
theorem norm_exp_smul_sub_quadratic_le (T : 𝔸) {H : ℝ} (hH : 0 ≤ H) :
    ‖NormedSpace.exp (H • T) - (1 + H • T + (H ^ 2 / 2) • (T * T))‖ ≤
      ‖T‖ ^ 3 / 6 * Real.exp (H * ‖T‖) * H ^ 3 := by
  have h := norm_exp_sub_quadratic_le (H • T)
  have e : (2 : ℝ)⁻¹ • (H • T) ^ 2 = (H ^ 2 / 2) • (T * T) := by
    rw [smul_pow, smul_smul, sq T]
    congr 1
    ring
  rw [e, norm_smul, Real.norm_of_nonneg hH] at h
  linarith

end Taylor

variable {n : ℕ}

section Bridge

/-- The operator of a sum of matrices. -/
theorem opE_add (A B : Matrix (Fin n) (Fin n) ℝ) : opE (A + B) = opE A + opE B := map_add _ A B

/-- The operator of a difference of matrices. -/
theorem opE_sub (A B : Matrix (Fin n) (Fin n) ℝ) : opE (A - B) = opE A - opE B := map_sub _ A B

/-- The operator of a product of matrices is the composition. -/
theorem opE_mul (A B : Matrix (Fin n) (Fin n) ℝ) : opE (A * B) = opE A * opE B := map_mul _ A B

/-- The operator of a scalar multiple of a matrix. -/
theorem opE_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : opE (c • A) = c • opE A :=
  map_smul _ c A

/-- The operator of the unit matrix is the identity. -/
theorem opE_one : opE (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := map_one _

/-- The entry of a product with a diagonal matrix in the middle. -/
theorem mul_diagonal_mul_apply (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (p q : Fin n) :
    (A * diagonal v * B) p q = ∑ r, A p r * v r * B r q := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

/-- The map from the matrices to their operators on Euclidean space is continuous. -/
theorem continuous_toEuclideanCLM : Continuous (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) :=
  LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap

/-- The operator of the exponential of a matrix is the exponential of its operator. -/
theorem opE_exp (A : Matrix (Fin n) (Fin n) ℝ) :
    opE (NormedSpace.exp A) = NormedSpace.exp (opE A) := by
  open scoped Matrix.Norms.Operator in
  let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
    NormedAlgebra.restrictScalars ℚ ℝ (Matrix (Fin n) (Fin n) ℝ)
  exact NormedSpace.map_exp (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) continuous_toEuclideanCLM A

/-- `‖U - 1‖ ≤ ‖A‖ e^{H‖A‖} · H` for `U = exp (H • A)`, `H ≥ 0`. -/
theorem norm_opE_exp_sub_one_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE (NormedSpace.exp (H • A) - 1)‖ ≤ ‖opE A‖ * Real.exp (H * ‖opE A‖) * H := by
  rw [opE_sub, opE_exp, opE_one, opE_smul]
  exact norm_exp_smul_sub_one_le (opE A) hH

/-- `‖U - (1 + H A)‖ ≤ ‖A‖²/2 · e^{H‖A‖} · H²` for `U = exp (H • A)`, `H ≥ 0`. -/
theorem norm_opE_exp_sub_linear_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE (NormedSpace.exp (H • A) - (1 + H • A))‖ ≤
      ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2 := by
  rw [opE_sub, opE_exp, opE_add, opE_one, opE_smul]
  exact norm_exp_smul_sub_linear_le (opE A) hH

/-- `‖U - (1 + H A + ½H² A²)‖ ≤ ‖A‖³/6 · e^{H‖A‖} · H³` for `U = exp (H • A)`, `H ≥ 0`. -/
theorem norm_opE_exp_sub_quadratic_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE (NormedSpace.exp (H • A) - (1 + H • A + (H ^ 2 / 2) • (A * A)))‖ ≤
      ‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖) * H ^ 3 := by
  rw [opE_sub, opE_exp, opE_add, opE_add, opE_one, opE_smul, opE_smul, opE_mul]
  exact norm_exp_smul_sub_quadratic_le (opE A) hH

/-- The matrix element of an operator of a matrix as a double sum. -/
theorem inner_opE_eq_sum (T : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE T y⟫ = ∑ p, ∑ q, x p * T p q * y q := by
  rw [inner_toEuclideanCLM]
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- Two matrices have the same matrix element between `x` and `y` if their entries agree wherever
the components of `x` and of `y` do not vanish. -/
theorem inner_opE_congr_of_ne_zero {x y : EuclideanSpace ℝ (Fin n)}
    {T T' : Matrix (Fin n) (Fin n) ℝ} (h : ∀ p q, x p ≠ 0 → y q ≠ 0 → T p q = T' p q) :
    ⟪x, opE T y⟫ = ⟪x, opE T' y⟫ := by
  rw [inner_opE_eq_sum, inner_opE_eq_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hp : x p = 0
  · rw [hp, zero_mul, zero_mul, zero_mul, zero_mul]
  · by_cases hq : y q = 0
    · rw [hq, mul_zero, mul_zero]
    · rw [h p q hp hq]

/-- A matrix element between vectors supported on two subsystems depends only on the block of the
matrix between the two. -/
theorem inner_opE_congr {κ : Type*} {sub : Fin n → κ} {s t : κ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, sub p ≠ s → x p = 0)
    (hy : ∀ q, sub q ≠ t → y q = 0) {T T' : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ p q, sub p = s → sub q = t → T p q = T' p q) :
    ⟪x, opE T y⟫ = ⟪x, opE T' y⟫ :=
  inner_opE_congr_of_ne_zero fun p q hp hq =>
    h p q (not_imp_comm.1 (hx p) hp) (not_imp_comm.1 (hy q) hq)

/-- `|⟪x, T y⟫| ≤ ‖T‖ ‖x‖ ‖y‖`. -/
theorem abs_inner_opE_le (T : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE T y⟫| ≤ ‖opE T‖ * (‖x‖ * ‖y‖) := by
  calc |⟪x, opE T y⟫| ≤ ‖x‖ * ‖opE T y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖opE T‖ * ‖y‖) := by gcongr; exact (opE T).le_opNorm y
    _ = ‖opE T‖ * (‖x‖ * ‖y‖) := by ring

/-- The spectral norm of a diagonal matrix with entries of modulus at most `c` is at most `c`. -/
theorem norm_opE_diagonal_le (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, |v i| ≤ c) :
    ‖opE (diagonal v)‖ ≤ c := by
  have h : ‖opE (diagonal v)‖ = ‖v‖ := by
    open scoped Matrix.Norms.L2Operator in
    exact (Matrix.l2_opNorm_toEuclideanCLM (diagonal v)).trans (Matrix.l2_opNorm_diagonal v)
  rw [h]
  exact (pi_norm_le_iff_of_nonneg hc).2 fun i => by simpa [Real.norm_eq_abs] using hv i

end Bridge

end OneStep

open OneStep

variable {n : ℕ}

/-- A scheme with one held sample at one macro step, as matrices on the states `Fin n`, which
`sub` groups into subsystems (the paper, Definition 2.1 and Section 2.2): `F` acts inside the
subsystems, `N` carries the new samples (partners at an earlier stage), `M` the old ones (partners
that do not run at an earlier stage), and the one-step map `X` obeys `X = F + M + N * X`. -/
structure HeldScheme (n : ℕ) (κ : Type*) where
  /-- the subsystem of a state -/
  sub : Fin n → κ
  /-- `partner s t`: subsystem `t` is a partner of subsystem `s` -/
  partner : κ → κ → Prop
  /-- the stage of a subsystem within the macro step -/
  stage : κ → ℕ
  /-- the local maps, `diag(F_i)` -/
  F : Matrix (Fin n) (Fin n) ℝ
  /-- the use of new samples, `G^new C` -/
  N : Matrix (Fin n) (Fin n) ℝ
  /-- the use of old samples, `G^old C` -/
  M : Matrix (Fin n) (Fin n) ℝ
  /-- the one-step map -/
  X : Matrix (Fin n) (Fin n) ℝ
  /-- `F` vanishes between different subsystems -/
  hF : ∀ p q, sub p ≠ sub q → F p q = 0
  /-- new samples come only from partners at an earlier stage -/
  hN : ∀ p q, ¬ (partner (sub p) (sub q) ∧ stage (sub q) < stage (sub p)) → N p q = 0
  /-- old samples come only from partners that do not run at an earlier stage -/
  hM : ∀ p q, ¬ (partner (sub p) (sub q) ∧ ¬ stage (sub q) < stage (sub p)) → M p q = 0
  /-- the one-step map: `(1 - N) X = F + M` -/
  hX : X = F + M + N * X

namespace HeldScheme

variable {κ : Type*} (S : HeldScheme n κ)

/-- The diagonal `0/1` matrix of the states whose subsystem runs at an earlier stage than `s`. -/
def early (s : κ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun r => if S.stage (S.sub r) < S.stage s then 1 else 0

/-- The sign `ς_{sk}` of the paper: `+1` if `k` runs at an earlier stage than `s`, else `-1`. -/
def sg (s k : κ) : ℝ := if S.stage k < S.stage s then 1 else -1

/-- The diagonal matrix of the signs `ς_{s, sub r}`. -/
def sgn (s : κ) : Matrix (Fin n) (Fin n) ℝ := diagonal fun r => S.sg s (S.sub r)

/-- Between two subsystems at the same stage the sign is `-1`: each uses a held sample of the
other. -/
theorem sg_of_stage_eq {s k : κ} (h : S.stage s = S.stage k) : S.sg s k = -1 := by
  have hn : ¬ S.stage k < S.stage s := by
    rw [h]
    exact lt_irrefl _
  unfold sg
  exact ite_eq_right hn

/-- In Jacobi mode all signs are `-1`. -/
theorem sg_of_jacobi {S : HeldScheme n κ} (hJ : ∀ s t, S.stage s = S.stage t) (s k : κ) :
    S.sg s k = -1 :=
  S.sg_of_stage_eq (hJ s k)

/-- The square of a sign is one. -/
theorem abs_sg (s k : κ) : |S.sg s k| = 1 := by
  by_cases h : S.stage k < S.stage s <;> simp [sg, h]

/-- If `k` runs before exactly one of `i` and `j` (it runs between them), the two signs towards
`k` are opposite: `ς_{jk} = -ς_{ik}`. -/
theorem sg_eq_neg_sg_of_not_iff {i j k : κ}
    (h : ¬ (S.stage k < S.stage i ↔ S.stage k < S.stage j)) : S.sg j k = -S.sg i k := by
  unfold sg
  by_cases hi : S.stage k < S.stage i
  · have hj : ¬ S.stage k < S.stage j := fun hj => h ⟨fun _ => hj, fun _ => hi⟩
    rw [ite_eq_left hi, ite_eq_right hj]
  · have hj : S.stage k < S.stage j := by
      by_contra hj
      exact h ⟨fun e => absurd e hi, fun e => absurd e hj⟩
    rw [ite_eq_right hi, ite_eq_left hj, neg_neg]

/-- If `k` runs before exactly one of `s` and `t`, the two signs towards `k` cancel:
`ς_{sk} + ς_{tk} = 0`. -/
theorem sg_add_sg_eq_zero {s t k : κ}
    (h : S.stage k < S.stage s ↔ ¬ S.stage k < S.stage t) : S.sg s k + S.sg t k = 0 := by
  rw [S.sg_eq_neg_sg_of_not_iff (i := s) (j := t) fun h' => iff_not_self (h'.symm.trans h),
    add_neg_cancel]

/-- `|tr T| ≤ n K` for an `n × n` matrix whose diagonal entries are at most `K` in modulus. -/
theorem abs_trace_le_of_diag {T : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (h : ∀ p, |T p p| ≤ K) :
    |Matrix.trace T| ≤ (n : ℝ) * K := by
  rw [Matrix.trace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ p, |Matrix.diag T p| ≤ ∑ _p : Fin n, K := Finset.sum_le_sum fun p _ => h p
  refine h1.trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|tr T| ≤ n ‖T‖` in the spectral norm. -/
theorem _root_.CoSimFoundations.OneStep.abs_trace_le (T : Matrix (Fin n) (Fin n) ℝ) :
    |T.trace| ≤ n * ‖opE T‖ := by
  refine abs_trace_le_of_diag fun p => ?_
  have h2 := abs_inner_opE_le T (unitE p) (unitE p)
  rwa [inner_unitE_opE, norm_unitE, mul_one, mul_one] at h2

/-- States `p` of a subsystem `s` and `q` of a subsystem `t ≠ s` that is not a partner of `s`:
their subsystems differ and are not partners, and the states differ. -/
theorem sub_ne_of_eq {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) {p q : Fin n}
    (hp : S.sub p = s) (hq : S.sub q = t) :
    S.sub p ≠ S.sub q ∧ ¬ S.partner (S.sub p) (S.sub q) ∧ p ≠ q := by
  subst hp hq
  exact ⟨hst, hnp, fun h => hst (congrArg S.sub h)⟩

/-- The signs are twice the mask of the early stages minus one: `ς_s = 2 early_s - 1`. -/
theorem sgn_eq (s : κ) : S.sgn s = (2 : ℝ) • S.early s - 1 := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    by_cases h : S.stage (S.sub p) < S.stage s
    · simp [sgn, sg, early, h]
      norm_num
    · simp [sgn, sg, early, h]
  · simp [sgn, early, hpq]

/-- The mask of the early stages is a coordinate projection: its spectral norm is at most one. -/
theorem norm_opE_early_le (s : κ) : ‖opE (S.early s)‖ ≤ 1 :=
  norm_opE_diagonal_le _ zero_le_one fun i => by
    by_cases h : S.stage (S.sub i) < S.stage s <;> simp [h]

/-- **Exact remainder of the scheme.** Between two different subsystems that are not partners,
`X = N (M + N) + N N (X - 1)` entrywise: the scheme passes a state across two links only through
new samples, and everything else has three factors. -/
theorem entry_eq_mul {p q : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) :
    S.X p q = (S.N * (S.M + S.N)) p q + (S.N * S.N * (S.X - 1)) p q := by
  have hNF : (S.N * S.F) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : S.sub r = S.sub q
    · rw [S.hN p r (fun h => hnp (hr ▸ h.1)), zero_mul]
    · rw [S.hF r q hr, mul_zero]
  have h1 : S.X p q = (S.N * S.X) p q := by
    have h := congrFun (congrFun S.hX p) q
    rw [Matrix.add_apply, Matrix.add_apply, S.hF p q hne, S.hM p q (fun h => hnp h.1), zero_add,
      zero_add] at h
    exact h
  have h2 : S.N * (S.M + S.N) + S.N * S.N * (S.X - 1) =
      S.N * (S.F + S.M + S.N * S.X) - S.N * S.F := by
    noncomm_ring
  rw [← Matrix.add_apply, h2, ← S.hX, Matrix.sub_apply, hNF, sub_zero]
  exact h1

/-- **Coupling coefficients, exactly.** Between different subsystems the coefficients of the
samples are `M + N = H A + E` with `E = X - 1 - H A - N (X - 1)`, for any matrix `A` and any `H`. -/
theorem coupling_eq (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) :
    S.M p q + S.N p q = H * A p q + (S.X - 1 - H • A - S.N * (S.X - 1)) p q := by
  have hpq : p ≠ q := fun h => hne (h ▸ rfl)
  have h := congrFun (congrFun S.hX p) q
  rw [Matrix.add_apply, Matrix.add_apply, S.hF p q hne, zero_add] at h
  have h2 : S.N * (S.X - 1) = S.N * S.X - S.N := by rw [Matrix.mul_sub, Matrix.mul_one]
  rw [h2]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hpq, smul_eq_mul]
  linarith

/-- **The new samples from the coupling coefficients.** If `M + N = H A + E` between different
subsystems, then `N p r = H A p r + E p r` if the subsystem of `r` runs before the subsystem of
`p`, and `N p r = 0` if not. -/
theorem N_apply_eq_ite {A E : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hE : ∀ p q, S.sub p ≠ S.sub q → S.M p q + S.N p q = H * A p q + E p q) (p r : Fin n) :
    S.N p r =
      (if S.stage (S.sub r) < S.stage (S.sub p) then 1 else 0) * (H * A p r + E p r) := by
  by_cases hr : S.stage (S.sub r) < S.stage (S.sub p)
  · have hpr : S.sub p ≠ S.sub r := fun h => by
      rw [h] at hr
      exact lt_irrefl _ hr
    have hM0 : S.M p r = 0 := S.hM p r (fun h => h.2 hr)
    simp only [hr, ↓reduceIte, one_mul]
    rw [← hE p r hpr, hM0, zero_add]
  · simp only [hr, ↓reduceIte, zero_mul]
    exact S.hN p r (fun h => hr h.2)

/-- **Expansion with the mask of the early stages.** If `M + N = H A + E` between different
subsystems, then between two different subsystems that are not partners
`X = H² A early A + H E early A + N E + N N (X - 1)` entrywise. -/
theorem entry_expand {A E : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hE : ∀ p q, S.sub p ≠ S.sub q → S.M p q + S.N p q = H * A p q + E p q) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q)) :
    S.X p q = H ^ 2 * (A * S.early (S.sub p) * A) p q + H * (E * S.early (S.sub p) * A) p q +
      (S.N * E) p q + (S.N * S.N * (S.X - 1)) p q := by
  rw [S.entry_eq_mul hne hnp]
  congr 1
  have hcol : ∀ r, S.N p r * (S.M + S.N) r q = S.N p r * (H * A r q + E r q) := by
    intro r
    by_cases hr : S.sub r = S.sub q
    · rw [S.hN p r (fun h => hnp (hr ▸ h.1)), zero_mul, zero_mul]
    · rw [Matrix.add_apply, hE r q hr]
  have hNE : (S.N * E) p q = ∑ r, S.N p r * E r q := Matrix.mul_apply
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hcol r)]
  simp only [early, mul_diagonal_mul_apply, hNE, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  linear_combination (H * A r q) * S.N_apply_eq_ite hE p r

/-- `‖H E early_s A‖ ≤ H (d H² · 1 · ‖A‖)` for `H ≥ 0` and `‖E‖ ≤ d H²`: the mask of the early
stages has norm at most one. -/
theorem norm_opE_smul_mul_early_mul_le {E : Matrix (Fin n) (Fin n) ℝ} {H d : ℝ} (hH : 0 ≤ H)
    (hd : ‖opE E‖ ≤ d * H ^ 2) (A : Matrix (Fin n) (Fin n) ℝ) (s : κ) :
    ‖opE (H • (E * S.early s * A))‖ ≤ H * (d * H ^ 2 * 1 * ‖opE A‖) := by
  rw [opE_smul, norm_smul, Real.norm_of_nonneg hH, opE_mul, opE_mul]
  refine mul_le_mul_of_nonneg_left ?_ hH
  refine (norm_mul_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul hd (S.norm_opE_early_le s) (norm_nonneg _) ((norm_nonneg _).trans hd)

/-- The constant of the forced block: `a² b + d (a + α) + α³/6 · e^{Hα}`, with `‖N‖ ≤ a H`,
`‖X - 1‖ ≤ b H`, `‖E‖ ≤ d H²`, `α = ‖A‖`. -/
noncomputable def forcedConst (a b d α H : ℝ) : ℝ :=
  a ^ 2 * b + d * (a + α) + α ^ 3 / 6 * Real.exp (H * α)

/-- **The forced block, from the coupling coefficients** (one-step form of Proposition 4.4 with
its remainder). `U = exp (H • A)`, `A` zero between different subsystems that are not partners,
`M + N = H A + E` between different subsystems, `‖N‖ ≤ a H`, `‖X - 1‖ ≤ b H`, `‖E‖ ≤ d H²`.
For `x` supported on a subsystem `s` and `y` on a subsystem `t ≠ s` that is not a partner of `s`:
`|⟪x, (X - U) y⟫ - ½H² ⟪x, A ς_s A y⟫| ≤ (a² b + d (a + ‖A‖) + ‖A‖³/6 e^{H‖A‖}) H³ ‖x‖ ‖y‖`. -/
theorem forced_block_of_coupling {A U E : Matrix (Fin n) (Fin n) ℝ} {H a b d : ℝ} (hH : 0 ≤ H)
    (hU : U = NormedSpace.exp (H • A))
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hE : ∀ p q, S.sub p ≠ S.sub q → S.M p q + S.N p q = H * A p q + E p q)
    (ha : ‖opE S.N‖ ≤ a * H) (hb : ‖opE (S.X - 1)‖ ≤ b * H) (hd : ‖opE E‖ ≤ d * H ^ 2)
    {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫| ≤
      forcedConst a b d ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  set R : Matrix (Fin n) (Fin n) ℝ := U - (1 + H • A + (H ^ 2 / 2) • (A * A)) with hR
  set T : Matrix (Fin n) (Fin n) ℝ :=
    H • (E * S.early s * A) + S.N * E + S.N * S.N * (S.X - 1) - R with hT
  have key : ∀ p q, S.sub p = s → S.sub q = t →
      (S.X - U - (H ^ 2 / 2) • (A * S.sgn s * A)) p q = T p q := by
    intro p q hp hq
    obtain ⟨hne, hnp', hpq⟩ := S.sub_ne_of_eq hst hnp hp hq
    have hX := S.entry_expand hE hne hnp'
    rw [hp] at hX
    have hUR : U p q = R p q + H ^ 2 / 2 * (A * A) p q := by
      simp only [hR, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hpq, smul_eq_mul, hA p q hne hnp']
      ring
    have hsg : (A * S.sgn s * A) p q = 2 * (A * S.early s * A) p q - (A * A) p q := by
      rw [S.sgn_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [hT, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hX, hUR, hsg]
    ring
  have hin : ⟪x, opE (S.X - U) y⟫ - H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫ =
      ⟪x, opE (S.X - U - (H ^ 2 / 2) • (A * S.sgn s * A)) y⟫ := by
    rw [opE_sub (S.X - U), opE_smul, FunLike.coe_sub, FunLike.coe_smul,
      Pi.sub_apply, Pi.smul_apply, inner_sub_right, inner_smul_right]
  rw [hin, inner_opE_congr hx hy key]
  refine (abs_inner_opE_le T x y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hRn : ‖opE R‖ ≤ ‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖) * H ^ 3 := by
    rw [hR, hU]
    exact norm_opE_exp_sub_quadratic_le A hH
  have haH : 0 ≤ a * H := le_trans (norm_nonneg _) ha
  have h1 := S.norm_opE_smul_mul_early_mul_le hH hd A s
  have h2 : ‖opE (S.N * E)‖ ≤ a * H * (d * H ^ 2) := by
    rw [opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul ha hd (norm_nonneg _) haH)
  have h3 : ‖opE (S.N * S.N * (S.X - 1))‖ ≤ a * H * (a * H) * (b * H) := by
    rw [opE_mul, opE_mul]
    refine (norm_mul_le _ _).trans ?_
    refine mul_le_mul ?_ hb (norm_nonneg _) (mul_nonneg haH haH)
    exact (norm_mul_le _ _).trans (mul_le_mul ha ha (norm_nonneg _) haH)
  have h4 : ‖opE T‖ ≤ ‖opE (H • (E * S.early s * A))‖ + ‖opE (S.N * E)‖ +
      ‖opE (S.N * S.N * (S.X - 1))‖ + ‖opE R‖ := by
    rw [hT, opE_sub, opE_add, opE_add]
    have n1 := norm_sub_le
      (opE (H • (E * S.early s * A)) + opE (S.N * E) + opE (S.N * S.N * (S.X - 1))) (opE R)
    have n2 := norm_add_le
      (opE (H • (E * S.early s * A)) + opE (S.N * E)) (opE (S.N * S.N * (S.X - 1)))
    have n3 := norm_add_le (opE (H • (E * S.early s * A))) (opE (S.N * E))
    linarith
  have h5 : forcedConst a b d ‖opE A‖ H * H ^ 3 = H * (d * H ^ 2 * 1 * ‖opE A‖) +
      a * H * (d * H ^ 2) + a * H * (a * H) * (b * H) +
      ‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖) * H ^ 3 := by
    simp only [forcedConst]
    ring
  rw [h5]
  linarith

/-- Explicit consistency of a scheme with the monolithic system at one macro step `H ≥ 0`: the
paper's `G = O(H)`, `‖X - U‖ = O(H²)` (and `X = 1 + O(H)`, which follows, see
`Consistent.of_step_error`) with their constants; `A` has no block between subsystems that are not
partners. `F = 1 + O(H)` is not needed. -/
structure Consistent (A U : Matrix (Fin n) (Fin n) ℝ) (H a b c : ℝ) : Prop where
  /-- the macro step is not negative -/
  hH : 0 ≤ H
  /-- `U` is the monolithic step -/
  hU : U = NormedSpace.exp (H • A)
  /-- `A` has no block between different subsystems that are not partners -/
  hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0
  /-- the coefficients of the new samples are `O(H)` -/
  ha : ‖opE S.N‖ ≤ a * H
  /-- the one-step map is `1 + O(H)` -/
  hb : ‖opE (S.X - 1)‖ ≤ b * H
  /-- the one-step error is `O(H²)` -/
  hc : ‖opE (S.X - U)‖ ≤ c * H ^ 2

/-- The size of the remainder of the coupling coefficients of a consistent scheme:
`d = c + a b + α²/2 · e^{Hα}`. -/
noncomputable def couplingConst (a b c α H : ℝ) : ℝ := c + a * b + α ^ 2 / 2 * Real.exp (H * α)

/-- The constant of the forced block for a consistent scheme, in terms of `‖N‖ ≤ a H`,
`‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²` and `α = ‖A‖`:
`a² b + (c + a b + α²/2 · e^{Hα}) (a + α) + α³/6 · e^{Hα}`. -/
noncomputable def forcedC (a b c α H : ℝ) : ℝ :=
  forcedConst a b (couplingConst a b c α H) α H

variable {S}

/-- `X = 1 + O(H)` follows from `‖X - U‖ ≤ c H²`: `‖X - 1‖ ≤ (c H + ‖A‖ e^{H‖A‖}) H`. -/
theorem Consistent.of_step_error {A U : Matrix (Fin n) (Fin n) ℝ} {H a c : ℝ} (hH : 0 ≤ H)
    (hU : U = NormedSpace.exp (H • A))
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (ha : ‖opE S.N‖ ≤ a * H) (hc : ‖opE (S.X - U)‖ ≤ c * H ^ 2) :
    S.Consistent A U H a (c * H + ‖opE A‖ * Real.exp (H * ‖opE A‖)) c := by
  refine ⟨hH, hU, hA, ha, ?_, hc⟩
  have h1 : S.X - 1 = (S.X - U) + (U - 1) := by abel
  have h2 : ‖opE (U - 1)‖ ≤ ‖opE A‖ * Real.exp (H * ‖opE A‖) * H := by
    rw [hU]
    exact norm_opE_exp_sub_one_le A hH
  rw [h1, opE_add]
  refine (norm_add_le _ _).trans ?_
  have h3 : (c * H + ‖opE A‖ * Real.exp (H * ‖opE A‖)) * H =
      c * H ^ 2 + ‖opE A‖ * Real.exp (H * ‖opE A‖) * H := by ring
  rw [h3]
  exact add_le_add hc h2

/-- **Consistency of the coupling coefficients, with its constant.** For a consistent scheme the
matrix `E = X - 1 - H A - N (X - 1)`, which is `M + N - H A` between different subsystems
(`coupling_eq`), has `‖E‖ ≤ (c + a b + ‖A‖²/2 · e^{H‖A‖}) H²`. -/
theorem Consistent.norm_coupling_le {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) :
    ‖opE (S.X - 1 - H • A - S.N * (S.X - 1))‖ ≤ couplingConst a b c ‖opE A‖ H * H ^ 2 := by
  have h1 : S.X - 1 - H • A - S.N * (S.X - 1) =
      (S.X - U) + (U - (1 + H • A)) - S.N * (S.X - 1) := by abel
  have h2 : ‖opE (U - (1 + H • A))‖ ≤ ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2 := by
    rw [h.hU]
    exact norm_opE_exp_sub_linear_le A h.hH
  have haH : 0 ≤ a * H := le_trans (norm_nonneg _) h.ha
  have h3 : ‖opE (S.N * (S.X - 1))‖ ≤ a * H * (b * H) := by
    rw [opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul h.ha h.hb (norm_nonneg _) haH)
  rw [h1, opE_sub, opE_add]
  refine (norm_sub_le _ _).trans ?_
  have h4 := norm_add_le (opE (S.X - U)) (opE (U - (1 + H • A)))
  have h5 : couplingConst a b c ‖opE A‖ H * H ^ 2 =
      c * H ^ 2 + ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2 + a * H * (b * H) := by
    simp only [couplingConst]
    ring
  rw [h5]
  linarith [h.hc]

/-- **The forced block** (Proposition 4.4, one-step form, with its remainder). For a consistent
scheme with one held sample, in any order of execution, `x` supported on a subsystem `s` and `y`
on a subsystem `t ≠ s` that is not a partner of `s`:
`|⟪x, (X - U) y⟫ - ½H² ⟪x, A ς_s A y⟫| ≤ C H³ ‖x‖ ‖y‖`,
`C = a² b + (c + a b + ‖A‖²/2 e^{H‖A‖}) (a + ‖A‖) + ‖A‖³/6 e^{H‖A‖}`. In the paper's notation
the left side is the block `Π_s (X - U) Π_tᵀ - ½H² Σ_k ς_{sk} A_{sk} A_{kt}` tested on `x`, `y`. -/
theorem Consistent.forced_block {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫| ≤
      forcedC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) :=
  S.forced_block_of_coupling h.hH h.hU h.hA (fun _ _ hne => S.coupling_eq A H hne) h.ha h.hb
    h.norm_coupling_le hst hnp hx hy

/-- The unit vector of a state is supported on the subsystem of the state. -/
theorem unitE_support (S : HeldScheme n κ) (p r : Fin n) (hr : S.sub r ≠ S.sub p) :
    (unitE p) r = 0 := by
  have hrp : r ≠ p := fun h => hr (h ▸ rfl)
  simp [unitE, hrp]

/-- The entry of `A ς_s A`. -/
theorem sgn_entry (S : HeldScheme n κ) (A : Matrix (Fin n) (Fin n) ℝ) (s : κ) (p q : Fin n) :
    (A * S.sgn s * A) p q = ∑ r, S.sg s (S.sub r) * A p r * A r q := by
  rw [sgn, mul_diagonal_mul_apply]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **The forced block, in entries** (Proposition 4.4, one-step form; for scalar stores
`sub = id` and `p`, `q` are the stores). For states `p`, `q` of different subsystems that are not
partners: `|X p q - U p q - ½H² Σ_r ς(sub p, sub r) A p r A r q| ≤ C H³`. -/
theorem Consistent.forced_entry {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {p q : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) :
    |S.X p q - U p q - H ^ 2 / 2 * ∑ r, S.sg (S.sub p) (S.sub r) * A p r * A r q| ≤
      forcedC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.forced_block hne hnp (S.unitE_support p) (S.unitE_support q)
  rwa [inner_unitE_opE, inner_unitE_opE, norm_unitE, norm_unitE, mul_one, mul_one,
    Matrix.sub_apply, S.sgn_entry] at h1

end HeldScheme

end CoSimFoundations
