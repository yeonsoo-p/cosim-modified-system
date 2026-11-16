/-
The trade between injection and damping on the two subsystems concerned (the paper, Section
"The trade between injection and damping", Theorem `thm:triple` and Corollary `cor:amount`).

**Statement.** `T` a real symmetric `n × n` matrix on states grouped into subsystems, `ι` a real
with `-ι |x|² ≤ xᵀ T x` for all `x` (as `ι = -λ_min (T)`), `i ≠ j` two subsystems with `n_i` and
`n_j` states, `T_ii`, `T_jj` the diagonal blocks and `T_ij` the block between the two. Then
  `2 ‖T_ij‖ ≤ tr T_ii + tr T_jj + (n_i + n_j) ι ≤ tr T + n ι`.
Only the two subsystems enter the middle term.

**Proof.** Let `d` be the `0/1` weight of the states of `i` and `j`, `D = diag d` and
  `T' = D T D - ι (1 - D)`.
Then `xᵀ T' x = (D x)ᵀ T (D x) - ι |(1 - D) x|² ≥ -ι |x|²`, `T'` is symmetric,
`tr T' + n ι = Σ_p d_p (T_pp + ι)`, and `eᵀ T' f = eᵀ T f` for `e`, `f` supported on the states of
weight one. The trace form of Theorem `thm:triple` (`damping_add_injection_ge`) for `T'` is the
first inequality (`two_mul_abs_le_sum_weight`); the second holds because `T_pp + ι ≥ 0` for every
state (`sum_weight_le_trace`).

**Forms.**
* `HeldScheme.pair_trace_law`: for unit vectors `e` supported on `i` and `f` on `j`, in the
  form of `TripleLawGeneral` (dot products): `2 |eᵀ T f| ≤ tr T_ii + tr T_jj + (n_i + n_j) ι`.
* `HeldScheme.pair_trace_le_trace`: the right side is at most `tr T + n ι`.
* `HeldScheme.two_mul_abs_inner_opE_le_pair_trace`: the same for operators on Euclidean space,
  in the form of `AmountLead`.
* `HeldScheme.two_mul_norm_cblock_le_pair_trace`: `2 ‖T_ij‖ ≤ tr T_ii + tr T_jj + (n_i + n_j) ι`
  with the spectral norm of the block.
* `HeldScheme.Consistent.amount_pair_trace`: for the numerical dissipation `Δ_R` of a consistent
  scheme with power-conserving coupling and two subsystems that are not partners,
  `(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ tr [Δ_R]_ii + tr [Δ_R]_jj + (n_i + n_j) ι`.
Here `tr T_ii` is `blockTrace T i` (the trace of the padded block, `trace_cblock_self`) and `n_i`
is `blockCard i`.
-/
import CoSimFoundations.AmountLead
import CoSimFoundations.ForcedNorm

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {n : ℕ}

/-! ### A weight on the states -/

/-- If `-ι |x|² ≤ xᵀ T x` for all `x`, every diagonal entry obeys `0 ≤ T_pp + ι`. -/
theorem diag_add_nonneg (T : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x)) (p : Fin n) : 0 ≤ T p p + ι := by
  have h := hι (Pi.single p 1)
  rw [single_one_dotProduct, single_one_dotProduct, Pi.single_eq_same, Matrix.mulVec_single_one]
    at h
  simp only [Matrix.col_apply] at h
  linarith

/-- The bilinear form of `D T D - ι (1 - D)`, `D = diag d`. -/
theorem dotProduct_compress (T : Matrix (Fin n) (Fin n) ℝ) (ι : ℝ) (d x y : Fin n → ℝ) :
    x ⬝ᵥ ((diagonal d * T * diagonal d - diagonal fun p => ι * (1 - d p)) *ᵥ y) =
      (d * x) ⬝ᵥ (T *ᵥ (d * y)) - ∑ p, ι * (1 - d p) * (x p * y p) := by
  have hD : ∀ u : Fin n → ℝ, diagonal d *ᵥ u = d * u := fun u => by
    funext p
    rw [mulVec_diagonal, Pi.mul_apply]
  have hA : ∀ u : Fin n → ℝ, x ⬝ᵥ (d * u) = (d * x) ⬝ᵥ u := fun u => by
    simp only [dotProduct, Pi.mul_apply]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hB : x ⬝ᵥ ((diagonal fun p => ι * (1 - d p)) *ᵥ y) = ∑ p, ι * (1 - d p) * (x p * y p) := by
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [Matrix.sub_mulVec, dotProduct_sub, hB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD,
    hD, hA]

/-- **The trade on the states of weight one.** Let `T` be symmetric with `-ι |x|² ≤ xᵀ T x` for
all `x`, `d` a weight with `d_p² = d_p` (zero or one), and `e`, `f` orthonormal vectors supported
on the states of weight one. Then `2 |eᵀ T f| ≤ Σ_p d_p (T_pp + ι)`. -/
theorem two_mul_abs_le_sum_weight (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x)) (d : Fin n → ℝ)
    (hd : ∀ p, d p * d p = d p) {e f : Fin n → ℝ} (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1)
    (hef : e ⬝ᵥ f = 0) (hde : ∀ p, d p * e p = e p) (hdf : ∀ p, d p * f p = f p) :
    2 * |e ⬝ᵥ (T *ᵥ f)| ≤ ∑ p, d p * (T p p + ι) := by
  have hsymm : (diagonal d * T * diagonal d - diagonal fun p => ι * (1 - d p)).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_transpose, Matrix.diagonal_transpose, hT.eq, Matrix.mul_assoc]
  have hlo : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤
      x ⬝ᵥ ((diagonal d * T * diagonal d - diagonal fun p => ι * (1 - d p)) *ᵥ x) := by
    intro x
    rw [dotProduct_compress]
    have h1 := hι (d * x)
    have h2 : -ι * (x ⬝ᵥ x) = -ι * ((d * x) ⬝ᵥ (d * x)) - ∑ p, ι * (1 - d p) * (x p * x p) := by
      simp only [dotProduct, Pi.mul_apply, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by linear_combination (ι * x p * x p) * hd p
    linarith
  have h := damping_add_injection_ge _ hsymm hlo he hf hef
  have e1 : d * e = e := funext fun p => hde p
  have e2 : d * f = f := funext fun p => hdf p
  have e3 : ∑ p, ι * (1 - d p) * (e p * f p) = 0 :=
    Finset.sum_eq_zero fun p _ => by linear_combination (-(ι * e p)) * hdf p
  have e4 : (diagonal d * T * diagonal d - diagonal fun p => ι * (1 - d p)).trace + n * ι =
      ∑ p, d p * (T p p + ι) := by
    have hn : (n : ℝ) * ι = ∑ _p : Fin n, ι := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hn, Matrix.trace, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.diag_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_apply_eq]
    linear_combination (T p p) * hd p
  rw [dotProduct_compress, e1, e2, e3, sub_zero, e4] at h
  exact h

/-- The weighted sum is at most the trace form: if `-ι |x|² ≤ xᵀ T x` for all `x` and
`d_p² = d_p`, then `Σ_p d_p (T_pp + ι) ≤ tr T + n ι`. -/
theorem sum_weight_le_trace (T : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x)) (d : Fin n → ℝ)
    (hd : ∀ p, d p * d p = d p) : ∑ p, d p * (T p p + ι) ≤ T.trace + n * ι := by
  have hn : (n : ℝ) * ι = ∑ _p : Fin n, ι := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hn, Matrix.trace, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  have h0 := diag_add_nonneg T hι p
  have h1 : d p ≤ 1 := by nlinarith [sq_nonneg (1 - d p), hd p]
  rw [Matrix.diag_apply]
  nlinarith

/-- The weighted sum is not negative. -/
theorem sum_weight_nonneg (T : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x)) (d : Fin n → ℝ)
    (hd : ∀ p, d p * d p = d p) : 0 ≤ ∑ p, d p * (T p p + ι) :=
  Finset.sum_nonneg fun p _ =>
    mul_nonneg (by nlinarith [sq_nonneg (d p), hd p]) (diag_add_nonneg T hι p)

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### Two subsystems -/

/-- The trace of the diagonal block of subsystem `i`: `tr T_ii = Σ_{p in i} T_pp`. -/
def blockTrace (T : Matrix (Fin n) (Fin n) ℝ) (i : κ) : ℝ :=
  ∑ p, if S.sub p = i then T p p else 0

/-- The number of states of subsystem `i`. -/
def blockCard (i : κ) : ℕ := (Finset.univ.filter fun p => S.sub p = i).card

/-- The trace of the padded diagonal block is the trace of the block. -/
theorem trace_cblock_self (T : Matrix (Fin n) (Fin n) ℝ) (i : κ) :
    (S.cblock i i T).trace = S.blockTrace T i := by
  rw [Matrix.trace, blockTrace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, S.cblock_apply]
  by_cases h : S.sub p = i
  · rw [ite_eq_left h, ite_eq_left h, one_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, zero_mul, zero_mul]

/-- The weighted sum for the weight of two different subsystems. -/
theorem sum_pair_weight (T : Matrix (Fin n) (Fin n) ℝ) (ι : ℝ) (i j : κ) :
    ∑ p, ((if S.sub p = i then (1 : ℝ) else 0) + (if S.sub p = j then (1 : ℝ) else 0)) *
        (T p p + ι) =
      S.blockTrace T i + S.blockTrace T j + ((S.blockCard i : ℝ) + S.blockCard j) * ι := by
  have hc : ∀ k : κ, (S.blockCard k : ℝ) = ∑ p, if S.sub p = k then (1 : ℝ) else 0 := fun k => by
    rw [blockCard, Finset.sum_boole]
  rw [hc i, hc j, blockTrace, blockTrace, add_mul, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hi : S.sub p = i
  · by_cases hj : S.sub p = j
    · simp only [ite_eq_left hi, ite_eq_left hj]
      ring
    · simp only [ite_eq_left hi, ite_eq_right hj]
      ring
  · by_cases hj : S.sub p = j
    · simp only [ite_eq_right hi, ite_eq_left hj]
      ring
    · simp only [ite_eq_right hi, ite_eq_right hj]
      ring

/-- The weight of two different subsystems is zero or one. -/
theorem pair_weight_mul_self {i j : κ} (hij : i ≠ j) (p : Fin n) :
    ((if S.sub p = i then (1 : ℝ) else 0) + (if S.sub p = j then (1 : ℝ) else 0)) *
        ((if S.sub p = i then (1 : ℝ) else 0) + (if S.sub p = j then (1 : ℝ) else 0)) =
      (if S.sub p = i then (1 : ℝ) else 0) + (if S.sub p = j then (1 : ℝ) else 0) := by
  by_cases hi : S.sub p = i
  · have hj : S.sub p ≠ j := fun h => hij (hi.symm.trans h)
    rw [ite_eq_left hi, ite_eq_right hj, add_zero, mul_one]
  · by_cases hj : S.sub p = j
    · rw [ite_eq_right hi, ite_eq_left hj, zero_add, mul_one]
    · rw [ite_eq_right hi, ite_eq_right hj, add_zero, mul_zero]

/-- **The trade on the two subsystems concerned** (the local form of Theorem `thm:triple`, in
the form of `damping_add_injection_ge`). Let `T` be symmetric with `-ι |x|² ≤ xᵀ T x` for all
`x`, `i ≠ j` subsystems, `e` a unit vector supported on `i` and `f` one supported on `j`. Then
`2 |eᵀ T f| ≤ tr T_ii + tr T_jj + (n_i + n_j) ι`. -/
theorem pair_trace_law (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x)) {i j : κ} (hij : i ≠ j)
    {e f : Fin n → ℝ} (hei : ∀ p, S.sub p ≠ i → e p = 0) (hfj : ∀ p, S.sub p ≠ j → f p = 0)
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) :
    2 * |e ⬝ᵥ (T *ᵥ f)| ≤
      S.blockTrace T i + S.blockTrace T j + ((S.blockCard i : ℝ) + S.blockCard j) * ι := by
  have hef : e ⬝ᵥ f = 0 := Finset.sum_eq_zero fun p _ => by
    by_cases hi : S.sub p = i
    · rw [hfj p fun h => hij (hi.symm.trans h), mul_zero]
    · rw [hei p hi, zero_mul]
  have hde : ∀ p, ((if S.sub p = i then (1 : ℝ) else 0) + (if S.sub p = j then (1 : ℝ) else 0)) *
      e p = e p := fun p => by
    by_cases hi : S.sub p = i
    · have hj : S.sub p ≠ j := fun h => hij (hi.symm.trans h)
      rw [ite_eq_left hi, ite_eq_right hj, add_zero, one_mul]
    · rw [hei p hi, mul_zero]
  have hdf : ∀ p, ((if S.sub p = i then (1 : ℝ) else 0) + (if S.sub p = j then (1 : ℝ) else 0)) *
      f p = f p := fun p => by
    by_cases hj : S.sub p = j
    · have hi : S.sub p ≠ i := fun h => hij (h.symm.trans hj)
      rw [ite_eq_right hi, ite_eq_left hj, zero_add, one_mul]
    · rw [hfj p hj, mul_zero]
  have h := two_mul_abs_le_sum_weight T hT hι _ (S.pair_weight_mul_self hij) he hf hef hde hdf
  rwa [S.sum_pair_weight] at h

/-- **The trade on two subsystems is not weaker than the trade on all:** if
`-ι |x|² ≤ xᵀ T x` for all `x` and `i ≠ j`, then
`tr T_ii + tr T_jj + (n_i + n_j) ι ≤ tr T + n ι`. -/
theorem pair_trace_le_trace (T : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x)) {i j : κ} (hij : i ≠ j) :
    S.blockTrace T i + S.blockTrace T j + ((S.blockCard i : ℝ) + S.blockCard j) * ι ≤
      T.trace + n * ι := by
  have h := sum_weight_le_trace T hι _ (S.pair_weight_mul_self hij)
  rwa [S.sum_pair_weight] at h

/-- The local trace form is not negative. -/
theorem pair_trace_nonneg (T : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x)) {i j : κ} (hij : i ≠ j) :
    0 ≤ S.blockTrace T i + S.blockTrace T j + ((S.blockCard i : ℝ) + S.blockCard j) * ι := by
  have h := sum_weight_nonneg T hι _ (S.pair_weight_mul_self hij)
  rwa [S.sum_pair_weight] at h

/-! ### Operators on Euclidean space -/

/-- The lower bound of the form of an operator, for dot products. -/
theorem dotProduct_lower_of_inner {T : Matrix (Fin n) (Fin n) ℝ} {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE T v⟫) (x : Fin n → ℝ) :
    -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x) := by
  have h := hlo (WithLp.toLp 2 x)
  rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct, inner_opE_eq_dotProduct] at h
  exact h

/-- **The trade on the two subsystems concerned, for operators** (in the form of
`two_mul_abs_inner_opE_le_trace_add`). If `T` is symmetric and `-ι ‖v‖² ≤ ⟪v, T v⟫` for all `v`,
then for subsystems `i ≠ j`, a unit vector `x` supported on `i` and a unit vector `y` supported
on `j`: `2 |⟪x, T y⟫| ≤ tr T_ii + tr T_jj + (n_i + n_j) ι`. -/
theorem two_mul_abs_inner_opE_le_pair_trace {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm)
    {ι : ℝ} (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE T v⟫) {i j : κ}
    (hij : i ≠ j) {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    2 * |⟪x, opE T y⟫| ≤
      S.blockTrace T i + S.blockTrace T j + ((S.blockCard i : ℝ) + S.blockCard j) * ι := by
  have he : WithLp.ofLp x ⬝ᵥ WithLp.ofLp x = 1 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq, hx1, one_pow]
  have hf : WithLp.ofLp y ⬝ᵥ WithLp.ofLp y = 1 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq, hy1, one_pow]
  rw [inner_opE_eq_dotProduct]
  exact S.pair_trace_law T hT (dotProduct_lower_of_inner hlo) hij hx hy he hf

/-- **The trade on the two subsystems concerned, with the norm of the block:** if `T` is
symmetric and `-ι ‖v‖² ≤ ⟪v, T v⟫` for all `v`, then for subsystems `i ≠ j`
`2 ‖T_ij‖ ≤ tr T_ii + tr T_jj + (n_i + n_j) ι`, with the spectral norm of the block. -/
theorem two_mul_norm_cblock_le_pair_trace {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm)
    {ι : ℝ} (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE T v⟫) {i j : κ}
    (hij : i ≠ j) :
    2 * ‖opE (S.cblock i j T)‖ ≤
      S.blockTrace T i + S.blockTrace T j + ((S.blockCard i : ℝ) + S.blockCard j) * ι := by
  have hR := S.pair_trace_nonneg T (dotProduct_lower_of_inner hlo) hij
  have key : ‖opE (S.cblock i j T)‖ ≤
      (S.blockTrace T i + S.blockTrace T j + ((S.blockCard i : ℝ) + S.blockCard j) * ι) / 2 := by
    refine (S.norm_opE_cblock_le_iff i j T (by linarith)).2 fun x y hx hy => ?_
    by_cases hx0 : x = 0
    · rw [hx0, inner_zero_left, abs_zero, norm_zero, zero_mul, mul_zero]
    by_cases hy0 : y = 0
    · rw [hy0, map_zero, inner_zero_right, abs_zero, norm_zero, mul_zero, mul_zero]
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hx' : ∀ p, S.sub p ≠ i → (‖x‖⁻¹ • x) p = 0 := fun p hp => by
      rw [PiLp.smul_apply, hx p hp, smul_zero]
    have hy' : ∀ q, S.sub q ≠ j → (‖y‖⁻¹ • y) q = 0 := fun q hq => by
      rw [PiLp.smul_apply, hy q hq, smul_zero]
    have hx1 : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
    have hy1 : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
    have h := S.two_mul_abs_inner_opE_le_pair_trace hT hlo hij hx' hy' hx1 hy1
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, abs_mul, abs_mul,
      abs_of_pos (inv_pos.2 hxn), abs_of_pos (inv_pos.2 hyn)] at h
    have h2 : |⟪x, opE T y⟫| = ‖x‖ * ‖y‖ * (‖x‖⁻¹ * (‖y‖⁻¹ * |⟪x, opE T y⟫|)) := by
      field_simp
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h (mul_nonneg hxn.le hyn.le)
    linarith
  linarith

/-! ### The numerical dissipation of a scheme -/

/-- **The amount on the two subsystems concerned** (the paper, Corollary `cor:amount`, with the
traces of the two diagonal blocks in place of the total damping). For a consistent scheme with
power-conserving coupling, `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, subsystems `i ≠ j` that are not
partners, unit vectors `x` supported on `i` and `y` on `j`,
`Δ_R = numDissipation A (modifiedSystem H S.X)` and a real `ι` with `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫` for
all `v`: `(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ tr [Δ_R]_ii + tr [Δ_R]_jj + (n_i + n_j) ι`,
`K = amountC a b c ‖A‖`. -/
theorem Consistent.amount_pair_trace {S : HeldScheme n κ} {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      S.blockTrace (numDissipation A (modifiedSystem H S.X)) i +
        S.blockTrace (numDissipation A (modifiedSystem H S.X)) j +
        ((S.blockCard i : ℝ) + S.blockCard j) * ι :=
  (h.amount_block hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1).trans
    (S.two_mul_abs_inner_opE_le_pair_trace (isSymm_numDissipation A _) hlo hij hx hy hx1 hy1)

end HeldScheme

end CoSimFoundations
