/-
The norm bound of the unavoidable error (the paper, Section 5, equation `eq:aij`):
between two subsystems `i ≠ j` that are not partners, every consistent scheme has

  `‖X - U‖ ≥ a_ij H² - C H³`,   `a_ij = ½ ‖Σ_k ς_ik A_ik A_kj‖`.

Setting of `ForcedBlock`, `Reaction`, `HalfStep`: a `HeldScheme` (`X = F + M + N * X`, states
grouped by `sub`), `U = exp (H • A)`, spectral norms `‖opE ·‖`, `S.Consistent A U H a b c`,
`A_ς = signedCoupling A`, `C = reactionC a b c ‖A‖ H`.

**How `a_ij` is expressed.** As the operator norm of a compressed matrix. For subsystems `s`, `t`
and a matrix `T`, `cblock s t T = mask_s T mask_t` is the block `(s, t)` of `T`, padded with
zeros (`cblock_apply`); its spectral norm is the spectral norm of the block
`Π_s T Π_tᵀ`, and

  `forcedCoeff A s t = ½ ‖opE (cblock s t (A_ς A))‖`

is `a_st`: the entries of the block are `(A_ς A) p q = Σ_{r ∉ s} ς(s, sub r) A p r A r q`, that
is `Σ_k ς_sk A_sk A_kt`. The norm of a compressed matrix is the supremum of the matrix elements
between the two subsystems (`norm_opE_cblock_le_iff`): `‖opE (cblock s t T)‖ ≤ K` if and only if
`|⟪x, T y⟫| ≤ K ‖x‖ ‖y‖` for all `x` supported on `s` and `y` supported on `t`.

**Results.** For a consistent scheme and `s ≠ t` that are not partners:
* `Consistent.norm_forced_block_sub_le`: `‖Π_s (X - U - ½H² A_ς A) Π_tᵀ‖ ≤ C H³`;
* `Consistent.forced_block_norm`: `|‖Π_s (X - U) Π_tᵀ‖ - a_st H²| ≤ C H³` (two-sided);
* `Consistent.forced_norm`: `a_st H² - C H³ ≤ ‖X - U‖` (the paper's `eq:aij`);
* `Consistent.cblock_signedCoupling_eq_sgn`: the block of `A_ς A` is the block of `A ς_s A`, the
  matrix of `ForcedBlock`; hence `a_st ≤ ½ ‖A‖²` (`Consistent.forcedCoeff_le`);
* `Consistent.forcedCoeff_jacobi`: if all subsystems run at the same stage (a Jacobi scheme),
  `a_st = ½ ‖[A²]_st‖`.

Proof. `Consistent.half_step_forced` bounds the matrix elements of `X - U - ½H² A_ς A` between
`s` and `t` by `C H³ ‖x‖ ‖y‖`; `norm_opE_cblock_le_iff` turns this into the norm of the block;
the block of a difference is the difference of the blocks, and a block is not larger than the
matrix (`norm_opE_cblock_le`).
-/
import CoSimFoundations.HalfStep
import CoSimFoundations.BlockExp

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The block between two subsystems, padded with zeros -/

/-- The block `(s, t)` of a matrix, padded with zeros: `mask_s T mask_t`. -/
def cblock (s t : κ) (T : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  S.mask s * T * S.mask t

/-- The entries of the padded block `(s, t)`. -/
theorem cblock_apply (s t : κ) (T : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    S.cblock s t T p q =
      (if S.sub p = s then 1 else 0) * T p q * (if S.sub q = t then 1 else 0) := by
  simp [cblock, mask, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The padded block depends only on the block. -/
theorem cblock_congr {s t : κ} {T T' : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ p q, S.sub p = s → S.sub q = t → T p q = T' p q) :
    S.cblock s t T = S.cblock s t T' := by
  ext p q
  rw [S.cblock_apply, S.cblock_apply]
  by_cases hp : S.sub p = s
  · by_cases hq : S.sub q = t
    · rw [h p q hp hq]
    · rw [ite_eq_right hq, mul_zero, mul_zero]
  · rw [ite_eq_right hp, zero_mul, zero_mul, zero_mul, zero_mul]

/-- The padded block of a difference. -/
theorem cblock_sub (s t : κ) (T T' : Matrix (Fin n) (Fin n) ℝ) :
    S.cblock s t (T - T') = S.cblock s t T - S.cblock s t T' := by
  rw [cblock, cblock, cblock, Matrix.mul_sub, Matrix.sub_mul]

/-- The padded block of a scalar multiple. -/
theorem cblock_smul (s t : κ) (c : ℝ) (T : Matrix (Fin n) (Fin n) ℝ) :
    S.cblock s t (c • T) = c • S.cblock s t T := by
  rw [cblock, cblock, Matrix.mul_smul, Matrix.smul_mul]

/-- The padded block of a negative. -/
theorem cblock_neg (s t : κ) (T : Matrix (Fin n) (Fin n) ℝ) :
    S.cblock s t (-T) = -S.cblock s t T := by
  rw [cblock, cblock, Matrix.mul_neg, Matrix.neg_mul]

/-- The matrix element of the padded block: the two vectors are cut to the two subsystems. -/
theorem inner_cblock (s t : κ) (T : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.cblock s t T) y⟫ = ⟪opE (S.mask s) x, opE T (opE (S.mask t) y)⟫ := by
  rw [inner_opE_eq_sum, inner_opE_eq_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [S.cblock_apply, S.opE_mask_apply, S.opE_mask_apply]
  ring

/-- Between vectors supported on `s` and on `t` the matrix elements of a matrix are those of its
block `(s, t)`. -/
theorem inner_cblock_of_support {s t : κ} (T : Matrix (Fin n) (Fin n) ℝ)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) : ⟪x, opE (S.cblock s t T) y⟫ = ⟪x, opE T y⟫ := by
  refine inner_opE_congr hx hy fun p q hp hq => ?_
  rw [S.cblock_apply, ite_eq_left hp, ite_eq_left hq, one_mul, mul_one]

/-- Cutting a vector to a subsystem does not make it longer. -/
theorem norm_opE_mask_apply_le (s : κ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖opE (S.mask s) x‖ ≤ ‖x‖ := by
  have h := (opE (S.mask s)).le_opNorm x
  have h1 := mul_le_mul_of_nonneg_right (S.norm_opE_mask_le s) (norm_nonneg x)
  linarith

/-- **The norm of a block is the supremum of the matrix elements between the two subsystems:**
`‖Π_s T Π_tᵀ‖ ≤ K` if and only if `|⟪x, T y⟫| ≤ K ‖x‖ ‖y‖` for all `x` supported on `s` and all
`y` supported on `t`. -/
theorem norm_opE_cblock_le_iff (s t : κ) (T : Matrix (Fin n) (Fin n) ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ‖opE (S.cblock s t T)‖ ≤ K ↔
      ∀ x y : EuclideanSpace ℝ (Fin n), (∀ p, S.sub p ≠ s → x p = 0) →
        (∀ q, S.sub q ≠ t → y q = 0) → |⟪x, opE T y⟫| ≤ K * (‖x‖ * ‖y‖) := by
  constructor
  · intro h x y hx hy
    rw [← S.inner_cblock_of_support T hx hy]
    exact (abs_inner_opE_le _ x y).trans (mul_le_mul_of_nonneg_right h (by positivity))
  · intro h
    refine ContinuousLinearMap.opNorm_le_of_re_inner_le hK fun u v hu hv => ?_
    have h1 := h (opE (S.mask s) v) (opE (S.mask t) u) (S.opE_mask_support s v)
      (S.opE_mask_support t u)
    have h2 := S.norm_opE_mask_apply_le s v
    have h3 := S.norm_opE_mask_apply_le t u
    rw [hv] at h2
    rw [hu] at h3
    have h4 : ‖opE (S.mask s) v‖ * ‖opE (S.mask t) u‖ ≤ 1 :=
      (mul_le_mul h2 h3 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [RCLike.re_to_real, real_inner_comm, S.inner_cblock]
    exact (le_abs_self _).trans (h1.trans ((mul_le_mul_of_nonneg_left h4 hK).trans_eq (mul_one K)))

/-- A block is not larger than the matrix: `‖Π_s T Π_tᵀ‖ ≤ ‖T‖`. -/
theorem norm_opE_cblock_le (s t : κ) (T : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (S.cblock s t T)‖ ≤ ‖opE T‖ :=
  (S.norm_opE_cblock_le_iff s t T (norm_nonneg _)).2 fun x y _ _ => abs_inner_opE_le T x y

/-- The matrix elements between `s` and `t` are bounded by the norm of the block. -/
theorem abs_inner_le_norm_cblock {s t : κ} (T : Matrix (Fin n) (Fin n) ℝ)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE T y⟫| ≤ ‖opE (S.cblock s t T)‖ * (‖x‖ * ‖y‖) :=
  (S.norm_opE_cblock_le_iff s t T (norm_nonneg _)).1 le_rfl x y hx hy

/-! ### The coefficient of the unavoidable error -/

/-- The coefficient `a_st = ½ ‖Σ_k ς_sk A_sk A_kt‖` of the unavoidable error between the
subsystems `s` and `t`: half the spectral norm of the block `(s, t)` of `A_ς A`. -/
noncomputable def forcedCoeff (A : Matrix (Fin n) (Fin n) ℝ) (s t : κ) : ℝ :=
  ‖opE (S.cblock s t (S.signedCoupling A * A))‖ / 2

/-- The coefficient of the unavoidable error is not negative. -/
theorem forcedCoeff_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (s t : κ) : 0 ≤ S.forcedCoeff A s t :=
  div_nonneg (norm_nonneg _) zero_le_two

/-- The signs `ς_s` form a diagonal matrix of spectral norm at most one. -/
theorem norm_opE_sgn_le (s : κ) : ‖opE (S.sgn s)‖ ≤ 1 :=
  norm_opE_diagonal_le _ zero_le_one fun i => by
    by_cases h : S.stage (S.sub i) < S.stage s <;> simp [sg, h]

variable {S}

/-- Between different subsystems that are not partners the block of `A_ς A` is the block of
`A ς_s A`, the matrix of `Consistent.forced_block`: the block `A_ss A_st` by which the two differ
vanishes because `A_st = 0`. -/
theorem Consistent.cblock_signedCoupling_eq_sgn {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    S.cblock s t (S.signedCoupling A * A) = S.cblock s t (A * S.sgn s * A) := by
  refine S.cblock_congr fun p q hp hq => ?_
  have h1 := S.sgn_row A p q
  rw [hp] at h1
  have h0 : (S.blockDiag A * A) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [S.blockDiag_apply]
    by_cases hr : S.sub p = S.sub r
    · have hrq : S.sub r ≠ S.sub q := by rw [← hr, hp, hq]; exact hst
      have hnp' : ¬ S.partner (S.sub r) (S.sub q) := by rw [← hr, hp, hq]; exact hnp
      rw [h.hA r q hrq hnp', mul_zero]
    · rw [ite_eq_right hr, zero_mul]
  rw [h1, h0, sub_zero]

/-- `a_st ≤ ½ ‖A‖²` between different subsystems that are not partners. -/
theorem Consistent.forcedCoeff_le {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    S.forcedCoeff A s t ≤ ‖opE A‖ ^ 2 / 2 := by
  have h1 : ‖opE (A * S.sgn s * A)‖ ≤ ‖opE A‖ * 1 * ‖opE A‖ := by
    rw [opE_mul, opE_mul]
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (S.norm_opE_sgn_le s) (norm_nonneg _))
  have h2 := S.norm_opE_cblock_le s t (A * S.sgn s * A)
  rw [forcedCoeff, h.cblock_signedCoupling_eq_sgn hst hnp]
  linarith

/-- **In a Jacobi scheme `a_st = ½ ‖[A²]_st‖`.** If all subsystems run at the same stage, then
between different subsystems that are not partners the block of `A_ς A` is minus the block of
`A²`. -/
theorem Consistent.forcedCoeff_jacobi {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hJ : ∀ k k' : κ, S.stage k = S.stage k') {s t : κ}
    (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    S.forcedCoeff A s t = ‖opE (S.cblock s t (A * A))‖ / 2 := by
  have e : S.cblock s t (A * S.sgn s * A) = S.cblock s t (-(A * A)) := by
    refine S.cblock_congr fun p q _ _ => ?_
    rw [S.sgn_entry, Matrix.neg_apply, Matrix.mul_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hs : S.sg s (S.sub r) = -1 := by
      have hlt : ¬ S.stage (S.sub r) < S.stage s := by
        rw [hJ (S.sub r) s]
        exact lt_irrefl _
      simp [sg, hlt]
    rw [hs]
    ring
  have e2 : opE (-S.cblock s t (A * A)) = -opE (S.cblock s t (A * A)) := map_neg _ _
  rw [forcedCoeff, h.cblock_signedCoupling_eq_sgn hst hnp, e, S.cblock_neg, e2, norm_neg]

/-! ### The norm bound -/

/-- **The block of `X - U` between subsystems that are not partners, in the spectral norm:**
`‖Π_s (X - U - ½H² A_ς A) Π_tᵀ‖ ≤ C H³`, `C = reactionC a b c ‖A‖ H`, for a consistent scheme with
one held sample in any order of execution and `s ≠ t` that are not partners. -/
theorem Consistent.norm_forced_block_sub_le {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    ‖opE (S.cblock s t (S.X - U - (H ^ 2 / 2) • (S.signedCoupling A * A)))‖ ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 := by
  refine (S.norm_opE_cblock_le_iff s t _ h.reaction_bound_nonneg).2 fun x y hx hy => ?_
  rw [inner_opE_sub, inner_opE_smul]
  exact (h.half_step_forced hst hnp hx hy).trans_eq (by ring)

/-- **The size of the unavoidable error, two-sided:** for a consistent scheme and `s ≠ t` that are
not partners, `|‖Π_s (X - U) Π_tᵀ‖ - a_st H²| ≤ C H³`, with
`a_st = forcedCoeff A s t = ½ ‖Σ_k ς_sk A_sk A_kt‖` and `C = reactionC a b c ‖A‖ H`. -/
theorem Consistent.forced_block_norm {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    |‖opE (S.cblock s t (S.X - U))‖ - S.forcedCoeff A s t * H ^ 2| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.norm_forced_block_sub_le hst hnp
  rw [S.cblock_sub, S.cblock_smul, opE_sub, opE_smul] at h1
  have h2 := abs_norm_sub_norm_le (opE (S.cblock s t (S.X - U)))
    ((H ^ 2 / 2) • opE (S.cblock s t (S.signedCoupling A * A)))
  have h3 : ‖(H ^ 2 / 2) • opE (S.cblock s t (S.signedCoupling A * A))‖ =
      S.forcedCoeff A s t * H ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), forcedCoeff]
    ring
  rw [h3] at h2
  exact h2.trans h1

/-- **The norm bound of the unavoidable error** (the paper, `eq:aij`). For a consistent scheme
with one held sample, in any order of execution, and two subsystems `s ≠ t` that are not partners:
`a_st H² - C H³ ≤ ‖X - U‖`, with `a_st = forcedCoeff A s t = ½ ‖Σ_k ς_sk A_sk A_kt‖` (half the
spectral norm of the block `(s, t)` of `A_ς A`) and `C = reactionC a b c ‖A‖ H`. -/
theorem Consistent.forced_norm {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    S.forcedCoeff A s t * H ^ 2 - reactionC a b c ‖opE A‖ H * H ^ 3 ≤ ‖opE (S.X - U)‖ := by
  have h1 := (abs_le.1 (h.forced_block_norm hst hnp)).1
  have h2 := S.norm_opE_cblock_le s t (S.X - U)
  linarith

/-- **The unavoidable error, tested on vectors:** for unit vectors `x` on `s` and `y` on `t`,
`½H² |⟪x, A_ς A y⟫| - C H³ ≤ ‖X - U‖`; `a_st` is the supremum of `½ |⟪x, A_ς A y⟫|` over such
vectors (`norm_opE_cblock_le_iff`). -/
theorem Consistent.forced_norm_of_unit {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    H ^ 2 / 2 * |⟪x, opE (S.signedCoupling A * A) y⟫| - reactionC a b c ‖opE A‖ H * H ^ 3 ≤
      ‖opE (S.X - U)‖ := by
  have h1 := h.forced_norm hst hnp
  have h2 := S.abs_inner_le_norm_cblock (S.signedCoupling A * A) hx hy
  rw [hx1, hy1, mul_one, mul_one] at h2
  have h3 : H ^ 2 / 2 * |⟪x, opE (S.signedCoupling A * A) y⟫| ≤ S.forcedCoeff A s t * H ^ 2 := by
    rw [forcedCoeff]
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ H ^ 2 / 2)
    linarith
  linarith

end HeldScheme

end CoSimFoundations
