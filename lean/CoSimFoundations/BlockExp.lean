/-
The exponential of a padded block (support for `ReactionDiag` and `ReactionSV`; the paper,
Proposition 6.1 and Theorem 6.2, the hypothesis "partner weights only", `F_i = e^{H A_i}`).

`ReactionDiag` states `F_s = e^{H A_s}` as: `F` and `exp (H • blk s A)` have the same block `s`,
where `blk s A = mask_s A mask_s` is the block `A_s` padded with zeros. Here this is tied to the
matrix `A_s` on the states of `s` alone: with
  `sblock s T = T.submatrix val val`   (the block `s` of `T`, a matrix on `{p // sub p = s}`),
* `sblock_exp_smul_blk`: `sblock s (exp (H • blk s A)) = exp (H • sblock s A)`, the block `s` of
  the exponential of the padded block is the exponential `e^{H A_s}` of the block;
* `block_eq_of_sblock`: if `sblock s F = exp (H • sblock s A)` (literally `F_s = e^{H A_s}`),
  then `F p q = exp (H • blk s A) p q` for all states `p`, `q` of `s`, which is the hypothesis
  `hFs` of `Consistent.reaction_partner_weights` and of the theorems of `ReactionSV`.

Proof: `sblock s (Z ^ k) = (sblock s A) ^ k` for `Z = blk s A` by induction (`Z` vanishes outside
the block), the exponential series of `Z` converges entrywise (`|(Z ^ k) p q| ≤ ‖Z‖ ^ k`), and
taking a block is a continuous additive map, so it commutes with the sum of the series.
-/
import CoSimFoundations.ReactionDiag
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Matrix

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

variable {n : ℕ}

/-- `‖Z ^ k‖ ≤ ‖Z‖ ^ k` in the spectral norm (also on the trivial space). -/
theorem norm_opE_pow_le (Z : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ‖opE (Z ^ k)‖ ≤ ‖opE Z‖ ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, opE_one]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ, opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- The entries of a power are bounded by the power of the spectral norm. -/
theorem abs_pow_apply_le (Z : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (p q : Fin n) :
    |(Z ^ k) p q| ≤ ‖opE Z‖ ^ k := by
  have h := abs_inner_opE_le (Z ^ k) (unitE p) (unitE q)
  rw [inner_unitE_opE, norm_unitE, norm_unitE, mul_one, mul_one] at h
  exact h.trans (norm_opE_pow_le Z k)

/-- The exponential series of a real matrix converges (entrywise). -/
theorem summable_exp_series (Z : Matrix (Fin n) (Fin n) ℝ) :
    Summable fun k : ℕ => ((k.factorial : ℝ)⁻¹) • Z ^ k := by
  refine Pi.summable.2 fun p => Pi.summable.2 fun q => ?_
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖opE Z‖) fun k => ?_
  have e : (((k.factorial : ℝ)⁻¹) • Z ^ k) p q = (k.factorial : ℝ)⁻¹ * (Z ^ k) p q := rfl
  rw [e, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (abs_pow_apply_le Z k p q) (by positivity)

end OneStep

open OneStep

variable {n : ℕ}

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- The block `s` of a matrix, as a matrix on the states of the subsystem `s`. -/
def sblock (s : κ) (T : Matrix (Fin n) (Fin n) ℝ) :
    Matrix {p // S.sub p = s} {p // S.sub p = s} ℝ :=
  T.submatrix Subtype.val Subtype.val

/-- The block `s` of the padded block is the block. -/
theorem sblock_blk (s : κ) (A : Matrix (Fin n) (Fin n) ℝ) :
    S.sblock s (S.blk s A) = S.sblock s A := by
  ext p q
  simp [sblock, blk_apply, p.2, q.2]

/-- The mask of a subsystem is a coordinate projection: its spectral norm is at most one. -/
theorem norm_opE_mask_le (s : κ) : ‖opE (S.mask s)‖ ≤ 1 :=
  norm_opE_diagonal_le _ zero_le_one fun i => by
    by_cases h : S.sub i = s <;> simp [h]

/-- The padded block is not larger than the matrix: `‖A_s‖ ≤ ‖A‖`. -/
theorem norm_opE_blk_le (s : κ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (S.blk s A)‖ ≤ ‖opE A‖ := by
  have h1 := S.norm_opE_mask_le s
  rw [blk, opE_mul, opE_mul]
  calc ‖opE (S.mask s) * opE A * opE (S.mask s)‖
      ≤ ‖opE (S.mask s) * opE A‖ * ‖opE (S.mask s)‖ := norm_mul_le _ _
    _ ≤ ‖opE (S.mask s)‖ * ‖opE A‖ * ‖opE (S.mask s)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * ‖opE A‖ * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h1 (norm_nonneg _)
          (by positivity)
    _ = ‖opE A‖ := by ring

/-- Padding commutes with scalar multiples. -/
theorem blk_smul (s : κ) (H : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    S.blk s (H • A) = H • S.blk s A := by
  rw [blk, blk, Matrix.mul_smul, Matrix.smul_mul]

/-- Multiplying by a padded block on the right acts within the block. -/
theorem sblock_mul_blk (s : κ) (T A : Matrix (Fin n) (Fin n) ℝ) :
    S.sblock s (T * S.blk s A) = S.sblock s T * S.sblock s A := by
  ext p q
  have key : ∑ r : {r // S.sub r = s}, T p r * A r q =
      ∑ r ∈ Finset.univ.filter fun r => S.sub r = s, T p r * A r q :=
    (Finset.sum_subtype _ (by simp) fun r => T p r * A r q).symm
  simp only [sblock, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [key, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [blk_apply, ite_eq_left q.2, mul_one]
  by_cases hr : S.sub r = s
  · simp [hr]
  · simp [hr]

/-- The block `s` of a power of the padded block is the power of the block. -/
theorem sblock_blk_pow (s : κ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    S.sblock s (S.blk s A ^ k) = S.sblock s A ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Matrix.submatrix_one _ Subtype.val_injective
  | succ k ih => rw [pow_succ, pow_succ, sblock_mul_blk, ih]

/-- The block `s` of the exponential of the padded block is the exponential of the block. -/
theorem sblock_exp_blk (s : κ) (A : Matrix (Fin n) (Fin n) ℝ) :
    S.sblock s (NormedSpace.exp (S.blk s A)) = NormedSpace.exp (S.sblock s A) := by
  have e1 : NormedSpace.exp (S.blk s A) = ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • S.blk s A ^ k :=
    congrFun (NormedSpace.exp_eq_tsum ℝ) _
  have e2 : NormedSpace.exp (S.sblock s A) = ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • S.sblock s A ^ k :=
    congrFun (NormedSpace.exp_eq_tsum ℝ) _
  have hs : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • S.blk s A ^ k)
      (NormedSpace.exp (S.blk s A)) := by
    rw [e1]
    exact (summable_exp_series _).hasSum
  let g : Matrix (Fin n) (Fin n) ℝ →+ Matrix {p // S.sub p = s} {p // S.sub p = s} ℝ :=
    { toFun := fun T => S.sblock s T
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Continuous g :=
    (continuous_id (X := Matrix (Fin n) (Fin n) ℝ)).matrix_submatrix Subtype.val Subtype.val
  have h2 := (hs.map g hg).tsum_eq
  change g (NormedSpace.exp (S.blk s A)) = _
  rw [← h2, e2]
  refine tsum_congr fun k => ?_
  change S.sblock s (((k.factorial : ℝ)⁻¹) • S.blk s A ^ k) = _
  rw [← sblock_blk_pow]
  rfl

/-- **The block of the exponential of the padded block**: the block `s` of
`exp (H • blk s A)` is `e^{H A_s}`. -/
theorem sblock_exp_smul_blk (s : κ) (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.sblock s (NormedSpace.exp (H • S.blk s A)) = NormedSpace.exp (H • S.sblock s A) := by
  rw [← blk_smul, sblock_exp_blk]
  rfl

/-- **Partner weights only, literally.** If the block `s` of `F` is `e^{H A_s}`, with `A_s` the
block of `A` on the states of `s`, then `F` and `exp (H • blk s A)` agree on the block `s`: the
hypothesis `hFs` of `Consistent.reaction_partner_weights`. -/
theorem block_eq_of_sblock {s : κ} {A : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hF : S.sblock s S.F = NormedSpace.exp (H • S.sblock s A)) (p q : Fin n)
    (hp : S.sub p = s) (hq : S.sub q = s) :
    S.F p q = NormedSpace.exp (H • S.blk s A) p q :=
  congrFun (congrFun (hF.trans (S.sblock_exp_smul_blk s A H).symm) ⟨p, hp⟩) ⟨q, hq⟩

end HeldScheme

end CoSimFoundations
