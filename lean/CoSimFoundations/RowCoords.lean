/-
Row coordinates of a real `2 × 2` defect (the paper, Lemma 7.1).

Identify `ℝ²` with `ℂ`. Every real-linear map of `ℂ` is `x ↦ z x + w x̄` for unique `z, w : ℂ`
(a rotation with scaling plus a reflection with scaling). For it:

* the largest stretch is `‖z‖ + ‖w‖`, attained;
* the least stretch is `|‖z‖ - ‖w‖|`, attained;
* its distance from the identity is `‖z - 1‖ + ‖w‖`.

With `z = (ζ₁ + ζ₂)/2` and `w̄ = (ζ₁ - ζ₂)/2` for the rows `ζ₁ = D₁₁ - i D₁₂`, `ζ₂ = D₂₂ + i D₂₁`
of a real matrix `D`, these are `√(1+ε) = |z| + |w|`, `√(1+ε₋) = ||z| - |w||` and
`α = |z - 1| + |w|`.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Normed.Operator.Basic

open Complex

namespace CoSimFoundations

/-- The real-linear map `x ↦ z x + w x̄` of `ℂ`. -/
noncomputable def rowMap (z w : ℂ) : ℂ →L[ℝ] ℂ :=
  z • ContinuousLinearMap.id ℝ ℂ + w • (conjCLE : ℂ →L[ℝ] ℂ)

@[simp]
theorem rowMap_apply (z w x : ℂ) : rowMap z w x = z * x + w * (starRingEnd ℂ) x := by
  simp [rowMap]

/-- The direction in which the two parts of `rowMap z w` are aligned. -/
noncomputable def alignDir (z w : ℂ) : ℂ := exp (((arg w - arg z) / 2 : ℝ) * I)

theorem norm_alignDir (z w : ℂ) : ‖alignDir z w‖ = 1 := by
  rw [alignDir, norm_exp_ofReal_mul_I]

theorem mul_alignDir (z w : ℂ) :
    z * alignDir z w = ‖z‖ * exp (((arg z + arg w) / 2 : ℝ) * I) := by
  have hz := norm_mul_exp_arg_mul_I z
  calc z * alignDir z w
      = (‖z‖ * exp (arg z * I)) * exp (((arg w - arg z) / 2 : ℝ) * I) := by rw [hz, alignDir]
    _ = ‖z‖ * exp (((arg z + arg w) / 2 : ℝ) * I) := by
        rw [mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring

theorem mul_conj_alignDir (z w : ℂ) :
    w * (starRingEnd ℂ) (alignDir z w) = ‖w‖ * exp (((arg z + arg w) / 2 : ℝ) * I) := by
  have hw := norm_mul_exp_arg_mul_I w
  calc w * (starRingEnd ℂ) (alignDir z w)
      = (‖w‖ * exp (arg w * I)) * exp ((starRingEnd ℂ) (((arg w - arg z) / 2 : ℝ) * I)) := by
        rw [hw, alignDir, ← Complex.exp_conj]
    _ = ‖w‖ * exp (((arg z + arg w) / 2 : ℝ) * I) := by
        rw [mul_assoc, ← Complex.exp_add]
        congr 2
        simp only [map_mul, conj_ofReal, conj_I]
        push_cast
        ring

/-- Every stretch of `rowMap z w` is at most `‖z‖ + ‖w‖`. -/
theorem norm_rowMap_apply_le (z w x : ℂ) : ‖rowMap z w x‖ ≤ (‖z‖ + ‖w‖) * ‖x‖ := by
  rw [rowMap_apply]
  calc ‖z * x + w * (starRingEnd ℂ) x‖ ≤ ‖z * x‖ + ‖w * (starRingEnd ℂ) x‖ := norm_add_le _ _
    _ = (‖z‖ + ‖w‖) * ‖x‖ := by rw [norm_mul, norm_mul, RCLike.norm_conj]; ring

/-- The largest stretch is attained in the aligned direction. -/
theorem norm_rowMap_alignDir (z w : ℂ) : ‖rowMap z w (alignDir z w)‖ = ‖z‖ + ‖w‖ := by
  rw [rowMap_apply, mul_alignDir, mul_conj_alignDir, ← add_mul, norm_mul,
    norm_exp_ofReal_mul_I, mul_one]
  have h : (0 : ℝ) ≤ ‖z‖ + ‖w‖ := by positivity
  rw [← ofReal_add, norm_real, Real.norm_of_nonneg h]

/-- **Largest stretch:** `‖rowMap z w‖ = ‖z‖ + ‖w‖`. -/
theorem opNorm_rowMap (z w : ℂ) : ‖rowMap z w‖ = ‖z‖ + ‖w‖ := by
  refine le_antisymm ((rowMap z w).opNorm_le_bound (by positivity) (norm_rowMap_apply_le z w)) ?_
  have h := (rowMap z w).le_opNorm (alignDir z w)
  rwa [norm_rowMap_alignDir, norm_alignDir, mul_one] at h

/-- **Accuracy in row coordinates:** `‖rowMap z w - 1‖ = ‖z - 1‖ + ‖w‖`. -/
theorem norm_rowMap_sub_one (z w : ℂ) : ‖rowMap z w - 1‖ = ‖z - 1‖ + ‖w‖ := by
  have h : rowMap z w - 1 = rowMap (z - 1) w := by
    ext x
    simp [rowMap, sub_mul]
    ring
  rw [h, opNorm_rowMap]

/-- **Least stretch, lower bound:** `|‖z‖ - ‖w‖| ‖x‖ ≤ ‖rowMap z w x‖`. -/
theorem abs_sub_mul_norm_le_rowMap (z w x : ℂ) : |‖z‖ - ‖w‖| * ‖x‖ ≤ ‖rowMap z w x‖ := by
  rw [rowMap_apply]
  have h := abs_norm_sub_norm_le (z * x) (-(w * (starRingEnd ℂ) x))
  rw [norm_neg, sub_neg_eq_add, norm_mul, norm_mul, RCLike.norm_conj, ← sub_mul, abs_mul,
    abs_of_nonneg (norm_nonneg x)] at h
  exact h

/-- **Least stretch, attained:** in the direction `I * alignDir z w`. -/
theorem norm_rowMap_I_mul_alignDir (z w : ℂ) :
    ‖rowMap z w (I * alignDir z w)‖ = |‖z‖ - ‖w‖| := by
  have h : rowMap z w (I * alignDir z w) =
      I * (((‖z‖ - ‖w‖ : ℝ) : ℂ) * exp (((arg z + arg w) / 2 : ℝ) * I)) := by
    rw [rowMap_apply, map_mul, conj_I]
    have h1 : z * (I * alignDir z w) = I * (z * alignDir z w) := by ring
    have h2 : w * (-I * (starRingEnd ℂ) (alignDir z w)) =
        -(I * (w * (starRingEnd ℂ) (alignDir z w))) := by ring
    rw [h1, h2, mul_alignDir, mul_conj_alignDir]
    push_cast
    ring
  rw [h, norm_mul, norm_I, one_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
    Real.norm_eq_abs]

end CoSimFoundations
