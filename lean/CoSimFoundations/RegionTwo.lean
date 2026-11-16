/-
Two states: the determinant in row coordinates, and the universal region is attained
(the paper, Lemma 7.1 and Thm 5.3 for `n = 2`).

* `det (x ↦ z x + w x̄) = ‖z‖² - ‖w‖²`.
* For stretches `s ≥ t > 0` and every `α` with `max{|s - 1|, |t - 1|} ≤ α ≤ 1 + s` there is a
  real-linear map of `ℂ` with largest stretch `s`, least stretch `t` and distance `α` from the
  identity: the rotations `e^{iφ}` of `diag(s, t)`, `0 ≤ φ ≤ π`, sweep the accuracy continuously
  from the lower to the upper bound.
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Order.IntermediateValue
import CoSimFoundations.RowCoords

open Complex

namespace CoSimFoundations

/-- **Determinant in row coordinates:** `det (x ↦ z x + w x̄) = ‖z‖² - ‖w‖²`. -/
theorem det_rowMap (z w : ℂ) :
    LinearMap.det (rowMap z w : ℂ →ₗ[ℝ] ℂ) = ‖z‖ ^ 2 - ‖w‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, coe_basisOneI_repr, ContinuousLinearMap.coe_coe,
    rowMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.sq_norm, normSq_apply]
  simp
  ring

/-- The accuracy of the rotated diagonal defect, as a function of the angle. -/
noncomputable def rotAccuracy (s t φ : ℝ) : ℝ :=
  ‖(((s + t) / 2 : ℝ) : ℂ) * exp ((φ : ℂ) * I) - 1‖ + (s - t) / 2

theorem continuous_rotAccuracy (s t : ℝ) : Continuous (rotAccuracy s t) := by
  unfold rotAccuracy
  fun_prop

theorem rotAccuracy_zero {s t : ℝ} : rotAccuracy s t 0 = |(s + t) / 2 - 1| + (s - t) / 2 := by
  have h : (((s + t) / 2 : ℝ) : ℂ) * exp (((0 : ℝ) : ℂ) * I) - 1 = (((s + t) / 2 - 1 : ℝ) : ℂ) := by
    simp
  rw [rotAccuracy, h, norm_real, Real.norm_eq_abs]

theorem rotAccuracy_pi {s t : ℝ} (hst : 0 ≤ s + t) :
    rotAccuracy s t Real.pi = 1 + s := by
  have h : (((s + t) / 2 : ℝ) : ℂ) * exp ((Real.pi : ℂ) * I) - 1 = ((-((s + t) / 2 + 1) : ℝ) : ℂ) := by
    rw [exp_pi_mul_I]; push_cast; ring
  rw [rotAccuracy, h, norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith)]
  ring

/-- **The universal region is attained for two states.** For `0 < t ≤ s` and every `α` between
`|(s + t)/2 - 1| + (s - t)/2 = max{|s - 1|, |t - 1|}` and `1 + s` there is a real-linear map of `ℂ`
with largest stretch `s`, least stretch `t` and distance `α` from the identity. -/
theorem exists_rowMap_of_region {s t α : ℝ} (ht : 0 < t) (hts : t ≤ s)
    (hlo : |(s + t) / 2 - 1| + (s - t) / 2 ≤ α) (hhi : α ≤ 1 + s) :
    ∃ z w : ℂ, ‖rowMap z w‖ = s ∧ (∀ x, t * ‖x‖ ≤ ‖rowMap z w x‖) ∧
      (∃ x, ‖x‖ = 1 ∧ ‖rowMap z w x‖ = t) ∧ ‖rowMap z w - 1‖ = α := by
  have hst : 0 ≤ s + t := by linarith
  obtain ⟨φ, -, hφ⟩ : ∃ φ ∈ Set.Icc (0 : ℝ) Real.pi, rotAccuracy s t φ = α := by
    have hcont : ContinuousOn (rotAccuracy s t) (Set.Icc 0 Real.pi) :=
      (continuous_rotAccuracy s t).continuousOn
    have hmem : α ∈ Set.Icc (rotAccuracy s t 0) (rotAccuracy s t Real.pi) := by
      rw [rotAccuracy_zero, rotAccuracy_pi hst]; exact ⟨hlo, hhi⟩
    exact intermediate_value_Icc Real.pi_pos.le hcont hmem
  set z : ℂ := (((s + t) / 2 : ℝ) : ℂ) * exp ((φ : ℂ) * I) with hz
  set w : ℂ := (((s - t) / 2 : ℝ) : ℂ) with hw
  have hnz : ‖z‖ = (s + t) / 2 := by
    rw [hz, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg (by linarith)]
  have hnw : ‖w‖ = (s - t) / 2 := by
    rw [hw, norm_real, Real.norm_of_nonneg (by linarith)]
  have habs : |‖z‖ - ‖w‖| = t := by
    rw [hnz, hnw]; ring_nf; exact abs_of_pos ht
  refine ⟨z, w, ?_, ?_, ?_, ?_⟩
  · rw [opNorm_rowMap, hnz, hnw]; ring
  · intro x
    have := abs_sub_mul_norm_le_rowMap z w x
    rwa [habs] at this
  · refine ⟨I * alignDir z w, ?_, ?_⟩
    · rw [norm_mul, norm_I, one_mul, norm_alignDir]
    · rw [norm_rowMap_I_mul_alignDir, habs]
  · rw [norm_rowMap_sub_one, hnw, ← hφ, rotAccuracy]

end CoSimFoundations
