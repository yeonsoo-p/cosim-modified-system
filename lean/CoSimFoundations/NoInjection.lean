/-
Never injecting energy costs damping.

`D` the defect, `U` the reference step, `X = D ∘ U`, on a finite-dimensional real inner product
space of dimension `n`. A scheme *never injects* if `‖D‖ ≤ 1`: after one macro step no state has
more energy than the reference gives it. Its total damping error is read from the determinant:
`n H δ̄ = ln |det D|`.

Let `e₁`, `e₂` be orthonormal with `⟪e₁, X e₂⟫ = 0 = ⟪e₂, X e₁⟫` (two stores that are not partners
in a Jacobi scheme with one held sample), `u = ⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫`,
`η = ‖U e₁ - e₁‖ + ‖U e₂ - e₂‖`, `α = ‖D - 1‖`.

* **Direction form.** If `‖D‖ ≤ 1` there is a unit vector `v` (the proof takes `(e₁ ± e₂)/√2`) with
  `‖D v‖² ≤ 1 + α² - 2 (|u| - α η)`: the state `(e₁ ± e₂)/√2` loses energy.
* **Determinant form.** If `‖D‖ ≤ 1` then `(det D)² ≤ 1 + α² - 2 (|u| - α η)`, that is,
  `n H δ̄ ≤ ½ ln (1 - 2 (|u| - α η) + α²)`: the total damping exceeds that of the reference by about
  `|u|`, which is `H² |[A²]_ij|` to leading order, for every scheme whose one-step error is of
  second order in the macro step. Without a bound on `α` nothing is forced (the uncoupled scheme
  `X = 1` of a lossless reference has `‖D‖ = 1`, `det D = 1`).

Proof. `S = ⟪e₁, (D-1) e₂⟫ + ⟪e₂, (D-1) e₁⟫` satisfies `|S + u| ≤ α η`
(`abs_inner_sub_one_add_le`, twice). The quadratic form of `D - 1` on `w± = e₁ ± e₂` is `q ± S`
(`inner_add_sub_one`, `inner_sub_sub_one`) and is at most `(‖D‖ - 1) ‖w‖² ≤ 0`
(`sq_add_inner_sub_one_le`); hence one of the two is at most `-2 |S|`. For that `w`,
`‖D w‖² ≤ ‖w‖² + 2 ⟪w, (D-1) w⟫ + α² ‖w‖² ≤ 2 - 4 |S| + 2 α²` (`norm_sq_apply_le`), and
`v = w / √2`. Finally `|det D| ≤ ‖D v‖ ‖D‖ⁿ⁻¹ ≤ ‖D v‖` (`abs_det_le_norm_apply_mul_opNorm_pow`).

* **Without local gains injection is forced** (the statement involves no reference; for a lossless
  reference `⟪e, X e⟫ = 1` is the value without a gain): if a store keeps its own state exactly, `⟪e, X e⟫ = 1`, and receives anything from another direction, `a = ⟪e, X f⟫ ≠ 0`, then
  `‖X‖² ≥ 1 + a²`.
  Proof: `⟪e, X (e + a f)⟫ = 1 + a² ≤ ‖X‖ ‖e + a f‖ = ‖X‖ √(1 + a²)`.
-/
import CoSimFoundations.DetStretch
import CoSimFoundations.TradeOff

open Module
open scoped RealInnerProductSpace

namespace CoSimFoundations

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The direction form before normalisation: one of `e₁ ± e₂` (squared norm `2`) loses energy. -/
theorem exists_norm_sq_eq_two_of_no_gain (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hD : ‖D‖ ≤ 1) :
    ∃ w : E, ‖w‖ ^ 2 = 2 ∧
      ‖D w‖ ^ 2 ≤ 2 * (1 + ‖D - 1‖ ^ 2 -
        2 * (|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| - ‖D - 1‖ * (‖U e₁ - e₁‖ + ‖U e₂ - e₂‖))) := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have r1 := abs_le.1 (abs_inner_sub_one_add_le D U h1 hz1)
  have r2 := abs_le.1 (abs_inner_sub_one_add_le D U h2 hz2)
  have dp := sq_add_inner_sub_one_le D (e₁ + e₂)
  have dm := sq_add_inner_sub_one_le D (e₁ - e₂)
  have np := norm_sq_apply_le D (e₁ + e₂)
  have nm := norm_sq_apply_le D (e₁ - e₂)
  rw [hp] at dp np
  rw [hm] at dm nm
  rw [inner_add_sub_one] at dp np
  rw [inner_sub_sub_one] at dm nm
  rcases le_total 0 (⟪e₁, (D - 1) e₂⟫ + ⟪e₂, (D - 1) e₁⟫) with hS | hS
  · refine ⟨e₁ - e₂, hm, ?_⟩
    rcases abs_cases (⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫) with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;>
      linarith [r1.1, r1.2, r2.1, r2.2]
  · refine ⟨e₁ + e₂, hp, ?_⟩
    rcases abs_cases (⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫) with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;>
      linarith [r1.1, r1.2, r2.1, r2.2]

/-- **Direction form.** A scheme that never injects loses energy in some state; the proof finds it
in the plane of the two stores between which it moves nothing. -/
theorem exists_unit_norm_sq_apply_le_of_no_gain (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hD : ‖D‖ ≤ 1) :
    ∃ v : E, ‖v‖ = 1 ∧
      ‖D v‖ ^ 2 ≤ 1 + ‖D - 1‖ ^ 2 -
        2 * (|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| - ‖D - 1‖ * (‖U e₁ - e₁‖ + ‖U e₂ - e₂‖)) := by
  obtain ⟨w, hw, hDw⟩ := exists_norm_sq_eq_two_of_no_gain D U h1 h2 h12 hz1 hz2 hD
  have hw0 : ‖w‖ ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0]
  · rw [map_smul, norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, hw,
      inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact hDw

/-- **Without local gains injection is forced:** a store that keeps its own state exactly and
receives `a` from another direction makes the step expansive. -/
theorem one_add_sq_le_opNorm_sq (X : E →L[ℝ] E) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) (hee : ⟪e, X e⟫ = 1) :
    1 + ⟪e, X f⟫ ^ 2 ≤ ‖X‖ ^ 2 := by
  generalize ha : ⟪e, X f⟫ = a
  have hXy : ⟪e, X (e + a • f)⟫ = 1 + a ^ 2 := by
    rw [map_add, map_smul, inner_add_right, inner_smul_right, hee, ha]
    ring
  have hy : ‖e + a • f‖ ^ 2 = 1 + a ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hef, norm_smul, he, hf, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  have h1 : 1 + a ^ 2 ≤ ‖X‖ * ‖e + a • f‖ := by
    calc 1 + a ^ 2 = ⟪e, X (e + a • f)⟫ := hXy.symm
      _ ≤ ‖e‖ * ‖X (e + a • f)‖ := real_inner_le_norm _ _
      _ ≤ ‖X‖ * ‖e + a • f‖ := by rw [he, one_mul]; exact X.le_opNorm _
  have hpos : 0 < 1 + a ^ 2 := by positivity
  have h2 : (1 + a ^ 2) ^ 2 ≤ (‖X‖ * ‖e + a • f‖) ^ 2 := pow_le_pow_left₀ hpos.le h1 2
  rw [mul_pow, hy] at h2
  nlinarith

end General

section FiniteDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A scheme that never injects has `|det D| ≤ ‖D v‖` for every unit vector `v`. -/
theorem abs_det_le_norm_apply_of_opNorm_le_one [Nontrivial E] (D : E →L[ℝ] E) (hD : ‖D‖ ≤ 1)
    {v : E} (hv : ‖v‖ = 1) :
    |LinearMap.det (D : E →ₗ[ℝ] E)| ≤ ‖D v‖ := by
  have h1 := abs_det_le_norm_apply_mul_opNorm_pow D hv
  have h2 : ‖D‖ ^ (finrank ℝ E - 1) ≤ 1 := pow_le_one₀ (norm_nonneg D) hD
  have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (D v))
  rw [mul_one] at h3
  exact h1.trans h3

/-- **Never injecting costs damping, determinant form.** -/
theorem det_sq_le_of_no_gain [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hD : ‖D‖ ≤ 1) :
    LinearMap.det (D : E →ₗ[ℝ] E) ^ 2 ≤ 1 + ‖D - 1‖ ^ 2 -
      2 * (|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| - ‖D - 1‖ * (‖U e₁ - e₁‖ + ‖U e₂ - e₂‖)) := by
  obtain ⟨v, hv, hDv⟩ := exists_unit_norm_sq_apply_le_of_no_gain D U h1 h2 h12 hz1 hz2 hD
  have h := abs_det_le_norm_apply_of_opNorm_le_one D hD hv
  calc LinearMap.det (D : E →ₗ[ℝ] E) ^ 2 = |LinearMap.det (D : E →ₗ[ℝ] E)| ^ 2 :=
        (sq_abs _).symm
    _ ≤ ‖D v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ ≤ _ := hDv

end FiniteDim

end CoSimFoundations
