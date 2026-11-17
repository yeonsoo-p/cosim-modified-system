/-
The chain of inequalities between the step-defect properties.

For a linear map `T` on a finite-dimensional real normed space `V` of dimension `n`, with
`α = ‖T - 1‖`, largest stretch `‖T‖` and least stretch `m` (attained, `EnergyExtremal`):

  `1 - α ≤ m`,   `m ^ n ≤ |det T|`,   `|det T| ≤ ‖T‖ ^ n`,   `‖T‖ ≤ 1 + α`.

With `T` the one-step defect in the energy norm, `1 + ε₋ = m²`, `1 + ε = ‖T‖²` and
`e^{nHδ̄} = |det T|`, this is the chain `1 - α ≤ √(1+ε₋) ≤ e^{Hδ̄} ≤ √(1+ε) ≤ 1 + α`.

The determinant bounds are proved by volume: a linear map scales Haar measure by `|det|`, the image
of the unit ball lies in the ball of radius `‖T‖` and contains the ball of radius `m`. No singular
value decomposition is used, and the norm need not come from an inner product.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Basic
import CoSimFoundations.EnergyExtremal

open MeasureTheory Metric Module

namespace CoSimFoundations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Cancelling a finite positive factor in an inequality of extended non-negative reals. -/
private theorem le_of_ofReal_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (h : ENNReal.ofReal a * c ≤ ENNReal.ofReal b * c) : a ≤ b := by
  have hfin : ENNReal.ofReal b * c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct
  have h1 := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb] at h1
  exact le_of_mul_le_mul_right h1 (ENNReal.toReal_pos hc0 hct)

/-- **The determinant by volume.** A linear map scales Haar measure by `|det T|`, and the ball of
radius `r ≥ 0` has `r ^ n` times the volume of the unit ball. So if the image of the unit ball
lies in the ball of radius `r`, then `|det T| ≤ r ^ n`, and if it contains that ball, then
`r ^ n ≤ |det T|`. -/
theorem abs_det_compare_of_image_closedBall (T : V →L[ℝ] V) {r : ℝ} (hr : 0 ≤ r) :
    (T '' closedBall (0 : V) 1 ⊆ closedBall (0 : V) r →
        |LinearMap.det (T : V →ₗ[ℝ] V)| ≤ r ^ finrank ℝ V) ∧
      (closedBall (0 : V) r ⊆ T '' closedBall (0 : V) 1 →
        r ^ finrank ℝ V ≤ |LinearMap.det (T : V →ₗ[ℝ] V)|) := by
  let _ : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hc0 : μ (closedBall (0 : V) 1) ≠ 0 := (measure_closedBall_pos μ 0 one_pos).ne'
  have hct : μ (closedBall (0 : V) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  refine ⟨fun hsub => ?_, fun hsub => ?_⟩
  · have h := measure_mono (μ := μ) hsub
    rw [Measure.addHaar_image_continuousLinearMap, Measure.addHaar_closedBall' μ (0 : V) hr] at h
    exact le_of_ofReal_mul_le (abs_nonneg _) (pow_nonneg hr _) hc0 hct h
  · have h := measure_mono (μ := μ) hsub
    rw [Measure.addHaar_image_continuousLinearMap, Measure.addHaar_closedBall' μ (0 : V) hr] at h
    exact le_of_ofReal_mul_le (pow_nonneg hr _) (abs_nonneg _) hc0 hct h

/-- **Largest stretch bounds the determinant:** `|det T| ≤ ‖T‖ ^ n`. -/
theorem abs_det_le_opNorm_pow (T : V →L[ℝ] V) :
    |LinearMap.det (T : V →ₗ[ℝ] V)| ≤ ‖T‖ ^ finrank ℝ V := by
  refine (abs_det_compare_of_image_closedBall T (norm_nonneg T)).1 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall_zero_iff] at hx ⊢
  calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    _ ≤ ‖T‖ * 1 := by gcongr
    _ = ‖T‖ := mul_one _

/-- **Least stretch bounds the determinant:** if `m ‖x‖ ≤ ‖T x‖` for all `x`, then
`m ^ n ≤ |det T|`. -/
theorem pow_le_abs_det_of_le (T : V →L[ℝ] V) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ x, m * ‖x‖ ≤ ‖T x‖) :
    m ^ finrank ℝ V ≤ |LinearMap.det (T : V →ₗ[ℝ] V)| := by
  rcases hm.eq_or_lt with rfl | hm'
  · rcases Nat.eq_zero_or_pos (finrank ℝ V) with h0 | hpos
    · have : (T : V →ₗ[ℝ] V) = LinearMap.id := by
        have := finrank_zero_iff.1 h0
        exact Subsingleton.elim _ _
      simp [h0, this]
    · simp [zero_pow hpos.ne']
  have hinj : Function.Injective (T : V →ₗ[ℝ] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := h x
    have hx' : T x = 0 := hx
    rw [hx', norm_zero] at h1
    have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    exact norm_le_zero_iff.1 this
  have hsurj : Function.Surjective (T : V →ₗ[ℝ] V) :=
    LinearMap.surjective_of_injective hinj
  refine (abs_det_compare_of_image_closedBall T hm'.le).2 fun y hy => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  refine ⟨x, ?_, rfl⟩
  rw [mem_closedBall_zero_iff] at hy ⊢
  have h1 : m * ‖x‖ ≤ m := (h x).trans hy
  nlinarith [norm_nonneg x]

/-- **Accuracy bounds the largest stretch:** `‖T‖ ≤ 1 + ‖T - 1‖`. -/
theorem opNorm_le_one_add (T : V →L[ℝ] V) : ‖T‖ ≤ 1 + ‖T - 1‖ := by
  have h : T = 1 + (T - 1) := by abel
  have h1 : ‖(1 : V →L[ℝ] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc ‖T‖ = ‖(1 : V →L[ℝ] V) + (T - 1)‖ := by rw [← h]
    _ ≤ ‖(1 : V →L[ℝ] V)‖ + ‖T - 1‖ := norm_add_le _ _
    _ ≤ 1 + ‖T - 1‖ := by gcongr

/-- **Accuracy bounds every stretch from below:** `(1 - ‖T - 1‖) ‖x‖ ≤ ‖T x‖`. -/
theorem one_sub_mul_norm_le (T : V →L[ℝ] V) (x : V) : (1 - ‖T - 1‖) * ‖x‖ ≤ ‖T x‖ := by
  have h1 : ‖x‖ - ‖T x‖ ≤ ‖x - T x‖ := norm_sub_norm_le x (T x)
  have h2 : ‖x - T x‖ = ‖(T - 1) x‖ := by
    rw [← norm_neg]; congr 1; simp
  have h3 : ‖(T - 1) x‖ ≤ ‖T - 1‖ * ‖x‖ := (T - 1).le_opNorm x
  nlinarith

/-- **The chain.** There is a least stretch `m`, attained at a unit vector, with
`1 - α ≤ m`, `m ^ n ≤ |det T| ≤ ‖T‖ ^ n` and `‖T‖ ≤ 1 + α`, where `α = ‖T - 1‖`. -/
theorem chain [Nontrivial V] (T : V →L[ℝ] V) :
    ∃ m : ℝ, (∃ x, ‖x‖ = 1 ∧ ‖T x‖ = m) ∧ (∀ y, m * ‖y‖ ≤ ‖T y‖) ∧
      1 - ‖T - 1‖ ≤ m ∧
      m ^ finrank ℝ V ≤ |LinearMap.det (T : V →ₗ[ℝ] V)| ∧
      |LinearMap.det (T : V →ₗ[ℝ] V)| ≤ ‖T‖ ^ finrank ℝ V ∧
      ‖T‖ ≤ 1 + ‖T - 1‖ := by
  obtain ⟨x, hx, hmin⟩ := exists_min_norm_apply T
  refine ⟨‖T x‖, ⟨x, hx, rfl⟩, hmin, ?_, pow_le_abs_det_of_le T (norm_nonneg _) hmin,
    abs_det_le_opNorm_pow T, opNorm_le_one_add T⟩
  simpa [hx] using one_sub_mul_norm_le T x

end CoSimFoundations
