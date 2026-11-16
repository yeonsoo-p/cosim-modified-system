/-
The defect is the difference accumulated over one macro step (the paper, Prop 5.2 (i), (ii)).

In a real Banach algebra, for a modified generator `Ã` and a reference generator `A`:

  `exp (H • Ã) * exp (H • (-A)) - 1 = ∫₀ᴴ exp (τ • Ã) * (Ã - A) * exp (τ • (-A)) dτ`,

and hence, if `‖exp (τ • Ã)‖ ≤ a` and `‖exp (τ • (-A))‖ ≤ b` on `[0, H]`,

  `‖exp (H • Ã) * exp (H • (-A)) - 1‖ ≤ H * (a * ‖Ã - A‖ * b)`.

So a lower bound `f` on the accuracy `α = ‖D - 1‖` is a lower bound `f / (H a b)` on the size of the
difference `Δ = Ã - A`. The paper's constant `κ_H = exp (H (λ_max R - λ_min R̃)₊)` is a bound for
`a * b` by the logarithmic norm; that estimate is not formalised here.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open NormedSpace

namespace CoSimFoundations

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The derivative of `τ ↦ exp (τ • Ã) * exp (τ • (-A))` is `exp (τ • Ã) * (Ã - A) * exp (τ • (-A))`. -/
theorem hasDerivAt_exp_mul_exp_neg (At A : 𝔸) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • At) * exp (u • (-A)))
      (exp (τ • At) * (At - A) * exp (τ • (-A))) τ := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have h1 : HasDerivAt (fun u : ℝ => exp (u • At)) (exp (τ • At) * At) τ :=
    hasDerivAt_exp_smul_const At τ
  have h2 : HasDerivAt (fun u : ℝ => exp (u • (-A))) (-A * exp (τ • (-A))) τ :=
    hasDerivAt_exp_smul_const' (-A) τ
  have h := h1.mul h2
  convert h using 1
  noncomm_ring

theorem continuous_exp_mul_sub_mul_exp_neg (At A : 𝔸) :
    Continuous (fun τ : ℝ => exp (τ • At) * (At - A) * exp (τ • (-A))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have h1 : Continuous (fun τ : ℝ => exp (τ • At)) :=
    exp_continuous.comp (continuous_id.smul continuous_const)
  have h2 : Continuous (fun τ : ℝ => exp (τ • (-A))) :=
    exp_continuous.comp (continuous_id.smul continuous_const)
  exact (h1.mul continuous_const).mul h2

/-- **The defect is the accumulated difference.** -/
theorem defect_sub_one_eq_integral (At A : 𝔸) (H : ℝ) :
    exp (H • At) * exp (H • (-A)) - 1 =
      ∫ τ in (0 : ℝ)..H, exp (τ • At) * (At - A) * exp (τ • (-A)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun τ _ => hasDerivAt_exp_mul_exp_neg At A τ)
    ((continuous_exp_mul_sub_mul_exp_neg At A).intervalIntegrable 0 H)
  rw [h]
  simp [exp_zero]

/-- **Accuracy is at most the step times the size of the difference**, up to the growth of the
two flows over the step. -/
theorem norm_defect_sub_one_le (At A : 𝔸) {H a b : ℝ} (hH : 0 ≤ H)
    (ha : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • At)‖ ≤ a) (hb : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • (-A))‖ ≤ b) :
    ‖exp (H • At) * exp (H • (-A)) - 1‖ ≤ H * (a * ‖At - A‖ * b) := by
  rw [defect_sub_one_eq_integral]
  have hbound : ∀ τ ∈ Set.uIoc (0 : ℝ) H,
      ‖exp (τ • At) * (At - A) * exp (τ • (-A))‖ ≤ a * ‖At - A‖ * b := by
    intro τ hτ
    rw [Set.uIoc_of_le hH] at hτ
    have hmem : τ ∈ Set.Icc 0 H := ⟨hτ.1.le, hτ.2⟩
    have ha' := ha τ hmem
    have hb' := hb τ hmem
    have ha0 : 0 ≤ a := (norm_nonneg _).trans ha'
    calc ‖exp (τ • At) * (At - A) * exp (τ • (-A))‖
        ≤ ‖exp (τ • At)‖ * ‖At - A‖ * ‖exp (τ • (-A))‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ a * ‖At - A‖ * b := by gcongr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_nonneg hH] at h
  rw [mul_comm]
  exact h

/-- **A floor under the accuracy is a floor under the difference.** -/
theorem floor_div_le_norm_difference (At A : 𝔸) {H a b f : ℝ} (hH : 0 < H) (hab : 0 < a * b)
    (ha : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • At)‖ ≤ a) (hb : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • (-A))‖ ≤ b)
    (hf : f ≤ ‖exp (H • At) * exp (H • (-A)) - 1‖) :
    f / (H * (a * b)) ≤ ‖At - A‖ := by
  have h := hf.trans (norm_defect_sub_one_le At A hH.le ha hb)
  rw [div_le_iff₀ (mul_pos hH hab)]
  calc f ≤ H * (a * ‖At - A‖ * b) := h
    _ = ‖At - A‖ * (H * (a * b)) := by ring

end CoSimFoundations
