/-
The growth of a flow is bounded by its dissipation, and the constant `κ_H` (the paper,
Prop 5.2 (ii)).

On a real Hilbert space (energy coordinates), if `⟪x, A x⟫ ≤ c ‖x‖²` for all `x` (the symmetric
part of `A` is at most `c`; for `A = J - R` this is `-λ_min R ≤ c`), then

  `‖exp (τ • A)‖ ≤ e^{c τ}` for `τ ≥ 0`.

Proof: `τ ↦ e^{-2cτ} ‖exp (τ • A) x‖²` has a nonpositive derivative.

With `⟪x, Ã x⟫ ≤ c₁ ‖x‖²` (`c₁ = -λ_min R̃`) and `-⟪x, A x⟫ ≤ c₂ ‖x‖²` (`c₂ = λ_max R`):

  `‖exp (H • Ã) * exp (H • (-A)) - 1‖ ≤ H · e^{H (c₁ + c₂)₊} · ‖Ã - A‖`,

which is `α ≤ κ_H · H ‖Δ‖` with `κ_H = exp (H (λ_max R - λ_min R̃)₊)`, and the floors of the
difference with this constant.
-/
import CoSimFoundations.DifferenceFloor
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open NormedSpace
open scoped RealInnerProductSpace

namespace CoSimFoundations

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Accuracy against the difference, with a joint bound `k` on the growth of the two flows. -/
theorem norm_defect_sub_one_le_of_mul_le (At A : 𝔸) {H k : ℝ} (hH : 0 ≤ H)
    (hk : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • At)‖ * ‖exp (τ • (-A))‖ ≤ k) :
    ‖exp (H • At) * exp (H • (-A)) - 1‖ ≤ H * (k * ‖At - A‖) := by
  refine norm_defect_sub_one_le_of_bound At A hH fun τ hτ => ?_
  calc ‖exp (τ • At)‖ * ‖At - A‖ * ‖exp (τ • (-A))‖
      = (‖exp (τ • At)‖ * ‖exp (τ • (-A))‖) * ‖At - A‖ := by ring
    _ ≤ k * ‖At - A‖ := mul_le_mul_of_nonneg_right (hk τ hτ) (norm_nonneg _)

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The trajectory `τ ↦ exp (τ • A) x` solves `ẏ = A y`. -/
theorem hasDerivAt_exp_smul_apply (A : E →L[ℝ] E) (x : E) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) x) (A (exp (τ • A) x)) τ := by
  let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  have h := (hasDerivAt_exp_smul_const' A τ).clm_apply (hasDerivAt_const τ x)
  simpa using h

/-- **Growth from dissipation, on a vector.** -/
theorem norm_exp_smul_apply_le (A : E →L[ℝ] E) {c : ℝ} (hA : ∀ x, ⟪x, A x⟫ ≤ c * ‖x‖ ^ 2)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : E) : ‖exp (τ • A) x‖ ≤ Real.exp (c * τ) * ‖x‖ := by
  let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Real.exp (-(2 * c) * u) * ‖exp (u • A) x‖ ^ 2)
      (Real.exp (-(2 * c) * u) * (-(2 * c)) * ‖exp (u • A) x‖ ^ 2 +
        Real.exp (-(2 * c) * u) * (2 * ⟪exp (u • A) x, A (exp (u • A) x)⟫)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(2 * c) * u))
        (Real.exp (-(2 * c) * u) * (-(2 * c))) u := by
      have := ((hasDerivAt_id u).const_mul (-(2 * c))).exp
      simpa using this
    exact h1.mul (hasDerivAt_exp_smul_apply A x u).norm_sq
  have hanti : Antitone (fun u : ℝ => Real.exp (-(2 * c) * u) * ‖exp (u • A) x‖ ^ 2) := by
    refine antitone_of_deriv_nonpos (fun u => (hd u).differentiableAt) (fun u => ?_)
    rw [(hd u).deriv]
    have h := hA (exp (u • A) x)
    have he := (Real.exp_pos (-(2 * c) * u)).le
    nlinarith [mul_nonneg he (sub_nonneg.2 h)]
  have h0 : Real.exp (-(2 * c) * τ) * ‖exp (τ • A) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have := hanti hτ
    simpa using this
  have hE : Real.exp (c * τ) ^ 2 * Real.exp (-(2 * c) * τ) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    have h2 : ((2 : ℕ) : ℝ) * (c * τ) + -(2 * c) * τ = 0 := by push_cast; ring
    rw [h2, Real.exp_zero]
  have hy : ‖exp (τ • A) x‖ ^ 2 ≤ (Real.exp (c * τ) * ‖x‖) ^ 2 := by
    calc ‖exp (τ • A) x‖ ^ 2
        = Real.exp (c * τ) ^ 2 * (Real.exp (-(2 * c) * τ) * ‖exp (τ • A) x‖ ^ 2) := by
          rw [← mul_assoc, hE, one_mul]
      _ ≤ Real.exp (c * τ) ^ 2 * ‖x‖ ^ 2 := by gcongr
      _ = (Real.exp (c * τ) * ‖x‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hy

/-- **Growth from dissipation:** `‖exp (τ • A)‖ ≤ e^{cτ}` when the symmetric part of `A` is at
most `c`. -/
theorem norm_exp_smul_le (A : E →L[ℝ] E) {c : ℝ} (hA : ∀ x, ⟪x, A x⟫ ≤ c * ‖x‖ ^ 2)
    {τ : ℝ} (hτ : 0 ≤ τ) : ‖exp (τ • A)‖ ≤ Real.exp (c * τ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (norm_exp_smul_apply_le A hA hτ)

/-- **Accuracy against the difference with the constant `κ_H`:**
`α ≤ e^{H (c₁ + c₂)₊} · H ‖Δ‖`, where `c₁ = -λ_min R̃` and `c₂ = λ_max R`. -/
theorem norm_defect_sub_one_le_kappa (At A : E →L[ℝ] E) {H c₁ c₂ : ℝ} (hH : 0 ≤ H)
    (hAt : ∀ x, ⟪x, At x⟫ ≤ c₁ * ‖x‖ ^ 2) (hA : ∀ x, -⟪x, A x⟫ ≤ c₂ * ‖x‖ ^ 2) :
    ‖exp (H • At) * exp (H • (-A)) - 1‖ ≤
      H * (Real.exp (H * max (c₁ + c₂) 0) * ‖At - A‖) := by
  refine norm_defect_sub_one_le_of_mul_le At A hH (fun τ hτ => ?_)
  have h1 := norm_exp_smul_le At hAt hτ.1
  have h2 : ‖exp (τ • (-A))‖ ≤ Real.exp (c₂ * τ) :=
    norm_exp_smul_le (-A) (fun x => by simpa using hA x) hτ.1
  calc ‖exp (τ • At)‖ * ‖exp (τ • (-A))‖ ≤ Real.exp (c₁ * τ) * Real.exp (c₂ * τ) := by gcongr
    _ = Real.exp ((c₁ + c₂) * τ) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (H * max (c₁ + c₂) 0) := by
        apply Real.exp_le_exp.2
        have hm := le_max_left (c₁ + c₂) 0
        have hm0 := le_max_right (c₁ + c₂) 0
        nlinarith [hτ.1, hτ.2, mul_le_mul_of_nonneg_right hm hτ.1,
          mul_le_mul_of_nonneg_left hτ.2 hm0]

/-- **Accuracy against the difference with a constant of the reference alone:**
`α ≤ H ‖Δ‖ · e^{H (g + ‖Δ‖)₊}`, where `g = a + b`, `a = -λ_min R`, `b = λ_max R` is the spread of
the reference's dissipation. No assumption on the scheme. -/
theorem norm_defect_sub_one_le_reference (At A : E →L[ℝ] E) {H a b : ℝ} (hH : 0 ≤ H)
    (hlow : ∀ x, ⟪x, A x⟫ ≤ a * ‖x‖ ^ 2) (hup : ∀ x, -⟪x, A x⟫ ≤ b * ‖x‖ ^ 2) :
    ‖exp (H • At) * exp (H • (-A)) - 1‖ ≤
      H * (Real.exp (H * max (a + ‖At - A‖ + b) 0) * ‖At - A‖) := by
  refine norm_defect_sub_one_le_kappa At A hH (fun x => ?_) hup
  have h1 : ⟪x, At x⟫ = ⟪x, A x⟫ + ⟪x, (At - A) x⟫ := by
    simp [inner_sub_right]
  have h2 : ⟪x, (At - A) x⟫ ≤ ‖At - A‖ * ‖x‖ ^ 2 := by
    calc ⟪x, (At - A) x⟫ ≤ ‖x‖ * ‖(At - A) x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖At - A‖ * ‖x‖) := by gcongr; exact (At - A).le_opNorm x
      _ = ‖At - A‖ * ‖x‖ ^ 2 := by ring
  have h3 := hlow x
  rw [h1]
  linarith

/-- **Link floor of the difference, with `κ_H`.** -/
theorem difference_link_floor_kappa (At A : E →L[ℝ] E) {H c₁ c₂ : ℝ} (hH : 0 ≤ H)
    (hAt : ∀ x, ⟪x, At x⟫ ≤ c₁ * ‖x‖ ^ 2) (hA : ∀ x, -⟪x, A x⟫ ≤ c₂ * ‖x‖ ^ 2)
    {e : E} (he : ‖e‖ = 1) (f : E) (h : ⟪e, exp (H • At) f⟫ = 0) :
    |⟪e, exp (H • A) f⟫| ≤
      H * (Real.exp (H * max (c₁ + c₂) 0) * ‖At - A‖) * ‖exp (H • A) f‖ :=
  difference_link_floor_of_le At A (norm_defect_sub_one_le_kappa At A hH hAt hA) he f h

/-- **Turning floor of the difference, with `κ_H`.** -/
theorem difference_turning_floor_kappa (At A : E →L[ℝ] E) {H c₁ c₂ : ℝ} (hH : 0 ≤ H)
    (hAt : ∀ x, ⟪x, At x⟫ ≤ c₁ * ‖x‖ ^ 2) (hA : ∀ x, -⟪x, A x⟫ ≤ c₂ * ‖x‖ ^ 2)
    {e : E} (he : ‖e‖ = 1) (h : 0 ≤ ⟪e, exp (H • At) e⟫) :
    -⟪e, exp (H • A) e⟫ ≤
      H * (Real.exp (H * max (c₁ + c₂) 0) * ‖At - A‖) * ‖exp (H • A) e‖ :=
  difference_turning_floor_of_le At A (norm_defect_sub_one_le_kappa At A hH hAt hA) he h

end CoSimFoundations
