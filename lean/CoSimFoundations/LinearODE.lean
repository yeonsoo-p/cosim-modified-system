/-
Linear time-invariant ODE with a forcing term: the variation-of-constants (Duhamel) formula.

  x' = A x + f(t)   on (a, b),   x continuous on [a, b],   f continuous on [a, b]
  ⟹  x b = exp((b - a) A) (x a) + ∫ s in a..b, exp((b - s) A) (f s).

A is a bounded operator on a real Banach space E, so the result covers matrices
(E = Fin n → ℝ) and every block-diagonal aggregate of the paper.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

open Set intervalIntegral MeasureTheory

namespace CoSimFoundations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The propagator `exp (t A)`. -/
noncomputable def prop (A : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E := NormedSpace.exp (t • A)

theorem prop_zero (A : E →L[ℝ] E) : prop A 0 = 1 := by
  simp [prop, NormedSpace.exp_zero]

theorem prop_mul_apply (A : E →L[ℝ] E) (s t : ℝ) (v : E) :
    (prop A s * prop A t) v = prop A s (prop A t v) := rfl

variable [CompleteSpace E]

/-- The group law `exp ((s + t) A) = exp (s A) exp (t A)`. -/
theorem prop_add (A : E →L[ℝ] E) (s t : ℝ) : prop A (s + t) = prop A s * prop A t := by
  let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  unfold prop
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl A).smul_left s |>.smul_right t)

theorem prop_apply_prop (A : E →L[ℝ] E) (s t : ℝ) (v : E) :
    prop A s (prop A t v) = prop A (s + t) v := by
  rw [prop_add]; rfl

theorem hasDerivAt_prop (A : E →L[ℝ] E) (t : ℝ) : HasDerivAt (prop A) (A * prop A t) t :=
  hasDerivAt_exp_smul_const' A t

theorem continuous_prop (A : E →L[ℝ] E) : Continuous (prop A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_prop A t).continuousAt

theorem prop_mul_prop_neg (A : E →L[ℝ] E) (t : ℝ) : prop A t * prop A (-t) = 1 := by
  rw [← prop_add, add_neg_cancel, prop_zero]

/-- **Variation of constants, uniqueness direction.** Every solution of `x' = A x + f` on `(a, b)`,
continuous on `[a, b]`, with `f` continuous on `[a, b]`, satisfies the Duhamel formula. -/
theorem duhamel {A : E →L[ℝ] E} {f x : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ioo a b, HasDerivAt x (A (x t) + f t) t) :
    x b = prop A (b - a) (x a) + ∫ s in a..b, prop A (b - s) (f s) := by
  -- y s = exp(-s A) x s has derivative exp(-s A) f s
  set y : ℝ → E := fun s => prop A (-s) (x s) with hy
  set g : ℝ → E := fun s => prop A (-s) (f s) with hg
  have hpn : ∀ s, HasDerivAt (fun s => prop A (-s)) (-(A * prop A (-s))) s := by
    intro s
    have hfun : (fun u : ℝ => prop A (-u)) = fun u => NormedSpace.exp (u • -A) := by
      funext u; simp [prop, neg_smul, smul_neg]
    have hval : -(A * prop A (-s)) = -A * NormedSpace.exp (s • -A) := by
      simp [prop, neg_smul, smul_neg, neg_mul]
    rw [hfun, hval]
    exact hasDerivAt_exp_smul_const' (-A) s
  have hderiv : ∀ s ∈ Ioo a b, HasDerivAt y (g s) s := by
    intro s hs
    have h := HasDerivAt.clm_apply (hpn s) (hode s hs)
    have hc : prop A (-s) (A (x s)) = A (prop A (-s) (x s)) := by
      have : Commute A (prop A (-s)) := by
        unfold prop
        exact ((Commute.refl A).smul_right (-s)).exp_right
      exact (congrArg (fun T : E →L[ℝ] E => T (x s)) this.eq).symm
    have hv : (-(A * prop A (-s))) (x s) + prop A (-s) (A (x s) + f s) = g s := by
      rw [map_add, hc]
      change -(A (prop A (-s) (x s))) + (A (prop A (-s) (x s)) + prop A (-s) (f s)) = g s
      simp only [hg]; abel
    rw [hv] at h
    exact h
  have hcont_p : ∀ c, Continuous fun s => prop A (c - s) :=
    fun c => (continuous_prop A).comp (continuous_const.sub continuous_id)
  have hgc : ContinuousOn g (Icc a b) := by
    have : Continuous fun s => prop A (-s) := (continuous_prop A).comp continuous_neg
    exact this.continuousOn.clm_apply hf
  have hyc : ContinuousOn y (Icc a b) := by
    have : Continuous fun s => prop A (-s) := (continuous_prop A).comp continuous_neg
    exact this.continuousOn.clm_apply hx
  have hint : IntervalIntegrable g volume a b :=
    (hgc.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hftc := integral_eq_sub_of_hasDerivAt_of_le hab hyc hderiv hint
  -- multiply by exp(b A)
  have hxb : x b = prop A b (y b) := by
    simp only [hy, prop_apply_prop, add_neg_cancel, prop_zero]
    rfl
  have hya : prop A b (y a) = prop A (b - a) (x a) := by
    simp only [hy, prop_apply_prop, sub_eq_add_neg]
  have hint' : prop A b (∫ s in a..b, g s) = ∫ s in a..b, prop A (b - s) (f s) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    congr 1; ext s
    simp only [hg, prop_apply_prop, sub_eq_add_neg]
  rw [hxb, show y b = y a + ∫ s in a..b, g s by rw [hftc]; abel, map_add, hya, hint']

/-- The Duhamel trajectory from `x₀` at time `a` under the forcing `f`. -/
noncomputable def duhamelSol (A : E →L[ℝ] E) (f : ℝ → E) (a : ℝ) (x₀ : E) (t : ℝ) : E :=
  prop A (t - a) x₀ + ∫ s in a..t, prop A (t - s) (f s)

omit [CompleteSpace E] in
theorem duhamelSol_start (A : E →L[ℝ] E) (f : ℝ → E) (a : ℝ) (x₀ : E) :
    duhamelSol A f a x₀ a = x₀ := by
  simp [duhamelSol, prop_zero]

/-- The factorised form `exp (t A) (exp (-a A) x₀ + ∫ exp (-s A) f s)`. -/
theorem duhamelSol_eq (A : E →L[ℝ] E) {f : ℝ → E} (hf : Continuous f) (a : ℝ) (x₀ : E) (t : ℝ) :
    duhamelSol A f a x₀ t = prop A t (prop A (-a) x₀ + ∫ s in a..t, prop A (-s) (f s)) := by
  have hint : IntervalIntegrable (fun s => prop A (-s) (f s)) volume a t :=
    (((continuous_prop A).comp continuous_neg).clm_apply hf).intervalIntegrable _ _
  rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint, prop_apply_prop]
  simp only [duhamelSol, prop_apply_prop, sub_eq_add_neg]

/-- **Variation of constants, existence direction.** For continuous forcing the Duhamel trajectory
solves `x' = A x + f` everywhere. -/
theorem hasDerivAt_duhamelSol (A : E →L[ℝ] E) {f : ℝ → E} (hf : Continuous f) (a : ℝ) (x₀ : E)
    (t : ℝ) : HasDerivAt (duhamelSol A f a x₀) (A (duhamelSol A f a x₀ t) + f t) t := by
  have hg : Continuous fun s => prop A (-s) (f s) :=
    ((continuous_prop A).comp continuous_neg).clm_apply hf
  have hI : HasDerivAt (fun u => prop A (-a) x₀ + ∫ s in a..u, prop A (-s) (f s))
      (prop A (-t) (f t)) t := by
    have := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    simpa using this.const_add (prop A (-a) x₀)
  have h := HasDerivAt.clm_apply (hasDerivAt_prop A t) hI
  have hfun : duhamelSol A f a x₀ = fun u => prop A u (prop A (-a) x₀ + ∫ s in a..u, prop A (-s) (f s)) :=
    funext (duhamelSol_eq A hf a x₀)
  rw [hfun]
  convert h using 1
  rw [prop_apply_prop, add_neg_cancel, prop_zero]
  rfl

/-- The Duhamel trajectory is the unique solution: any solution on `[a, b]` with the same start
agrees with it at `b`. -/
theorem eq_duhamelSol {A : E →L[ℝ] E} {f x : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ioo a b, HasDerivAt x (A (x t) + f t) t) :
    x b = duhamelSol A f a (x a) b :=
  duhamel hab hx hf hode

end CoSimFoundations
