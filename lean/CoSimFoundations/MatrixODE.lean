/-
Bridge from matrices to operators, and the variation-of-constants formula for matrices:

  ẋ = A x + f(t)  on (a, b)   ⟹   x b = exp((b - a) A) x a + ∫ s in a..b, exp((b - s) A) f s.

Used for the exact step of a subsystem over one step with continuous forcing (
the hold signals are polynomials on each step). Chaining over consecutive steps, locally integrable
inputs (Lemma 1.1 and Thm 2.1 allow `w ∈ L¹_loc`) and the rescaling `t = t_k + σ H` that gives the
moments `E(τ) = exp(τ H A_K)`, `M^r(τ) = H ∫₀^τ exp((τ - s) H A_K) B_K V^r(s) ds` (eq. 7) are not
formalized here.
-/
import CoSimFoundations.LinearODE
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Matrix Set intervalIntegral MeasureTheory

namespace CoSimFoundations

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A matrix as a continuous linear operator on `X → ℝ`. -/
noncomputable def matCLM : Matrix X X ℝ →ₗ[ℝ] ((X → ℝ) →L[ℝ] (X → ℝ)) where
  toFun A := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  map_add' A B := by ext v i; simp
  map_smul' c A := by ext v i; simp

@[simp] theorem matCLM_apply (A : Matrix X X ℝ) (v : X → ℝ) : matCLM A v = A *ᵥ v := rfl

/-- `matCLM` as a ring homomorphism. -/
noncomputable def matRingHom : Matrix X X ℝ →+* ((X → ℝ) →L[ℝ] (X → ℝ)) where
  toFun := matCLM
  map_one' := by ext v i; simp
  map_mul' A B := by ext v i; simp [mulVec_mulVec]
  map_zero' := by ext v i; simp
  map_add' A B := matCLM.map_add A B

theorem continuous_matRingHom : Continuous (matRingHom (X := X)) :=
  (matCLM (X := X)).continuous_of_finiteDimensional

/-- `exp (t A) v = prop (A as an operator) t v`. -/
theorem exp_smul_mulVec (A : Matrix X X ℝ) (t : ℝ) (v : X → ℝ) :
    NormedSpace.exp (t • A) *ᵥ v = prop (matCLM A) t v := by
  open scoped Matrix.Norms.Operator in
  let _ : NormedAlgebra ℚ (Matrix X X ℝ) := NormedAlgebra.restrictScalars ℚ ℝ (Matrix X X ℝ)
  have h := NormedSpace.map_exp matRingHom continuous_matRingHom (t • A)
  have hs : matRingHom (t • A) = t • matCLM A := matCLM.map_smul t A
  rw [hs] at h
  calc NormedSpace.exp (t • A) *ᵥ v = matRingHom (NormedSpace.exp (t • A)) v := rfl
    _ = NormedSpace.exp (t • matCLM A) v := congrArg (fun T => T v) h
    _ = prop (matCLM A) t v := rfl

/-- **Variation of constants for matrices.** -/
theorem duhamel_mat {A : Matrix X X ℝ} {f x : ℝ → X → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ioo a b, HasDerivAt x (A *ᵥ x t + f t) t) :
    x b = NormedSpace.exp ((b - a) • A) *ᵥ x a +
      ∫ s in a..b, NormedSpace.exp ((b - s) • A) *ᵥ f s := by
  have h := duhamel (A := matCLM A) hab hx hf (by simpa using hode)
  simpa only [exp_smul_mulVec] using h

end CoSimFoundations
