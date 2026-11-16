/-
`det (exp A) = exp (trace A)` for real square matrices (listed as a TODO in Mathlib's
`MatrixExponential`). Used for the mean damping error `(1 / (n H)) ln det D` and for
`det E_i > 0`.

Proof: `g u = det (exp (u A))` satisfies `g (s + t) = g s * g t` and `g' 0 = trace A`
(differentiate the Leibniz expansion entrywise at the identity), so `g' = trace A * g`,
and `g u * exp (-(trace A) u)` is constant.
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Trace

open NormedSpace Matrix Equiv

namespace CoSimFoundations

variable {n : Type*} [Fintype n] [DecidableEq n]

section
open scoped Matrix.Norms.Operator

/-- Each entry of `u ↦ exp (u A)` is differentiable, with the entry of `A exp (t A)`. -/
theorem hasDerivAt_exp_smul_entry (A : Matrix n n ℝ) (i j : n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) i j) ((A * exp (t • A)) i j) t := by
  have h : HasDerivAt (fun u : ℝ => exp (u • A)) (A * exp (t • A)) t :=
    hasDerivAt_exp_smul_const' A t
  let L : Matrix n n ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

end

/-- A permutation other than the identity moves some point other than any given one. -/
theorem exists_moved_ne {σ : Perm n} (hσ : σ ≠ 1) (i : n) : ∃ j, j ≠ i ∧ σ j ≠ j := by
  obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  by_cases hki : k = i
  · subst hki
    exact ⟨σ k, hk, fun h => hk (σ.injective h)⟩
  · exact ⟨k, hki, hk⟩

/-- **Jacobi's formula at the identity, along `exp (u A)`.** -/
theorem hasDerivAt_det_exp_smul_zero (A : Matrix n n ℝ) :
    HasDerivAt (fun u : ℝ => (exp (u • A)).det) A.trace 0 := by
  have hterm : ∀ σ : Perm n, HasDerivAt (fun u : ℝ => ∏ i, exp (u • A) (σ i) i)
      (∑ i, (∏ j ∈ Finset.univ.erase i, exp ((0 : ℝ) • A) (σ j) j) •
        (A * exp ((0 : ℝ) • A)) (σ i) i) 0 :=
    fun σ => HasDerivAt.fun_finsetProd fun i _ => hasDerivAt_exp_smul_entry A (σ i) i 0
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun σ _ => (hterm σ).const_mul (((Perm.sign σ : ℤ) : ℝ)))
  have hfun : (fun u : ℝ => (exp (u • A)).det) =
      fun u => ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℝ) * ∏ i, exp (u • A) (σ i) i := by
    funext u; rw [det_apply']
  rw [hfun]
  convert hsum using 1
  simp only [zero_smul, exp_zero, mul_one, smul_eq_mul]
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [trace, Matrix.one_apply]
  · intro σ _ hσ
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
    obtain ⟨j, hji, hσj⟩ := exists_moved_ne hσ i
    apply mul_eq_zero_of_left
    exact Finset.prod_eq_zero (i := j) (Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩)
      (by simp [hσj])
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The group law for `det (exp (u A))`. -/
theorem det_exp_smul_add (A : Matrix n n ℝ) (s t : ℝ) :
    (exp ((s + t) • A)).det = (exp (s • A)).det * (exp (t • A)).det := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left s |>.smul_right t),
    det_mul]

theorem hasDerivAt_det_exp_smul (A : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (exp (u • A)).det) ((exp (t • A)).det * A.trace) t := by
  have h0 : HasDerivAt (fun u : ℝ => (exp (u • A)).det) A.trace (t - t) := by
    rw [sub_self]; exact hasDerivAt_det_exp_smul_zero A
  have h1 := (h0.comp_sub_const t t).const_mul (exp (t • A)).det
  have hfun : (fun u : ℝ => (exp (u • A)).det) =
      fun u => (exp (t • A)).det * (exp ((u - t) • A)).det := by
    funext u; rw [← det_exp_smul_add, add_sub_cancel]
  rw [hfun]; exact h1

/-- **`det (exp A) = exp (trace A)`.** -/
theorem det_exp (A : Matrix n n ℝ) : (exp A).det = Real.exp A.trace := by
  set g : ℝ → ℝ := fun u => (exp (u • A)).det * Real.exp (-(A.trace * u)) with hg
  have hd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h1 := hasDerivAt_det_exp_smul A u
    have h2 : HasDerivAt (fun u => Real.exp (-(A.trace * u)))
        (Real.exp (-(A.trace * u)) * -(A.trace * 1)) u :=
      (((hasDerivAt_id u).const_mul A.trace).neg).exp
    convert h1.mul h2 using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) 1 0
  simp only [hg, one_smul, mul_one, zero_smul, exp_zero, det_one, mul_zero, neg_zero,
    Real.exp_zero] at hc
  have hpos : Real.exp (-A.trace) ≠ 0 := (Real.exp_pos _).ne'
  calc (exp A).det = (exp A).det * Real.exp (-A.trace) * Real.exp A.trace := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = Real.exp A.trace := by rw [hc, one_mul]

end CoSimFoundations
