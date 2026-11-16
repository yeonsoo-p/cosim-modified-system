/-
The reference step of two stores in closed form (the paper, eq. (12)/(13), underdamped case).

In a real Banach algebra, if `B = c • 1 + N` and `N * N = -(ν²) • 1` with `ν ≠ 0`, then

  `exp (t • B) = e^{c t} • (cos (ν t) • 1 + (sin (ν t) / ν) • N)`.

For two stores, `A = !![-r₁, -ω; ω, -r₂]`, `c = -(r₁ + r₂)/2`, `d = (r₁ - r₂)/2`, `ν² = ω² - d² > 0`:

  `U = exp (H • A) = e^{cH} !![cos νH - (d/ν) sin νH, -(ω/ν) sin νH; (ω/ν) sin νH, cos νH + (d/ν) sin νH]`,

which is the angle form of the paper with `μ = νH`, `cot φ = d/ν`.
The proof is by uniqueness for `f' = B f`, `f 0 = 1`.
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open NormedSpace

namespace CoSimFoundations

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Uniqueness for `f' = B f`.** A solution with `f 0 = 1` is `t ↦ exp (t • B)`. -/
theorem eq_exp_smul_of_hasDerivAt {B : 𝔸} {f : ℝ → 𝔸} (hf : ∀ t, HasDerivAt f (B * f t) t)
    (h0 : f 0 = 1) (t : ℝ) : f t = exp (t • B) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • (-B))) (exp (s • (-B)) * (-B)) s :=
    fun s => hasDerivAt_exp_smul_const (-B) s
  have hg : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • (-B)) * f u) 0 s := by
    intro s
    have h := (hE s).mul (hf s)
    convert h using 1
    rw [mul_assoc, neg_mul, mul_neg, neg_add_cancel]
  have hconst : exp (t • (-B)) * f t = exp ((0 : ℝ) • (-B)) * f 0 :=
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  rw [zero_smul, exp_zero, one_mul, h0] at hconst
  have hinv : exp (t • B) * exp (t • (-B)) = 1 := by
    rw [← exp_add_of_commute ((Commute.refl B).neg_right.smul_left t |>.smul_right t), smul_neg,
      add_neg_cancel, exp_zero]
  calc f t = exp (t • B) * exp (t • (-B)) * f t := by rw [hinv, one_mul]
    _ = exp (t • B) * (exp (t • (-B)) * f t) := mul_assoc _ _ _
    _ = exp (t • B) := by rw [hconst, mul_one]

/-- **Exponential of a scalar plus a square root of a negative scalar.** -/
theorem exp_smul_of_sq_eq_neg {c ν : ℝ} (hν : ν ≠ 0) {B N : 𝔸} (hB : B = c • (1 : 𝔸) + N)
    (hN : N * N = -(ν ^ 2) • (1 : 𝔸)) (t : ℝ) :
    exp (t • B) =
      Real.exp (c * t) • (Real.cos (ν * t) • (1 : 𝔸) + (Real.sin (ν * t) / ν) • N) := by
  symm
  refine eq_exp_smul_of_hasDerivAt (f := fun s : ℝ =>
    Real.exp (c * s) • (Real.cos (ν * s) • (1 : 𝔸) + (Real.sin (ν * s) / ν) • N)) (fun s => ?_)
    (by simp) t
  have he : HasDerivAt (fun u : ℝ => Real.exp (c * u)) (Real.exp (c * s) * c) s := by
    simpa using ((hasDerivAt_id s).const_mul c).exp
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (ν * u)) (-Real.sin (ν * s) * ν) s := by
    simpa using ((hasDerivAt_id s).const_mul ν).cos
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (ν * u) / ν) (Real.cos (ν * s)) s := by
    have h := (((hasDerivAt_id s).const_mul ν).sin).div_const ν
    have e : Real.cos (ν * id s) * (ν * 1) / ν = Real.cos (ν * s) := by
      simp only [id, mul_one]; field_simp
    rw [e] at h
    exact h
  have hP : HasDerivAt (fun u : ℝ => Real.cos (ν * u) • (1 : 𝔸) + (Real.sin (ν * u) / ν) • N)
      ((-Real.sin (ν * s) * ν) • (1 : 𝔸) + Real.cos (ν * s) • N) s :=
    (hcos.smul_const (1 : 𝔸)).add (hsin.smul_const N)
  have h : HasDerivAt (fun u : ℝ =>
      Real.exp (c * u) • (Real.cos (ν * u) • (1 : 𝔸) + (Real.sin (ν * u) / ν) • N))
      (Real.exp (c * s) • ((-Real.sin (ν * s) * ν) • (1 : 𝔸) + Real.cos (ν * s) • N) +
        (Real.exp (c * s) * c) • (Real.cos (ν * s) • (1 : 𝔸) + (Real.sin (ν * s) / ν) • N)) s :=
    he.smul hP
  convert h using 1
  rw [hB]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hN, smul_add,
    smul_smul, neg_smul, smul_neg]
  match_scalars
  all_goals first | (field_simp; ring) | field_simp

end Algebra

section TwoStores

open Matrix
open scoped Matrix.Norms.Operator

/-- **The reference step of two stores, underdamped.** -/
theorem exp_twoStore {r₁ r₂ ω ν : ℝ} (hν : ν ≠ 0) (hν2 : ν ^ 2 = ω ^ 2 - ((r₁ - r₂) / 2) ^ 2)
    (H : ℝ) :
    exp (H • !![-r₁, -ω; ω, -r₂]) =
      Real.exp (-((r₁ + r₂) / 2) * H) •
        !![Real.cos (ν * H) - (r₁ - r₂) / 2 / ν * Real.sin (ν * H), -(ω / ν * Real.sin (ν * H));
           ω / ν * Real.sin (ν * H), Real.cos (ν * H) + (r₁ - r₂) / 2 / ν * Real.sin (ν * H)] := by
  have hB : (!![-r₁, -ω; ω, -r₂] : Matrix (Fin 2) (Fin 2) ℝ) =
      (-((r₁ + r₂) / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        !![-((r₁ - r₂) / 2), -ω; ω, (r₁ - r₂) / 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  have hN : (!![-((r₁ - r₂) / 2), -ω; ω, (r₁ - r₂) / 2] : Matrix (Fin 2) (Fin 2) ℝ) *
      !![-((r₁ - r₂) / 2), -ω; ω, (r₁ - r₂) / 2] = -(ν ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hν2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine (exp_smul_of_sq_eq_neg hν hB hN H).trans ?_
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

end TwoStores

end CoSimFoundations
