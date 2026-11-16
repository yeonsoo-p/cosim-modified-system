/-
The front in the basis, for a pair with equal dissipation (the paper, Cor 7.6): the algebra.

With `J = !![0, -1; 1, 0]` and the reference generator `A = -r • 1 + (h / H) • J` (two stores that
exchange energy, equal dissipation `r`, `h = ω H`):

* `exp (H • (c • 1 + ν • J)) = e^{cH} • (cos (ν H) • 1 + sin (ν H) • J)`;
* the generator `Ã = (log s̄ / H - r) • 1 + (π / (2H)) • J` has the one-step map
  `(s̄ e^{-rH}) • J`, a quarter turn scaled by `s̄ e^{-rH}`: the step of the stick of zero height with
  foot `s̄`, whose binding row lies on its wall (its diagonal vanishes);
* its difference from the reference is `Ã - A = (log s̄ / H) • 1 - ((h - π/2) / H) • J`:
  numerical dissipation `-(log s̄ / H) • 1`, numerical interconnection `-(ψ / H) • J` with the
  overshoot `ψ = h - π/2`, the same for every `s̄`.

That these sticks are the front is Thm 7.4 and is not formalised here.
-/
import CoSimFoundations.TwoStoreStep

open NormedSpace Matrix

namespace CoSimFoundations

open scoped Matrix.Norms.Operator

/-- The rotation generator of the plane. -/
def Jm : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem Jm_mul_Jm : Jm * Jm = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Exponential of a scaling plus a rotation generator.** -/
theorem exp_smul_one_add_smul_Jm {c ν : ℝ} (hν : ν ≠ 0) (H : ℝ) :
    exp (H • (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ν • Jm)) =
      Real.exp (c * H) • (Real.cos (ν * H) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        Real.sin (ν * H) • Jm) := by
  have hN : (ν • Jm) * (ν • Jm) = -(ν ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [smul_mul_smul_comm, Jm_mul_Jm]
    simp [pow_two]
  refine (exp_smul_of_sq_eq_neg hν rfl hN H).trans ?_
  congr 2
  rw [smul_smul, div_mul_cancel₀ _ hν]

/-- **The step of a front stick of zero height:** a quarter turn scaled by `s̄ e^{-rH}`. -/
theorem exp_front_stick {H s r : ℝ} (hH : 0 < H) (hs : 0 < s) :
    exp (H • ((Real.log s / H - r) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (Real.pi / (2 * H)) • Jm)) = (s * Real.exp (-r * H)) • Jm := by
  have hν : Real.pi / (2 * H) ≠ 0 := div_ne_zero Real.pi_ne_zero (by positivity)
  rw [exp_smul_one_add_smul_Jm hν H]
  have h1 : Real.pi / (2 * H) * H = Real.pi / 2 := by field_simp
  have h2 : (Real.log s / H - r) * H = Real.log s + -r * H := by
    field_simp
    ring
  rw [h1, h2, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.exp_add, Real.exp_log hs]
  simp

/-- **The front in the basis:** the difference of the stick with foot `s̄` from the reference
`A = -r • 1 + (h / H) • J` is `(log s̄ / H) • 1 - ((h - π/2) / H) • J`. -/
theorem front_difference {H : ℝ} (hH : H ≠ 0) (s r h : ℝ) :
    ((Real.log s / H - r) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (Real.pi / (2 * H)) • Jm) -
        ((-r) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (h / H) • Jm) =
      (Real.log s / H) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ((h - Real.pi / 2) / H) • Jm := by
  match_scalars <;> field_simp <;> ring

/-- The reference step for equal dissipation: `e^{-rH}` times the rotation by `h`. -/
theorem exp_reference_equal {H h : ℝ} (hH : H ≠ 0) (hh : h ≠ 0) (r : ℝ) :
    exp (H • ((-r) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (h / H) • Jm)) =
      Real.exp (-r * H) • (Real.cos h • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin h • Jm) := by
  rw [exp_smul_one_add_smul_Jm (div_ne_zero hh hH) H, div_mul_cancel₀ _ hH]

end CoSimFoundations
