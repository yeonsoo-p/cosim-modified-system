/-
Conservation of total damping in sequential coupling (the paper, Thm 4.4).

In Gauss–Seidel mode with one held sample and no feedthrough the step matrix `X` satisfies
`Lo * X = R`, where, in the order of execution `b`, `Lo` is block lower triangular with identity
diagonal blocks (a subsystem uses the new samples of those that ran before it) and `R` is block
upper triangular with the local exponentials `exp (H • G a)` on the diagonal,
`G a = A_a + B_a K_a C_a`. Then `det X = ∏ det (exp (H • G a))`, and if `X = exp (H • Ã)`:

  `tr Ã = ∑ a, tr (G a)`:

the total damping of the modified system does not depend on the coupling weights.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import CoSimFoundations.DetExp

open Matrix NormedSpace

namespace CoSimFoundations

open scoped Matrix.Norms.Operator

variable {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] [DecidableEq α] [LinearOrder α]

/-- If a block lower triangular factor with identity diagonal blocks turns `X` into a block upper
triangular matrix `R`, then `det X` is the product of the determinants of the diagonal blocks of
`R`. -/
theorem det_eq_prod_det_blocks_of_factor (b : n → α) (Lo X R : Matrix n n ℝ)
    (hLo : Loᵀ.BlockTriangular b) (hLo1 : ∀ a, Lo.toSquareBlock b a = 1)
    (hR : R.BlockTriangular b) (h : Lo * X = R) :
    X.det = ∏ a, (R.toSquareBlock b a).det := by
  have hdetLo : Lo.det = 1 := by
    rw [← det_transpose, hLo.det_fintype]
    refine Finset.prod_eq_one fun a _ => ?_
    have : Loᵀ.toSquareBlock b a = (Lo.toSquareBlock b a)ᵀ := rfl
    rw [this, hLo1 a, transpose_one, det_one]
  have h1 := congrArg det h
  rw [det_mul, hdetLo, one_mul] at h1
  rw [h1, hR.det_fintype]

/-- **Conservation of total damping.** With `Lo * exp (H • Ã) = R` as above and diagonal blocks
`exp (H • G a)` of `R`: `tr Ã = ∑ a, tr (G a)`, whatever the off-diagonal blocks are. -/
theorem trace_modified_eq_sum_trace (b : n → α) {H : ℝ} (hH : H ≠ 0) (At Lo R : Matrix n n ℝ)
    (G : ∀ a, Matrix { i // b i = a } { i // b i = a } ℝ)
    (hLo : Loᵀ.BlockTriangular b) (hLo1 : ∀ a, Lo.toSquareBlock b a = 1)
    (hR : R.BlockTriangular b) (hblocks : ∀ a, R.toSquareBlock b a = exp (H • G a))
    (h : Lo * exp (H • At) = R) :
    At.trace = ∑ a, (G a).trace := by
  have h1 := det_eq_prod_det_blocks_of_factor b Lo (exp (H • At)) R hLo hLo1 hR h
  simp only [hblocks, det_exp, trace_smul, smul_eq_mul] at h1
  rw [← Real.exp_sum, Real.exp_eq_exp, ← Finset.mul_sum] at h1
  exact mul_left_cancel₀ hH h1

end CoSimFoundations
