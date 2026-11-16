/-
Gauss–Seidel mode for networks of scalar stores, one held sample: the step matrix, its triangular
factorisation and the conservation of total damping (the paper, Thm 4.4, end to end).

Store `i` runs after the stores `j < i` and uses their new samples, and the old samples of the
stores `j > i`. With `λ_i = a_i + b_i k_i c_i`, `E_i = e^{λ_i H}` and `γ_i = g(λ_i, H) b_i`
(`ScalarStores`), one step obeys, for every store,

  `x_i(H) = E_i x_i(0) + γ_i (Σ_{j<i} w i j c_j x_j(H) + Σ_{j>i} w i j c_j x_j(0))`,

that is `Lo · x(H) = R · x(0)` with `Lo` unit lower triangular and `R` upper triangular with the
`E_i` on its diagonal. Hence `x(H) = X x(0)` with `X = Lo⁻¹ R`, `det X = ∏ E_i`, and if
`X = exp (H • Ã)` then `tr Ã = Σ (a_i + b_i k_i c_i)`: the weights do not enter.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CoSimFoundations.ScalarStores
import CoSimFoundations.DetExp

open Real Matrix

namespace CoSimFoundations

namespace ScalarNet

variable {n : ℕ} (N : ScalarNet n)

/-- `γ_i = g(λ_i, H) b_i`: what a unit held input does to store `i` over one step. -/
noncomputable def inGain (H : ℝ) (k : Fin n → ℝ) (i : Fin n) : ℝ :=
  holdGain (N.rate k i) H * N.b i

/-- The left factor: identity minus the use of new samples of earlier stores. -/
noncomputable def gsLo (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then 1 else 0) - (if j < i then N.inGain H k i * w i j * N.c j else 0)

/-- The right factor: local exponentials plus the use of old samples of later stores. -/
noncomputable def gsR (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then exp (N.rate k i * H) else 0) +
    (if i < j then N.inGain H k i * w i j * N.c j else 0)

/-- The Gauss–Seidel step matrix. -/
noncomputable def gsStep (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (N.gsLo H k w)⁻¹ * N.gsR H k w

theorem gsLo_lower (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    (N.gsLo H k w).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hlt : i < j := hij
  simp [gsLo, hlt.ne, hlt.not_gt]

theorem gsR_upper (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    (N.gsR H k w).BlockTriangular id := by
  intro i j hij
  have hlt : j < i := hij
  simp [gsR, hlt.ne', hlt.not_gt]

theorem det_gsLo (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    (N.gsLo H k w).det = 1 := by
  rw [det_of_isLowerTriangular _ (N.gsLo_lower H k w)]
  exact Finset.prod_eq_one fun i _ => by simp [gsLo]

theorem det_gsR (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    (N.gsR H k w).det = ∏ i, exp (N.rate k i * H) := by
  rw [det_of_isUpperTriangular (N.gsR_upper H k w)]
  exact Finset.prod_congr rfl fun i _ => by simp [gsR]

/-- **The factorisation:** `Lo * X = R`. -/
theorem gsLo_mul_gsStep (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    N.gsLo H k w * N.gsStep H k w = N.gsR H k w := by
  have hu : IsUnit (N.gsLo H k w).det := by rw [det_gsLo]; exact isUnit_one
  rw [gsStep, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- **Total damping of a Gauss–Seidel step:** `det X = ∏ e^{λ_i H}`, whatever the weights. -/
theorem det_gsStep (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    (N.gsStep H k w).det = ∏ i, exp (N.rate k i * H) := by
  have h := congrArg det (N.gsLo_mul_gsStep H k w)
  rwa [det_mul, det_gsLo, one_mul, det_gsR] at h

/-- **The step matrix is the step.** If during one macro step every store obeys its equation with
the new samples of the earlier stores and the old samples of the later ones, then
`x(H) = X x(0)`. -/
theorem gs_step_eq (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) {x : Fin n → ℝ → ℝ}
    (hx : ∀ i t, HasDerivAt (x i)
      (N.a i * x i t + N.b i * ((∑ j, if j < i then w i j * (N.c j * x j H) else 0) +
        (∑ j, if i < j then w i j * (N.c j * x j 0) else 0) + k i * (N.c i * x i t))) t) :
    (fun i => x i H) = N.gsStep H k w *ᵥ fun i => x i 0 := by
  have hrow : N.gsLo H k w *ᵥ (fun i => x i H) = N.gsR H k w *ᵥ fun i => x i 0 := by
    funext i
    have h := scalar_step (lam := N.rate k i)
      (β := N.b i * ((∑ j, if j < i then w i j * (N.c j * x j H) else 0) +
        ∑ j, if i < j then w i j * (N.c j * x j 0) else 0)) (x := x i) (fun t => by
        convert hx i t using 1
        simp only [rate]; ring) H
    simp only [mulVec, dotProduct, gsLo, gsR, inGain, sub_mul, add_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have e1 : (∑ j, if j < i then holdGain (N.rate k i) H * N.b i * w i j * N.c j * x j H else 0) =
        holdGain (N.rate k i) H * (N.b i * ∑ j, if j < i then w i j * (N.c j * x j H) else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    have e2 : (∑ j, if i < j then holdGain (N.rate k i) H * N.b i * w i j * N.c j * x j 0 else 0) =
        holdGain (N.rate k i) H * (N.b i * ∑ j, if i < j then w i j * (N.c j * x j 0) else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    rw [e1, e2, h]
    ring
  have hu : IsUnit (N.gsLo H k w).det := by rw [det_gsLo]; exact isUnit_one
  have := congrArg (fun v => (N.gsLo H k w)⁻¹ *ᵥ v) hrow
  simp only [mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, one_mulVec] at this
  rw [this, gsStep]

open scoped Matrix.Norms.Operator in
/-- **Conservation of total damping.** If the Gauss–Seidel step has a modified system,
`X = exp (H • Ã)` with `H ≠ 0`, then `tr Ã = Σ (a_i + b_i k_i c_i)`: the trace of the modified
system is that of the uncoupled stores plus the gains, whatever the weights are. -/
theorem trace_modified_gs {H : ℝ} (hH : H ≠ 0) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (At : Matrix (Fin n) (Fin n) ℝ) (h : N.gsStep H k w = NormedSpace.exp (H • At)) :
    At.trace = ∑ i, (N.a i + N.b i * k i * N.c i) := by
  have h1 := N.det_gsStep H k w
  rw [h, det_exp, trace_smul, smul_eq_mul, ← Real.exp_sum, Real.exp_eq_exp] at h1
  have h2 : H * At.trace = H * ∑ i, N.rate k i := by
    rw [h1, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  exact mul_left_cancel₀ hH h2

end ScalarNet

end CoSimFoundations
