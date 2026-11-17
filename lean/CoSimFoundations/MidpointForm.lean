/-
The exact midpoint form of the zero-order hold (the paper, Section `sec:half`: the statement
behind "a held sample is half a macro step old, a new sample half a macro step ahead", without a
remainder).

**Setting** (`HalfStepZOH`): `A = A₀ + A_c` (`blockDiag`, `coupling`), `φ = phiOne (H • A₀)`
(`φ₁(H A₀) = ∫₀¹ e^{s H A₀} ds`, block diagonal, `e^{H A₀} = 1 + H φ A₀`), the zero-order hold
`S.zoh A hA H` with `F = e^{H A₀}`, old samples `zohOld`, new samples `zohNew` and the one-step
map `X = F + M + N X`. The signed coupling is `A_ς` (`signedCoupling`).

**Every hold** (`held_midpoint_ring`, `held_midpoint`): in a ring, `X = F + M + N X` implies
  `(1 + F - (N - M)) (X - 1) = (F - 1 + M + N) (X + 1)`,
that is `((1 + F)/2 - (N - M)/2) (X - 1) = (F - 1 + M + N) (X + 1)/2`.
Proof: the difference of the two sides is `2 (X - (F + M + N X))`.

**The coefficients of the zero-order hold by the stages** (`zohNew_eq`, `zohOld_eq`; these and
the statements on `couplingNew`, `couplingOld` named below are in `HalfStepZOH`): with
`A_new` the coupling from the subsystems of an earlier stage (`couplingNew`) and `A_old` the rest
of the coupling (`couplingOld`), `A_old + A_new = A_c`, `A_new - A_old = A_ς`
(`couplingOld_add_couplingNew`, `couplingNew_sub_couplingOld`),
  `zohNew = H φ A_new`,   `zohOld = H φ A_old`,
because `φ` is block diagonal and the stage of a state is that of its subsystem. So the step is
`x' - x = H φ (A₀ x + A_old x + A_new x')`.

**The midpoint form** (`zoh_midpoint_of_eq`, `zoh_midpoint`), exact, for every assignment of
stages (shared stages included) and every `H`:
  `(1 + (H/2) φ A₀ - (H/2) φ A_ς) (X - 1) = (H/2) φ A (X + 1)`.
Proof: the identity of every hold with `1 + F = 2 + H φ A₀`, `N - M = H φ A_ς`,
`F - 1 + M + N = H φ A` (`φ` commutes with `A₀`, `mul_phiOne_comm`).

**With `Ψ = φ⁻¹ + (H/2) A₀`** (`midpointPsi`; `zoh_midpoint_of_left_inv`, `zoh_midpoint_psi`,
`zoh_midpoint_psi_mulVec`): if `φ` is invertible,
  `(Ψ - (H/2) A_ς) (X - 1) = (H/2) A (X + 1)`,
  `(Ψ - (H/2) A_ς) (x' - x) = H A (x' + x)/2` for `x' = X x`.
`φ₁(Z)` is not invertible for every `Z` (it vanishes on an eigenvalue `2πi k`, `k ≠ 0`, of `Z`),
so the hypothesis `IsUnit (det φ)` is needed. It holds if `‖H A₀‖ ≤ 1` (`isUnit_det_phiOne`:
`‖φ₁(W) - 1‖ ≤ ‖W‖/2 + ‖W‖²/6 · e^{‖W‖} < 1`), in particular if `0 ≤ H` and `H ‖A‖ ≤ 1`
(`zoh_midpoint_psi_of_le`, `zoh_midpoint_psi_of_norm_le`).
-/
import CoSimFoundations.ZeroOrderHold

open Matrix
open scoped Nat

namespace CoSimFoundations

/-! ### Every hold -/

/-- **The midpoint identity of every hold, in a ring:** if `X = F + M + N X`, then
`(1 + F - (N - M)) (X - 1) = (F - 1 + M + N) (X + 1)`. -/
theorem held_midpoint_ring {R : Type*} [Ring R] {F M N X : R} (hX : X = F + M + N * X) :
    (1 + F - (N - M)) * (X - 1) = (F - 1 + M + N) * (X + 1) := by
  have key : (1 + F - (N - M)) * (X - 1) - (F - 1 + M + N) * (X + 1) =
      (X - (F + M + N * X)) + (X - (F + M + N * X)) := by
    noncomm_ring
  rw [← sub_eq_zero, key, ← hX, sub_self, add_zero]

/-! ### `φ₁` in a Banach algebra -/

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `φ₁(W)` commutes with `W`. -/
theorem mul_phi_one_comm (W : 𝔸) : W * phi 1 W = phi 1 W * W := by
  have h1 : HasSum (fun j : ℕ => W * ((((j + 1)! : ℕ) : ℝ)⁻¹ • W ^ j)) (W * phi 1 W) :=
    (summable_phi 1 W).hasSum.mul_left W
  have h2 : HasSum (fun j : ℕ => ((((j + 1)! : ℕ) : ℝ)⁻¹ • W ^ j) * W) (phi 1 W * W) :=
    (summable_phi 1 W).hasSum.mul_right W
  have e : (fun j : ℕ => W * ((((j + 1)! : ℕ) : ℝ)⁻¹ • W ^ j)) =
      fun j : ℕ => ((((j + 1)! : ℕ) : ℝ)⁻¹ • W ^ j) * W :=
    funext fun j => by rw [mul_smul_comm, smul_mul_assoc, ← pow_succ', ← pow_succ]
  rw [e] at h1
  exact h1.unique h2

/-- `‖φ₁(W) - 1‖ ≤ ‖W‖/2 + ‖W‖²/6 · e^{‖W‖}`. -/
theorem norm_phi_one_sub_one_le_add (W : 𝔸) :
    ‖phi 1 W - 1‖ ≤ ‖W‖ / 2 + ‖W‖ ^ 2 / 6 * Real.exp ‖W‖ := by
  have e : phi 1 W - 1 = (2 : ℝ)⁻¹ • W + W * W * phi 3 W := by
    rw [phi_one_eq]
    abel
  have h2 : ‖(2 : ℝ)⁻¹ • W‖ = ‖W‖ / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h2.le (norm_sq_mul_phi_three_le W))

/-- **`φ₁(W)` is invertible for `‖W‖ ≤ 1`:** then `‖φ₁(W) - 1‖ ≤ 1/2 + e/6 < 1`. -/
theorem isUnit_phi_one {W : 𝔸} (hW : ‖W‖ ≤ 1) : IsUnit (phi 1 W) := by
  have h1 := norm_phi_one_sub_one_le_add W
  have h2 : Real.exp ‖W‖ ≤ 3 := (Real.exp_le_exp.2 hW).trans Real.exp_one_lt_three.le
  have h3 : ‖W‖ ^ 2 / 6 * Real.exp ‖W‖ ≤ 1 ^ 2 / 6 * Real.exp 1 :=
    mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg W) hW 2) (by norm_num))
      (Real.exp_le_exp.2 hW) (Real.exp_nonneg _) (by norm_num)
  have h4 := Real.exp_one_lt_three
  have h5 : ‖1 - phi 1 W‖ < 1 := by
    rw [norm_sub_rev]
    linarith
  have h6 := isUnit_one_sub_of_norm_lt_one h5
  rwa [sub_sub_cancel] at h6

end Algebra

open OneStep

variable {n : ℕ}

/-! ### `φ₁` of a matrix -/

/-- `φ₁(Z)` commutes with `Z`, for a real matrix. -/
theorem mul_phiOne_comm (Z : Matrix (Fin n) (Fin n) ℝ) : Z * phiOne Z = phiOne Z * Z := by
  have h : opE (Z * phiOne Z) = opE (phiOne Z * Z) := by
    rw [opE_mul, opE_mul, opE_phiOne]
    exact mul_phi_one_comm _
  exact (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective h

/-- `e^Z = 1 + φ₁(Z) Z` for a real matrix. -/
theorem exp_eq_one_add_phiOne_mul (Z : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp Z = 1 + phiOne Z * Z := by
  rw [exp_eq_one_add_mul_phiOne, mul_phiOne_comm]

/-- **`φ₁(Z)` is an invertible matrix if `‖Z‖ ≤ 1`** (spectral norm). -/
theorem isUnit_det_phiOne {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : ‖opE Z‖ ≤ 1) :
    IsUnit (phiOne Z).det := by
  have h : IsUnit (opE (phiOne Z)) := by
    rw [opE_phiOne]
    exact isUnit_phi_one hZ
  have h2 := h.map (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm
  rw [StarAlgEquiv.symm_apply_apply] at h2
  exact (Matrix.isUnit_iff_isUnit_det _).1 h2

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- **The midpoint identity of every scheme with one held sample:**
`((1 + F)/2 - (N - M)/2) (X - 1) = (F - 1 + M + N) (X + 1)/2`. -/
theorem held_midpoint :
    ((1 / 2 : ℝ) • (1 + S.F) - (1 / 2 : ℝ) • (S.N - S.M)) * (S.X - 1) =
      (1 / 2 : ℝ) • ((S.F - 1 + S.M + S.N) * (S.X + 1)) := by
  rw [← smul_sub, smul_mul_assoc, held_midpoint_ring S.hX]

/-! ### The coefficients of the zero-order hold with `φ = φ₁(H A₀)` -/

/-- `e^{H A₀} = 1 + H φ A₀`, `φ = φ₁(H A₀)`. -/
theorem exp_smul_blockDiag_eq (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    NormedSpace.exp (H • S.blockDiag A) =
      1 + H • (phiOne (H • S.blockDiag A) * S.blockDiag A) := by
  rw [exp_eq_one_add_phiOne_mul, mul_smul_comm]

/-- The coefficients of the new samples are `H φ A_new`, `φ = φ₁(H A₀)`. -/
theorem zohNew_eq_smul (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.zohNew A H = H • (phiOne (H • S.blockDiag A) * S.couplingNew A) := by
  rw [S.zohNew_eq, zohKernel, smul_mul_assoc]

/-- The coefficients of the old samples are `H φ A_old`, `φ = φ₁(H A₀)`. -/
theorem zohOld_eq_smul (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.zohOld A H = H • (phiOne (H • S.blockDiag A) * S.couplingOld A) := by
  rw [S.zohOld_eq, zohKernel, smul_mul_assoc]

/-- **What the zero-order hold integrates, times the macro step:**
`e^{H A₀} - 1 + zohOld + zohNew = H φ A`, `φ = φ₁(H A₀)`. -/
theorem exp_sub_one_add_zohOld_add_zohNew (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    NormedSpace.exp (H • S.blockDiag A) - 1 + S.zohOld A H + S.zohNew A H =
      H • (phiOne (H • S.blockDiag A) * A) := by
  have hA : phiOne (H • S.blockDiag A) * A =
      phiOne (H • S.blockDiag A) * S.blockDiag A +
        (phiOne (H • S.blockDiag A) * S.couplingOld A +
          phiOne (H • S.blockDiag A) * S.couplingNew A) := by
    rw [← mul_add, ← mul_add, S.couplingOld_add_couplingNew, S.blockDiag_add_coupling]
  rw [S.exp_smul_blockDiag_eq, S.zohNew_eq_smul, S.zohOld_eq_smul, hA]
  module

/-- **The matrix on the left of the midpoint form of the zero-order hold:**
`½ (1 + e^{H A₀}) - ½ (zohNew - zohOld) = 1 + (H/2) φ A₀ - (H/2) φ A_ς`, `φ = φ₁(H A₀)`. -/
theorem half_one_add_exp_sub_half_zoh (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    (1 / 2 : ℝ) • (1 + NormedSpace.exp (H • S.blockDiag A)) -
        (1 / 2 : ℝ) • (S.zohNew A H - S.zohOld A H) =
      1 + (H / 2) • (phiOne (H • S.blockDiag A) * S.blockDiag A) -
        (H / 2) • (phiOne (H • S.blockDiag A) * S.signedCoupling A) := by
  have hς : phiOne (H • S.blockDiag A) * S.signedCoupling A =
      phiOne (H • S.blockDiag A) * S.couplingNew A -
        phiOne (H • S.blockDiag A) * S.couplingOld A := by
    rw [← mul_sub, S.couplingNew_sub_couplingOld]
  rw [S.exp_smul_blockDiag_eq, S.zohNew_eq_smul, S.zohOld_eq_smul, hς]
  module

/-! ### The midpoint form -/

/-- **The exact midpoint form of the zero-order hold, without an inverse.** Let
`φ = φ₁(H A₀)`. Every matrix `X` with `X = e^{H A₀} + zohOld + zohNew · X` (the one-step map of
the zero-order hold in the assignment of stages of `S`, shared stages included) obeys
`(1 + (H/2) φ A₀ - (H/2) φ A_ς) (X - 1) = (H/2) φ A (X + 1)`. -/
theorem zoh_midpoint_of_eq (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X = NormedSpace.exp (H • S.blockDiag A) + S.zohOld A H + S.zohNew A H * X) :
    (1 + (H / 2) • (phiOne (H • S.blockDiag A) * S.blockDiag A) -
        (H / 2) • (phiOne (H • S.blockDiag A) * S.signedCoupling A)) * (X - 1) =
      (H / 2) • (phiOne (H • S.blockDiag A) * A * (X + 1)) := by
  have e1 : 1 + NormedSpace.exp (H • S.blockDiag A) - (S.zohNew A H - S.zohOld A H) =
      (2 : ℝ) • (1 + (H / 2) • (phiOne (H • S.blockDiag A) * S.blockDiag A) -
        (H / 2) • (phiOne (H • S.blockDiag A) * S.signedCoupling A)) := by
    rw [← S.half_one_add_exp_sub_half_zoh A H]
    module
  have e2 : NormedSpace.exp (H • S.blockDiag A) - 1 + S.zohOld A H + S.zohNew A H =
      (2 : ℝ) • ((H / 2) • (phiOne (H • S.blockDiag A) * A)) := by
    rw [S.exp_sub_one_add_zohOld_add_zohNew A H]
    module
  have h := held_midpoint_ring hX
  rw [e1, e2, smul_mul_assoc, smul_mul_assoc] at h
  have h' := smul_right_injective (Matrix (Fin n) (Fin n) ℝ) (two_ne_zero (α := ℝ)) h
  rw [h', smul_mul_assoc]

/-- **The exact midpoint form of the zero-order hold, with a left inverse of `φ`.** If
`φi · φ₁(H A₀) = 1`, every matrix `X` with `X = e^{H A₀} + zohOld + zohNew · X` obeys
`(φi + (H/2) A₀ - (H/2) A_ς) (X - 1) = (H/2) A (X + 1)`. -/
theorem zoh_midpoint_of_left_inv (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    {X φi : Matrix (Fin n) (Fin n) ℝ} (hi : φi * phiOne (H • S.blockDiag A) = 1)
    (hX : X = NormedSpace.exp (H • S.blockDiag A) + S.zohOld A H + S.zohNew A H * X) :
    (φi + (H / 2) • S.blockDiag A - (H / 2) • S.signedCoupling A) * (X - 1) =
      (H / 2) • (A * (X + 1)) := by
  have h := congrArg (fun T => φi * T) (S.zoh_midpoint_of_eq A H hX)
  have e1 : φi * (1 + (H / 2) • (phiOne (H • S.blockDiag A) * S.blockDiag A) -
      (H / 2) • (phiOne (H • S.blockDiag A) * S.signedCoupling A)) =
      φi + (H / 2) • S.blockDiag A - (H / 2) • S.signedCoupling A := by
    rw [mul_sub, mul_add, mul_one, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc, hi,
      one_mul, one_mul]
  have e2 : φi * ((H / 2) • (phiOne (H • S.blockDiag A) * A * (X + 1))) =
      (H / 2) • (A * (X + 1)) := by
    rw [mul_smul_comm, mul_assoc, ← mul_assoc, hi, one_mul]
  have h3 : φi * ((1 + (H / 2) • (phiOne (H • S.blockDiag A) * S.blockDiag A) -
      (H / 2) • (phiOne (H • S.blockDiag A) * S.signedCoupling A)) * (X - 1)) =
      φi * ((H / 2) • (phiOne (H • S.blockDiag A) * A * (X + 1))) := h
  rw [← mul_assoc, e1, e2] at h3
  exact h3

/-- The matrix `Ψ = φ₁(H A₀)⁻¹ + (H/2) A₀` of the midpoint form (the matrix inverse; it is the
inverse of `φ₁(H A₀)` if that matrix is invertible, `isUnit_det_phiOne`). -/
noncomputable def midpointPsi (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (phiOne (H • S.blockDiag A))⁻¹ + (H / 2) • S.blockDiag A

/-- **The exact midpoint form with `Ψ`, for every solution of the implicit equation.** If
`φ₁(H A₀)` is invertible, every matrix `X` with `X = e^{H A₀} + zohOld + zohNew · X` obeys
`(Ψ - (H/2) A_ς) (X - 1) = (H/2) A (X + 1)`. -/
theorem zoh_midpoint_psi_of_eq (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X = NormedSpace.exp (H • S.blockDiag A) + S.zohOld A H + S.zohNew A H * X) :
    (S.midpointPsi A H - (H / 2) • S.signedCoupling A) * (X - 1) = (H / 2) • (A * (X + 1)) :=
  S.zoh_midpoint_of_left_inv A H (Matrix.nonsing_inv_mul _ hφ) hX

/-- **The exact midpoint form of the zero-order hold `S.zoh A hA H`, without an inverse**
(every assignment of stages, every `H`): with `φ = φ₁(H A₀)` and `X` its one-step map,
`(1 + (H/2) φ A₀ - (H/2) φ A_ς) (X - 1) = (H/2) φ A (X + 1)`. -/
theorem zoh_midpoint (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (1 + (H / 2) • (phiOne (H • S.blockDiag A) * S.blockDiag A) -
        (H / 2) • (phiOne (H • S.blockDiag A) * S.signedCoupling A)) *
        ((S.zoh A hA H).X - 1) =
      (H / 2) • (phiOne (H • S.blockDiag A) * A * ((S.zoh A hA H).X + 1)) :=
  S.zoh_midpoint_of_eq A H (S.zoh A hA H).hX

/-- **The exact midpoint form of the zero-order hold `S.zoh A hA H`:** if `φ₁(H A₀)` is
invertible, `(Ψ - (H/2) A_ς) (X - 1) = (H/2) A (X + 1)`, `Ψ = φ₁(H A₀)⁻¹ + (H/2) A₀`, for every
assignment of stages. -/
theorem zoh_midpoint_psi (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (S.midpointPsi A H - (H / 2) • S.signedCoupling A) * ((S.zoh A hA H).X - 1) =
      (H / 2) • (A * ((S.zoh A hA H).X + 1)) :=
  S.zoh_midpoint_psi_of_eq A H hφ (S.zoh A hA H).hX

/-- **The exact midpoint form on a state:** if `φ₁(H A₀)` is invertible and `x' = X x` is the
step of the zero-order hold `S.zoh A hA H`, then `(Ψ - (H/2) A_ς) (x' - x) = H A (x' + x)/2`. -/
theorem zoh_midpoint_psi_mulVec (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) (x : Fin n → ℝ) :
    (S.midpointPsi A H - (H / 2) • S.signedCoupling A) *ᵥ ((S.zoh A hA H).X *ᵥ x - x) =
      H • (A *ᵥ ((1 / 2 : ℝ) • ((S.zoh A hA H).X *ᵥ x + x))) := by
  have h := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ => T *ᵥ x) (S.zoh_midpoint_psi A hA H hφ)
  have e1 : (S.zoh A hA H).X *ᵥ x - x = ((S.zoh A hA H).X - 1) *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have e2 : (S.zoh A hA H).X *ᵥ x + x = ((S.zoh A hA H).X + 1) *ᵥ x := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have h3 : ((S.midpointPsi A H - (H / 2) • S.signedCoupling A) * ((S.zoh A hA H).X - 1)) *ᵥ x =
      ((H / 2) • (A * ((S.zoh A hA H).X + 1))) *ᵥ x := h
  rw [e1, e2, Matrix.mulVec_mulVec, h3, Matrix.smul_mulVec, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, smul_smul]
  congr 1
  ring

/-- **The midpoint form with `Ψ` for a small macro step:** for `0 ≤ H` and `H ‖A₀‖ ≤ 1` the
matrix `φ₁(H A₀)` is invertible, and the zero-order hold `S.zoh A hA H`, in every assignment of
stages, obeys `(Ψ - (H/2) A_ς) (X - 1) = (H/2) A (X + 1)`. -/
theorem zoh_midpoint_psi_of_le (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 ≤ H) (h0 : H * ‖opE (S.blockDiag A)‖ ≤ 1) :
    (S.midpointPsi A H - (H / 2) • S.signedCoupling A) * ((S.zoh A hA H).X - 1) =
      (H / 2) • (A * ((S.zoh A hA H).X + 1)) := by
  refine S.zoh_midpoint_psi A hA H (isUnit_det_phiOne ?_)
  rw [opE_smul, norm_smul, Real.norm_of_nonneg hH]
  exact h0

/-- **The midpoint form with `Ψ` under `H ‖A‖ ≤ 1`:** for `0 ≤ H` and `H ‖A‖ ≤ 1` (spectral
norm of the monolithic matrix) the zero-order hold `S.zoh A hA H`, in every assignment of stages,
obeys `(Ψ - (H/2) A_ς) (X - 1) = (H/2) A (X + 1)`. -/
theorem zoh_midpoint_psi_of_norm_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1) :
    (S.midpointPsi A H - (H / 2) • S.signedCoupling A) * ((S.zoh A hA H).X - 1) =
      (H / 2) • (A * ((S.zoh A hA H).X + 1)) :=
  S.zoh_midpoint_psi_of_le A hA hH
    ((mul_le_mul_of_nonneg_left (S.norm_opE_blockDiag_le A) hH).trans hAH)

end HeldScheme

end CoSimFoundations
