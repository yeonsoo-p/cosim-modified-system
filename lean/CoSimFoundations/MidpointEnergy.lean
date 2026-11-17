/-
The exact energy balance of the zero-order hold for subsystems with dynamics of their own: the
matrix algebra (the paper, Section "Energy stored and energy created", Proposition `prop:lent`;
part (iii) of that proposition is the case `A_i = 0`, which is `StoredEnergy` /
`LosslessEnergy`. The statements here are the exact form for `A_i ≠ 0`).

**Setting.** Real `n × n` matrices. The monolithic matrix is `A = A₀ + A_old + A_new`, `A₀` the
part inside the subsystems, `A_old + A_new = A_c` the coupling, `A_new` the blocks whose source
runs at an earlier stage. With `φ = φ₁(H A₀) = phiOne (H • A₀)` the one-step map `X` of the
zero-order hold obeys the implicit equation
  `X - 1 = H φ (A₀ + A_old + A_new X)`.                                             (hX)
The signed coupling is `A_ς = A_new - A_old = A_seq - A_par` (links between two stages, links
within one stage). `φi` is a left inverse of `φ`, and
  `Ψ = φi + (H/2) A₀` (`psi`),   `Q = Ψ - (H/2) A_seq` (`storedQ`).

**Statements.**
* `midpoint_rel`: from (hX), `(Q + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`. Proof: multiply (hX)
  by `φi` and use `A₀ + A_old + A_new X = ½ A (X+1) - ½ A₀ (X-1) + ½ A_ς (X-1)`.
* (a) `transpose_inv_phiOne_of_skew`, `psi_transpose_of_skew`: if `A₀ᵀ = -A₀` and
  `φi φ₁(H A₀) = 1`, then `φiᵀ = φi + H A₀` and `Ψᵀ = Ψ`. Proof: `φ₁(Z)ᵀ = φ₁(Zᵀ)`
  (`phiOne_transpose`), `φ₁(-Z) = e^{-Z} φ₁(Z)` (`phiOne_neg`, from `φ₁(Z) = ∫₀¹ e^{sZ} ds` and
  the substitution `s ↦ 1 - s`), so `φᵀ = e^{-H A₀} φ`; and `φi + H A₀ = φi e^{H A₀}` because
  `e^{H A₀} = 1 + H A₀ φ` and `φ` commutes with `A₀` (`commute_phiOne`).
* (b) `energy_balance`: if `Ψᵀ = Ψ`, `A_seqᵀ = A_seq`, `A_parᵀ = -A_par`, then for every `x`, with
  `x' = X x`, `x̄ = ½ (x' + x)`:
    `½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x)`.
  Proof: `Q` is symmetric, so the left side is `x̄ᵀ Q (x' - x)`; insert `midpoint_rel`.
  `energy_balance_lossless`: if moreover `Aᵀ = -A`, `x'ᵀ Q x' - xᵀ Q x = H (A_par x̄)ᵀ (x' - x)`.
  The same as a matrix identity (`transpose_mul_mul_sub`):
    `Xᵀ Q X - Q = (H/4) (X+1)ᵀ (A + Aᵀ) (X+1) + (H/2) (Xᵀ A_par - A_par X)`.
* (c) `invariant`, `invariant_pow`: if `A_par = 0` (that is `A_new - A_old = A_seq`), `Q` is
  symmetric and `Aᵀ = -A`, then `Xᵀ Q X = Q` and `(X^k)ᵀ Q X^k = Q` for all `k`.
* (d) `norm_pow_sq_le`: if moreover `lmin ‖y‖² ≤ yᵀ Q y ≤ lmax ‖y‖²` with `lmin > 0`, then
  `‖X^k x‖² ≤ lmax/lmin ‖x‖²` for all `k` and `x`.

The theorems with the suffix `_of_rel` start from the relation of `midpoint_rel` with any `Q`.
`MidpointEnergyZOH` instantiates the statements with the zero-order hold of `HalfStepZOH`.

**Hypotheses that are not derived here.** A left inverse `φi` of `φ₁(H A₀)` is a hypothesis.
In (b) the symmetry of `Ψ` is a hypothesis; it is proved in (a) for lossless subsystems only.
The bounds of the form `Q` in (d) are hypotheses.
-/
import CoSimFoundations.StoredEnergy
import CoSimFoundations.HalfStepZOH
import CoSimFoundations.BarrierConstants

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace MidpointEnergy

open OneStep

/-! ### `φ₁`: reflection, transpose, commutation -/

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `φ₁(-Z) = e^{-Z} φ₁(Z)` in a real Banach algebra: `φ₁(Z) = ∫₀¹ e^{sZ} ds`, and
`e^{-Z} e^{sZ} = e^{-(1-s)Z}`. -/
theorem phi_one_neg (Z : 𝔸) : phi 1 (-Z) = NormedSpace.exp (-Z) * phi 1 Z := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have h1 := smul_phi_one_eq_integral (-Z) 1
  have h2 := smul_phi_one_eq_integral Z 1
  simp only [one_smul] at h1 h2
  have hc : Continuous fun s : ℝ => NormedSpace.exp (s • Z) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have h3 := (ContinuousLinearMap.mul ℝ 𝔸 (NormedSpace.exp (-Z))).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  have h4 := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (fun s : ℝ => NormedSpace.exp (s • -Z)) 1
  rw [sub_self, sub_zero] at h4
  rw [h1, h2]
  refine h4.symm.trans (Eq.trans (intervalIntegral.integral_congr fun s _ => ?_) h3)
  show NormedSpace.exp ((1 - s) • -Z) = NormedSpace.exp (-Z) * NormedSpace.exp (s • Z)
  have hcomm : Commute (-Z) (s • Z) := ((Commute.refl Z).smul_right s).neg_left
  rw [← NormedSpace.exp_add_of_commute hcomm]
  congr 1
  module

end Algebra

variable {n : ℕ}

/-- The operator of the negative of a matrix. -/
theorem opE_neg (A : Matrix (Fin n) (Fin n) ℝ) : opE (-A) = -opE A := map_neg _ A

/-- `φ₁(-Z) = e^{-Z} φ₁(Z)` for a real matrix. -/
theorem phiOne_neg (Z : Matrix (Fin n) (Fin n) ℝ) :
    phiOne (-Z) = NormedSpace.exp (-Z) * phiOne Z := by
  have h : opE (phiOne (-Z)) = opE (NormedSpace.exp (-Z) * phiOne Z) := by
    rw [opE_phiOne, opE_mul, opE_exp, opE_phiOne, opE_neg]
    exact phi_one_neg _
  exact (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective h

/-- `φ₁(Z)ᵀ = φ₁(Zᵀ)` for a real matrix. -/
theorem phiOne_transpose (Z : Matrix (Fin n) (Fin n) ℝ) : (phiOne Z)ᵀ = phiOne Zᵀ := by
  unfold phiOne
  rw [Matrix.transpose_tsum]
  refine tsum_congr fun j => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow]

/-- A matrix that commutes with `Z` commutes with `φ₁(Z)`. -/
theorem commute_phiOne {B Z : Matrix (Fin n) (Fin n) ℝ} (h : Commute B Z) :
    Commute B (phiOne Z) := by
  have h1 := (hasSum_phiOne Z).mul_left B
  have h2 := (hasSum_phiOne Z).mul_right B
  have e : (fun j : ℕ => B * ((((j + 1).factorial : ℕ) : ℝ)⁻¹ • Z ^ j)) =
      fun j : ℕ => ((((j + 1).factorial : ℕ) : ℝ)⁻¹ • Z ^ j) * B := by
    funext j
    rw [Matrix.mul_smul, Matrix.smul_mul, (h.pow_right j).eq]
  rw [e] at h1
  exact h1.unique h2

/-- `φ₁(0) = 1`. -/
theorem _root_.CoSimFoundations.HeldScheme.phiOne_zero_eq_one :
    phiOne (0 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h2 := (hasSum_phiOne (0 : Matrix (Fin n) (Fin n) ℝ)).unique
    (hasSum_single (f := fun j : ℕ => (((j + 1).factorial : ℕ) : ℝ)⁻¹ •
      (0 : Matrix (Fin n) (Fin n) ℝ) ^ j) 0 fun j hj => by
        rw [zero_pow hj, smul_zero])
  rw [h2]
  simp

open scoped Matrix.Norms.Operator in
/-- `e^Z e^{-Z} = 1` for a real matrix. -/
theorem exp_mul_exp_neg (Z : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp Z * NormedSpace.exp (-Z) = 1 :=
  _root_.CoSimFoundations.exp_mul_exp_neg Z

/-- **The transpose of the inverse of `φ₁(H A₀)` for a lossless `A₀`.** If `A₀ᵀ = -A₀` and `φi`
is a left inverse of `φ = φ₁(H A₀)`, then `φiᵀ = φi + H A₀`: `φᵀ = φ₁(-H A₀) = e^{-H A₀} φ` and
`φi + H A₀ = φi e^{H A₀}`. -/
theorem transpose_inv_phiOne_of_skew {A0 φi : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hA0 : A0ᵀ = -A0) (hφ : φi * phiOne (H • A0) = 1) : φiᵀ = φi + H • A0 := by
  have hT : (phiOne (H • A0))ᵀ = NormedSpace.exp (-(H • A0)) * phiOne (H • A0) := by
    rw [phiOne_transpose, Matrix.transpose_smul, hA0, smul_neg, phiOne_neg]
  have hc : H • A0 * phiOne (H • A0) = phiOne (H • A0) * (H • A0) :=
    (commute_phiOne (Commute.refl (H • A0))).eq
  have hφ' : phiOne (H • A0) * φi = 1 := mul_eq_one_comm.1 hφ
  have h1 : φiᵀ * (phiOne (H • A0))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hφ', Matrix.transpose_one]
  have e : φi + H • A0 = φi * NormedSpace.exp (H • A0) := by
    rw [exp_eq_one_add_mul_phiOne, Matrix.mul_add, Matrix.mul_one, hc, ← Matrix.mul_assoc, hφ,
      Matrix.one_mul]
  have h2 : (φi + H • A0) * (phiOne (H • A0))ᵀ = 1 := by
    rw [e, hT, Matrix.mul_assoc, ← Matrix.mul_assoc (NormedSpace.exp (H • A0)),
      exp_mul_exp_neg, Matrix.one_mul, hφ]
  have h3 : (phiOne (H • A0))ᵀ * (φi + H • A0) = 1 := mul_eq_one_comm.1 h2
  calc φiᵀ = φiᵀ * ((phiOne (H • A0))ᵀ * (φi + H • A0)) := by rw [h3, Matrix.mul_one]
    _ = φi + H • A0 := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/-! ### The matrices `Ψ` and `Q` -/

/-- The matrix `Ψ = φi + (H/2) A₀`, `φi` the inverse of `φ = φ₁(H A₀)`. -/
noncomputable def psi (φi A0 : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  φi + (H / 2) • A0

/-- The matrix of the stored energy, `Q = Ψ - (H/2) A_seq = φi + (H/2) A₀ - (H/2) A_seq`. -/
noncomputable def storedQ (φi A0 Aseq : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  psi φi A0 H - (H / 2) • Aseq

variable {X φ φi A A0 Aold Anew Aseq Apar Q : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}

/-- **(a) `Ψ` is symmetric for lossless subsystems.** If `A₀ᵀ = -A₀` and `φi` is a left inverse of
`φ₁(H A₀)`, then `Ψ = φi + (H/2) A₀` is symmetric. -/
theorem psi_transpose_of_skew (hA0 : A0ᵀ = -A0) (hφ : φi * phiOne (H • A0) = 1) :
    (psi φi A0 H)ᵀ = psi φi A0 H := by
  rw [psi, Matrix.transpose_add, Matrix.transpose_smul, transpose_inv_phiOne_of_skew hA0 hφ, hA0]
  module

/-- `Q = Ψ - (H/2) A_seq` is symmetric if `Ψ` and `A_seq` are. -/
theorem storedQ_transpose (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) (hseq : Aseqᵀ = Aseq) :
    (storedQ φi A0 Aseq H)ᵀ = storedQ φi A0 Aseq H := by
  rw [storedQ, Matrix.transpose_sub, Matrix.transpose_smul, hΨ, hseq]

/-! ### The midpoint relation -/

/-- **The midpoint relation.** If `φi φ = 1`, the one-step map obeys
`X - 1 = H φ (A₀ + A_old + A_new X)`, `A = A₀ + A_old + A_new` and
`A_new - A_old = A_seq - A_par`, then `(Q + (H/2) A_par) (X - 1) = (H/2) A (X + 1)` with
`Q = φi + (H/2) A₀ - (H/2) A_seq`. No symmetry is assumed. -/
theorem midpoint_rel (hφ : φi * φ = 1) (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq - Apar) :
    (storedQ φi A0 Aseq H + (H / 2) • Apar) * (X - 1) = (H / 2) • (A * (X + 1)) := by
  have h1 : φi * (X - 1) = H • (A0 + Aold + Anew * X) := by
    rw [hX, Matrix.mul_smul, ← Matrix.mul_assoc, hφ, Matrix.one_mul]
  have h2 : storedQ φi A0 Aseq H + (H / 2) • Apar = φi + (H / 2) • (A0 - (Anew - Aold)) := by
    rw [hsplit, storedQ, psi]
    module
  rw [h2, Matrix.add_mul, h1, ← hA]
  simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_one]
  module

/-! ### The balance from the midpoint relation -/

/-- A skew matrix has the quadratic form zero: `yᵀ A y = 0` if `Aᵀ = -A`. -/
theorem inner_opE_self_of_skew (hA : Aᵀ = -A) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, opE A y⟫ = 0 := by
  have h := OneStep.inner_opE_transpose A y y
  rw [hA, opE_neg, _root_.neg_apply, inner_neg_right] at h
  linarith

/-- For a skew matrix, `uᵀ A v = -(A u)ᵀ v`. -/
theorem inner_opE_of_skew (hA : Aᵀ = -A) (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, opE A v⟫ = -⟪opE A u, v⟫ := by
  rw [OneStep.inner_opE_transpose A v u, hA, opE_neg, _root_.neg_apply, inner_neg_right,
    real_inner_comm]

/-- **The balance of one step with a remainder.** If `(Q + R) (X - 1) = (H/2) A (X + 1)` and
`Qᵀ = Q`, then for every `x`, with `x' = X x` and `x̄ = ½ (x' + x)`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ - x̄ᵀ R (x' - x)`. Nothing is assumed about `R`: multiply the
relation on `x` by `x̄ᵀ`; `x̄ᵀ Q (x' - x) = ½ (x'ᵀ Q x' - xᵀ Q x)` because `Q` is symmetric. -/
theorem energy_balance_rem_of_rel {R : Matrix (Fin n) (Fin n) ℝ}
    (hmid : (Q + R) * (X - 1) = (H / 2) • (A * (X + 1))) (hQ : Qᵀ = Q)
    (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE X x, opE Q (opE X x)⟫ - ⟪x, opE Q x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE X x + x), opE A ((1 / 2 : ℝ) • (opE X x + x))⟫ -
        ⟪(1 / 2 : ℝ) • (opE X x + x), opE R (opE X x - x)⟫ := by
  have hv : opE Q (opE X x - x) + opE R (opE X x - x) = (H / 2) • opE A (opE X x + x) := by
    have h := congrArg (fun M => opE M x) hmid
    simpa only [opE_mul_apply, opE_add, opE_sub, opE_smul, opE_one, _root_.add_apply,
      _root_.sub_apply, _root_.smul_apply, one_apply_eq_self] using h
  have hsym : ⟪x, opE Q (opE X x)⟫ = ⟪opE X x, opE Q x⟫ := by
    rw [OneStep.inner_opE_transpose Q (opE X x) x, hQ]
  have hQd : ⟪opE X x + x, opE Q (opE X x - x)⟫ =
      ⟪opE X x, opE Q (opE X x)⟫ - ⟪x, opE Q x⟫ := by
    rw [map_sub, inner_sub_right, inner_add_left, inner_add_left, hsym]
    ring
  have h1 : ⟪opE X x + x, opE Q (opE X x - x)⟫ + ⟪opE X x + x, opE R (opE X x - x)⟫ =
      H / 2 * ⟪opE X x + x, opE A (opE X x + x)⟫ := by
    have h := congrArg (fun v => ⟪opE X x + x, v⟫) hv
    simpa only [inner_add_right, real_inner_smul_right] using h
  rw [hQd] at h1
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  linear_combination (1 / 2 : ℝ) * h1

/-- **(b) The exact balance of one step, from the midpoint relation.** If
`(Q + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`, `Qᵀ = Q` and `A_parᵀ = -A_par`, then for every
`x`, with `x' = X x` and `x̄ = ½ (x' + x)`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x)`. -/
theorem energy_balance_of_rel
    (hmid : (Q + (H / 2) • Apar) * (X - 1) = (H / 2) • (A * (X + 1)))
    (hQ : Qᵀ = Q) (hpar : Aparᵀ = -Apar) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE X x, opE Q (opE X x)⟫ - ⟪x, opE Q x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE X x + x), opE A ((1 / 2 : ℝ) • (opE X x + x))⟫ +
        H / 2 * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ := by
  have h := energy_balance_rem_of_rel hmid hQ x
  simp only [opE_smul, _root_.smul_apply, real_inner_smul_right] at h
  rw [inner_opE_of_skew hpar] at h
  linear_combination h

/-- **(b) The exact balance of one step for a lossless network, from the midpoint relation.** If
moreover `Aᵀ = -A`: `x'ᵀ Q x' - xᵀ Q x = H (A_par x̄)ᵀ (x' - x)`, `x' = X x`, `x̄ = ½ (x' + x)`.
The stored energy `xᵀ Q x` changes only through the links within one stage. -/
theorem energy_balance_lossless_of_rel
    (hmid : (Q + (H / 2) • Apar) * (X - 1) = (H / 2) • (A * (X + 1)))
    (hQ : Qᵀ = Q) (hpar : Aparᵀ = -Apar) (hA : Aᵀ = -A) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪opE X x, opE Q (opE X x)⟫ - ⟪x, opE Q x⟫ =
      H * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ := by
  have h := energy_balance_of_rel hmid hQ hpar x
  rw [inner_opE_self_of_skew hA] at h
  linarith

/-- **(b) The balance of one step as a matrix identity, from the midpoint relation.** If
`(Q + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`, `Qᵀ = Q` and `A_parᵀ = -A_par`, then
`Xᵀ Q X - Q = (H/4) (X + 1)ᵀ (A + Aᵀ) (X + 1) + (H/2) (Xᵀ A_par - A_par X)`. -/
theorem transpose_mul_mul_sub_of_rel
    (hmid : (Q + (H / 2) • Apar) * (X - 1) = (H / 2) • (A * (X + 1)))
    (hQ : Qᵀ = Q) (hpar : Aparᵀ = -Apar) :
    Xᵀ * Q * X - Q =
      (H / 4) • ((X + 1)ᵀ * (A + Aᵀ) * (X + 1)) + (H / 2) • (Xᵀ * Apar - Apar * X) := by
  have h1 : Q * (X - 1) = (H / 2) • (A * (X + 1)) - (H / 2) • (Apar * (X - 1)) := by
    rw [← hmid, Matrix.add_mul, Matrix.smul_mul, add_sub_cancel_right]
  have h2 : (X - 1)ᵀ * Q = (H / 2) • ((X + 1)ᵀ * Aᵀ) + (H / 2) • ((X - 1)ᵀ * Apar) := by
    have h : (X - 1)ᵀ * Q = (Q * (X - 1))ᵀ := by rw [Matrix.transpose_mul, hQ]
    rw [h, h1]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_mul, Matrix.transpose_one, hpar, Matrix.mul_neg, smul_neg,
      sub_neg_eq_add]
  have h3 : (2 : ℝ) • (Xᵀ * Q * X - Q) =
      (X + 1)ᵀ * (Q * (X - 1)) + (X - 1)ᵀ * Q * (X + 1) := by
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.add_mul,
      Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    module
  have h4 : Xᵀ * Q * X - Q =
      (1 / 2 : ℝ) • ((X + 1)ᵀ * (Q * (X - 1)) + (X - 1)ᵀ * Q * (X + 1)) := by
    rw [← h3, smul_smul]
    norm_num
  rw [h4, h1, h2]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.add_mul,
    Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
  module

/-- **(c) The invariant, from the midpoint relation.** If `Q (X - 1) = (H/2) A (X + 1)`,
`Qᵀ = Q` and `Aᵀ = -A`, then `Xᵀ Q X = Q`. -/
theorem invariant_of_rel (hmid : Q * (X - 1) = (H / 2) • (A * (X + 1))) (hQ : Qᵀ = Q)
    (hA : Aᵀ = -A) : Xᵀ * Q * X = Q := by
  have hmid' : (Q + (H / 2) • (0 : Matrix (Fin n) (Fin n) ℝ)) * (X - 1) =
      (H / 2) • (A * (X + 1)) := by
    rw [smul_zero, add_zero]
    exact hmid
  have h := transpose_mul_mul_sub_of_rel hmid' hQ (by rw [Matrix.transpose_zero, neg_zero])
  rw [hA, add_neg_cancel, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul,
    sub_zero, smul_zero, smul_zero, add_zero] at h
  exact sub_eq_zero.1 h

/-- **(d) A matrix with a positive definite invariant form is bounded.** If `Yᵀ Q Y = Q` and
`lmin ‖y‖² ≤ yᵀ Q y ≤ lmax ‖y‖²` for all `y`, then `lmin ‖Y x‖² ≤ lmax ‖x‖²`. -/
theorem norm_sq_le_of_invariant {Y : Matrix (Fin n) (Fin n) ℝ} {lmin lmax : ℝ}
    (hY : Yᵀ * Q * Y = Q)
    (hlo : ∀ y : EuclideanSpace ℝ (Fin n), lmin * ‖y‖ ^ 2 ≤ ⟪y, opE Q y⟫)
    (hhi : ∀ y : EuclideanSpace ℝ (Fin n), ⟪y, opE Q y⟫ ≤ lmax * ‖y‖ ^ 2)
    (x : EuclideanSpace ℝ (Fin n)) : lmin * ‖opE Y x‖ ^ 2 ≤ lmax * ‖x‖ ^ 2 := by
  have e := inner_opE_transpose_mul_mul Y Q x
  rw [hY] at e
  have h1 := hlo (opE Y x)
  have h2 := hhi x
  linarith

/-- **(d) The trajectory is bounded for all times, from an invariant form.** If `Xᵀ Q X = Q`,
`0 < lmin` and `lmin ‖y‖² ≤ yᵀ Q y ≤ lmax ‖y‖²` for all `y`, then
`‖X^k x‖² ≤ lmax/lmin ‖x‖²` for all `k` and `x`. -/
theorem norm_pow_sq_le_of_invariant {lmin lmax : ℝ} (hX : Xᵀ * Q * X = Q) (hpos : 0 < lmin)
    (hlo : ∀ y : EuclideanSpace ℝ (Fin n), lmin * ‖y‖ ^ 2 ≤ ⟪y, opE Q y⟫)
    (hhi : ∀ y : EuclideanSpace ℝ (Fin n), ⟪y, opE Q y⟫ ≤ lmax * ‖y‖ ^ 2) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ‖opE (X ^ k) x‖ ^ 2 ≤ lmax / lmin * ‖x‖ ^ 2 := by
  have h := norm_sq_le_of_invariant (transpose_pow_mul_mul_pow hX k) hlo hhi x
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-! ### The balance from the implicit equation of the one-step map -/

/-- **(b) The exact balance of one step.** Let `φi φ = 1`, `X - 1 = H φ (A₀ + A_old + A_new X)`,
`A = A₀ + A_old + A_new`, `A_new - A_old = A_seq - A_par`, and let `Ψ = φi + (H/2) A₀` and
`A_seq` be symmetric and `A_par` skew. With `Q = Ψ - (H/2) A_seq`, `x' = X x`, `x̄ = ½ (x' + x)`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x)` for every `x`. -/
theorem energy_balance (hφ : φi * φ = 1) (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq - Apar)
    (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) (hseq : Aseqᵀ = Aseq) (hpar : Aparᵀ = -Apar)
    (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE X x, opE (storedQ φi A0 Aseq H) (opE X x)⟫ -
        ⟪x, opE (storedQ φi A0 Aseq H) x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE X x + x), opE A ((1 / 2 : ℝ) • (opE X x + x))⟫ +
        H / 2 * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ :=
  energy_balance_of_rel (midpoint_rel hφ hX hA hsplit) (storedQ_transpose hΨ hseq) hpar x

/-- **(b) The exact balance of one step for a lossless network.** In the setting of
`energy_balance`, if moreover `Aᵀ = -A`:
`x'ᵀ Q x' - xᵀ Q x = H (A_par x̄)ᵀ (x' - x)` for every `x`. -/
theorem energy_balance_lossless (hφ : φi * φ = 1)
    (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq - Apar)
    (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) (hseq : Aseqᵀ = Aseq) (hpar : Aparᵀ = -Apar)
    (hskew : Aᵀ = -A) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪opE X x, opE (storedQ φi A0 Aseq H) (opE X x)⟫ - ⟪x, opE (storedQ φi A0 Aseq H) x⟫ =
      H * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ :=
  energy_balance_lossless_of_rel (midpoint_rel hφ hX hA hsplit) (storedQ_transpose hΨ hseq) hpar
    hskew x

/-- **(b) The balance of one step as a matrix identity.** In the setting of `energy_balance`:
`Xᵀ Q X - Q = (H/4) (X + 1)ᵀ (A + Aᵀ) (X + 1) + (H/2) (Xᵀ A_par - A_par X)`. -/
theorem transpose_mul_mul_sub (hφ : φi * φ = 1)
    (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq - Apar)
    (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) (hseq : Aseqᵀ = Aseq) (hpar : Aparᵀ = -Apar) :
    Xᵀ * storedQ φi A0 Aseq H * X - storedQ φi A0 Aseq H =
      (H / 4) • ((X + 1)ᵀ * (A + Aᵀ) * (X + 1)) + (H / 2) • (Xᵀ * Apar - Apar * X) :=
  transpose_mul_mul_sub_of_rel (midpoint_rel hφ hX hA hsplit) (storedQ_transpose hΨ hseq) hpar

/-- **(c) The invariant.** Let `φi φ = 1`, `X - 1 = H φ (A₀ + A_old + A_new X)`,
`A = A₀ + A_old + A_new` with `Aᵀ = -A`, let no link lie within one stage,
`A_new - A_old = A_seq`, and let `Ψ = φi + (H/2) A₀` and `A_seq` be symmetric. Then
`Xᵀ Q X = Q` with `Q = Ψ - (H/2) A_seq`. -/
theorem invariant (hφ : φi * φ = 1) (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq)
    (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) (hseq : Aseqᵀ = Aseq) (hskew : Aᵀ = -A) :
    Xᵀ * storedQ φi A0 Aseq H * X = storedQ φi A0 Aseq H := by
  have hmid := midpoint_rel (Aseq := Aseq) (Apar := 0) hφ hX hA (by rw [sub_zero]; exact hsplit)
  rw [smul_zero, add_zero] at hmid
  exact invariant_of_rel hmid (storedQ_transpose hΨ hseq) hskew

/-- **(c) The invariant along the trajectory.** In the setting of `invariant`,
`(X^k)ᵀ Q X^k = Q` for all `k`. -/
theorem invariant_pow (hφ : φi * φ = 1) (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq)
    (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) (hseq : Aseqᵀ = Aseq) (hskew : Aᵀ = -A) (k : ℕ) :
    (X ^ k)ᵀ * storedQ φi A0 Aseq H * X ^ k = storedQ φi A0 Aseq H :=
  transpose_pow_mul_mul_pow (invariant hφ hX hA hsplit hΨ hseq hskew) k

/-- **(d) The trajectory is bounded for all times.** In the setting of `invariant`, if
`0 < lmin` and `lmin ‖y‖² ≤ yᵀ Q y ≤ lmax ‖y‖²` for all `y`, then
`‖X^k x‖² ≤ lmax/lmin ‖x‖²` for all `k` and `x`. -/
theorem norm_pow_sq_le {lmin lmax : ℝ} (hφ : φi * φ = 1)
    (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq)
    (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) (hseq : Aseqᵀ = Aseq) (hskew : Aᵀ = -A)
    (hpos : 0 < lmin)
    (hlo : ∀ y : EuclideanSpace ℝ (Fin n), lmin * ‖y‖ ^ 2 ≤ ⟪y, opE (storedQ φi A0 Aseq H) y⟫)
    (hhi : ∀ y : EuclideanSpace ℝ (Fin n), ⟪y, opE (storedQ φi A0 Aseq H) y⟫ ≤ lmax * ‖y‖ ^ 2)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ‖opE (X ^ k) x‖ ^ 2 ≤ lmax / lmin * ‖x‖ ^ 2 :=
  norm_pow_sq_le_of_invariant (invariant hφ hX hA hsplit hΨ hseq hskew) hpos hlo hhi k x

end MidpointEnergy

end CoSimFoundations
