/-
The zero-order hold in the reversed order of execution is the adjoint of the hold (the paper,
Section `sec:half`, Remark `rem:reversed`): `X_rev(H) = X(-H)⁻¹`, exactly, for every macro step.

**Setting** (`HalfStepZOH`, `MidpointForm`, `ReversedOrder`). `A = A₀ + A_old + A_new`
(`blockDiag`, `couplingOld`, `couplingNew`), `K(H) = H φ₁(H A₀)` (`zohKernel`), and the one-step
map of the zero-order hold in the stages of `S` solves
  `X(H) = e^{H A₀} + K(H) A_old + K(H) A_new X(H)`.
`S.restage st` is the frame of `S` with the stages `st`, and `S.Reversed st` says that `st` puts
every pair of subsystems at different stages in the opposite order.

**No link within a stage** (`restage_couplingNew`, `restage_couplingOld`). If `A` has no entry
between two different subsystems at the same stage (in particular if no two partners share a
stage, `no_link_within_stage`), a reversed assignment exchanges the two parts of the coupling:
  `A_new^rev = A_old`,   `A_old^rev = A_new`.
With a link within a stage this fails: that link is in `A_old` in both orders.

**The identity in a ring** (`reversed_adjoint_ring`). Let `E E' = 1`, `E K' = -K`,
  `X' = E' + K' P + K' Q X'`,   `Y = E + K Q + K P Y`,   `L (1 - K P) = 1`.
Then `Y X' = 1`. Proof: `E X' = 1 - K P - K Q X'`, so `(E + K Q) X' = 1 - K P`; and
`(1 - K P) Y = E + K Q`; hence `(1 - K P) Y X' = 1 - K P`, and `L` cancels the factor.

**The adjoint** (`zoh_reversed_mul_neg_of_eq`, `zoh_reversed_mul_zoh_neg`,
`zoh_neg_mul_zoh_reversed`, `zoh_reversed_eq_inv`). With `E = e^{H A₀}`, `E' = e^{-H A₀}`,
`K = K(H)`, `K' = K(-H)`, `P = A_old`, `Q = A_new`: `E K(-H) = -K(H)` because
`φ₁(-Z) = e^{-Z} φ₁(Z)` (`MidpointEnergy.phiOne_neg`), and `K P` is the matrix of the new samples
of the reversed order, which is nilpotent, so `L = Σ_k (K P)^k`. Therefore, for every `H`,
  `X_rev(H) X(-H) = 1`,   `X(-H) X_rev(H) = 1`,   `X_rev(H) = X(-H)⁻¹`.
No hypothesis on the size of `H` and no invertibility of `φ₁` is needed. In particular the
one-step map of a sequential zero-order hold is invertible for every `H` (`isUnit_det_zoh_X`).

**The symmetric composition** (`zoh_two_step_symmetric`). `Φ(H) = X_rev(H) X(H)`, the order
reversed in every second macro step, obeys `Φ(H) Φ(-H) = 1`.

**The matrix of the midpoint form** (`midpointPsi_neg`, `midpointE_restage_eq_neg`). If
`φ₁(H A₀)` is invertible, `Ψ(-H) = Ψ(H)` for `Ψ(H) = φ₁(H A₀)⁻¹ + (H/2) A₀`
(`φ₁(-H A₀)⁻¹ = φ₁(H A₀)⁻¹ e^{H A₀} = φ₁(H A₀)⁻¹ + H A₀`), and if no two partners share a stage
the matrix `Ψ - (H/2) A_ς` of the reversed order at `H` is that of the original order at `-H`.
-/
import CoSimFoundations.MidpointForm
import CoSimFoundations.ReversedOrder
import CoSimFoundations.MidpointEnergy

open Matrix

namespace CoSimFoundations

/-- **The adjoint identity in a ring.** If `E E' = 1`, `E K' = -K`, `X' = E' + K' P + K' Q X'`,
`Y = E + K Q + K P Y` and `1 - K P` has a left inverse `L`, then `Y X' = 1`. -/
theorem reversed_adjoint_ring {R : Type*} [Ring R] {E E' K K' P Q X' Y L : R}
    (hE : E * E' = 1) (hK : E * K' = -K) (hX : X' = E' + K' * P + K' * Q * X')
    (hY : Y = E + K * Q + K * P * Y) (hL : L * (1 - K * P) = 1) : Y * X' = 1 := by
  have h0 : E * X' = E * (E' + K' * P + K' * Q * X') := congrArg (fun T => E * T) hX
  have h1 : (E + K * Q) * X' = 1 - K * P := by
    calc (E + K * Q) * X' = E * X' + K * Q * X' := add_mul _ _ _
      _ = E * E' + E * K' * P + E * K' * Q * X' + K * Q * X' := by
        rw [h0]
        noncomm_ring
      _ = 1 - K * P := by
        rw [hE, hK]
        noncomm_ring
  have h2 : (1 - K * P) * Y = E + K * Q := by
    rw [sub_mul, one_mul, sub_eq_iff_eq_add]
    exact hY
  calc Y * X' = L * (1 - K * P) * Y * X' := by rw [hL, one_mul]
    _ = L * (((1 - K * P) * Y) * X') := by noncomm_ring
    _ = 1 := by rw [h2, h1, hL]

namespace HeldScheme

variable {n : ℕ} {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The parts of the coupling in a reversed assignment -/

/-- If no two partners share a stage and `A` has no block between subsystems that are not
partners, `A` has no entry between two different subsystems at the same stage. -/
theorem no_link_within_stage {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t) :
    ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) = S.stage (S.sub q) → A p q = 0 :=
  fun p q hpq hst => hA p q hpq fun hp => hns _ _ hpq hp hst

/-- **The new samples of a reversed order are the old samples of the original order:** if `A`
has no entry between two different subsystems at the same stage, `A_new^rev = A_old`. -/
theorem restage_couplingNew {st : κ → ℕ} (hrev : S.Reversed st)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) = S.stage (S.sub q) → A p q = 0) :
    (S.restage st).couplingNew A = S.couplingOld A := by
  ext p q
  have e : (S.restage st).couplingNew A p q =
      if st (S.sub q) < st (S.sub p) then S.coupling A p q else 0 := rfl
  rw [e, S.couplingOld_apply]
  rcases lt_trichotomy (S.stage (S.sub p)) (S.stage (S.sub q)) with h1 | h1 | h1
  · rw [ite_eq_left ((hrev _ _).2 h1), ite_eq_right (lt_asymm h1)]
  · have h2 : ¬ st (S.sub q) < st (S.sub p) := fun h => by
      have h3 := (hrev _ _).1 h
      omega
    have h4 : ¬ S.stage (S.sub q) < S.stage (S.sub p) := by omega
    rw [ite_eq_right h2, ite_eq_right h4, S.coupling_apply]
    by_cases hpq : S.sub p = S.sub q
    · rw [ite_eq_left hpq]
    · rw [ite_eq_right hpq, hseq p q hpq h1]
  · have h2 : ¬ st (S.sub q) < st (S.sub p) := fun h => by
      have h3 := (hrev _ _).1 h
      omega
    rw [ite_eq_right h2, ite_eq_left h1]

/-- **The old samples of a reversed order are the new samples of the original order:** if `A`
has no entry between two different subsystems at the same stage, `A_old^rev = A_new`. -/
theorem restage_couplingOld {st : κ → ℕ} (hrev : S.Reversed st)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) = S.stage (S.sub q) → A p q = 0) :
    (S.restage st).couplingOld A = S.couplingNew A := by
  have h1 : (S.restage st).couplingOld A + (S.restage st).couplingNew A = S.coupling A :=
    (S.restage st).couplingOld_add_couplingNew A
  have h2 := S.couplingOld_add_couplingNew A
  rw [S.restage_couplingNew hrev hseq, ← h2, add_comm] at h1
  exact add_left_cancel h1

/-! ### The kernel at `-H` -/

/-- `e^{H A₀} K(-H) = -K(H)` for the kernel `K(H) = H φ₁(H A₀)` of the zero-order hold. -/
theorem exp_mul_zohKernel_neg (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    NormedSpace.exp (H • S.blockDiag A) * S.zohKernel A (-H) = -S.zohKernel A H := by
  have hW : (-H) • S.blockDiag A = -(H • S.blockDiag A) := neg_smul _ _
  rw [zohKernel, zohKernel, hW, MidpointEnergy.phiOne_neg, neg_smul, mul_neg, mul_smul_comm,
    ← mul_assoc, MidpointEnergy.exp_mul_exp_neg, one_mul]

/-- `e^{H A₀} e^{-H A₀} = 1`. -/
theorem exp_blockDiag_mul_exp_neg (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    NormedSpace.exp (H • S.blockDiag A) * NormedSpace.exp ((-H) • S.blockDiag A) = 1 := by
  rw [neg_smul]
  exact MidpointEnergy.exp_mul_exp_neg _

/-! ### The adjoint -/

/-- **The reversed order is the adjoint, for every solution of the two implicit equations.**
Let `A` have no entry between two different subsystems at the same stage and let `st` be a
reversed assignment of stages. If `X'` solves the equation of the zero-order hold in the stages
of `S` with the macro step `-H` and `Y` that of the zero-order hold in the stages `st` with the
macro step `H`, then `Y X' = 1`. -/
theorem zoh_reversed_mul_neg_of_eq {st : κ → ℕ} (hrev : S.Reversed st)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) = S.stage (S.sub q) → A p q = 0)
    (H : ℝ) {X' Y : Matrix (Fin n) (Fin n) ℝ}
    (hX' : X' = NormedSpace.exp ((-H) • S.blockDiag A) + S.zohOld A (-H) +
      S.zohNew A (-H) * X')
    (hY : Y = NormedSpace.exp (H • S.blockDiag A) + (S.restage st).zohOld A H +
      (S.restage st).zohNew A H * Y) : Y * X' = 1 := by
  have hN' : (S.restage st).zohNew A H = S.zohKernel A H * S.couplingOld A := by
    rw [(S.restage st).zohNew_eq, S.restage_couplingNew hrev hseq]
    rfl
  have hM' : (S.restage st).zohOld A H = S.zohKernel A H * S.couplingNew A := by
    rw [(S.restage st).zohOld_eq, S.restage_couplingOld hrev hseq]
    rfl
  have hX2 : X' = NormedSpace.exp ((-H) • S.blockDiag A) +
      S.zohKernel A (-H) * S.couplingOld A + S.zohKernel A (-H) * S.couplingNew A * X' := by
    rw [← S.zohOld_eq, ← S.zohNew_eq]
    exact hX'
  have hY2 : Y = NormedSpace.exp (H • S.blockDiag A) + S.zohKernel A H * S.couplingNew A +
      S.zohKernel A H * S.couplingOld A * Y := by
    rw [← hM', ← hN']
    exact hY
  have hnil : (S.restage st).zohNew A H ^ (S.restage st).stageBound = 0 :=
    (S.restage st).pow_stageBound_eq_zero fun p q h => by simp [zohNew, h]
  have hL : (∑ k ∈ Finset.range (S.restage st).stageBound, (S.restage st).zohNew A H ^ k) *
      (1 - S.zohKernel A H * S.couplingOld A) = 1 := by
    rw [← hN', geom_sum_mul_neg, hnil, sub_zero]
  exact reversed_adjoint_ring (S.exp_blockDiag_mul_exp_neg A H) (S.exp_mul_zohKernel_neg A H)
    hX2 hY2 hL

/-- **The zero-order hold in the reversed order is the adjoint of the hold** (the paper, Remark
`rem:reversed`): if no two partners share a stage and `st` is a reversed assignment of stages,
then for every macro step `H` the one-step map `X_rev(H)` of the zero-order hold in the stages
`st` and the one-step map `X(-H)` of the zero-order hold in the stages of `S` with the macro step
`-H` obey `X_rev(H) X(-H) = 1`. -/
theorem zoh_reversed_mul_zoh_neg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) (H : ℝ) :
    ((S.restage st).zoh A hA H).X * (S.zoh A hA (-H)).X = 1 :=
  S.zoh_reversed_mul_neg_of_eq hrev (S.no_link_within_stage hA hns) H (S.zoh A hA (-H)).hX
    ((S.restage st).zoh A hA H).hX

/-- The adjoint identity in the other order of the factors: `X(-H) X_rev(H) = 1`. -/
theorem zoh_neg_mul_zoh_reversed {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) (H : ℝ) :
    (S.zoh A hA (-H)).X * ((S.restage st).zoh A hA H).X = 1 :=
  mul_eq_one_comm.1 (S.zoh_reversed_mul_zoh_neg hA hns hrev H)

/-- **`X_rev(H) = X(-H)⁻¹`** (the paper, Remark `rem:reversed`): if no two partners share a stage,
the one-step map of the zero-order hold in a reversed assignment of stages is the inverse of the
one-step map of the zero-order hold in the original stages with the macro step `-H`. -/
theorem zoh_reversed_eq_inv {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) (H : ℝ) :
    ((S.restage st).zoh A hA H).X = ((S.zoh A hA (-H)).X)⁻¹ :=
  (Matrix.inv_eq_left_inv (S.zoh_reversed_mul_zoh_neg hA hns hrev H)).symm

/-- The adjoint identity with the signs exchanged: `X(H) X_rev(-H) = 1`. -/
theorem zoh_mul_zoh_reversed_neg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) (H : ℝ) :
    (S.zoh A hA H).X * ((S.restage st).zoh A hA (-H)).X = 1 := by
  have h := S.zoh_neg_mul_zoh_reversed hA hns hrev (-H)
  rwa [neg_neg] at h

/-- **The one-step map of a sequential zero-order hold is invertible for every macro step:** if
no two partners share a stage and a reversed assignment of stages exists (for finitely many
subsystems, `reversed_revStage_sup`), `det X(H)` is a unit. -/
theorem isUnit_det_zoh_X {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) (H : ℝ) : IsUnit (S.zoh A hA H).X.det :=
  Matrix.isUnit_det_of_right_inverse (S.zoh_mul_zoh_reversed_neg hA hns hrev H)

/-- **Reversing the order in every second macro step is a symmetric method** (the paper, Remark
`rem:reversed`): if no two partners share a stage, the map of two macro steps
`Φ(H) = X_rev(H) X(H)` obeys `Φ(H) Φ(-H) = 1`. -/
theorem zoh_two_step_symmetric {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) (H : ℝ) :
    (((S.restage st).zoh A hA H).X * (S.zoh A hA H).X) *
      (((S.restage st).zoh A hA (-H)).X * (S.zoh A hA (-H)).X) = 1 := by
  rw [mul_assoc, ← mul_assoc (S.zoh A hA H).X, S.zoh_mul_zoh_reversed_neg hA hns hrev H, one_mul,
    S.zoh_reversed_mul_zoh_neg hA hns hrev H]

/-! ### The matrix of the midpoint form -/

/-- **`Ψ` is even in `H`** (the paper, Remark `rem:reversed`): if `φ₁(H A₀)` is invertible,
`Ψ(-H) = Ψ(H)` for `Ψ(H) = φ₁(H A₀)⁻¹ + (H/2) A₀`. -/
theorem midpointPsi_neg (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    S.midpointPsi A (-H) = S.midpointPsi A H := by
  have hW : (-H) • S.blockDiag A = -(H • S.blockDiag A) := neg_smul _ _
  have hinv : (NormedSpace.exp (-(H • S.blockDiag A)))⁻¹ = NormedSpace.exp (H • S.blockDiag A) :=
    Matrix.inv_eq_left_inv (MidpointEnergy.exp_mul_exp_neg _)
  have e : (phiOne (H • S.blockDiag A))⁻¹ * NormedSpace.exp (H • S.blockDiag A) =
      (phiOne (H • S.blockDiag A))⁻¹ + H • S.blockDiag A := by
    rw [exp_eq_one_add_phiOne_mul, mul_add, mul_one, ← mul_assoc, Matrix.nonsing_inv_mul _ hφ,
      one_mul]
  rw [midpointPsi, midpointPsi, hW, MidpointEnergy.phiOne_neg, Matrix.mul_inv_rev, hinv, e]
  module

/-- **The matrix of the reversed order is the matrix of the hold with the macro step `-H`**
(the paper, Remark `rem:reversed`): if `φ₁(H A₀)` is invertible, no two partners share a stage and
`st` is a reversed assignment of stages, then `Ψ(H) - (H/2) A_ς^rev = Ψ(-H) - (-H/2) A_ς`, and
both are `Ψ(H) + (H/2) A_ς`. -/
theorem midpointE_restage_eq_neg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (S.restage st).midpointPsi A H - (H / 2) • (S.restage st).signedCoupling A =
        S.midpointPsi A (-H) - (-H / 2) • S.signedCoupling A ∧
      S.midpointPsi A (-H) - (-H / 2) • S.signedCoupling A =
        S.midpointPsi A H + (H / 2) • S.signedCoupling A := by
  have h1 : (S.restage st).signedCoupling A = -S.signedCoupling A :=
    (neg_eq_of_add_eq_zero_right (S.signedCoupling_add_restage_eq_zero hrev hA hns)).symm
  have h2 : (S.restage st).midpointPsi A H = S.midpointPsi A H := rfl
  rw [h1, h2, S.midpointPsi_neg A H hφ]
  constructor <;> module

end HeldScheme

end CoSimFoundations
