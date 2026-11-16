/-
The exact energy balance of the zero-order hold for subsystems with dynamics of their own: the
zero-order hold of the library (the paper, Section "Energy stored and energy created",
Proposition `prop:lent`; part (iii) of that proposition is the case `A_i = 0` of
`zoh_invariant`, proved in `StoredEnergy`).

`MidpointEnergy` proves the statements from the implicit equation of the one-step map,
`X - 1 = H φ (A₀ + A_old + A_new X)`. Here the equation is proved for the zero-order hold of
`HalfStepZOH` and the statements are instantiated.

**The scheme.** A `HeldScheme` `S` (subsystems `sub`, stages `stage`, `X = F + M + N X`) with
  `hF : S.F = e^{H A₀}`,   `hMN : S.M + S.N = G°C = H φ₁(H A₀) A_c`,
`A₀ = S.blockDiag A`, `A_c = S.coupling A`; this is the hypothesis of `zoh_staggered`, and
`S.zoh A hA H` satisfies it. The pattern of `M` and `N` then gives `N = zohNew`, `M = zohOld`
(`N_eq_zohNew`, `M_eq_zohOld`).

**The split of the coupling by the stages.** `newPart S A = A_new`: the entries of `A_c` whose
column runs at an earlier stage than the row; `oldPart S A = A_old`: the others.
`A_old + A_new = A_c` and `A_new - A_old = A_ς = signedCoupling` (`oldPart_add_newPart`,
`newPart_sub_oldPart`). Because `φ₁(H A₀)` has no entry between different subsystems,
`zohNew = H φ₁(H A₀) A_new` and `zohOld = H φ₁(H A₀) A_old` (`zohNew_eq`, `zohOld_eq`), and with
`e^{H A₀} = 1 + H A₀ φ₁(H A₀)` the implicit equation follows (`zoh_implicit`).

**The statements.** `φ = φ₁(H A₀)` is assumed invertible (`IsUnit φ.det`), and
  `zohPsi S A H = Ψ = φ⁻¹ + (H/2) A₀`,   `zohQ S A H = Q = Ψ - (H/2) A_seq`,
`A_seq = S.seqCoupling A`, `A_par = S.parCoupling A` of `StoredEnergy`.
* `zoh_midpoint`: `(Q + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`, for every `A`.
* (a) `zohPsi_transpose`: `Ψᵀ = Ψ` if `A₀ᵀ = -A₀`.
* (b) `zoh_energy_balance`: for a lossless coupling (`A q p = -A p q` between different
  subsystems) and `Ψᵀ = Ψ`: `½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x)`,
  `x' = X x`, `x̄ = ½ (x' + x)`; `zoh_transpose_mul_mul_sub` is the matrix form.
  `zoh_energy_balance_lossless`: for `Aᵀ = -A`, `x'ᵀ Q x' - xᵀ Q x = H (A_par x̄)ᵀ (x' - x)`.
* (c) `zoh_invariant`, `zoh_invariant_pow`: for `Aᵀ = -A` and `A_par = 0`, `Xᵀ Q X = Q` and
  `(X^k)ᵀ Q X^k = Q`. `A_par = 0` if different subsystems never share a stage
  (`parCoupling_eq_zero` of `StoredEnergy`) or if partners never share a stage and `A` has entries
  only between partners (`parCoupling_eq_zero_of_partner`).
* (d) `zoh_norm_pow_sq_le`: if moreover `lmin ‖y‖² ≤ yᵀ Q y ≤ lmax ‖y‖²`, `lmin > 0`, then
  `‖X^k x‖² ≤ lmax/lmin ‖x‖²`.
* For the scheme `S.zoh A hA H` itself: `zohScheme_energy_balance_lossless`,
  `zohScheme_invariant_pow`, `zohScheme_norm_pow_sq_le`.

**Hypotheses that are not derived here.** The invertibility of `φ₁(H A₀)` (it holds for
`H ‖A₀‖ ≤ 1`; that is not used here). In (b) for subsystems that are not lossless, the symmetry of
`Ψ`. In (d) the bounds of `Q`.
-/
import CoSimFoundations.MidpointEnergy

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace MidpointEnergy

open OneStep

variable {n : ℕ} {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The split of the coupling by the stages -/

/-- The coupling on the new samples, `A_new`: the entries of `A_c` from a subsystem that runs at
an earlier stage. -/
noncomputable def newPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if S.stage (S.sub q) < S.stage (S.sub p) then S.coupling A p q else 0

/-- The coupling on the old samples, `A_old`: the entries of `A_c` from a subsystem that does not
run at an earlier stage. -/
noncomputable def oldPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if S.stage (S.sub q) < S.stage (S.sub p) then 0 else S.coupling A p q

/-- The entries of `A_new`. -/
theorem newPart_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    newPart S A p q = if S.stage (S.sub q) < S.stage (S.sub p) then S.coupling A p q else 0 :=
  rfl

/-- The entries of `A_old`. -/
theorem oldPart_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    oldPart S A p q = if S.stage (S.sub q) < S.stage (S.sub p) then 0 else S.coupling A p q :=
  rfl

/-- `A_old + A_new = A_c`. -/
theorem oldPart_add_newPart (A : Matrix (Fin n) (Fin n) ℝ) :
    oldPart S A + newPart S A = S.coupling A := by
  ext p q
  rw [Matrix.add_apply, oldPart_apply, newPart_apply]
  by_cases h : S.stage (S.sub q) < S.stage (S.sub p)
  · rw [ite_eq_left h, ite_eq_left h, zero_add]
  · rw [ite_eq_right h, ite_eq_right h, add_zero]

/-- `A_new - A_old = A_ς`, the signed coupling. -/
theorem newPart_sub_oldPart (A : Matrix (Fin n) (Fin n) ℝ) :
    newPart S A - oldPart S A = S.signedCoupling A := by
  ext p q
  rw [Matrix.sub_apply, newPart_apply, oldPart_apply, S.signedCoupling_apply, S.coupling_apply]
  by_cases hpq : S.sub p = S.sub q
  · rw [ite_eq_left hpq, ite_self, sub_zero, ite_eq_left hpq]
  · rw [ite_eq_right hpq, ite_eq_right hpq, HeldScheme.sg]
    by_cases h : S.stage (S.sub q) < S.stage (S.sub p)
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, sub_zero, one_mul]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, zero_sub, neg_one_mul]

/-- `A₀ + A_old + A_new = A`. -/
theorem blockDiag_add_oldPart_add_newPart (A : Matrix (Fin n) (Fin n) ℝ) :
    S.blockDiag A + oldPart S A + newPart S A = A := by
  rw [add_assoc, oldPart_add_newPart, S.blockDiag_add_coupling]

/-- `A_new - A_old = A_seq - A_par`. -/
theorem newPart_sub_oldPart_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    newPart S A - oldPart S A = S.seqCoupling A - S.parCoupling A := by
  rw [newPart_sub_oldPart, S.signedCoupling_eq]

/-- The coefficients of the new samples of the zero-order hold are `H φ₁(H A₀) A_new`: the kernel
has no entry between different subsystems, so the cut along the stages commutes with it. -/
theorem zohNew_eq (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.zohNew A H = S.zohKernel A H * newPart S A := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases h : S.stage (S.sub q) < S.stage (S.sub p)
  · have e : S.zohNew A H p q = S.zohCoupling A H p q := by simp [HeldScheme.zohNew, h]
    rw [e, HeldScheme.zohCoupling, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : S.sub p = S.sub r
    · rw [newPart_apply, ← hr, ite_eq_left h]
    · rw [S.zohKernel_apply_eq_zero A H hr, zero_mul, zero_mul]
  · have e : S.zohNew A H p q = 0 := by simp [HeldScheme.zohNew, h]
    rw [e]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    by_cases hr : S.sub p = S.sub r
    · rw [newPart_apply, ← hr, ite_eq_right h, mul_zero]
    · rw [S.zohKernel_apply_eq_zero A H hr, zero_mul]

/-- The coefficients of the old samples of the zero-order hold are `H φ₁(H A₀) A_old`. -/
theorem zohOld_eq (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.zohOld A H = S.zohKernel A H * oldPart S A := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases h : S.stage (S.sub q) < S.stage (S.sub p)
  · have e : S.zohOld A H p q = 0 := by simp [HeldScheme.zohOld, h]
    rw [e]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    by_cases hr : S.sub p = S.sub r
    · rw [oldPart_apply, ← hr, ite_eq_left h, mul_zero]
    · rw [S.zohKernel_apply_eq_zero A H hr, zero_mul]
  · have e : S.zohOld A H p q = S.zohCoupling A H p q := by simp [HeldScheme.zohOld, h]
    rw [e, HeldScheme.zohCoupling, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : S.sub p = S.sub r
    · rw [oldPart_apply, ← hr, ite_eq_right h]
    · rw [S.zohKernel_apply_eq_zero A H hr, zero_mul, zero_mul]

variable {A : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}

/-- In a scheme with `M + N = G°C` the coefficients of the new samples are `zohNew` (the pattern
of `M` and `N` leaves no choice). -/
theorem N_eq_zohNew (hMN : S.M + S.N = S.zohCoupling A H) : S.N = S.zohNew A H := by
  ext p q
  by_cases h : S.stage (S.sub q) < S.stage (S.sub p)
  · have hM : S.M p q = 0 := S.hM p q fun h' => h'.2 h
    have e := congrFun (congrFun hMN p) q
    rw [Matrix.add_apply, hM, zero_add] at e
    rw [e]
    simp [HeldScheme.zohNew, h]
  · have hN : S.N p q = 0 := S.hN p q fun h' => h h'.2
    rw [hN]
    simp [HeldScheme.zohNew, h]

/-- In a scheme with `M + N = G°C` the coefficients of the old samples are `zohOld`. -/
theorem M_eq_zohOld (hMN : S.M + S.N = S.zohCoupling A H) : S.M = S.zohOld A H := by
  have h := S.zohOld_add_zohNew A H
  rw [← hMN, ← N_eq_zohNew S hMN] at h
  exact (add_right_cancel h).symm

/-- **The implicit equation of the zero-order hold.** A scheme with `F = e^{H A₀}` and
`M + N = G°C` has `X - 1 = H φ₁(H A₀) (A₀ + A_old + A_new X)`. -/
theorem zoh_implicit (hF : S.F = NormedSpace.exp (H • S.blockDiag A))
    (hMN : S.M + S.N = S.zohCoupling A H) :
    S.X - 1 = H • (phiOne (H • S.blockDiag A) *
      (S.blockDiag A + oldPart S A + newPart S A * S.X)) := by
  have hc : H • S.blockDiag A * phiOne (H • S.blockDiag A) =
      phiOne (H • S.blockDiag A) * (H • S.blockDiag A) :=
    (commute_phiOne (Commute.refl (H • S.blockDiag A))).eq
  have hX : S.X - 1 = S.F + S.M + S.N * S.X - 1 := congrArg (fun M => M - 1) S.hX
  rw [hX, hF, M_eq_zohOld S hMN, N_eq_zohNew S hMN, zohOld_eq, zohNew_eq, HeldScheme.zohKernel,
    exp_eq_one_add_mul_phiOne, hc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_assoc]
  module

/-! ### The matrices `Ψ` and `Q` of the zero-order hold -/

variable (A H) in
/-- `Ψ = φ₁(H A₀)⁻¹ + (H/2) A₀` for the subsystems of `S`. -/
noncomputable def zohPsi : Matrix (Fin n) (Fin n) ℝ :=
  psi (phiOne (H • S.blockDiag A))⁻¹ (S.blockDiag A) H

variable (A H) in
/-- The matrix of the stored energy of the zero-order hold,
`Q = φ₁(H A₀)⁻¹ + (H/2) A₀ - (H/2) A_seq`. -/
noncomputable def zohQ : Matrix (Fin n) (Fin n) ℝ :=
  storedQ (phiOne (H • S.blockDiag A))⁻¹ (S.blockDiag A) (S.seqCoupling A) H

variable (A H) in
/-- `Q = φ₁(H A₀)⁻¹ + (H/2) A₀ - (H/2) A_seq`. -/
theorem zohQ_eq : zohQ S A H =
    (phiOne (H • S.blockDiag A))⁻¹ + (H / 2) • S.blockDiag A - (H / 2) • S.seqCoupling A :=
  rfl

/-- For subsystems without dynamics of their own, `A₀ = 0`, the matrix is that of `StoredEnergy`
and of the paper's Proposition `prop:lent` (iii): `Q = 1 - (H/2) A_seq`. -/
theorem zohQ_of_blockDiag_eq_zero (hA0 : S.blockDiag A = 0) :
    zohQ S A H = 1 - (H / 2) • S.seqCoupling A := by
  have h1 : phiOne (0 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    have h2 := (hasSum_phiOne (0 : Matrix (Fin n) (Fin n) ℝ)).unique
      (hasSum_single (f := fun j : ℕ => (((j + 1).factorial : ℕ) : ℝ)⁻¹ •
        (0 : Matrix (Fin n) (Fin n) ℝ) ^ j) 0 fun j hj => by
          rw [zero_pow hj, smul_zero])
    rw [h2]
    simp
  rw [zohQ_eq, hA0, smul_zero, h1, inv_one, smul_zero, add_zero]

/-- **(a) `Ψ` is symmetric for lossless subsystems:** if `A₀ᵀ = -A₀` and `φ₁(H A₀)` is
invertible, then `Ψᵀ = Ψ`. -/
theorem zohPsi_transpose (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hA0 : (S.blockDiag A)ᵀ = -S.blockDiag A) : (zohPsi S A H)ᵀ = zohPsi S A H :=
  psi_transpose_of_skew hA0 (Matrix.nonsing_inv_mul _ hφ)

/-- The block-diagonal part of a skew matrix is skew. -/
theorem blockDiag_transpose_of_skew (hA : Aᵀ = -A) : (S.blockDiag A)ᵀ = -S.blockDiag A := by
  ext p q
  have h : A q p = -A p q := by
    have h' := congrFun (congrFun hA p) q
    rwa [Matrix.transpose_apply, Matrix.neg_apply] at h'
  rw [Matrix.transpose_apply, Matrix.neg_apply, S.blockDiag_apply, S.blockDiag_apply]
  by_cases hpq : S.sub p = S.sub q
  · rw [ite_eq_left hpq, ite_eq_left hpq.symm, h]
  · rw [ite_eq_right hpq, ite_eq_right fun e => hpq e.symm, neg_zero]

/-- A skew matrix is a lossless coupling. -/
theorem coupling_skew_of_skew (hA : Aᵀ = -A) :
    ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q := fun p q _ => by
  have h' := congrFun (congrFun hA p) q
  rwa [Matrix.transpose_apply, Matrix.neg_apply] at h'

/-- If partners never share a stage and `A` has entries only between partners, there is no
parallel part. -/
theorem parCoupling_eq_zero_of_partner
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hstage : ∀ s t, S.partner s t → S.stage s ≠ S.stage t) : S.parCoupling A = 0 := by
  ext p q
  rw [S.parCoupling_apply, Matrix.zero_apply]
  by_cases h : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)
  · rw [ite_eq_left h]
    exact hA p q h.1 fun hp => hstage _ _ hp h.2
  · rw [ite_eq_right h]

/-! ### The midpoint relation and the balance -/

/-- **The midpoint relation of the zero-order hold.** A scheme with `F = e^{H A₀}` and
`M + N = G°C`, `φ₁(H A₀)` invertible, has
`(Q + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`, for every matrix `A` and every order. -/
theorem zoh_midpoint (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H) :
    (zohQ S A H + (H / 2) • S.parCoupling A) * (S.X - 1) = (H / 2) • (A * (S.X + 1)) :=
  midpoint_rel (Matrix.nonsing_inv_mul _ hφ) (zoh_implicit S hF hMN)
    (blockDiag_add_oldPart_add_newPart S A) (newPart_sub_oldPart_eq S A)

/-- **(b) The exact balance of one step of the zero-order hold.** For a lossless coupling
(`A q p = -A p q` between different subsystems), `φ₁(H A₀)` invertible and `Ψ` symmetric, and
for every `x`, with `x' = X x` and `x̄ = ½ (x' + x)`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x)`. -/
theorem zoh_energy_balance (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hΨ : (zohPsi S A H)ᵀ = zohPsi S A H) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE S.X x, opE (zohQ S A H) (opE S.X x)⟫ - ⟪x, opE (zohQ S A H) x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE S.X x + x), opE A ((1 / 2 : ℝ) • (opE S.X x + x))⟫ +
        H / 2 * ⟪opE (S.parCoupling A) ((1 / 2 : ℝ) • (opE S.X x + x)), opE S.X x - x⟫ :=
  energy_balance (Matrix.nonsing_inv_mul _ hφ) (zoh_implicit S hF hMN)
    (blockDiag_add_oldPart_add_newPart S A) (newPart_sub_oldPart_eq S A) hΨ
    (S.seqCoupling_transpose hskew) (S.parCoupling_transpose hskew) x

/-- **(b) The balance of one step of the zero-order hold as a matrix identity.** For a lossless
coupling, `φ₁(H A₀)` invertible and `Ψ` symmetric:
`Xᵀ Q X - Q = (H/4) (X + 1)ᵀ (A + Aᵀ) (X + 1) + (H/2) (Xᵀ A_par - A_par X)`. -/
theorem zoh_transpose_mul_mul_sub (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hΨ : (zohPsi S A H)ᵀ = zohPsi S A H) :
    S.Xᵀ * zohQ S A H * S.X - zohQ S A H =
      (H / 4) • ((S.X + 1)ᵀ * (A + Aᵀ) * (S.X + 1)) +
        (H / 2) • (S.Xᵀ * S.parCoupling A - S.parCoupling A * S.X) :=
  transpose_mul_mul_sub (Matrix.nonsing_inv_mul _ hφ) (zoh_implicit S hF hMN)
    (blockDiag_add_oldPart_add_newPart S A) (newPart_sub_oldPart_eq S A) hΨ
    (S.seqCoupling_transpose hskew) (S.parCoupling_transpose hskew)

/-- **(b) The exact balance of one step of the zero-order hold of a lossless network.** If
`Aᵀ = -A` (lossless subsystems, lossless coupling) and `φ₁(H A₀)` is invertible, then for every
`x`, with `x' = X x` and `x̄ = ½ (x' + x)`: `x'ᵀ Q x' - xᵀ Q x = H (A_par x̄)ᵀ (x' - x)`. The
stored energy changes only through the links within one stage. -/
theorem zoh_energy_balance_lossless (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hA : Aᵀ = -A) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪opE S.X x, opE (zohQ S A H) (opE S.X x)⟫ - ⟪x, opE (zohQ S A H) x⟫ =
      H * ⟪opE (S.parCoupling A) ((1 / 2 : ℝ) • (opE S.X x + x)), opE S.X x - x⟫ :=
  energy_balance_lossless (Matrix.nonsing_inv_mul _ hφ) (zoh_implicit S hF hMN)
    (blockDiag_add_oldPart_add_newPart S A) (newPart_sub_oldPart_eq S A)
    (zohPsi_transpose S hφ (blockDiag_transpose_of_skew S hA))
    (S.seqCoupling_transpose (coupling_skew_of_skew S hA))
    (S.parCoupling_transpose (coupling_skew_of_skew S hA)) hA x

/-! ### The invariant -/

/-- **(c) The invariant of the zero-order hold of a lossless network without links within a
stage.** If `Aᵀ = -A`, `A_par = 0` and `φ₁(H A₀)` is invertible, then `Xᵀ Q X = Q` with
`Q = φ₁(H A₀)⁻¹ + (H/2) A₀ - (H/2) A_seq`. -/
theorem zoh_invariant (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hA : Aᵀ = -A) (hpar : S.parCoupling A = 0) :
    S.Xᵀ * zohQ S A H * S.X = zohQ S A H :=
  invariant (Matrix.nonsing_inv_mul _ hφ) (zoh_implicit S hF hMN)
    (blockDiag_add_oldPart_add_newPart S A)
    (by rw [newPart_sub_oldPart_eq, hpar, sub_zero])
    (zohPsi_transpose S hφ (blockDiag_transpose_of_skew S hA))
    (S.seqCoupling_transpose (coupling_skew_of_skew S hA)) hA

/-- **(c) The invariant along the trajectory:** in the setting of `zoh_invariant`,
`(X^k)ᵀ Q X^k = Q` for all `k`. -/
theorem zoh_invariant_pow (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hA : Aᵀ = -A) (hpar : S.parCoupling A = 0) (k : ℕ) :
    (S.X ^ k)ᵀ * zohQ S A H * S.X ^ k = zohQ S A H :=
  transpose_pow_mul_mul_pow (zoh_invariant S hφ hF hMN hA hpar) k

/-- **(d) The trajectory is bounded for all times:** in the setting of `zoh_invariant`, if
`0 < lmin` and `lmin ‖y‖² ≤ yᵀ Q y ≤ lmax ‖y‖²` for all `y`, then
`‖X^k x‖² ≤ lmax/lmin ‖x‖²` for all `k` and `x`. -/
theorem zoh_norm_pow_sq_le {lmin lmax : ℝ} (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hA : Aᵀ = -A) (hpar : S.parCoupling A = 0) (hpos : 0 < lmin)
    (hlo : ∀ y : EuclideanSpace ℝ (Fin n), lmin * ‖y‖ ^ 2 ≤ ⟪y, opE (zohQ S A H) y⟫)
    (hhi : ∀ y : EuclideanSpace ℝ (Fin n), ⟪y, opE (zohQ S A H) y⟫ ≤ lmax * ‖y‖ ^ 2)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖opE (S.X ^ k) x‖ ^ 2 ≤ lmax / lmin * ‖x‖ ^ 2 :=
  norm_pow_sq_le_of_invariant (zoh_invariant S hφ hF hMN hA hpar) hpos hlo hhi k x

/-! ### The zero-order hold `S.zoh A hA H` -/

/-- **(b) for the zero-order hold `S.zoh A hA H` of a lossless network**, in any order of
execution: if `Aᵀ = -A` and `φ₁(H A₀)` is invertible, then for every `x`, with `x' = X x` and
`x̄ = ½ (x' + x)`: `x'ᵀ Q x' - xᵀ Q x = H (A_par x̄)ᵀ (x' - x)`. -/
theorem zohScheme_energy_balance_lossless
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) (hskew : Aᵀ = -A)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪opE (S.zoh A hA H).X x, opE (zohQ S A H) (opE (S.zoh A hA H).X x)⟫ -
        ⟪x, opE (zohQ S A H) x⟫ =
      H * ⟪opE (S.parCoupling A) ((1 / 2 : ℝ) • (opE (S.zoh A hA H).X x + x)),
        opE (S.zoh A hA H).X x - x⟫ :=
  zoh_energy_balance_lossless (S.zoh A hA H) hφ (S.zoh_F A hA H) (S.zoh_M_add_N A hA H) hskew x

/-- **(c) for the zero-order hold `S.zoh A hA H`**: if `Aᵀ = -A`, no two partners share a stage
and `φ₁(H A₀)` is invertible, then `(X^k)ᵀ Q X^k = Q` for all `k`,
`Q = φ₁(H A₀)⁻¹ + (H/2) A₀ - (H/2) A_seq`. -/
theorem zohScheme_invariant_pow
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) (hskew : Aᵀ = -A)
    (hstage : ∀ s t, S.partner s t → S.stage s ≠ S.stage t) (k : ℕ) :
    ((S.zoh A hA H).X ^ k)ᵀ * zohQ S A H * (S.zoh A hA H).X ^ k = zohQ S A H :=
  zoh_invariant_pow (S.zoh A hA H) hφ (S.zoh_F A hA H) (S.zoh_M_add_N A hA H) hskew
    (parCoupling_eq_zero_of_partner (S.zoh A hA H) hA hstage) k

/-- **(d) for the zero-order hold `S.zoh A hA H`**: if `Aᵀ = -A`, no two partners share a stage,
`φ₁(H A₀)` is invertible, `0 < lmin` and `lmin ‖y‖² ≤ yᵀ Q y ≤ lmax ‖y‖²` for all `y`, then
`‖X^k x‖² ≤ lmax/lmin ‖x‖²` for all `k` and `x`. -/
theorem zohScheme_norm_pow_sq_le {lmin lmax : ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) (hskew : Aᵀ = -A)
    (hstage : ∀ s t, S.partner s t → S.stage s ≠ S.stage t) (hpos : 0 < lmin)
    (hlo : ∀ y : EuclideanSpace ℝ (Fin n), lmin * ‖y‖ ^ 2 ≤ ⟪y, opE (zohQ S A H) y⟫)
    (hhi : ∀ y : EuclideanSpace ℝ (Fin n), ⟪y, opE (zohQ S A H) y⟫ ≤ lmax * ‖y‖ ^ 2)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖opE ((S.zoh A hA H).X ^ k) x‖ ^ 2 ≤ lmax / lmin * ‖x‖ ^ 2 :=
  zoh_norm_pow_sq_le (S.zoh A hA H) hφ (S.zoh_F A hA H) (S.zoh_M_add_N A hA H) hskew
    (parCoupling_eq_zero_of_partner (S.zoh A hA H) hA hstage) hpos hlo hhi k x

end MidpointEnergy

end CoSimFoundations
