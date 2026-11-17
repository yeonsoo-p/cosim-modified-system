/-
The exact energy balance of the zero-order hold without the hypothesis that `Ψ` is symmetric
(the paper, Section "Energy stored and energy created", Proposition `prop:lent`, eq.
`eq:balance`, with its last term `x̄ᵀ skw(Ψ₀) d`).

`MidpointEnergy.energy_balance` assumes `Ψᵀ = Ψ`. Here `Ψ` is any matrix,
  `sym Ψ = ½ (Ψ + Ψᵀ)` (`sym` of `Setting`),   `skw Ψ = ½ (Ψ - Ψᵀ)` (`skw`),
  `Q = sym Ψ - (H/2) A_seq` (`symQ` for `Ψ = φi + (H/2) A₀`).

**Statements** (`x' = X x`, `x̄ = ½ (x' + x)`, `d = x' - x`; vectors in `EuclideanSpace`, matrices
as operators `opE`, as in `MidpointEnergy`).
* `energy_balance_skew_of_rel`: if `(Q + K + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`, `Qᵀ = Q`
  and `A_parᵀ = -A_par`, then for every `x`
    `½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ d - x̄ᵀ K d`.
  Nothing is assumed about `K`. Proof: multiply the relation on `x` by `x̄ᵀ`:
  `x̄ᵀ Q d + x̄ᵀ K d + (H/2) x̄ᵀ A_par d = H x̄ᵀ A x̄`; `x̄ᵀ Q d = ½ (x'ᵀ Q x' - xᵀ Q x)`
  because `Q` is symmetric, and `x̄ᵀ A_par d = -(A_par x̄)ᵀ d` because `A_par` is skew.
* `energy_balance_skew_of_midpoint`: the same from the midpoint relation
  `(Ψ - (H/2) A_seq + (H/2) A_par) (X - 1) = (H/2) A (X + 1)` with `A_seqᵀ = A_seq`,
  `A_parᵀ = -A_par`, for `Q = sym Ψ - (H/2) A_seq` and `K = skw Ψ` (`Ψ = sym Ψ + skw Ψ`).
* `energy_balance_skew`: the same from the implicit equation of the one-step map,
  `X - 1 = H φ (A₀ + A_old + A_new X)`, `φi φ = 1`, `Ψ = φi + (H/2) A₀`
  (`MidpointEnergy.midpoint_rel`). This is eq. `eq:balance` with `x̄ᵀ A x̄` in the place of
  `-x̄ᵀ R x̄`; `energy_balance_skew_diss` is the form with `R = -sym A` (`inner_opE_sym`: a
  quadratic form sees the symmetric part only).
* The reduction: if `Ψᵀ = Ψ`, `sym Ψ = Ψ`, `skw Ψ = 0`, `symQ = storedQ`
  (`symQ_eq_storedQ`), and the balance `energy_balance_skew` is `MidpointEnergy.energy_balance`.
* `psi_transpose_of_symm`: `Ψᵀ = Ψ` if `A₀ᵀ = A₀` (`φ₁(H A₀)` is then symmetric). With
  `psi_transpose_of_skew` of `MidpointEnergy`: the last term of the balance vanishes if `A₀` is
  symmetric, and if `A₀` is skew.
* The zero-order hold of the library (a `HeldScheme` with `F = e^{H A₀}`, `M + N = G°C`,
  `φ₁(H A₀)` invertible, lossless coupling): `zohQSym S A H = sym Ψ - (H/2) A_seq`,
  `zoh_energy_balance_skew`, `zoh_energy_balance_skew_diss`, and for the scheme `S.zoh A hA H`
  itself `zohScheme_energy_balance_skew`. `skw_zohPsi_of_skew`, `skw_zohPsi_of_symm`: the last
  term vanishes for skew and for symmetric `A₀`.

**What is not here.** The paper says that the last term vanishes "if every `A_i` is symmetric or
skew" (the choice may differ from subsystem to subsystem) and is `O(H³ |x|²)` otherwise. Proved
here: it vanishes if `A₀ = diag(A_i)` as a whole is symmetric, and if it is skew. The mixed case
and the bound `O(H³ |x|²)` are not formalised. The invertibility of `φ₁(H A₀)` is a hypothesis
(it holds for `‖H A₀‖ ≤ 1`, `isUnit_det_phiOne`).
-/
import CoSimFoundations.MidpointEnergyZOH
import CoSimFoundations.Setting

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace MidpointEnergy

open OneStep

variable {n : ℕ}

/-! ### Symmetric and skew part -/

/-- `skw M = ½ (M - Mᵀ)`. -/
noncomputable def skw (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (M - Mᵀ)

/-- `sym M + skw M = M`. -/
theorem sym_add_skw (M : Matrix (Fin n) (Fin n) ℝ) : sym M + skw M = M := by
  rw [sym, skw]
  module

/-- `sym M` is symmetric. -/
theorem sym_transpose (M : Matrix (Fin n) (Fin n) ℝ) : (sym M)ᵀ = sym M := by
  rw [sym, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- `skw M` is skew. -/
theorem skw_transpose (M : Matrix (Fin n) (Fin n) ℝ) : (skw M)ᵀ = -skw M := by
  rw [skw, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose, ← smul_neg,
    neg_sub]

/-- The symmetric part of a symmetric matrix is the matrix. -/
theorem sym_eq_self {M : Matrix (Fin n) (Fin n) ℝ} (h : Mᵀ = M) : sym M = M := by
  rw [sym, h]
  module

/-- The skew part of a symmetric matrix is zero. -/
theorem skw_eq_zero {M : Matrix (Fin n) (Fin n) ℝ} (h : Mᵀ = M) : skw M = 0 := by
  rw [skw, h, sub_self, smul_zero]

/-- The operator of the zero matrix. -/
theorem opE_zero : opE (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := map_zero _

/-- A quadratic form sees the symmetric part only: `yᵀ (sym A) y = yᵀ A y`. -/
theorem inner_opE_sym (A : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, opE (sym A) y⟫ = ⟪y, opE A y⟫ := by
  rw [inner_opE_eq_dotProduct, inner_opE_eq_dotProduct, dotProduct_mulVec_sym]

section General

variable {X φ φi A A0 Aold Anew Aseq Apar Q K : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}

/-! ### The balance from a midpoint relation -/

/-- **The exact balance of one step with a part `K` that is not in the quadratic form.** If
`(Q + K + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`, `Qᵀ = Q` and `A_parᵀ = -A_par`, then for every
`x`, with `x' = X x`, `x̄ = ½ (x' + x)`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x) - x̄ᵀ K (x' - x)`.
Nothing is assumed about `K`. -/
theorem energy_balance_skew_of_rel
    (hmid : (Q + K + (H / 2) • Apar) * (X - 1) = (H / 2) • (A * (X + 1)))
    (hQ : Qᵀ = Q) (hpar : Aparᵀ = -Apar) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE X x, opE Q (opE X x)⟫ - ⟪x, opE Q x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE X x + x), opE A ((1 / 2 : ℝ) • (opE X x + x))⟫ +
        H / 2 * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ -
        ⟪(1 / 2 : ℝ) • (opE X x + x), opE K (opE X x - x)⟫ := by
  rw [add_assoc] at hmid
  have h := energy_balance_rem_of_rel hmid hQ x
  simp only [opE_add, opE_smul, _root_.add_apply, _root_.smul_apply, inner_add_right,
    real_inner_smul_right] at h
  rw [inner_opE_of_skew hpar] at h
  linear_combination h

/-- **The exact balance of one step from the midpoint relation, for any `Ψ`** (eq. `eq:balance`).
If `(Ψ - (H/2) A_seq + (H/2) A_par) (X - 1) = (H/2) A (X + 1)`, `A_seqᵀ = A_seq` and
`A_parᵀ = -A_par`, then with `Q = sym Ψ - (H/2) A_seq`, `x' = X x`, `x̄ = ½ (x' + x)`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x) - x̄ᵀ (skw Ψ) (x' - x)`
for every `x`. No symmetry of `Ψ` is assumed. -/
theorem energy_balance_skew_of_midpoint {Psi : Matrix (Fin n) (Fin n) ℝ}
    (hmid : (Psi - (H / 2) • Aseq + (H / 2) • Apar) * (X - 1) = (H / 2) • (A * (X + 1)))
    (hseq : Aseqᵀ = Aseq) (hpar : Aparᵀ = -Apar) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE X x, opE (sym Psi - (H / 2) • Aseq) (opE X x)⟫ -
        ⟪x, opE (sym Psi - (H / 2) • Aseq) x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE X x + x), opE A ((1 / 2 : ℝ) • (opE X x + x))⟫ +
        H / 2 * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ -
        ⟪(1 / 2 : ℝ) • (opE X x + x), opE (skw Psi) (opE X x - x)⟫ := by
  have e : Psi - (H / 2) • Aseq + (H / 2) • Apar =
      sym Psi - (H / 2) • Aseq + skw Psi + (H / 2) • Apar := by
    rw [sym, skw]
    module
  have hQ : (sym Psi - (H / 2) • Aseq)ᵀ = sym Psi - (H / 2) • Aseq := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, sym_transpose, hseq]
  rw [e] at hmid
  exact energy_balance_skew_of_rel hmid hQ hpar x

/-! ### The balance from the implicit equation of the one-step map -/

/-- The matrix of the modified energy without a hypothesis on `Ψ`:
`Q = sym Ψ - (H/2) A_seq`, `Ψ = φi + (H/2) A₀`. -/
noncomputable def symQ (φi A0 Aseq : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  sym (psi φi A0 H) - (H / 2) • Aseq

/-- `Q = sym Ψ - (H/2) A_seq` is symmetric if `A_seq` is. -/
theorem symQ_transpose (hseq : Aseqᵀ = Aseq) : (symQ φi A0 Aseq H)ᵀ = symQ φi A0 Aseq H := by
  rw [symQ, Matrix.transpose_sub, Matrix.transpose_smul, sym_transpose, hseq]

/-- If `Ψ` is symmetric, `sym Ψ - (H/2) A_seq` is the matrix `Q = Ψ - (H/2) A_seq` of
`MidpointEnergy`. -/
theorem symQ_eq_storedQ (hΨ : (psi φi A0 H)ᵀ = psi φi A0 H) :
    symQ φi A0 Aseq H = storedQ φi A0 Aseq H := by
  rw [symQ, storedQ, sym_eq_self hΨ]

/-- **The exact balance of one step, without a hypothesis on `Ψ`** (eq. `eq:balance`). Let
`φi φ = 1`, `X - 1 = H φ (A₀ + A_old + A_new X)`, `A = A₀ + A_old + A_new`,
`A_new - A_old = A_seq - A_par`, `A_seq` symmetric and `A_par` skew. With `Ψ = φi + (H/2) A₀`,
`Q = sym Ψ - (H/2) A_seq`, `x' = X x`, `x̄ = ½ (x' + x)`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x) - x̄ᵀ (skw Ψ) (x' - x)`
for every `x`. -/
theorem energy_balance_skew (hφ : φi * φ = 1) (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq - Apar)
    (hseq : Aseqᵀ = Aseq) (hpar : Aparᵀ = -Apar) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE X x, opE (symQ φi A0 Aseq H) (opE X x)⟫ -
        ⟪x, opE (symQ φi A0 Aseq H) x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE X x + x), opE A ((1 / 2 : ℝ) • (opE X x + x))⟫ +
        H / 2 * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ -
        ⟪(1 / 2 : ℝ) • (opE X x + x), opE (skw (psi φi A0 H)) (opE X x - x)⟫ :=
  energy_balance_skew_of_midpoint (Psi := psi φi A0 H) (midpoint_rel hφ hX hA hsplit) hseq hpar x

/-- **Eq. `eq:balance` with the dissipation `R = -sym A`.** In the setting of
`energy_balance_skew`:
`½ (x'ᵀ Q x' - xᵀ Q x) = -H x̄ᵀ R x̄ + (H/2) (A_par x̄)ᵀ (x' - x) - x̄ᵀ (skw Ψ) (x' - x)`. -/
theorem energy_balance_skew_diss {R : Matrix (Fin n) (Fin n) ℝ} (hφ : φi * φ = 1)
    (hX : X - 1 = H • (φ * (A0 + Aold + Anew * X)))
    (hA : A0 + Aold + Anew = A) (hsplit : Anew - Aold = Aseq - Apar)
    (hseq : Aseqᵀ = Aseq) (hpar : Aparᵀ = -Apar) (hR : R = -sym A)
    (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE X x, opE (symQ φi A0 Aseq H) (opE X x)⟫ -
        ⟪x, opE (symQ φi A0 Aseq H) x⟫) =
      -(H * ⟪(1 / 2 : ℝ) • (opE X x + x), opE R ((1 / 2 : ℝ) • (opE X x + x))⟫) +
        H / 2 * ⟪opE Apar ((1 / 2 : ℝ) • (opE X x + x)), opE X x - x⟫ -
        ⟪(1 / 2 : ℝ) • (opE X x + x), opE (skw (psi φi A0 H)) (opE X x - x)⟫ := by
  rw [hR, opE_neg, _root_.neg_apply, inner_neg_right, mul_neg, neg_neg, inner_opE_sym]
  exact energy_balance_skew hφ hX hA hsplit hseq hpar x

/-! ### When the last term vanishes -/

/-- **`Ψ` is symmetric for symmetric subsystems.** If `A₀ᵀ = A₀` and `φi` is a left inverse of
`φ₁(H A₀)`, then `Ψ = φi + (H/2) A₀` is symmetric: `φ₁(H A₀)ᵀ = φ₁(H A₀ᵀ) = φ₁(H A₀)`. -/
theorem psi_transpose_of_symm (hA0 : A0ᵀ = A0) (hφ : φi * phiOne (H • A0) = 1) :
    (psi φi A0 H)ᵀ = psi φi A0 H := by
  have hT : (phiOne (H • A0))ᵀ = phiOne (H • A0) := by
    rw [phiOne_transpose, Matrix.transpose_smul, hA0]
  have hφ' : phiOne (H • A0) * φi = 1 := mul_eq_one_comm.1 hφ
  have h1 : φiᵀ * phiOne (H • A0) = 1 := by
    have h := congrArg Matrix.transpose hφ'
    rwa [Matrix.transpose_mul, hT, Matrix.transpose_one] at h
  have h2 : φiᵀ = φi := by
    calc φiᵀ = φiᵀ * (phiOne (H • A0) * φi) := by rw [hφ', Matrix.mul_one]
      _ = φi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [psi, Matrix.transpose_add, Matrix.transpose_smul, h2, hA0]

end General

/-! ### The zero-order hold of the library -/

section ZOH

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)
variable {A : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}

variable (A H) in
/-- The matrix of the modified energy of the zero-order hold without a hypothesis on `Ψ`,
`Q = sym Ψ - (H/2) A_seq` with `Ψ = φ₁(H A₀)⁻¹ + (H/2) A₀` (`zohPsi`). -/
noncomputable def zohQSym : Matrix (Fin n) (Fin n) ℝ :=
  symQ (phiOne (H • S.blockDiag A))⁻¹ (S.blockDiag A) (S.seqCoupling A) H

variable (A H) in
/-- `Q = sym Ψ - (H/2) A_seq`. -/
theorem zohQSym_eq : zohQSym S A H = sym (zohPsi S A H) - (H / 2) • S.seqCoupling A := rfl

/-- `Q = sym Ψ - (H/2) A_seq` is symmetric for a lossless coupling. -/
theorem zohQSym_transpose (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    (zohQSym S A H)ᵀ = zohQSym S A H :=
  symQ_transpose (S.seqCoupling_transpose hskew)

/-- If `Ψ` is symmetric, `zohQSym` is the matrix `zohQ` of `MidpointEnergyZOH`. -/
theorem zohQSym_eq_zohQ (hΨ : (zohPsi S A H)ᵀ = zohPsi S A H) : zohQSym S A H = zohQ S A H :=
  symQ_eq_storedQ hΨ

/-- The last term of the balance vanishes for lossless subsystems: if `A₀ᵀ = -A₀` and
`φ₁(H A₀)` is invertible, `skw Ψ = 0`. -/
theorem skw_zohPsi_of_skew (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hA0 : (S.blockDiag A)ᵀ = -S.blockDiag A) : skw (zohPsi S A H) = 0 :=
  skw_eq_zero (zohPsi_transpose S hφ hA0)

/-- The last term of the balance vanishes for symmetric subsystems: if `A₀ᵀ = A₀` and
`φ₁(H A₀)` is invertible, `skw Ψ = 0`. -/
theorem skw_zohPsi_of_symm (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hA0 : (S.blockDiag A)ᵀ = S.blockDiag A) : skw (zohPsi S A H) = 0 :=
  skw_eq_zero (psi_transpose_of_symm hA0 (Matrix.nonsing_inv_mul _ hφ))

/-- **The exact balance of one step of the zero-order hold, without a hypothesis on `Ψ`** (eq.
`eq:balance`). A scheme with `F = e^{H A₀}` and `M + N = G°C`, a lossless coupling
(`A q p = -A p q` between different subsystems) and `φ₁(H A₀)` invertible. For every `x`, with
`x' = X x`, `x̄ = ½ (x' + x)`, `Q = sym Ψ - (H/2) A_seq`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x) - x̄ᵀ (skw Ψ) (x' - x)`. -/
theorem zoh_energy_balance_skew (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE S.X x, opE (zohQSym S A H) (opE S.X x)⟫ - ⟪x, opE (zohQSym S A H) x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE S.X x + x), opE A ((1 / 2 : ℝ) • (opE S.X x + x))⟫ +
        H / 2 * ⟪opE (S.parCoupling A) ((1 / 2 : ℝ) • (opE S.X x + x)), opE S.X x - x⟫ -
        ⟪(1 / 2 : ℝ) • (opE S.X x + x), opE (skw (zohPsi S A H)) (opE S.X x - x)⟫ :=
  energy_balance_skew (Matrix.nonsing_inv_mul _ hφ) (zoh_implicit S hF hMN)
    (blockDiag_add_oldPart_add_newPart S A) (newPart_sub_oldPart_eq S A)
    (S.seqCoupling_transpose hskew) (S.parCoupling_transpose hskew) x

/-- **Eq. `eq:balance` for the zero-order hold with the dissipation `R = -sym A`.** In the
setting of `zoh_energy_balance_skew`:
`½ (x'ᵀ Q x' - xᵀ Q x) = -H x̄ᵀ R x̄ + (H/2) (A_par x̄)ᵀ (x' - x) - x̄ᵀ (skw Ψ) (x' - x)`. -/
theorem zoh_energy_balance_skew_diss (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE S.X x, opE (zohQSym S A H) (opE S.X x)⟫ - ⟪x, opE (zohQSym S A H) x⟫) =
      -(H * ⟪(1 / 2 : ℝ) • (opE S.X x + x), opE (-sym A) ((1 / 2 : ℝ) • (opE S.X x + x))⟫) +
        H / 2 * ⟪opE (S.parCoupling A) ((1 / 2 : ℝ) • (opE S.X x + x)), opE S.X x - x⟫ -
        ⟪(1 / 2 : ℝ) • (opE S.X x + x), opE (skw (zohPsi S A H)) (opE S.X x - x)⟫ :=
  energy_balance_skew_diss (Matrix.nonsing_inv_mul _ hφ) (zoh_implicit S hF hMN)
    (blockDiag_add_oldPart_add_newPart S A) (newPart_sub_oldPart_eq S A)
    (S.seqCoupling_transpose hskew) (S.parCoupling_transpose hskew) rfl x

/-- **Eq. `eq:balance` for the zero-order hold `S.zoh A hA H`**, in any order of execution: for
a lossless coupling and `φ₁(H A₀)` invertible, for every `x`, with `x' = X x`, `x̄ = ½ (x' + x)`,
`Q = sym Ψ - (H/2) A_seq`:
`½ (x'ᵀ Q x' - xᵀ Q x) = H x̄ᵀ A x̄ + (H/2) (A_par x̄)ᵀ (x' - x) - x̄ᵀ (skw Ψ) (x' - x)`. -/
theorem zohScheme_energy_balance_skew
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (x : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * (⟪opE (S.zoh A hA H).X x, opE (zohQSym S A H) (opE (S.zoh A hA H).X x)⟫ -
        ⟪x, opE (zohQSym S A H) x⟫) =
      H * ⟪(1 / 2 : ℝ) • (opE (S.zoh A hA H).X x + x),
          opE A ((1 / 2 : ℝ) • (opE (S.zoh A hA H).X x + x))⟫ +
        H / 2 * ⟪opE (S.parCoupling A) ((1 / 2 : ℝ) • (opE (S.zoh A hA H).X x + x)),
          opE (S.zoh A hA H).X x - x⟫ -
        ⟪(1 / 2 : ℝ) • (opE (S.zoh A hA H).X x + x),
          opE (skw (zohPsi S A H)) (opE (S.zoh A hA H).X x - x)⟫ :=
  zoh_energy_balance_skew (S.zoh A hA H) hφ (S.zoh_F A hA H) (S.zoh_M_add_N A hA H) hskew x

end ZOH

end MidpointEnergy

end CoSimFoundations
