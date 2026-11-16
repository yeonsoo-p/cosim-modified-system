/-
Symmetric and skew part of the signed coupling for power-conjugate ports (the paper, Section
"Energy stored and energy created": the matrix `E = Ψ₀ - ½H A_ς` of the midpoint form, the matrix
`Q` of the modified energy and the coupling within a stage).

**Setting** (`StoredEnergy`, `MidpointForm`, `MidpointEnergyZOH`, `MidpointEnergySkew`). `A_ς` is
the signed coupling (`signedCoupling`), `A_seq` its blocks between subsystems at different stages
(`seqCoupling`), `A_par` the blocks of `A` between different subsystems at the same stage
(`parCoupling`), `A_ς = A_seq - A_par` (`signedCoupling_eq`). `sym M = ½ (M + Mᵀ)`,
`skw M = ½ (M - Mᵀ)`. `Ψ = φ₁(H A₀)⁻¹ + ½H A₀` (`midpointPsi`, the same matrix as `zohPsi`,
`midpointPsi_eq_zohPsi`) and `E = Ψ - ½H A_ς` (`midpointE`), the matrix of the midpoint form
`E (X - 1) = ½H A (X + 1)` (`zoh_midpointE` of `MidpointStability`).

**Statements**, for power-conjugate ports (`A q p = -A p q` between different subsystems), any
assignment of stages and any `H`:
* `sym_signedCoupling`, `skw_signedCoupling`: `sym A_ς = A_seq`, `skw A_ς = -A_par`
  (`A_seq` is symmetric and `A_par` is skew, `seqCoupling_transpose`, `parCoupling_transpose`);
* `sym_midpointE`: `sym E = sym Ψ - ½H A_seq`, the matrix `zohQSym` of the modified energy;
* `sym_midpointE_eq_zohQ`, `sym_midpointE_of_skew`, `sym_midpointE_of_symm`: if `Ψ` is symmetric,
  in particular if `φ₁(H A₀)` is invertible and `A₀` is skew or symmetric, `sym E = Q`
  (`zohQ = Ψ - ½H A_seq`);
* `skw_midpointE`: `skw E = skw Ψ + ½H A_par`; `skw_midpointE_of_skew`: `skw E = ½H A_par` if
  `φ₁(H A₀)` is invertible and `A₀` is skew.
No statement needs a sequential order: a link within a stage is in `A_par`.
-/
import CoSimFoundations.MidpointEnergySkew
import CoSimFoundations.MidpointForm
import CoSimFoundations.MidpointStability

open Matrix

namespace CoSimFoundations

namespace HeldScheme

open MidpointEnergy

variable {n : ℕ} {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The signed coupling -/

/-- **The symmetric part of the signed coupling is its sequential part** (power-conjugate
ports): `sym A_ς = A_seq`. -/
theorem sym_signedCoupling {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    sym (S.signedCoupling A) = S.seqCoupling A := by
  rw [S.signedCoupling_eq, sym, Matrix.transpose_sub, S.seqCoupling_transpose hskew,
    S.parCoupling_transpose hskew]
  module

/-- **The skew part of the signed coupling is minus the coupling within a stage**
(power-conjugate ports): `skw A_ς = -A_par`. -/
theorem skw_signedCoupling {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    skw (S.signedCoupling A) = -S.parCoupling A := by
  rw [S.signedCoupling_eq, skw, Matrix.transpose_sub, S.seqCoupling_transpose hskew,
    S.parCoupling_transpose hskew]
  module

/-- `A_seq = sym A_ς` for power-conjugate ports. -/
theorem seqCoupling_eq_sym {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    S.seqCoupling A = sym (S.signedCoupling A) :=
  (S.sym_signedCoupling hskew).symm

/-- `A_par = -skw A_ς` for power-conjugate ports. -/
theorem parCoupling_eq_neg_skw {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    S.parCoupling A = -skw (S.signedCoupling A) := by
  rw [S.skw_signedCoupling hskew, neg_neg]

/-! ### The matrix of the midpoint form -/

/-- The matrix `Ψ` of `MidpointForm` is the matrix `Ψ` of `MidpointEnergyZOH`. -/
theorem midpointPsi_eq_zohPsi (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.midpointPsi A H = zohPsi S A H := rfl

/-- **The symmetric part of `E` is the matrix of the modified energy** (power-conjugate ports):
`sym E = sym Ψ - ½H A_seq` (`zohQSym`), for every assignment of stages and every `H`. -/
theorem sym_midpointE {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (H : ℝ) :
    sym (S.midpointE A H) = zohQSym S A H := by
  have h1 : sym (S.midpointE A H) =
      sym (S.midpointPsi A H) - (H / 2) • sym (S.signedCoupling A) := by
    rw [midpointE, sym, sym, sym, Matrix.transpose_sub, Matrix.transpose_smul]
    module
  rw [h1, S.sym_signedCoupling hskew, zohQSym_eq, S.midpointPsi_eq_zohPsi]

/-- **`Q = sym E`** (power-conjugate ports, `Ψ` symmetric): if `Ψᵀ = Ψ`, the symmetric part of
`E` is the matrix `Q = Ψ - ½H A_seq` of the stored energy (`zohQ`). -/
theorem sym_midpointE_eq_zohQ {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {H : ℝ}
    (hΨ : (zohPsi S A H)ᵀ = zohPsi S A H) : sym (S.midpointE A H) = zohQ S A H := by
  rw [S.sym_midpointE hskew, zohQSym_eq_zohQ S hΨ]

/-- **`Q = sym E` for lossless subsystems:** if the ports are power-conjugate, `A₀ᵀ = -A₀` and
`φ₁(H A₀)` is invertible, then `sym E = Q`. -/
theorem sym_midpointE_of_skew {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {H : ℝ}
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hA0 : (S.blockDiag A)ᵀ = -S.blockDiag A) : sym (S.midpointE A H) = zohQ S A H :=
  S.sym_midpointE_eq_zohQ hskew (zohPsi_transpose S hφ hA0)

/-- **`Q = sym E` for symmetric subsystems:** if the ports are power-conjugate, `A₀ᵀ = A₀` and
`φ₁(H A₀)` is invertible, then `sym E = Q`. -/
theorem sym_midpointE_of_symm {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {H : ℝ}
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hA0 : (S.blockDiag A)ᵀ = S.blockDiag A) : sym (S.midpointE A H) = zohQ S A H :=
  S.sym_midpointE_eq_zohQ hskew (psi_transpose_of_symm hA0 (Matrix.nonsing_inv_mul _ hφ))

/-- **The skew part of `E`** (power-conjugate ports): `skw E = skw Ψ + ½H A_par`, for every
assignment of stages and every `H`. -/
theorem skw_midpointE {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (H : ℝ) :
    skw (S.midpointE A H) = skw (zohPsi S A H) + (H / 2) • S.parCoupling A := by
  have h1 : skw (S.midpointE A H) =
      skw (S.midpointPsi A H) - (H / 2) • skw (S.signedCoupling A) := by
    rw [midpointE, skw, skw, skw, Matrix.transpose_sub, Matrix.transpose_smul]
    module
  rw [h1, S.skw_signedCoupling hskew, S.midpointPsi_eq_zohPsi, smul_neg, sub_neg_eq_add]

/-- **The skew part of `E` for lossless subsystems:** if the ports are power-conjugate,
`A₀ᵀ = -A₀` and `φ₁(H A₀)` is invertible, then `skw E = ½H A_par`. -/
theorem skw_midpointE_of_skew {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {H : ℝ}
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det)
    (hA0 : (S.blockDiag A)ᵀ = -S.blockDiag A) :
    skw (S.midpointE A H) = (H / 2) • S.parCoupling A := by
  rw [S.skw_midpointE hskew, skw_zohPsi_of_skew S hφ hA0, zero_add]

end HeldScheme

end CoSimFoundations
