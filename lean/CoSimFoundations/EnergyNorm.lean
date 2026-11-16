/-
The energy inner product `⟪x, y⟫_Q = xᵀ Q y` (Q positive definite) and its toolkit.

`QSpace E` is `ℝⁿ` carrying the energy inner product, so Mathlib's adjoints and operator norms
are the energy-norm ones:
  `‖x‖² = xᵀQx = 2 S(x)`,
  the Q-adjoint of a matrix `A` is `Q⁻¹ Aᵀ Q`,
  `‖D x‖² ≤ ‖D‖² ‖x‖²` reads `S(Dx) ≤ ‖D‖_Q² S(x)` (the paper's `ε = ‖D‖_Q² - 1` bounds the
  relative energy added per step),
  the energy rate of a generator `Δ` is the quadratic form of `sym(QΔ)`, and `Q`-skew generators
  (`QΔ` skew) conserve energy.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension
import CoSimFoundations.Setting

open Matrix

namespace CoSimFoundations

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite energy matrix. -/
structure EnergyForm (n : Type*) [Fintype n] where
  Q : Matrix n n ℝ
  posDef : Q.PosDef

/-- `ℝⁿ` with the energy inner product of `E`. -/
def QSpace (_E : EnergyForm n) : Type _ := n → ℝ

namespace QSpace

variable (E : EnergyForm n)

noncomputable instance : NormedAddCommGroup (QSpace E) := E.Q.toNormedAddCommGroup E.posDef
noncomputable instance : InnerProductSpace ℝ (QSpace E) := E.Q.toInnerProductSpace E.posDef.posSemidef

/-- Coordinates. -/
def ofVec (x : n → ℝ) : QSpace E := x
def toVec (x : QSpace E) : n → ℝ := x

instance : FiniteDimensional ℝ (QSpace E) :=
  inferInstanceAs (FiniteDimensional ℝ (n → ℝ))

variable {E}

theorem inner_eq (x y : QSpace E) :
    (inner ℝ x y : ℝ) = toVec E x ⬝ᵥ (E.Q *ᵥ toVec E y) := by
  show (E.Q *ᵥ toVec E y) ⬝ᵥ star (toVec E x) = _
  rw [star_trivial, dotProduct_comm]

theorem norm_sq_eq (x : QSpace E) : ‖x‖ ^ 2 = toVec E x ⬝ᵥ (E.Q *ᵥ toVec E x) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]

/-- A matrix as an operator on `QSpace E`. -/
noncomputable def op (A : Matrix n n ℝ) : QSpace E →L[ℝ] QSpace E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ofVec E (A *ᵥ toVec E x)
      map_add' := fun x y => mulVec_add A x y
      map_smul' := fun c x => mulVec_smul A c x }

theorem toVec_op (A : Matrix n n ℝ) (x : QSpace E) : toVec E (op A x) = A *ᵥ toVec E x := rfl

theorem Q_symm : E.Qᵀ = E.Q := E.posDef.isHermitian.eq

/-- **The `Q`-adjoint** of `A` is `Q⁻¹ Aᵀ Q`. -/
theorem adjoint_op (A : Matrix n n ℝ) :
    ContinuousLinearMap.adjoint (op (E := E) A) = op (E.Q⁻¹ * Aᵀ * E.Q) := by
  have hQ : IsUnit E.Q.det := E.posDef.isUnit.map (Matrix.detMonoidHom)
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  set B := E.Q⁻¹ * Aᵀ * E.Q
  have hB : Bᵀ * E.Q = E.Q * A := by
    simp only [B, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_symm,
      Matrix.mul_assoc, nonsing_inv_mul _ hQ, Matrix.mul_one]
  rw [inner_eq, inner_eq, toVec_op, toVec_op]
  calc (B *ᵥ toVec E x) ⬝ᵥ (E.Q *ᵥ toVec E y)
      = (E.Q *ᵥ toVec E y) ⬝ᵥ (B *ᵥ toVec E x) := dotProduct_comm _ _
    _ = toVec E x ⬝ᵥ (Bᵀ *ᵥ (E.Q *ᵥ toVec E y)) := dot_mulVec_swap _ _ _
    _ = toVec E x ⬝ᵥ (E.Q *ᵥ (A *ᵥ toVec E y)) := by rw [mulVec_mulVec, hB, ← mulVec_mulVec]

/-- **Energy added per step is bounded by the energy-norm:** `S(Dx) ≤ ‖D‖_Q² S(x)`, i.e.
`(Dx)ᵀQ(Dx) ≤ ‖D‖_Q² xᵀQx`. -/
theorem energy_le_opNorm_sq (D : Matrix n n ℝ) (x : n → ℝ) :
    (D *ᵥ x) ⬝ᵥ (E.Q *ᵥ (D *ᵥ x)) ≤ ‖op (E := E) D‖ ^ 2 * (x ⬝ᵥ (E.Q *ᵥ x)) := by
  have h := (op (E := E) D).le_opNorm (ofVec E x)
  have h2 : ‖op (E := E) D (ofVec E x)‖ ^ 2 ≤ (‖op (E := E) D‖ * ‖ofVec E x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, norm_sq_eq, norm_sq_eq, toVec_op] at h2
  exact h2

end QSpace

/-! ### The energy split of a generator (Thm 5.2) -/

section Split

variable (Q : Matrix n n ℝ)

/-- The `Q`-adjoint `X⋆ = Q⁻¹ Xᵀ Q`. -/
noncomputable def qAdj (X : Matrix n n ℝ) : Matrix n n ℝ := Q⁻¹ * Xᵀ * Q

/-- The operator inner product `⟪X, Y⟫_Q = tr (X⋆ Y)`. -/
noncomputable def qInner (X Y : Matrix n n ℝ) : ℝ := trace (qAdj Q X * Y)

variable {Q}

/-- **The power form sees only `sym(QΔ)`:** `xᵀ Q Δ x = xᵀ sym(QΔ) x` (an algebraic identity).
With `Plant.hasDerivAt_storage` it gives the energy rate `d/dt ½ xᵀQx = xᵀ sym(QΔ) x` along
`ẋ = Δ x`. -/
theorem energy_rate_eq (Δ : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (Q *ᵥ (Δ *ᵥ x)) = x ⬝ᵥ (sym (Q * Δ) *ᵥ x) := by
  rw [dotProduct_mulVec_sym, mulVec_mulVec]

/-- **`Q`-skew generators are energy-neutral:** if `QΔ` is skew, the power form `xᵀ Q Δ x`
vanishes. -/
theorem energy_rate_skew {Δ : Matrix n n ℝ} (hΔ : (Q * Δ)ᵀ = -(Q * Δ)) (x : n → ℝ) :
    x ⬝ᵥ (Q *ᵥ (Δ *ᵥ x)) = 0 := by
  rw [mulVec_mulVec]
  have h : x ⬝ᵥ ((Q * Δ) *ᵥ x) = x ⬝ᵥ ((Q * Δ)ᵀ *ᵥ x) := by
    rw [dot_mulVec_swap]
  rw [hΔ, neg_mulVec, dotProduct_neg] at h
  linarith

theorem trace_qAdj (hQ : IsUnit Q.det) (X : Matrix n n ℝ) : trace (qAdj Q X) = trace X := by
  rw [qAdj, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, mul_nonsing_inv _ hQ,
    Matrix.mul_one, trace_transpose]

theorem qAdj_mul (hQ : IsUnit Q.det) (X Y : Matrix n n ℝ) :
    qAdj Q (X * Y) = qAdj Q Y * qAdj Q X := by
  simp only [qAdj, transpose_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hQ]

/-- **Orthogonality of the energy split (Thm 5.2).** A `Q`-self-adjoint generator (`S⋆ = S`, the
part that adds or removes energy) and a `Q`-skew one (`K⋆ = -K`, energy-neutral) are orthogonal in
`⟪X, Y⟫_Q = tr (X⋆ Y)`. -/
theorem qInner_selfAdjoint_skew (hQ : IsUnit Q.det) {S K : Matrix n n ℝ} (hS : qAdj Q S = S)
    (hK : qAdj Q K = -K) : qInner Q S K = 0 := by
  have h1 : trace (qAdj Q (S * K)) = trace (S * K) := trace_qAdj hQ _
  rw [qAdj_mul hQ, hK, hS, Matrix.neg_mul, trace_neg, trace_mul_comm] at h1
  rw [qInner, hS]
  linarith

end Split

end CoSimFoundations
