/-
The setting, for the aggregate plant.

Paper notation → Lean:
  x ∈ ℝⁿ, u, y ∈ ℝᵐ, w ∈ ℝᵖ          states, ports, external inputs: `X → ℝ`, `U → ℝ`, `W → ℝ`
  A, B, C, D, G, Q (block diagonal)   fields of `Plant` (the block structure is not used here)
  S(x) = ½ xᵀQx                       `Plant.storage`
  𝒟(x, u) = [x; u]ᵀ R [x; u]          `Plant.diss`, with `Plant.R` the block matrix of eq. (2)
  u = L y, L + Lᵀ = 0                 `IsSkew L`
  A_ref, C_ref (eq. 3)                `Plant.Aref`, `Plant.Cref`
  A_K, B_K, C_K, D_K (eq. 6)          `Plant.AK`, `Plant.BK`, `Plant.CK`, `Plant.DK`
The dissipation form is called `diss` because `D` is the feedthrough.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Calculus.FDeriv.Pi

open Matrix

namespace CoSimFoundations

variable {X U W : Type*} [Fintype X] [Fintype U] [Fintype W] [DecidableEq X] [DecidableEq U]

/-- `sym M = ½ (M + Mᵀ)`. -/
noncomputable def sym {ι : Type*} (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 / 2 : ℝ) • (M + Mᵀ)

/-- `uᵀ (M x) = xᵀ (Mᵀ u)`. -/
theorem dot_mulVec_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → ℝ) (M : Matrix ι κ ℝ) (x : κ → ℝ) : u ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (Mᵀ *ᵥ u) := by
  rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- A quadratic form only sees the symmetric part: `xᵀ (sym M) x = xᵀ M x`. -/
theorem dotProduct_mulVec_sym {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (sym M *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
  have h : x ⬝ᵥ (Mᵀ *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
    rw [dot_mulVec_swap, transpose_transpose]
  simp only [sym, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, h, smul_eq_mul]
  ring

/-- A linear plant with quadratic storage. -/
structure Plant (X U W : Type*) where
  A : Matrix X X ℝ
  B : Matrix X U ℝ
  C : Matrix U X ℝ
  D : Matrix U U ℝ
  G : Matrix X W ℝ
  Q : Matrix X X ℝ

namespace Plant

variable (P : Plant X U W)

/-- Output equation `y = C x + D u`. -/
def out (x : X → ℝ) (u : U → ℝ) : U → ℝ := P.C *ᵥ x + P.D *ᵥ u

/-- Right-hand side `A x + B u + G w`. -/
def rhs (x : X → ℝ) (u : U → ℝ) (w : W → ℝ) : X → ℝ := P.A *ᵥ x + P.B *ᵥ u + P.G *ᵥ w

/-- Storage `S(x) = ½ xᵀ Q x`. -/
noncomputable def storage (x : X → ℝ) : ℝ := (1 / 2 : ℝ) * (x ⬝ᵥ (P.Q *ᵥ x))

/-- The matrix `R` of eq. (2): `[[-sym(QA), ½(Cᵀ - QB)], [½(C - BᵀQ), sym D]]`. -/
noncomputable def R : Matrix (X ⊕ U) (X ⊕ U) ℝ :=
  fromBlocks (-sym (P.Q * P.A)) ((1 / 2 : ℝ) • (P.Cᵀ - P.Q * P.B))
    ((1 / 2 : ℝ) • (P.C - P.Bᵀ * P.Q)) (sym P.D)

/-- The dissipation form `𝒟(x, u) = [x; u]ᵀ R [x; u]` of eq. (2). -/
noncomputable def diss (x : X → ℝ) (u : U → ℝ) : ℝ :=
  Sum.elim x u ⬝ᵥ (P.R *ᵥ Sum.elim x u)

/-- The block form of `𝒟` expanded (`Q` symmetric): `-xᵀQAx + xᵀ(Cᵀ - QB)u + uᵀDu`. -/
theorem diss_eq (hQ : P.Qᵀ = P.Q) (x : X → ℝ) (u : U → ℝ) :
    P.diss x u = -(x ⬝ᵥ ((P.Q * P.A) *ᵥ x)) + x ⬝ᵥ ((P.Cᵀ - P.Q * P.B) *ᵥ u) +
      u ⬝ᵥ (P.D *ᵥ u) := by
  have hcross : u ⬝ᵥ ((P.C - P.Bᵀ * P.Q) *ᵥ x) = x ⬝ᵥ ((P.Cᵀ - P.Q * P.B) *ᵥ u) := by
    rw [dot_mulVec_swap, transpose_sub, transpose_mul, transpose_transpose, hQ]
  have hneg : x ⬝ᵥ ((-sym (P.Q * P.A)) *ᵥ x) = -(x ⬝ᵥ ((P.Q * P.A) *ᵥ x)) := by
    rw [neg_mulVec, dotProduct_neg, dotProduct_mulVec_sym]
  simp only [diss, R, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, dotProduct_add, hneg, smul_mulVec, dotProduct_smul, hcross,
    dotProduct_mulVec_sym, smul_eq_mul]
  ring

/-- **Lemma 1.1, pointwise form.** `xᵀQ(Ax + Bu + Gw) = yᵀu - 𝒟(x, u) + xᵀQGw`. -/
theorem power_identity (hQ : P.Qᵀ = P.Q) (x : X → ℝ) (u : U → ℝ) (w : W → ℝ) :
    x ⬝ᵥ (P.Q *ᵥ P.rhs x u w) = P.out x u ⬝ᵥ u - P.diss x u + x ⬝ᵥ (P.Q *ᵥ (P.G *ᵥ w)) := by
  have hC : (P.C *ᵥ x) ⬝ᵥ u = x ⬝ᵥ (P.Cᵀ *ᵥ u) := by rw [dotProduct_comm, dot_mulVec_swap]
  have hD : (P.D *ᵥ u) ⬝ᵥ u = u ⬝ᵥ (P.D *ᵥ u) := dotProduct_comm _ _
  rw [P.diss_eq hQ]
  simp only [rhs, out, mulVec_add, dotProduct_add, add_dotProduct, hC, hD, mulVec_mulVec,
    sub_mulVec, dotProduct_sub]
  ring

/-- Storage as a double sum. -/
theorem storage_eq_sum (x : X → ℝ) :
    P.storage x = (1 / 2 : ℝ) * ∑ i, ∑ j, x i * P.Q i j * x j := by
  simp only [storage, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- Derivative of the storage along a differentiable trajectory (`Q` symmetric). -/
theorem hasDerivAt_storage (hQ : P.Qᵀ = P.Q) {x : ℝ → X → ℝ} {x' : X → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => P.storage (x s)) (x t ⬝ᵥ (P.Q *ᵥ x')) t := by
  have hc : ∀ i, HasDerivAt (fun s => x s i) (x' i) t := fun i => hasDerivAt_pi.1 hx i
  have h := (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      ((hc i).mul_const (P.Q i j)).mul (hc j)).const_mul (1 / 2 : ℝ)
  simp only [storage_eq_sum]
  convert h using 1
  have hsym : ∀ i j, P.Q i j = P.Q j i := fun i j => by
    rw [← transpose_apply P.Q j i, hQ]
  have hswap : ∑ i, ∑ j, x' i * P.Q i j * x t j = ∑ i, ∑ j, x t i * P.Q i j * x' j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]; ring
  simp only [Finset.sum_add_distrib, hswap, dotProduct, mulVec, Finset.mul_sum]
  ring_nf

/-- **Lemma 1.1 (exact energy balance).** Along a solution of `ẋ = Ax + Bu + Gw`,
`d/dt S(x) = yᵀu - 𝒟(x, u) + xᵀQGw`. -/
theorem energy_balance (hQ : P.Qᵀ = P.Q) {x : ℝ → X → ℝ} {u : U → ℝ} {w : W → ℝ} {t : ℝ}
    (hx : HasDerivAt x (P.rhs (x t) u w) t) :
    HasDerivAt (fun s => P.storage (x s))
      (P.out (x t) u ⬝ᵥ u - P.diss (x t) u + x t ⬝ᵥ (P.Q *ᵥ (P.G *ᵥ w))) t := by
  rw [← P.power_identity hQ]
  exact P.hasDerivAt_storage hQ hx

/-! ### Routing and the reference (§1.2) -/

/-- The reference `A_ref = A + B L (I - D L)⁻¹ C` (eq. 3). -/
noncomputable def Aref (L : Matrix U U ℝ) : Matrix X X ℝ :=
  P.A + P.B * L * (1 - P.D * L)⁻¹ * P.C

/-- `C_ref = (I - D L)⁻¹ C` (eq. 3). -/
noncomputable def Cref (L : Matrix U U ℝ) : Matrix U X ℝ := (1 - P.D * L)⁻¹ * P.C

/-- **Eq. (3).** If the reference is well posed (`I - D L` invertible), eliminating `u = L y`
gives `y = C_ref x` and `ẋ = A_ref x + G w`. -/
theorem reference_eq (L : Matrix U U ℝ) (hwp : IsUnit (1 - P.D * L).det) {x : X → ℝ}
    {u : U → ℝ} (w : W → ℝ) (hu : u = L *ᵥ P.out x u) :
    P.out x u = P.Cref L *ᵥ x ∧ P.rhs x u w = P.Aref L *ᵥ x + P.G *ᵥ w := by
  set y := P.out x u with hy
  have hy' : y = P.C *ᵥ x + P.D *ᵥ (L *ᵥ y) := by
    rw [hy, out]; nth_rewrite 1 [hu]; rfl
  have hlin : (1 - P.D * L) *ᵥ y = P.C *ᵥ x := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec]
    nth_rewrite 1 [hy']
    abel
  have hyx : y = P.Cref L *ᵥ x := by
    rw [Cref, ← mulVec_mulVec, ← hlin, mulVec_mulVec, nonsing_inv_mul _ hwp, one_mulVec]
  refine ⟨hyx, ?_⟩
  rw [rhs, hu, hyx, Aref, Cref]
  simp only [add_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-! ### The locally closed subsystem (§1.4, eq. 6) -/

/-- `A_K = A + B (I - K D)⁻¹ K C`. -/
noncomputable def AK (K : Matrix U U ℝ) : Matrix X X ℝ := P.A + P.B * (1 - K * P.D)⁻¹ * K * P.C
/-- `B_K = B (I - K D)⁻¹`. -/
noncomputable def BK (K : Matrix U U ℝ) : Matrix X U ℝ := P.B * (1 - K * P.D)⁻¹
/-- `C_K = (I - D K)⁻¹ C`. -/
noncomputable def CK (K : Matrix U U ℝ) : Matrix U X ℝ := (1 - P.D * K)⁻¹ * P.C
/-- `D_K = (I - D K)⁻¹ D`. -/
noncomputable def DK (K : Matrix U U ℝ) : Matrix U U ℝ := (1 - P.D * K)⁻¹ * P.D

/-- **Eq. (6).** With `u = c + K y` holding pointwise (C4) and `I - D K` invertible:
`ẋ = A_K x + B_K c + G w`, `y = C_K x + D_K c`, `u = (I - K D)⁻¹ (c + K C x)`. -/
theorem local_closure (K : Matrix U U ℝ) (hK : IsUnit (1 - P.D * K).det) {x : X → ℝ}
    {u c : U → ℝ} (w : W → ℝ) (hu : u = c + K *ᵥ P.out x u) :
    P.rhs x u w = P.AK K *ᵥ x + P.BK K *ᵥ c + P.G *ᵥ w ∧
      P.out x u = P.CK K *ᵥ x + P.DK K *ᵥ c ∧
      u = (1 - K * P.D)⁻¹ *ᵥ (c + K *ᵥ (P.C *ᵥ x)) := by
  have hK' : IsUnit (1 - K * P.D).det := by rwa [det_one_sub_mul_comm]
  set y := P.out x u with hy
  have hyu : y = P.C *ᵥ x + P.D *ᵥ u := rfl
  have hu' : (1 - K * P.D) *ᵥ u = c + K *ᵥ (P.C *ᵥ x) := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec]
    nth_rewrite 1 [hu]
    rw [hyu, mulVec_add]
    abel
  have hux : u = (1 - K * P.D)⁻¹ *ᵥ (c + K *ᵥ (P.C *ᵥ x)) := by
    rw [← hu', mulVec_mulVec, nonsing_inv_mul _ hK', one_mulVec]
  have hy' : (1 - P.D * K) *ᵥ y = P.C *ᵥ x + P.D *ᵥ c := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec]
    nth_rewrite 1 [hyu]
    nth_rewrite 1 [hu]
    rw [mulVec_add]
    abel
  have hyx : y = P.CK K *ᵥ x + P.DK K *ᵥ c := by
    rw [CK, DK, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_add, ← hy', mulVec_mulVec,
      nonsing_inv_mul _ hK, one_mulVec]
  refine ⟨?_, hyx, hux⟩
  rw [rhs, hux, AK, BK]
  simp only [mulVec_add, add_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  abel

end Plant

/-! ### Power-conserving routing (§1.2) -/

/-- `L` is skew: `L + Lᵀ = 0`. -/
def IsSkew (L : Matrix U U ℝ) : Prop := Lᵀ = -L

/-- **§1.2.** The routing is power-conserving (`yᵀ L y = 0` for all `y`) iff `L` is skew. -/
theorem power_conserving_iff (L : Matrix U U ℝ) :
    (∀ y : U → ℝ, y ⬝ᵥ (L *ᵥ y) = 0) ↔ IsSkew L := by
  constructor
  · intro h
    ext i j
    have hpol : ∀ y z : U → ℝ, y ⬝ᵥ (L *ᵥ z) + z ⬝ᵥ (L *ᵥ y) = 0 := by
      intro y z
      have := h (y + z)
      rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h y, h z] at this
      linarith
    have := hpol (Pi.single j 1) (Pi.single i 1)
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, ite_mul, one_mul, mul_one,
      mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    rw [transpose_apply, Matrix.neg_apply]
    linarith
  · intro hL y
    have h1 : y ⬝ᵥ (L *ᵥ y) = y ⬝ᵥ (Lᵀ *ᵥ y) := by rw [dot_mulVec_swap]
    rw [hL, neg_mulVec, dotProduct_neg] at h1
    linarith

end CoSimFoundations
