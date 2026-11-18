/-
The largest energy over a run of the sequential zero-order hold on the lossless chain of three
stores, with the middle store first (the paper, Section `sec:energy`: "With the middle store
first it is the bound `(1+h/√2)/(1-h/√2)` itself: in the coordinates `Q^{1/2} x` the step fixes
the direction of `Q^{1/2}(1,0,1)` and turns the orthogonal plane, which contains the extreme
eigenvectors of `Q`, by an angle `θ` with `2 cos θ = 2 - 2h²`").

**Setting.** The chain `A = ω [[0,-1,0],[1,0,-1],[0,1,0]]` (`chainA`), stores `0, 1, 2`, the
middle store `1` at the first stage and the end stores at the second. With `h = ω H` the
zero-order hold of the library (`HeldScheme.zoh` on `chainScheme`) has the one-step map

  `X = [[1-h², -h, h²], [h, 1, -h], [h², h, 1-h²]]`          (`chainX`, `chainScheme_zoh_X`).

**Statements.** `κ = (1 + h/√2)/(1 - h/√2)` (`chainKappa`), `‖·‖` the Euclidean norm.
* `chainX_transpose_mul_chainQ_mul`: `Xᵀ Q X = Q` with `Q = 1 - (h/2) S`, `S` the signed coupling
  `ω⁻¹ A_seq` (`chainQ`); in quadratic forms `q(X y) = q(y)`,
  `q(y) = |y|² + h y₀ y₁ - h y₁ y₂` (`chainForm_pow_mulVec`), and
  `(1 - h/√2) |y|² ≤ q(y) ≤ (1 + h/√2) |y|²` (`chainForm_bounds`).
* `chain_norm_pow_sq_le`: `‖X^k x‖² ≤ κ ‖x‖²` for all `k`, `x`, `0 ≤ h < √2`.
* The extreme eigenvectors `v = (1, √2, -1)` (of `λ_max(Q) = 1 + h/√2`) and `w = (1, -√2, -1)`
  (of `λ_min(Q)`) lie in the plane orthogonal to the fixed vector `(1, 0, 1)`; with
  `cos θ = 1 - h²` and `ρ = h(√2 + h)/sin θ`, `ρ² = κ` (`chainRho_sq`),
  `X^k v = cos(kθ) v - ρ sin(kθ) w` (`chainX_pow_mulVec_vMax`), hence
  `|X^k v|² = 4 (cos²(kθ) + κ sin²(kθ))` (`sq3_chainX_pow_mulVec_vMax`).
* If `θ/π` is irrational, `cos²(kθ)` comes arbitrarily close to `0` (`exists_cos_sq_lt`, from the
  density of an irrational rotation, `AddCircle.denseRange_zsmul_coe_iff`), so
  `chain_exists_norm_pow_sq_gt`: for every `ε > 0` some `k` and unit `x` have
  `‖X^k x‖² > κ - ε`, and
  `chain_iSup_norm_pow_sq`: `⨆_k ‖X^k‖² = κ` (operator norms on Euclidean space).
* `θ/π` is irrational if `h²` is rational and not `1/2`, `1`, `3/2`, by Niven's theorem
  (`irrational_arccos_div_pi`); `chain_iSup_norm_pow_sq_of_rat` and the paper's value
  `chain_iSup_norm_pow_sq_tenth` (`h = 1/10`).

The statement is not true for every `0 < h < 1`: at `h² = 1/2` (`cos θ = 1/2`) and wherever
`e^{iθ}` is a root of unity (for instance `2 - 2h² = 2 cos(2π/5)`) the powers of `X` take finitely
many values; the hypothesis on `θ/π` is the one the paper's argument uses.
-/
import CoSimFoundations.FloorMatrix
import CoSimFoundations.HalfStepZOH
import CoSimFoundations.StoredEnergy
import Mathlib.NumberTheory.Niven
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Matrix Real
open scoped Nat

namespace CoSimFoundations

/-- The one-step map of the zero-order hold on the lossless chain of three stores with the
middle store first, `h = ω H`: the middle store advances on the old samples of the ends, the ends
on the new sample of the middle. -/
def chainX (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - h ^ 2, -h, h ^ 2; h, 1, -h; h ^ 2, h, 1 - h ^ 2]

/-- The invariant form `Q = 1 - (h/2) S`, `S = [[0,-1,0],[-1,0,1],[0,1,0]]` the signed coupling
divided by `ω` (both links between two stages). -/
noncomputable def chainQ (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, h / 2, 0; h / 2, 1, -h / 2; 0, -h / 2, 1]

/-- **The stored energy is invariant:** `Xᵀ Q X = Q`. -/
theorem chainX_transpose_mul_chainQ_mul (h : ℝ) :
    (chainX h)ᵀ * chainQ h * chainX h = chainQ h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chainX, chainQ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-! ### The one-step map from the zero-order hold of the library -/

/-- The lossless chain of three scalar stores with the rate `ω`. -/
def chainA (ω : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -ω, 0; ω, 0, -ω; 0, ω, 0]

/-- The chain as a scheme: every store a subsystem, the end stores partners of the middle one,
the middle store at the first stage and the end stores at the second. (The coefficients `F = 1`,
`N = M = 0` are placeholders; `HeldScheme.zoh` replaces them by those of the zero-order hold.) -/
def chainScheme : HeldScheme 3 (Fin 3) where
  sub := id
  partner := fun s t => s ≠ t ∧ (s = 1 ∨ t = 1)
  stage := ![1, 0, 1]
  F := 1
  N := 0
  M := 0
  X := 1
  hF := fun _ _ h => Matrix.one_apply_ne h
  hN := fun _ _ _ => rfl
  hM := fun _ _ _ => rfl
  hX := by simp

/-- The chain has no entry between stores that are not partners. -/
theorem chainA_not_partner (ω : ℝ) : ∀ p q, chainScheme.sub p ≠ chainScheme.sub q →
    ¬ chainScheme.partner (chainScheme.sub p) (chainScheme.sub q) → chainA ω p q = 0 := by
  intro p q h1 h2
  fin_cases p <;> fin_cases q <;> simp_all [chainScheme, chainA]

/-- `φ₁(0) = 1`. -/
theorem phiOne_zero {n : ℕ} : phiOne (0 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h := hasSum_phiOne (0 : Matrix (Fin n) (Fin n) ℝ)
  have e : (fun j : ℕ => ((((j + 1)! : ℕ) : ℝ))⁻¹ • (0 : Matrix (Fin n) (Fin n) ℝ) ^ j) =
      fun j => if j = 0 then 1 else 0 := by
    funext j
    rcases j with _ | j
    · simp
    · simp
  rw [e] at h
  exact h.unique (hasSum_ite_eq 0 1)

/-- **The one-step map of the zero-order hold of the library on the chain, middle store first,**
is `chainX (ω H)`. -/
theorem chainScheme_zoh_X (ω H : ℝ) :
    (chainScheme.zoh (chainA ω) (chainA_not_partner ω) H).X = chainX (ω * H) := by
  have hbd : chainScheme.blockDiag (chainA ω) = 0 := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [HeldScheme.blockDiag_apply, chainScheme, chainA]
  have hc : chainScheme.zohCoupling (chainA ω) H = H • chainA ω := by
    rw [HeldScheme.zohCoupling, HeldScheme.zohKernel, HeldScheme.coupling, hbd, smul_zero,
      phiOne_zero, sub_zero, Matrix.smul_mul, Matrix.one_mul]
  set S' := chainScheme.zoh (chainA ω) (chainA_not_partner ω) H with hS'
  have hF : S'.F = 1 := by
    rw [hS', HeldScheme.zoh_F]
    have hbd' : (chainScheme.zoh (chainA ω) (chainA_not_partner ω) H).blockDiag (chainA ω) =
        0 := hbd
    rw [hbd', smul_zero, NormedSpace.exp_zero]
  have hN : S'.N = !![0, -(ω * H), 0; 0, 0, 0; 0, ω * H, 0] := by
    show chainScheme.zohNew (chainA ω) H = _
    ext p q
    rw [HeldScheme.zohNew, Matrix.of_apply, hc]
    fin_cases p <;> fin_cases q <;> simp [chainScheme, chainA] <;> ring
  have hM : S'.M = !![0, 0, 0; ω * H, 0, -(ω * H); 0, 0, 0] := by
    show chainScheme.zohOld (chainA ω) H = _
    ext p q
    rw [HeldScheme.zohOld, Matrix.of_apply, hc]
    fin_cases p <;> fin_cases q <;> simp [chainScheme, chainA] <;> ring
  have hu := S'.isUnit_det_one_sub_N
  have hmul : (1 - S'.N) * chainX (ω * H) = S'.F + S'.M := by
    rw [hN, hF, hM]
    ext p q
    fin_cases p <;> fin_cases q <;> simp [chainX, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  rw [S'.X_eq_inv_mul, ← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-- The sum of squares on `Fin 3 → ℝ`. -/
def sq3 (y : Fin 3 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2

/-- The quadratic form of `Q`: `q(y) = |y|² + h y₀ y₁ - h y₁ y₂`. -/
def chainForm (h : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  sq3 y + h * y 0 * y 1 - h * y 1 * y 2

/-- `q(y) = yᵀ Q y`. -/
theorem dotProduct_chainQ_mulVec (h : ℝ) (y : Fin 3 → ℝ) :
    y ⬝ᵥ (chainQ h *ᵥ y) = chainForm h y := by
  simp [chainQ, chainForm, sq3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- One step keeps the form: `q(X y) = q(y)`. -/
theorem chainForm_mulVec (h : ℝ) (y : Fin 3 → ℝ) : chainForm h (chainX h *ᵥ y) = chainForm h y := by
  simp [chainX, chainForm, sq3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Every power keeps the form: `q(X^k y) = q(y)`. -/
theorem chainForm_pow_mulVec (h : ℝ) (k : ℕ) (y : Fin 3 → ℝ) :
    chainForm h (chainX h ^ k *ᵥ y) = chainForm h y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, ih, chainForm_mulVec]

/-- **The bounds of the form:** `(1 - h/√2) |y|² ≤ q(y) ≤ (1 + h/√2) |y|²` for `h ≥ 0`
(the eigenvalues of `Q` are `1` and `1 ± h/√2`). -/
theorem chainForm_bounds {h : ℝ} (hh : 0 ≤ h) (y : Fin 3 → ℝ) :
    (1 - h / √2) * sq3 y ≤ chainForm h y ∧ chainForm h y ≤ (1 + h / √2) * sq3 y := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  -- `√2 |y₁ (y₂ - y₀)| ≤ |y|²`
  have h1 : √2 * (y 1 * (y 2 - y 0)) ≤ sq3 y := by
    unfold sq3
    nlinarith [sq_nonneg (y 1 - √2 * (y 2 - y 0) / 2), sq_nonneg (y 0 + y 2)]
  have h2 : -(√2 * (y 1 * (y 2 - y 0))) ≤ sq3 y := by
    unfold sq3
    nlinarith [sq_nonneg (y 1 + √2 * (y 2 - y 0) / 2), sq_nonneg (y 0 + y 2)]
  have e : h / √2 * (√2 * (y 1 * (y 2 - y 0))) = h * (y 1 * (y 2 - y 0)) := by
    field_simp
  have hh' : 0 ≤ h / √2 := div_nonneg hh hs0.le
  have h3 := mul_le_mul_of_nonneg_left h1 hh'
  have h4 := mul_le_mul_of_nonneg_left h2 hh'
  rw [e] at h3
  rw [mul_neg, e] at h4
  unfold chainForm
  constructor <;> nlinarith

/-- `κ = (1 + h/√2)/(1 - h/√2)`, the ratio of the extreme eigenvalues of `Q`. -/
noncomputable def chainKappa (h : ℝ) : ℝ := (1 + h / √2) / (1 - h / √2)

/-- **The energy never exceeds `κ` times its initial value:** `|X^k y|² ≤ κ |y|²` for
`0 ≤ h < √2`. -/
theorem sq3_chainX_pow_mulVec_le {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < √2) (k : ℕ)
    (y : Fin 3 → ℝ) : sq3 (chainX h ^ k *ᵥ y) ≤ chainKappa h * sq3 y := by
  have hs0 : 0 < √2 := by positivity
  have hpos : 0 < 1 - h / √2 := by
    rw [sub_pos, div_lt_one hs0]
    exact hh1
  have h1 := (chainForm_bounds hh0 (chainX h ^ k *ᵥ y)).1
  have h2 := (chainForm_bounds hh0 y).2
  rw [chainForm_pow_mulVec] at h1
  rw [chainKappa, div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-- The squared Euclidean norm is the sum of squares. -/
theorem norm_sq_eq_sq3 (x : EuclideanSpace ℝ (Fin 3)) : ‖x‖ ^ 2 = sq3 (WithLp.ofLp x) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  rfl

/-- The matrix acting on Euclidean space, in the sum of squares. -/
theorem norm_opE_sq_eq_sq3 (M : Matrix (Fin 3) (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖opE M x‖ ^ 2 = sq3 (M *ᵥ WithLp.ofLp x) := by
  rw [norm_sq_eq_sq3, opE, ofLp_toEuclideanCLM]

/-- **The bound of the paper for the chain, middle store first:** `‖X^k x‖² ≤ κ ‖x‖²` for every
`k` and `x`, `0 ≤ h < √2`. -/
theorem chain_norm_pow_sq_le {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < √2) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin 3)) : ‖opE (chainX h ^ k) x‖ ^ 2 ≤ chainKappa h * ‖x‖ ^ 2 := by
  rw [norm_opE_sq_eq_sq3, norm_sq_eq_sq3]
  exact sq3_chainX_pow_mulVec_le hh0 hh1 k _

/-! ### The orbit of the extreme eigenvector -/

/-- The eigenvector `(1, √2, -1)` of `Q` for its largest eigenvalue `1 + h/√2`. -/
noncomputable def vMax : Fin 3 → ℝ := ![1, √2, -1]

/-- The eigenvector `(1, -√2, -1)` of `Q` for its least eigenvalue `1 - h/√2`. -/
noncomputable def vMin : Fin 3 → ℝ := ![1, -√2, -1]

/-- `h/√2 = h √2/2`. -/
theorem div_sqrt_two_eq (h : ℝ) : h / √2 = h * √2 / 2 := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : √2 ≠ 0 := by positivity
  field_simp
  linear_combination (-h) * hs

/-- `v` is an eigenvector of `Q` for `1 + h/√2`. -/
theorem chainQ_mulVec_vMax (h : ℝ) : chainQ h *ᵥ vMax = (1 + h / √2) • vMax := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i
  fin_cases i <;>
    simp [chainQ, vMax, Matrix.mulVec, dotProduct, Fin.sum_univ_three, div_sqrt_two_eq] <;>
    first | ring1 | linear_combination (-h / 2) * hs

/-- `w` is an eigenvector of `Q` for `1 - h/√2`. -/
theorem chainQ_mulVec_vMin (h : ℝ) : chainQ h *ᵥ vMin = (1 - h / √2) • vMin := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i
  fin_cases i <;>
    simp [chainQ, vMin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, div_sqrt_two_eq] <;>
    first | ring1 | linear_combination (-h / 2) * hs

/-- One step on `v`: `X v = (1 - h²) v - h(√2 + h) w`. -/
theorem chainX_mulVec_vMax (h : ℝ) :
    chainX h *ᵥ vMax = (1 - h ^ 2) • vMax - (h * (√2 + h)) • vMin := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i
  fin_cases i <;> simp [chainX, vMax, vMin, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-h) * hs

/-- One step on `w`: `X w = h(√2 - h) v + (1 - h²) w`. -/
theorem chainX_mulVec_vMin (h : ℝ) :
    chainX h *ᵥ vMin = (h * (√2 - h)) • vMax + (1 - h ^ 2) • vMin := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i
  fin_cases i <;> simp [chainX, vMax, vMin, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-h) * hs

/-- The angle of the turn, `cos θ = 1 - h²`. -/
noncomputable def chainTheta (h : ℝ) : ℝ := Real.arccos (1 - h ^ 2)

/-- `ρ = h(√2 + h)/sin θ`. -/
noncomputable def chainRho (h : ℝ) : ℝ := h * (√2 + h) / Real.sin (chainTheta h)

section Angle

variable {h : ℝ} (hh0 : 0 < h) (hh1 : h < √2)
include hh0 hh1

theorem sq_lt_two_of_lt_sqrt : h ^ 2 < 2 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem cos_chainTheta : Real.cos (chainTheta h) = 1 - h ^ 2 := by
  have := sq_lt_two_of_lt_sqrt hh0 hh1
  exact Real.cos_arccos (by nlinarith) (by nlinarith)

theorem sin_chainTheta_sq : Real.sin (chainTheta h) ^ 2 = h ^ 2 * (2 - h ^ 2) := by
  rw [Real.sin_sq, cos_chainTheta hh0 hh1]
  ring

theorem sin_chainTheta_pos : 0 < Real.sin (chainTheta h) := by
  have h2 := sq_lt_two_of_lt_sqrt hh0 hh1
  rw [chainTheta, Real.sin_arccos]
  apply Real.sqrt_pos.2
  have : 0 < h ^ 2 * (2 - h ^ 2) := mul_pos (by positivity) (by linarith)
  nlinarith

/-- `ρ sin θ = h(√2 + h)`. -/
theorem chainRho_mul_sin : chainRho h * Real.sin (chainTheta h) = h * (√2 + h) := by
  rw [chainRho, div_mul_cancel₀ _ (sin_chainTheta_pos hh0 hh1).ne']

/-- `ρ h(√2 - h) = sin θ`. -/
theorem chainRho_mul_beta : chainRho h * (h * (√2 - h)) = Real.sin (chainTheta h) := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsin := sin_chainTheta_pos hh0 hh1
  have hsq := sin_chainTheta_sq hh0 hh1
  rw [chainRho]
  field_simp
  linear_combination -hsq + h ^ 2 * hs

/-- `ρ² = κ`. -/
theorem chainRho_sq : chainRho h ^ 2 = chainKappa h := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hsin := sin_chainTheta_pos hh0 hh1
  have hsq := sin_chainTheta_sq hh0 hh1
  have hne : √2 - h ≠ 0 := by linarith
  rw [chainRho, chainKappa, div_pow, hsq]
  have h2 : (2 : ℝ) - h ^ 2 = (√2 - h) * (√2 + h) := by linear_combination -hs
  rw [h2]
  have hh0' : h ≠ 0 := hh0.ne'
  have hp : √2 + h ≠ 0 := by linarith
  field_simp

/-- **The orbit of `v`:** `X^k v = cos(kθ) v - ρ sin(kθ) w`. -/
theorem chainX_pow_mulVec_vMax (k : ℕ) :
    chainX h ^ k *ᵥ vMax = Real.cos (k * chainTheta h) • vMax -
      (chainRho h * Real.sin (k * chainTheta h)) • vMin := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, chainX_mulVec_vMax, chainX_mulVec_vMin]
    have hc := cos_chainTheta hh0 hh1
    have hα := chainRho_mul_sin hh0 hh1
    have hβ := chainRho_mul_beta hh0 hh1
    have hcos : Real.cos ((k + 1 : ℕ) * chainTheta h) =
        Real.cos (k * chainTheta h) * (1 - h ^ 2) -
          Real.sin (k * chainTheta h) * Real.sin (chainTheta h) := by
      rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, hc]
    have hsin : Real.sin ((k + 1 : ℕ) * chainTheta h) =
        Real.sin (k * chainTheta h) * (1 - h ^ 2) +
          Real.cos (k * chainTheta h) * Real.sin (chainTheta h) := by
      rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add, hc]
    linear_combination (norm := module)
      (-hcos - Real.sin (k * chainTheta h) * hβ) • vMax +
        (chainRho h * hsin + Real.cos (k * chainTheta h) * hα) • vMin

/-- **The energy along the orbit of `v`:** `|X^k v|² = 4 (cos²(kθ) + κ sin²(kθ))`. -/
theorem sq3_chainX_pow_mulVec_vMax (k : ℕ) :
    sq3 (chainX h ^ k *ᵥ vMax) =
      4 * (Real.cos (k * chainTheta h) ^ 2 + chainKappa h * Real.sin (k * chainTheta h) ^ 2) := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [chainX_pow_mulVec_vMax hh0 hh1, ← chainRho_sq hh0 hh1]
  simp [sq3, vMax, vMin]
  linear_combination (Real.cos (k * chainTheta h) ^ 2 +
    chainRho h ^ 2 * Real.sin (k * chainTheta h) ^ 2 +
    2 * chainRho h * Real.cos (k * chainTheta h) * Real.sin (k * chainTheta h)) * hs

end Angle

/-! ### The irrational rotation -/

/-- **An irrational turn comes arbitrarily close to a quarter turn:** if `θ/π` is irrational,
then for every `ε > 0` some `k` has `cos²(kθ) < ε`. -/
theorem exists_cos_sq_lt {θ : ℝ} (hθ : Irrational (θ / π)) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, Real.cos (k * θ) ^ 2 < ε := by
  have hd : DenseRange (fun z : ℤ => z • (θ : AddCircle π)) :=
    AddCircle.denseRange_zsmul_coe_iff.2 hθ
  set δ := min 1 ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    have := min_le_left 1 ε
    linarith
  have hδε : δ ≤ ε / 2 := by
    have := min_le_right 1 ε
    linarith
  obtain ⟨z, hz⟩ := hd.exists_dist_lt ((π / 2 : ℝ) : AddCircle π) hδ0
  have e1 : z • (θ : AddCircle π) = (((z : ℝ) * θ : ℝ) : AddCircle π) := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  rw [e1, dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hz
  set m := round (π⁻¹ * (π / 2 - (z : ℝ) * θ)) with hm
  set e := π / 2 - (z : ℝ) * θ - (m : ℝ) * π with he
  have hcz : Real.cos ((z : ℝ) * θ) = Real.cos ((m : ℝ) * π) * Real.sin e := by
    have h1 : (z : ℝ) * θ = π / 2 - ((m : ℝ) * π + e) := by rw [he]; ring
    rw [h1, Real.cos_pi_div_two_sub, Real.sin_add, Real.sin_int_mul_pi, zero_mul, zero_add]
  have habs : |Real.cos ((z : ℝ) * θ)| < δ := by
    rw [hcz, abs_mul]
    calc |Real.cos ((m : ℝ) * π)| * |Real.sin e| ≤ 1 * |e| :=
          mul_le_mul (Real.abs_cos_le_one _) Real.abs_sin_le_abs (abs_nonneg _) zero_le_one
      _ < δ := by rw [one_mul]; exact hz
  refine ⟨z.natAbs, ?_⟩
  have hk : Real.cos ((z.natAbs : ℝ) * θ) = Real.cos ((z : ℝ) * θ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    rcases abs_choice (z : ℝ) with h | h <;> rw [h]
    rw [neg_mul, Real.cos_neg]
  rw [hk, ← sq_abs]
  have h0 := abs_nonneg (Real.cos ((z : ℝ) * θ))
  nlinarith

/-- **Irrationality of the turn from Niven's theorem:** for `0 < h < √2` with `h²` rational and
`h² ∉ {1/2, 1, 3/2}`, `arccos(1 - h²)/π` is irrational. -/
theorem irrational_arccos_div_pi {h : ℝ} (hh0 : 0 < h) (hh1 : h < √2)
    (hq : ∃ q : ℚ, h ^ 2 = q) (h1 : h ^ 2 ≠ 1 / 2) (h2 : h ^ 2 ≠ 1) (h3 : h ^ 2 ≠ 3 / 2) :
    Irrational (Real.arccos (1 - h ^ 2) / π) := by
  rintro ⟨r, hr⟩
  obtain ⟨q, hq⟩ := hq
  have hlt := sq_lt_two_of_lt_sqrt hh0 hh1
  have hcos : Real.cos (Real.arccos (1 - h ^ 2)) = 1 - h ^ 2 :=
    Real.cos_arccos (by nlinarith) (by nlinarith)
  have hθ : Real.arccos (1 - h ^ 2) = r * π := by
    rw [hr]
    field_simp
  have hn := niven ⟨r, hθ⟩ ⟨1 - q, by rw [hcos, hq]; push_cast; ring⟩
  rw [hcos] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  have hpos : 0 < h ^ 2 := by positivity
  rcases hn with h' | h' | h' | h' | h'
  · linarith
  · exact h3 (by linarith)
  · exact h2 (by linarith)
  · exact h1 (by linarith)
  · linarith

/-! ### The supremum -/

/-- **The bound is approached:** if `arccos(1 - h²)/π` is irrational, `0 < h < √2`, then for
every `ε > 0` there are `k` and a unit vector `x` with `‖X^k x‖² > κ - ε`. -/
theorem chain_exists_norm_pow_sq_gt {h : ℝ} (hh0 : 0 < h) (hh1 : h < √2)
    (hirr : Irrational (Real.arccos (1 - h ^ 2) / π)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (x : EuclideanSpace ℝ (Fin 3)), ‖x‖ = 1 ∧
      chainKappa h - ε < ‖opE (chainX h ^ k) x‖ ^ 2 := by
  have hκ : 0 < chainKappa h := by
    rw [← chainRho_sq hh0 hh1]
    have := sin_chainTheta_pos hh0 hh1
    have : 0 < chainRho h := by
      rw [chainRho]
      positivity
    positivity
  obtain ⟨k, hk⟩ := exists_cos_sq_lt hirr (div_pos hε hκ)
  replace hk : Real.cos (k * chainTheta h) ^ 2 < ε / chainKappa h := hk
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨k, WithLp.toLp 2 ((1 / 2 : ℝ) • vMax), ?_, ?_⟩
  · have h1 : ‖WithLp.toLp 2 ((1 / 2 : ℝ) • vMax)‖ ^ 2 = 1 := by
      rw [norm_sq_eq_sq3]
      simp [sq3, vMax]
      linear_combination (1 / 4 : ℝ) * hs
    have h2 := norm_nonneg (WithLp.toLp 2 ((1 / 2 : ℝ) • vMax) : EuclideanSpace ℝ (Fin 3))
    nlinarith
  · rw [norm_opE_sq_eq_sq3, WithLp.ofLp_toLp, Matrix.mulVec_smul]
    have e : sq3 ((1 / 2 : ℝ) • (chainX h ^ k *ᵥ vMax)) =
        (1 / 4) * sq3 (chainX h ^ k *ᵥ vMax) := by
      simp [sq3]
      ring
    rw [e, sq3_chainX_pow_mulVec_vMax hh0 hh1]
    have hsc := Real.sin_sq_add_cos_sq (k * chainTheta h)
    have h3 : chainKappa h * Real.cos (k * chainTheta h) ^ 2 < ε := by
      rw [lt_div_iff₀ hκ] at hk
      linarith
    have h4 := sq_nonneg (Real.cos (k * chainTheta h))
    nlinarith

/-- **The largest energy over a run is `κ`:** for `0 < h < √2` with `arccos(1 - h²)/π`
irrational, `⨆_k ‖X^k‖² = (1 + h/√2)/(1 - h/√2)`, the operator norm on Euclidean space. -/
theorem chain_iSup_norm_pow_sq {h : ℝ} (hh0 : 0 < h) (hh1 : h < √2)
    (hirr : Irrational (Real.arccos (1 - h ^ 2) / π)) :
    ⨆ k : ℕ, ‖opE (chainX h ^ k)‖ ^ 2 = chainKappa h := by
  have hκ : 0 ≤ chainKappa h := by
    rw [← chainRho_sq hh0 hh1]
    positivity
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun k => ?_) (fun w hw => ?_)
  · have hb : ‖opE (chainX h ^ k)‖ ≤ √(chainKappa h) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
      have h1 := chain_norm_pow_sq_le hh0.le hh1 k x
      have h2 : ‖opE (chainX h ^ k) x‖ ≤ √(chainKappa h * ‖x‖ ^ 2) :=
        Real.le_sqrt_of_sq_le h1
      rwa [Real.sqrt_mul hκ, Real.sqrt_sq (norm_nonneg x)] at h2
    calc ‖opE (chainX h ^ k)‖ ^ 2 ≤ √(chainKappa h) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = chainKappa h := Real.sq_sqrt hκ
  · obtain ⟨k, x, hx, hk⟩ := chain_exists_norm_pow_sq_gt hh0 hh1 hirr (sub_pos.2 hw)
    refine ⟨k, ?_⟩
    have h1 : ‖opE (chainX h ^ k) x‖ ≤ ‖opE (chainX h ^ k)‖ := by
      have := (opE (chainX h ^ k)).le_opNorm x
      rwa [hx, mul_one] at this
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith

/-- **The largest energy over a run for rational `h²`:** `⨆_k ‖X^k‖² = κ` if `0 < h < √2`, `h²`
is rational and `h² ∉ {1/2, 1, 3/2}`. -/
theorem chain_iSup_norm_pow_sq_of_rat {h : ℝ} (hh0 : 0 < h) (hh1 : h < √2)
    (hq : ∃ q : ℚ, h ^ 2 = q) (h1 : h ^ 2 ≠ 1 / 2) (h2 : h ^ 2 ≠ 1) (h3 : h ^ 2 ≠ 3 / 2) :
    ⨆ k : ℕ, ‖opE (chainX h ^ k)‖ ^ 2 = chainKappa h :=
  chain_iSup_norm_pow_sq hh0 hh1 (irrational_arccos_div_pi hh0 hh1 hq h1 h2 h3)

/-- **The value of the paper, `h = 0.1`:** `⨆_k ‖X^k‖² = (1 + 0.1/√2)/(1 - 0.1/√2)`. -/
theorem chain_iSup_norm_pow_sq_tenth :
    ⨆ k : ℕ, ‖opE (chainX (1 / 10) ^ k)‖ ^ 2 = (1 + 1 / 10 / √2) / (1 - 1 / 10 / √2) := by
  have hs : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact chain_iSup_norm_pow_sq_of_rat (by norm_num) (by linarith) ⟨1 / 100, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num)

end CoSimFoundations
