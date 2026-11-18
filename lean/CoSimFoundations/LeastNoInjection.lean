/-
The least one-step error without injection, on the chain of three stores (the paper, Section 5,
Example "the chain of three, by order of execution").

**Paper.** On the chain `A = [[-r, -ω, 0], [ω, 0, -ω], [0, ω, -r]]` (scalar stores `1, 2, 3`;
`1, 3` are not partners) only `P_13 = ½ ς_12 A_12 A_23` and `P_31 = ½ ς_32 A_32 A_21` of
`P = ½ A_ς A` are out of reach. A scheme that injects no energy to leading order has
`sym (P + Z) ⪯ 0`, and the least one-step error among these schemes is `H² g_σ`,
`g_σ = min {‖P + Z‖ : Z ∈ 𝒵, sym (P + Z) ⪯ 0}`: `g_σ = ω²` in the Jacobi order and with the middle
store first (`P_13 = P_31 = ∓½ω²`), `g_σ = ½ω²` from end to end (`P_31 = -P_13`), against
`e_σ = ½ω²` with injection allowed in all three.

**What is formalised.**
* **The bound for one pair, every scheme** (`two_mul_abs_sub_le_norm_of_form_le`,
  `Consistent.least_no_injection_le`): if `⟪x, M x⟫ ≤ ε ‖x‖²` and `M_ij = M_ji = p`, `i ≠ j`, then
  `‖M‖ ≥ 2 |p| - ε`. Hence, for a consistent scheme (any subsystems, any order) and two states
  `i`, `j` of subsystems that are not partners with `P_ij = P_ji = p`, and every bound `ι` of the
  injection (`-ι ‖v‖² ≤ ⟪v, Δ_R v⟫`, as in `AmountLead`):
    `‖X - U‖ ≥ 2 |p| H² - H ι - (K + 2 √(card κ) C₃) H³`,
  `K = diffLeadC b c ‖A‖`, `C₃ = reactionC a b c ‖A‖ H`: a scheme that injects at most
  `ι = O(H²)` has one-step error at least `2 |p| H² - O(H³)`. This is the scheme level.
* **The chain** (`chain3A`, `chain3Frame`, `chain3Jacobi`, `chain3Middle`, `chain3End`): the
  matrices
  `P_13`, `P_31` in the three orders (`chain3_halfStepTerm_02`, `chain3_halfStepTerm_20`), the reach
  for scalar stores (`chain3_mem_reach_iff`), and the least values at the level of the matrices
  `P + Z` over the reach (`chain3_least_jacobi`, `chain3_least_middle`, `chain3_least_end`):
    with injection allowed: `e_σ = ½ω²` (minimisers `chainSym`, `chainSkew`);
    without injection (`⟪x, (P + Z) x⟫ ≤ 0` for all `x`): `g_σ = ω²`, `ω²`, `½ω²`
    (minimisers `chainMin`, `chainMin`, `chainSkew`).
* **Attained by schemes** (`chain3_no_injection_attained`): the scheme `reachScheme` of the
  minimiser without injection has `‖X - U‖ ≤ H² g_σ + reachK σ β H³` and injection rate
  `ι = -λ_min (Δ_R) ≤ K' H²`, in each of the three orders.
-/
import CoSimFoundations.LeastSpread
import CoSimFoundations.ReachCompletionExamples

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-! ### One pair -/

/-- **One pair with a bound of the form** (with a margin). If `⟪x, M x⟫ ≤ ε ‖x‖²` for all `x`
and `M_ij = M_ji = p`, `i ≠ j`, then `2 |p| - ε ≤ ‖M‖`. -/
theorem two_mul_abs_sub_le_norm_of_form_le {M : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n}
    (hij : i ≠ j) {p ε : ℝ} (hpij : M i j = p) (hpji : M j i = p)
    (hle : ∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE M x⟫ ≤ ε * ‖x‖ ^ 2) :
    2 * |p| - ε ≤ ‖opE M‖ := by
  have form : ∀ t : ℝ, t ^ 2 = 1 →
      ⟪unitE i + t • unitE j, opE M (unitE i + t • unitE j)⟫ = M i i + 2 * t * p + M j j := by
    intro t ht
    rw [inner_opE_unitE_add, hpij, hpji, ht]
    ring
  have key : ∀ t : ℝ, t ^ 2 = 1 → |M i i + 2 * t * p + M j j| ≤ 2 * ‖opE M‖ := by
    intro t ht
    have h := abs_inner_opE_self_le M (unitE i + t • unitE j)
    rw [form t ht, norm_unitE_add_sq hij, ht] at h
    linarith
  have h1 := hle (unitE i + (1 : ℝ) • unitE j)
  have h2 := hle (unitE i + (-1 : ℝ) • unitE j)
  rw [form 1 (by norm_num), norm_unitE_add_sq hij] at h1
  rw [form (-1) (by norm_num), norm_unitE_add_sq hij] at h2
  have k1 := key 1 (by norm_num)
  have k2 := key (-1) (by norm_num)
  have a1 := neg_abs_le (M i i + 2 * 1 * p + M j j)
  have a2 := neg_abs_le (M i i + 2 * (-1) * p + M j j)
  rcases le_total 0 p with hp | hp
  · rw [abs_of_nonneg hp]
    nlinarith
  · rw [abs_of_nonpos hp]
    nlinarith

/-- An entry is at most the spectral norm: `|M i j| ≤ ‖M‖`. -/
theorem abs_apply_le_norm_opE (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |M i j| ≤ ‖opE M‖ := by
  have h := abs_inner_opE_le M (unitE i) (unitE j)
  rwa [inner_unitE_opE, norm_unitE, norm_unitE, mul_one, mul_one] at h

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

/-- **The least one-step error without injection, every scheme** (every family with
`ι ≤ C H²` has `α ≥ H² (g_σ - O(H))`, for one pair). For a consistent scheme whose coupling and
coefficients act through the outputs, `0 < H`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, two states `i`, `j` of
different subsystems that are not partners (in both directions) with `P_ij = P_ji = p`,
`P = ½ A_ς A`, and every bound `ι` of the injection, `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫`:
`‖X - U‖ ≥ 2 |p| H² - H ι - (K + 2 √(card κ) C₃) H³`. -/
theorem Consistent.least_no_injection_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) {i j : Fin n} (hij : S.sub i ≠ S.sub j)
    (hnp : ¬ S.partner (S.sub i) (S.sub j)) (hnp' : ¬ S.partner (S.sub j) (S.sub i)) {p : ℝ}
    (hpij : S.halfStepTerm A i j = p) (hpji : S.halfStepTerm A j i = p) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    2 * |p| * H ^ 2 - H * ι - (diffLeadC b c ‖opE A‖ +
        2 * (Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H)) * H ^ 3 ≤
      ‖opE (S.X - U)‖ := by
  set K := diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H
  set Z := S.reachLead A H
  have hZ : Z ∈ S.reach Θ := h.reachLead_mem hΘ hAΘ hGΘ
  have hE : ‖opE (difference A H S.X - H • (S.halfStepTerm A + Z))‖ ≤ K * H ^ 2 := by
    have h1 := h.norm_difference_sub_halfStepLead_le hH hbH hAH
    rwa [S.halfStepLead_eq A hH.ne', smul_smul,
      show H⁻¹ * H ^ 2 = H by field_simp] at h1
  have hij' : i ≠ j := fun e => hij (congrArg S.sub e)
  -- the entries of `P + Z`
  have hm1 : (S.halfStepTerm A + Z) i j = p := by rw [Matrix.add_apply, hpij, hZ.1 i j hij hnp,
    add_zero]
  have hm2 : (S.halfStepTerm A + Z) j i = p := by rw [Matrix.add_apply, hpji,
    hZ.1 j i (Ne.symm hij) hnp', add_zero]
  -- the form of `P + Z`
  have hform : ∀ x : EuclideanSpace ℝ (Fin n),
      ⟪x, opE (S.halfStepTerm A + Z) x⟫ ≤ (ι / H + K * H) * ‖x‖ ^ 2 := by
    intro x
    have h1 := hlo x
    rw [inner_numDissipation_self] at h1
    have h2 := abs_le.1 (abs_inner_opE_self_le
      (difference A H S.X - H • (S.halfStepTerm A + Z)) x)
    have h3 : ⟪x, opE (difference A H S.X - H • (S.halfStepTerm A + Z)) x⟫ =
        ⟪x, opE (modifiedSystem H S.X - A) x⟫ - H * ⟪x, opE (S.halfStepTerm A + Z) x⟫ := by
      rw [inner_opE_sub, inner_opE_smul]
      rfl
    have h4 := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖x‖)
    have h5 : H * ⟪x, opE (S.halfStepTerm A + Z) x⟫ ≤ (ι + K * H ^ 2) * ‖x‖ ^ 2 := by
      nlinarith [h2.1]
    rw [show (ι / H + K * H) * ‖x‖ ^ 2 = H⁻¹ * ((ι + K * H ^ 2) * ‖x‖ ^ 2) by
      field_simp]
    rw [le_inv_mul_iff₀ hH]
    exact h5
  have h6 := two_mul_abs_sub_le_norm_of_form_le hij' hm1 hm2 hform
  -- from `P + Z` to `X - U`
  have h7 := h.norm_sub_reachLead_le hH.ne'
  have h8 := norm_sub_le (opE (S.X - U)) (opE (S.X - U - H ^ 2 • (S.halfStepTerm A + Z)))
  rw [← opE_sub, sub_sub_cancel, opE_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at h8
  have h9 := mul_le_mul_of_nonneg_left h6 (sq_nonneg H)
  have e : H ^ 2 * (2 * |p| - (ι / H + K * H)) = 2 * |p| * H ^ 2 - H * ι - K * H ^ 3 := by
    field_simp
    ring
  rw [e] at h9
  linarith

/-! ### A frame and the chain of three stores -/

variable (S)

/-- **A frame**: the scheme with `F = 1`, `N = M = 0`, `X = 1` on given subsystems, partners and
stages. The reach and the half-step term depend on the frame only. -/
def frame (sub : Fin n → κ) (partner : κ → κ → Prop) (stage : κ → ℕ) : HeldScheme n κ where
  sub := sub
  partner := partner
  stage := stage
  F := 1
  N := 0
  M := 0
  X := 1
  hF := fun _ _ h => Matrix.one_apply_ne fun e => h (congrArg sub e)
  hN := fun _ _ _ => rfl
  hM := fun _ _ _ => rfl
  hX := by simp

end HeldScheme

/-- The chain of three stores, `A = [[-r, -ω, 0], [ω, 0, -ω], [0, ω, -r]]` (the paper, eq.
`eq:chain3` with the store dissipation `r` and the coupling rate `ω`). -/
def chain3A (r ω : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-r, -ω, 0; ω, 0, -ω; 0, ω, -r]

/-- The partners of the chain: neighbouring stores. -/
def chain3Partner (i j : Fin 3) : Prop := (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i

/-- The chain of three scalar stores as a frame, with the stages `st`. -/
def chain3Frame (st : Fin 3 → ℕ) : HeldScheme 3 (Fin 3) :=
  HeldScheme.frame id chain3Partner st

/-- The Jacobi order: all stores at one stage. -/
def chain3Jacobi : Fin 3 → ℕ := fun _ => 0

/-- The middle store first. -/
def chain3Middle : Fin 3 → ℕ := ![1, 0, 1]

/-- From end to end: store `i` at stage `i`. -/
def chain3End : Fin 3 → ℕ := fun i => i

/-- The chain has no entries between the stores that are not partners. -/
theorem chain3A_pattern (st : Fin 3 → ℕ) (r ω : ℝ) :
    ∀ p q, (chain3Frame st).sub p ≠ (chain3Frame st).sub q →
      ¬ (chain3Frame st).partner ((chain3Frame st).sub p) ((chain3Frame st).sub q) →
        chain3A r ω p q = 0 := by
  intro p q hne hnp
  simp only [chain3Frame, HeldScheme.frame, id, chain3Partner] at hne hnp
  fin_cases p <;> fin_cases q <;> simp_all [chain3A]

/-- **The reach on the chain** (scalar stores, `Θ = 0`): the matrices with zero entries `(1, 3)`
and `(3, 1)` (indices `0`, `2`). -/
theorem chain3_mem_reach_iff (st : Fin 3 → ℕ) (Z : Matrix (Fin 3) (Fin 3) ℝ) :
    Z ∈ (chain3Frame st).reach 0 ↔ Z 0 2 = 0 ∧ Z 2 0 = 0 := by
  constructor
  · rintro ⟨h, -⟩
    refine ⟨h 0 2 (by show (0 : Fin 3) ≠ 2; decide) ?_,
      h 2 0 (by show (2 : Fin 3) ≠ 0; decide) ?_⟩ <;>
      simp [chain3Frame, HeldScheme.frame, chain3Partner]
  · rintro ⟨h1, h2⟩
    refine ⟨fun p q hne hnp => ?_, by rw [Matrix.mul_zero]⟩
    simp only [chain3Frame, HeldScheme.frame, id, chain3Partner] at hne hnp
    fin_cases p <;> fin_cases q <;> simp_all

/-- The entry `(1, 3)` of `P = ½ A_ς A` on the chain: `½ ς_12 ω²`. -/
theorem chain3_halfStepTerm_02 (st : Fin 3 → ℕ) (r ω : ℝ) :
    (chain3Frame st).halfStepTerm (chain3A r ω) 0 2 = (chain3Frame st).sg 0 1 * ω ^ 2 / 2 := by
  simp [HeldScheme.halfStepTerm, HeldScheme.signedCoupling_apply, Matrix.mul_apply,
    Fin.sum_univ_three, chain3A, chain3Frame, HeldScheme.frame]
  ring

/-- The entry `(3, 1)` of `P = ½ A_ς A` on the chain: `½ ς_32 ω²`. -/
theorem chain3_halfStepTerm_20 (st : Fin 3 → ℕ) (r ω : ℝ) :
    (chain3Frame st).halfStepTerm (chain3A r ω) 2 0 = (chain3Frame st).sg 2 1 * ω ^ 2 / 2 := by
  simp [HeldScheme.halfStepTerm, HeldScheme.signedCoupling_apply, Matrix.mul_apply,
    Fin.sum_univ_three, chain3A, chain3Frame, HeldScheme.frame]
  ring

theorem chain3_sg_jacobi (s k : Fin 3) : (chain3Frame chain3Jacobi).sg s k = -1 := by
  simp [HeldScheme.sg, chain3Frame, HeldScheme.frame, chain3Jacobi]

theorem chain3_sg_middle_01 : (chain3Frame chain3Middle).sg 0 1 = 1 := by
  simp [HeldScheme.sg, chain3Frame, HeldScheme.frame, chain3Middle]

theorem chain3_sg_middle_21 : (chain3Frame chain3Middle).sg 2 1 = 1 := by
  simp [HeldScheme.sg, chain3Frame, HeldScheme.frame, chain3Middle]

theorem chain3_sg_end_01 : (chain3Frame chain3End).sg 0 1 = -1 := by
  simp [HeldScheme.sg, chain3Frame, HeldScheme.frame, chain3End]

theorem chain3_sg_end_21 : (chain3Frame chain3End).sg 2 1 = 1 := by
  simp [HeldScheme.sg, chain3Frame, HeldScheme.frame, chain3End]

/-! ### The least values on the chain -/

/-- The symmetric matrix `p (e_i e_jᵀ + e_j e_iᵀ)`. -/
noncomputable def chainSym (i j : Fin n) (p : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  p • (single i j 1 + single j i 1)

theorem chainSym_apply {i j : Fin n} (hij : i ≠ j) (p : ℝ) :
    chainSym i j p i j = p ∧ chainSym i j p j i = p := by
  constructor <;> simp [chainSym, hij, Ne.symm hij]

/-- `‖p (e_i e_jᵀ + e_j e_iᵀ)‖ = |p|` for `i ≠ j`. -/
theorem norm_chainSym {i j : Fin n} (hij : i ≠ j) (p : ℝ) : ‖opE (chainSym i j p)‖ = |p| := by
  refine le_antisymm (norm_opE_le_of_abs_inner_le (abs_nonneg p) fun x y => ?_) ?_
  · rw [chainSym, inner_opE_smul, inner_opE_add, inner_opE_single, inner_opE_single, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg p)
    have hx := sq_add_sq_le_norm_sq hij x
    have hy := sq_add_sq_le_norm_sq hij y
    have hsq : (x i * y j + x j * y i) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
      have hl : (x i * y j + x j * y i) ^ 2 ≤ (x i ^ 2 + x j ^ 2) * (y i ^ 2 + y j ^ 2) := by
        nlinarith [sq_nonneg (x i * y i - x j * y j)]
      rw [mul_pow]
      exact hl.trans (mul_le_mul hx hy (by positivity) (sq_nonneg _))
    exact abs_le_of_sq_le_sq hsq (by positivity)
  · have h := abs_apply_le_norm_opE (chainSym i j p) i j
    rwa [(chainSym_apply hij p).1] at h

/-- The least norm when the two unreachable entries are `p` and `q` with `|q| = |p|`, `i ≠ j`,
and every other entry is free: `|p|`, attained by `p e_i e_jᵀ + q e_j e_iᵀ`. -/
theorem isLeast_norm_two_entries {i j : Fin n} (hij : i ≠ j) (P : Matrix (Fin n) (Fin n) ℝ)
    (𝓡 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hR : ∀ Z, Z ∈ 𝓡 ↔ Z i j = 0 ∧ Z j i = 0) {p : ℝ} (hp : P i j = p)
    (hq : P j i = p ∨ P j i = -p) :
    IsLeast {r | ∃ Z ∈ 𝓡, r = ‖opE (P + Z)‖} |p| := by
  refine ⟨?_, ?_⟩
  · rcases hq with hq | hq
    · refine ⟨chainSym i j p - P, (hR _).2 ⟨?_, ?_⟩, ?_⟩
      · rw [Matrix.sub_apply, (chainSym_apply hij p).1, hp, sub_self]
      · rw [Matrix.sub_apply, (chainSym_apply hij p).2, hq, sub_self]
      · rw [add_sub_cancel, norm_chainSym hij]
    · refine ⟨chainSkew i j p - P, (hR _).2 ⟨?_, ?_⟩, ?_⟩
      · rw [Matrix.sub_apply, (chainSkew_apply hij p).1, hp, sub_self]
      · rw [Matrix.sub_apply, (chainSkew_apply hij p).2, hq, sub_self]
      · rw [add_sub_cancel, norm_chainSkew hij]
  · rintro _ ⟨Z, hZ, rfl⟩
    have h := abs_apply_le_norm_opE (P + Z) i j
    rwa [Matrix.add_apply, ((hR Z).1 hZ).1, add_zero, hp] at h

/-- **Without injection, equal entries** (Jacobi and middle store first): if the two
unreachable entries are both `p` and every other entry is free, the least norm of `P + Z` with
`⟪x, (P + Z) x⟫ ≤ 0` for all `x` is `2 |p|`, attained by `chainMin`. -/
theorem isLeast_no_injection_equal {i j : Fin n} (hij : i ≠ j) (P : Matrix (Fin n) (Fin n) ℝ)
    (𝓡 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hR : ∀ Z, Z ∈ 𝓡 ↔ Z i j = 0 ∧ Z j i = 0) {p : ℝ} (hp : P i j = p) (hq : P j i = p) :
    IsLeast {r | ∃ Z ∈ 𝓡, (∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE (P + Z) x⟫ ≤ 0) ∧
      r = ‖opE (P + Z)‖} (2 * |p|) := by
  obtain ⟨h1, h2, h3⟩ := chainMin_form_nonpos hij p
  refine ⟨⟨chainMin i j p - P, (hR _).2 ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [Matrix.sub_apply, h1, hp, sub_self]
  · rw [Matrix.sub_apply, h2, hq, sub_self]
  · rw [add_sub_cancel]
    exact h3
  · rw [add_sub_cancel, norm_chainMin hij]
  · rintro _ ⟨Z, hZ, hneg, rfl⟩
    refine two_mul_abs_le_norm_of_form_nonpos hij ?_ ?_ hneg
    · rw [Matrix.add_apply, ((hR Z).1 hZ).1, add_zero, hp]
    · rw [Matrix.add_apply, ((hR Z).1 hZ).2, add_zero, hq]

/-- **Without injection, opposite entries** (from end to end): if the two unreachable entries
are `p` and `-p`, the least norm of `P + Z` with `⟪x, (P + Z) x⟫ ≤ 0` is `|p|`, attained by the
skew matrix `chainSkew` (form `0`). -/
theorem isLeast_no_injection_opposite {i j : Fin n} (hij : i ≠ j) (P : Matrix (Fin n) (Fin n) ℝ)
    (𝓡 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hR : ∀ Z, Z ∈ 𝓡 ↔ Z i j = 0 ∧ Z j i = 0) {p : ℝ} (hp : P i j = p) (hq : P j i = -p) :
    IsLeast {r | ∃ Z ∈ 𝓡, (∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE (P + Z) x⟫ ≤ 0) ∧
      r = ‖opE (P + Z)‖} |p| := by
  obtain ⟨h1, h2⟩ := chainSkew_apply hij p
  refine ⟨⟨chainSkew i j p - P, (hR _).2 ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [Matrix.sub_apply, h1, hp, sub_self]
  · rw [Matrix.sub_apply, h2, hq, sub_self]
  · intro x
    rw [add_sub_cancel, inner_chainSkew_self]
  · rw [add_sub_cancel, norm_chainSkew hij]
  · rintro _ ⟨Z, hZ, -, rfl⟩
    have h := abs_apply_le_norm_opE (P + Z) i j
    rwa [Matrix.add_apply, ((hR Z).1 hZ).1, add_zero, hp] at h

/-- **The chain, Jacobi order**: with injection allowed the least `‖P + Z‖` is `½ ω²`;
without injection it is `ω²`. -/
theorem chain3_least_jacobi (r ω : ℝ) :
    IsLeast {e | ∃ Z ∈ (chain3Frame chain3Jacobi).reach 0,
      e = ‖opE ((chain3Frame chain3Jacobi).halfStepTerm (chain3A r ω) + Z)‖} (ω ^ 2 / 2) ∧
    IsLeast {g | ∃ Z ∈ (chain3Frame chain3Jacobi).reach 0,
      (∀ x : EuclideanSpace ℝ (Fin 3),
        ⟪x, opE ((chain3Frame chain3Jacobi).halfStepTerm (chain3A r ω) + Z) x⟫ ≤ 0) ∧
      g = ‖opE ((chain3Frame chain3Jacobi).halfStepTerm (chain3A r ω) + Z)‖} (ω ^ 2) := by
  have hp : (chain3Frame chain3Jacobi).halfStepTerm (chain3A r ω) 0 2 = -(ω ^ 2 / 2) := by
    rw [chain3_halfStepTerm_02, chain3_sg_jacobi]
    ring
  have hq : (chain3Frame chain3Jacobi).halfStepTerm (chain3A r ω) 2 0 = -(ω ^ 2 / 2) := by
    rw [chain3_halfStepTerm_20, chain3_sg_jacobi]
    ring
  have habs : |-(ω ^ 2 / 2)| = ω ^ 2 / 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
  constructor
  · have h := isLeast_norm_two_entries (by decide) _ _ (chain3_mem_reach_iff chain3Jacobi) hp
      (Or.inl hq)
    rwa [habs] at h
  · have h := isLeast_no_injection_equal (by decide) _ _ (chain3_mem_reach_iff chain3Jacobi) hp hq
    rwa [habs, show 2 * (ω ^ 2 / 2) = ω ^ 2 by ring] at h

/-- **The chain, middle store first**: with injection allowed the least `‖P + Z‖` is `½ ω²`;
without injection it is `ω²`. -/
theorem chain3_least_middle (r ω : ℝ) :
    IsLeast {e | ∃ Z ∈ (chain3Frame chain3Middle).reach 0,
      e = ‖opE ((chain3Frame chain3Middle).halfStepTerm (chain3A r ω) + Z)‖} (ω ^ 2 / 2) ∧
    IsLeast {g | ∃ Z ∈ (chain3Frame chain3Middle).reach 0,
      (∀ x : EuclideanSpace ℝ (Fin 3),
        ⟪x, opE ((chain3Frame chain3Middle).halfStepTerm (chain3A r ω) + Z) x⟫ ≤ 0) ∧
      g = ‖opE ((chain3Frame chain3Middle).halfStepTerm (chain3A r ω) + Z)‖} (ω ^ 2) := by
  have hp : (chain3Frame chain3Middle).halfStepTerm (chain3A r ω) 0 2 = ω ^ 2 / 2 := by
    rw [chain3_halfStepTerm_02, chain3_sg_middle_01]
    ring
  have hq : (chain3Frame chain3Middle).halfStepTerm (chain3A r ω) 2 0 = ω ^ 2 / 2 := by
    rw [chain3_halfStepTerm_20, chain3_sg_middle_21]
    ring
  have habs : |ω ^ 2 / 2| = ω ^ 2 / 2 := abs_of_nonneg (by positivity)
  constructor
  · have h := isLeast_norm_two_entries (by decide) _ _ (chain3_mem_reach_iff chain3Middle) hp
      (Or.inl hq)
    rwa [habs] at h
  · have h := isLeast_no_injection_equal (by decide) _ _ (chain3_mem_reach_iff chain3Middle) hp hq
    rwa [habs, show 2 * (ω ^ 2 / 2) = ω ^ 2 by ring] at h

/-- **The chain, from end to end**: with and without injection the least `‖P + Z‖` is
`½ ω²`. -/
theorem chain3_least_end (r ω : ℝ) :
    IsLeast {e | ∃ Z ∈ (chain3Frame chain3End).reach 0,
      e = ‖opE ((chain3Frame chain3End).halfStepTerm (chain3A r ω) + Z)‖} (ω ^ 2 / 2) ∧
    IsLeast {g | ∃ Z ∈ (chain3Frame chain3End).reach 0,
      (∀ x : EuclideanSpace ℝ (Fin 3),
        ⟪x, opE ((chain3Frame chain3End).halfStepTerm (chain3A r ω) + Z) x⟫ ≤ 0) ∧
      g = ‖opE ((chain3Frame chain3End).halfStepTerm (chain3A r ω) + Z)‖} (ω ^ 2 / 2) := by
  have hp : (chain3Frame chain3End).halfStepTerm (chain3A r ω) 0 2 = -(ω ^ 2 / 2) := by
    rw [chain3_halfStepTerm_02, chain3_sg_end_01]
    ring
  have hq : (chain3Frame chain3End).halfStepTerm (chain3A r ω) 2 0 = -(-(ω ^ 2 / 2)) := by
    rw [chain3_halfStepTerm_20, chain3_sg_end_21]
    ring
  have habs : |-(ω ^ 2 / 2)| = ω ^ 2 / 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
  constructor
  · have h := isLeast_norm_two_entries (by decide) _ _ (chain3_mem_reach_iff chain3End) hp
      (Or.inr hq)
    rwa [habs] at h
  · have h := isLeast_no_injection_opposite (by decide) _ _ (chain3_mem_reach_iff chain3End) hp hq
    rwa [habs] at h

/-! ### Attained by schemes -/

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

/-- **A minimiser without injection is attained by a scheme** (attainment). For a `Z` in the
pattern of the reach with `⟪x, (P + Z) x⟫ ≤ 0` for all `x`, at least one state, `0 < H`,
`‖A‖ ≤ β`, `‖Z‖ ≤ β²`, `H β ≤ 1/27`, `σ H β ≤ 1/6`, the scheme that reaches `Z` has
`‖X - U‖ ≤ H² ‖P + Z‖ + reachK σ β H³` and injection rate `-λ_min (Δ_R) ≤ K' H²`,
`K' = diffLeadC (9β) ((6 + 27σ) β²) ‖A‖ + reachK σ β`. -/
theorem no_injection_attained [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → Z p q = 0)
    (hneg : ∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE (S.halfStepTerm A + Z) x⟫ ≤ 0)
    (hn : 0 < n) {H β : ℝ} (hH : 0 < H) (hAβ : ‖opE A‖ ≤ β) (hZβ : ‖opE Z‖ ≤ β ^ 2)
    (hβH : H * β ≤ 1 / 27) (hσ : Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6) :
    ‖opE ((S.reachScheme A hA Z hZ H).X - NormedSpace.exp (H • A))‖ ≤
        H ^ 2 * ‖opE (S.halfStepTerm A + Z)‖ + reachK (Real.sqrt (Fintype.card κ)) β * H ^ 3 ∧
      -lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ H).X)) ≤
        (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
          reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 := by
  have hβH4 : H * β ≤ 1 / 4 := by linarith
  have h1 := norm_reachScheme_sub_le (hA := hA) (hZ := hZ) hH.le hAβ hZβ hβH4 hσ
  have h2 := norm_sub_norm_le (opE ((S.reachScheme A hA Z hZ H).X - NormedSpace.exp (H • A)))
    (opE ((S.reachScheme A hA Z hZ H).X - NormedSpace.exp (H • A) -
      H ^ 2 • (S.halfStepTerm A + Z)))
  rw [← opE_sub, sub_sub_cancel, opE_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at h2
  refine ⟨by linarith, ?_⟩
  obtain ⟨-, h3⟩ := reachScheme_extremes (hA := hA) (hZ := hZ) hn hH hAβ hZβ hβH hσ
  have := nonempty_sphere hn
  have h4 : lamMax (sym (S.halfStepTerm A + Z)) ≤ 0 := lamMax_le_of fun x => by
    have e : ⟪x, opE (sym (S.halfStepTerm A + Z)) x⟫ = ⟪x, opE (S.halfStepTerm A + Z) x⟫ := by
      rw [inner_sym]
      ring
    rw [e, zero_mul]
    exact hneg x
  have h5 := mul_le_mul_of_nonneg_left h4 hH.le
  have h6 := (abs_le.1 h3).1
  linarith

end HeldScheme

/-- **The chain without injection, attained by schemes**: in the Jacobi order and with the
middle store first, the scheme that reaches `chainMin 0 2 p - P` (`p = P_13`), and from end to end
the scheme that reaches `chainSkew 0 2 p - P`, inject no energy to leading order and have the
one-step error `H² g_σ + O(H³)`, `g_σ = ω²`, `ω²`, `½ ω²`. Stated for any stages with
`P_31 = P_13` (`chainMin`) and `P_31 = -P_13` (`chainSkew`); the three orders give these by
`chain3_halfStepTerm_02`, `chain3_halfStepTerm_20` and the signs `chain3_sg_jacobi`,
`chain3_sg_middle_01`, ... -/
theorem chain3_no_injection_attained (st : Fin 3 → ℕ) (r ω : ℝ)
    (hsym : (chain3Frame st).sg 2 1 = (chain3Frame st).sg 0 1 ∨
      (chain3Frame st).sg 2 1 = -(chain3Frame st).sg 0 1) :
    ∃ Z, ∃ hZ : Z ∈ (chain3Frame st).reach 0,
      (∀ x : EuclideanSpace ℝ (Fin 3),
        ⟪x, opE ((chain3Frame st).halfStepTerm (chain3A r ω) + Z) x⟫ ≤ 0) ∧
      ‖opE ((chain3Frame st).halfStepTerm (chain3A r ω) + Z)‖ =
        (if (chain3Frame st).sg 2 1 = (chain3Frame st).sg 0 1 then ω ^ 2 else ω ^ 2 / 2) ∧
      ∀ {H β : ℝ}, 0 < H → ‖opE (chain3A r ω)‖ ≤ β → ‖opE Z‖ ≤ β ^ 2 → H * β ≤ 1 / 27 →
        Real.sqrt 3 * (H * β) ≤ 1 / 6 →
        ‖opE (((chain3Frame st).reachScheme (chain3A r ω) (chain3A_pattern st r ω) Z hZ.1 H).X -
            NormedSpace.exp (H • chain3A r ω))‖ ≤
          H ^ 2 * (if (chain3Frame st).sg 2 1 = (chain3Frame st).sg 0 1 then ω ^ 2 else ω ^ 2 / 2) +
            HeldScheme.reachK (Real.sqrt 3) β * H ^ 3 ∧
        -lamMin (numDissipation (chain3A r ω) (modifiedSystem H
            ((chain3Frame st).reachScheme (chain3A r ω) (chain3A_pattern st r ω) Z hZ.1 H).X)) ≤
          (diffLeadC (9 * β) ((6 + 27 * Real.sqrt 3) * β ^ 2) ‖opE (chain3A r ω)‖ +
            HeldScheme.reachK (Real.sqrt 3) β) * H ^ 2 := by
  have hq20 := chain3_halfStepTerm_20 st r ω
  set P := (chain3Frame st).halfStepTerm (chain3A r ω)
  set p := (chain3Frame st).sg 0 1 * ω ^ 2 / 2
  have hp : P 0 2 = p := chain3_halfStepTerm_02 st r ω
  have hsg : |(chain3Frame st).sg 0 1| = 1 := (chain3Frame st).abs_sg 0 1
  have hpabs : |p| = ω ^ 2 / 2 := by
    rw [abs_div, abs_mul, hsg, one_mul, abs_of_nonneg (sq_nonneg ω), abs_two]
  have hcard : Real.sqrt (Fintype.card (Fin 3)) = Real.sqrt 3 := by simp
  -- the minimiser
  obtain ⟨M, hM02, hM20, hMneg, hMnorm⟩ : ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M 0 2 = p ∧
      M 2 0 = P 2 0 ∧ (∀ x : EuclideanSpace ℝ (Fin 3), ⟪x, opE M x⟫ ≤ 0) ∧
      ‖opE M‖ =
        (if (chain3Frame st).sg 2 1 = (chain3Frame st).sg 0 1 then ω ^ 2 else ω ^ 2 / 2) := by
    by_cases h : (chain3Frame st).sg 2 1 = (chain3Frame st).sg 0 1
    · have hq : P 2 0 = p := by rw [hq20, h]
      obtain ⟨h1, h2, h3⟩ := chainMin_form_nonpos (by decide : (0 : Fin 3) ≠ 2) p
      refine ⟨chainMin 0 2 p, h1, by rw [h2, hq], h3, ?_⟩
      rw [norm_chainMin (by decide), hpabs, ite_eq_left h]
      ring
    · have h' := hsym.resolve_left h
      have hq : P 2 0 = -p := by rw [hq20, h']; ring
      obtain ⟨h1, h2⟩ := chainSkew_apply (by decide : (0 : Fin 3) ≠ 2) p
      refine ⟨chainSkew 0 2 p, h1, by rw [h2, hq], fun x => ?_, ?_⟩
      · rw [inner_chainSkew_self]
      · rw [norm_chainSkew (by decide), hpabs, ite_eq_right h]
  have hZ : M - P ∈ (chain3Frame st).reach 0 := (chain3_mem_reach_iff st _).2
    ⟨by rw [Matrix.sub_apply, hM02, hp, sub_self], by rw [Matrix.sub_apply, hM20, sub_self]⟩
  refine ⟨M - P, hZ, by rw [add_sub_cancel]; exact hMneg, by rw [add_sub_cancel]; exact hMnorm,
    fun {H β} hH hAβ hZβ hβH hσ => ?_⟩
  have hσ' : Real.sqrt (Fintype.card (Fin 3)) * (H * β) ≤ 1 / 6 := by rw [hcard]; exact hσ
  have h := (chain3Frame st).no_injection_attained (chain3A_pattern st r ω) hZ.1
    (by rw [add_sub_cancel]; exact hMneg) (by norm_num) hH hAβ hZβ hβH hσ'
  rw [add_sub_cancel, hMnorm, hcard] at h
  exact h

end CoSimFoundations
