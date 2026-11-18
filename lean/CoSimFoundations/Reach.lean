/-
What the coefficients reach (the paper, Lemma "the reach of the coefficients", `lem:reach`, eq.
`eq:reach`).

**Paper.** `𝒵` is the set of the matrices `Y + W C` with `Y` block diagonal and `W_ij = 0` unless
`j ∈ 𝒫(i)`. Every scheme has `X - U = H² (½ A_ς A + Z) + O(H³)` with a bounded `Z ∈ 𝒵`, and for
every `Z = Y + W C ∈ 𝒵` the coefficients `F_i = e^{H A_i} + H² Y_i`, `G_ij = G°_ij + H² W_ij` form a
scheme with this expansion.

**Representation.** A scheme is a `HeldScheme` (states `Fin n`, grouped into subsystems by `sub`);
it has no output map. The block `W_ij C_j` "ends with the output map of `j`": it vanishes on the
kernel of `C_j`. With `Θ` the matrix of the projections `Θ_j` onto the kernels of the `C_j` (block
diagonal), this is `W_ij C_j Θ_j = 0`. So the reach is (`reach Θ`)
  `{Z | Z p q = 0 between different subsystems that are not partners, and A_c(Z) Θ = 0}`,
where `A_c(Z) = coupling Z` is the part of `Z` between different subsystems. The partner blocks
need not be split into `W` and `C`: a block `M` with `M Θ_j = 0` is `(M C_j⁺) C_j`. For `Θ = 0`
(every state is an output, as for scalar stores) the reach is the block diagonal plus the partner
blocks. The hypotheses that the coupling and the coefficients of the samples act through the
outputs are `coupling A * Θ = 0` (`A_ij = B_i L_ij C_j`) and `(M + N) * Θ = 0` (`M + N = G C`).

* **Every consistent scheme** (`Consistent.reachLead_mem`, `Consistent.norm_sub_reachLead_le`,
  `Consistent.norm_reachLead_le`, `Consistent.exists_reach`): `Z_H = reachLead`, the two brackets
  of the half-step normal form of `HalfStep` divided by `H²`, lies in `reach Θ`, and
    `‖X - U - H² (½ A_ς A + Z_H)‖ ≤ √(card κ) C₃ H³`,   `‖Z_H‖ ≤ c + ‖½ A_ς A‖ + √(card κ) C₃ H`,
  `C₃ = reactionC a b c ‖A‖ H`.
* **Every element of the reach is reached** (`reachScheme`, `reachScheme_consistent`,
  `norm_reachScheme_sub_le`, `reachScheme_samples_mul_eq_zero`, `exists_reachScheme`): for a
  matrix `Z` with the pattern of the reach, the scheme with `F = e^{H A₀} + H² Y`, `Y` the block
  diagonal of `Z`, and the coefficients of the zero-order hold plus `H²` times the part of `Z`
  between partners, split into new and old samples by the order of execution. For `‖A‖ ≤ β`,
  `‖Z‖ ≤ β²`, `0 ≤ H`, `H β ≤ 1/4` and `σ H β ≤ 1/6`, `σ = √(card κ)`, it is consistent with
    `‖N‖ ≤ 3σβ H`,  `‖X - 1‖ ≤ 9β H`,  `‖X - e^{HA}‖ ≤ (6 + 27σ) β² H²`,
  and `‖X - e^{HA} - H² (½ A_ς A + Z)‖ ≤ (1 + 7σ + 74σ² + 81σ³) β³ H³` (`reachK`). If `Z ∈ reach Θ`
  and `coupling A * Θ = 0`, its coefficients of the samples act through the outputs.

The constants: `β` is a common scale of `‖A‖` and `√‖Z‖`; `e^{Hβ} ≤ e^{1/4} ≤ 4/3`.
-/
import CoSimFoundations.ZeroOrderHold
import CoSimFoundations.ReachCompletion

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The parts of a matrix are linear -/

/-- The block-diagonal part of a sum. -/
theorem blockDiag_add (T T' : Matrix (Fin n) (Fin n) ℝ) :
    S.blockDiag (T + T') = S.blockDiag T + S.blockDiag T' := by
  ext p q
  simp only [blockDiag_apply, Matrix.add_apply]
  split_ifs <;> simp

/-- The block-diagonal part of a multiple. -/
theorem blockDiag_smul (c : ℝ) (T : Matrix (Fin n) (Fin n) ℝ) :
    S.blockDiag (c • T) = c • S.blockDiag T := by
  ext p q
  simp only [blockDiag_apply, Matrix.smul_apply]
  split_ifs <;> simp

/-- The coupling part of zero. -/
theorem coupling_zero : S.coupling 0 = 0 := by
  ext p q
  rw [S.coupling_apply, Matrix.zero_apply]
  split_ifs <;> rfl

/-- The coupling part of a sum. -/
theorem coupling_add (T T' : Matrix (Fin n) (Fin n) ℝ) :
    S.coupling (T + T') = S.coupling T + S.coupling T' := by
  rw [coupling, coupling, coupling, S.blockDiag_add]
  abel

/-- The coupling part of a multiple. -/
theorem coupling_smul (c : ℝ) (T : Matrix (Fin n) (Fin n) ℝ) :
    S.coupling (c • T) = c • S.coupling T := by
  rw [coupling, coupling, S.blockDiag_smul, smul_sub]

/-- A matrix without entries between different subsystems has no coupling part. -/
theorem coupling_eq_zero_of_block {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : ∀ p q, S.sub p ≠ S.sub q → T p q = 0) : S.coupling T = 0 := by
  ext p q
  rw [S.coupling_apply, Matrix.zero_apply]
  by_cases h : S.sub p = S.sub q
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, hT p q h]

/-- The coupling part commutes with a block-diagonal factor on the right:
`A_c(T) Θ = A_c(T Θ)` if `Θ` has no entries between different subsystems. -/
theorem coupling_mul_of_block {T Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) :
    S.coupling T * Θ = S.coupling (T * Θ) := by
  ext p q
  rw [S.coupling_apply (T * Θ), Matrix.mul_apply, Matrix.mul_apply]
  by_cases hpq : S.sub p = S.sub q
  · rw [ite_eq_left hpq]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : S.sub r = S.sub q
    · rw [S.coupling_apply, ite_eq_left (hpq.trans hr.symm), zero_mul]
    · rw [hΘ r q hr, mul_zero]
  · rw [ite_eq_right hpq]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : S.sub r = S.sub q
    · rw [S.coupling_apply, ite_eq_right (fun e => hpq (e.trans hr))]
    · rw [hΘ r q hr, mul_zero, mul_zero]

/-- The part of the coupling on the new samples is at most `√(card κ)` times the coupling part:
in the rows of a subsystem `s` it is the coupling part times the mask of the stages before `s`. -/
theorem norm_opE_couplingNew_le [Fintype κ] (T : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (S.couplingNew T)‖ ≤ Real.sqrt (Fintype.card κ) * ‖opE (S.coupling T)‖ := by
  refine S.norm_opE_le_of_rows (norm_nonneg _) fun s x hx y => ?_
  have e : ⟪x, opE (S.couplingNew T) y⟫ = ⟪x, opE (S.coupling T * S.early s) y⟫ := by
    refine inner_opE_congr_row hx y fun p q hp => ?_
    have e' : (S.coupling T * S.early s) p q =
        S.coupling T p q * (if S.stage (S.sub q) < S.stage s then 1 else 0) := by
      rw [early, Matrix.mul_diagonal]
    rw [e', ← hp]
    by_cases hs : S.stage (S.sub q) < S.stage (S.sub p) <;> simp [couplingNew, hs]
  rw [e]
  exact (abs_inner_opE_le _ x y).trans (mul_le_mul_of_nonneg_right
    (norm_opE_mul_le_of_norm_le_one _ (S.norm_opE_early_le s)) (by positivity))

/-! ### The reach -/

/-- **What the coefficients reach** (the paper, `lem:reach`: `𝒵 = {Y + W C}`), for the kernels `Θ`
of the output maps: the matrices without entries between different subsystems that are not partners
whose coupling part vanishes on the kernels of the outputs, `A_c(Z) Θ = 0`. -/
def reach (Θ : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {Z | (∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → Z p q = 0) ∧
    S.coupling Z * Θ = 0}
  add_mem' := by
    rintro Z Z' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun p q hne hnp => ?_, ?_⟩
    · rw [Matrix.add_apply, h1 p q hne hnp, h1' p q hne hnp, add_zero]
    · rw [S.coupling_add, Matrix.add_mul, h2, h2', add_zero]
  zero_mem' := by
    refine ⟨fun _ _ _ _ => rfl, ?_⟩
    rw [S.coupling_zero, Matrix.zero_mul]
  smul_mem' := by
    rintro c Z ⟨h1, h2⟩
    refine ⟨fun p q hne hnp => ?_, ?_⟩
    · rw [Matrix.smul_apply, h1 p q hne hnp, smul_zero]
    · rw [S.coupling_smul, Matrix.smul_mul, h2, smul_zero]

theorem mem_reach {Θ Z : Matrix (Fin n) (Fin n) ℝ} :
    Z ∈ S.reach Θ ↔
      (∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → Z p q = 0) ∧
        S.coupling Z * Θ = 0 := Iff.rfl

/-- A matrix without entries between different subsystems is in the reach. -/
theorem mem_reach_of_block {Θ Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ p q, S.sub p ≠ S.sub q → Z p q = 0) : Z ∈ S.reach Θ :=
  ⟨fun p q hne _ => hZ p q hne, by rw [S.coupling_eq_zero_of_block hZ, Matrix.zero_mul]⟩

/-- The identity is in the reach. -/
theorem one_mem_reach (Θ : Matrix (Fin n) (Fin n) ℝ) : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ S.reach Θ :=
  S.mem_reach_of_block fun _ _ h => Matrix.one_apply_ne fun e => h (congrArg S.sub e)

/-- **The half-step term** `P = ½ A_ς A` of the paper. -/
noncomputable def halfStepTerm (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (S.signedCoupling A * A)

/-! ### Every scheme: the two brackets are in the reach -/

/-- **The reached matrix of a scheme**, `Z_H = H⁻² [(F - 1 - H A₀ - ½H² A₀²) +`
`(M + N - H A_c - ½H² A₀ A_c)]`: the two brackets of the half-step normal form (`halfStepLead`)
divided by `H²`, the paper's `[(F - e^{H A₀}) + (G - G°) C] / H²` up to `O(H)`. -/
noncomputable def reachLead (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (H ^ 2)⁻¹ • ((S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
    (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)))

/-- The leading term of the normal form is `H² (P + Z_H)`. -/
theorem halfStepLead_eq (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : H ≠ 0) :
    S.halfStepLead A H = H ^ 2 • (S.halfStepTerm A + S.reachLead A H) := by
  rw [halfStepLead, halfStepTerm, reachLead, smul_add, smul_smul, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 hH), one_smul, show H ^ 2 * (1 / 2 : ℝ) = H ^ 2 / 2 by ring]
  abel

/-- The first bracket has no entries between different subsystems. -/
theorem local_bracket_apply_eq_zero (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) :
    ((S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A) :
      Matrix (Fin n) (Fin n) ℝ)) p q = 0 := by
  have hpq : p ≠ q := fun e => hne (e ▸ rfl)
  have h2 : (S.blockDiag A * S.blockDiag A) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [S.blockDiag_apply, S.blockDiag_apply]
    by_cases hr : S.sub p = S.sub r
    · rw [ite_eq_right fun e => hne (hr.trans e), mul_zero]
    · rw [ite_eq_right hr, zero_mul]
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.smul_apply, S.hF p q hne, Matrix.one_apply_ne hpq, S.blockDiag_apply, ite_eq_right hne,
    h2]
  simp

/-- The second bracket has no entries between subsystems that are not partners. -/
theorem sample_bracket_apply_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    {p q : Fin n} (hnp : ¬ S.partner (S.sub p) (S.sub q)) :
    ((S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A) :
      Matrix (Fin n) (Fin n) ℝ)) p q = 0 := by
  have hc : ∀ r, S.sub r = S.sub p → S.coupling A r q = 0 := by
    intro r hr
    rw [S.coupling_apply]
    by_cases e : S.sub r = S.sub q
    · rw [ite_eq_left e]
    · rw [ite_eq_right e]
      exact hA r q e (by rw [hr]; exact hnp)
  have h2 : (S.blockDiag A * S.coupling A) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : S.sub p = S.sub r
    · rw [hc r hr.symm, mul_zero]
    · rw [S.blockDiag_apply, ite_eq_right hr, zero_mul]
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, S.hM p q (fun h' => hnp h'.1), S.hN p q (fun h' => hnp h'.1),
    hc p rfl, h2]
  simp

variable {S}

/-- **The reached matrix of a consistent scheme is in the reach** (the paper, `lem:reach`: "the
first two terms of (half) lie in `𝒵`"). `Θ` is block diagonal, the coupling and the coefficients of
the samples act through the outputs: `A_c Θ = 0`, `(M + N) Θ = 0`. -/
theorem Consistent.reachLead_mem {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) : S.reachLead A H ∈ S.reach Θ := by
  refine ⟨fun p q hne hnp => ?_, ?_⟩
  · rw [reachLead, Matrix.smul_apply, Matrix.add_apply, S.local_bracket_apply_eq_zero A H hne,
      S.sample_bracket_apply_eq_zero h.hA H hnp, add_zero, smul_zero]
  · have h1 : S.coupling (S.F - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) = 0 :=
      S.coupling_eq_zero_of_block fun p q hne => S.local_bracket_apply_eq_zero A H hne
    have h2 : (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) *
        Θ = 0 := by
      rw [Matrix.sub_mul, Matrix.sub_mul, hGΘ, Matrix.smul_mul, hAΘ, Matrix.smul_mul,
        Matrix.mul_assoc, hAΘ, Matrix.mul_zero]
      simp
    rw [reachLead, S.coupling_smul, S.coupling_add, h1, zero_add, Matrix.smul_mul,
      S.coupling_mul_of_block hΘ, h2, S.coupling_zero, smul_zero]

/-- **Every scheme, the expansion** (the paper, eq. `eq:reach`): for a consistent scheme and
`H ≠ 0`, `‖X - U - H² (½ A_ς A + Z_H)‖ ≤ √(card κ) C₃ H³`, `C₃ = reactionC a b c ‖A‖ H`. -/
theorem Consistent.norm_sub_reachLead_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) (hH : H ≠ 0) :
    ‖opE (S.X - U - H ^ 2 • (S.halfStepTerm A + S.reachLead A H))‖ ≤
      Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 3 := by
  rw [← S.halfStepLead_eq A hH]
  exact h.norm_half_step_le

/-- **Every scheme, the size of the reached matrix:** `‖½ A_ς A + Z_H‖ ≤ c + √(card κ) C₃ H` and
`‖Z_H‖ ≤ c + ‖½ A_ς A‖ + √(card κ) C₃ H` for `H > 0`. -/
theorem Consistent.norm_reachLead_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) (hH : 0 < H) :
    ‖opE (S.halfStepTerm A + S.reachLead A H)‖ ≤
        c + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ∧
      ‖opE (S.reachLead A H)‖ ≤
        c + ‖opE (S.halfStepTerm A)‖ +
          Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H := by
  have h1 := h.norm_sub_reachLead_le hH.ne'
  have h2 : ‖opE (H ^ 2 • (S.halfStepTerm A + S.reachLead A H))‖ ≤
      c * H ^ 2 + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 3 := by
    have e : H ^ 2 • (S.halfStepTerm A + S.reachLead A H) =
        (S.X - U) - (S.X - U - H ^ 2 • (S.halfStepTerm A + S.reachLead A H)) := by abel
    rw [e, opE_sub]
    exact (norm_sub_le _ _).trans (add_le_add h.hc h1)
  rw [opE_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at h2
  have hH2 : 0 < H ^ 2 := by positivity
  have h3 : ‖opE (S.halfStepTerm A + S.reachLead A H)‖ ≤
      c + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H := by
    refine le_of_mul_le_mul_left ?_ hH2
    calc H ^ 2 * ‖opE (S.halfStepTerm A + S.reachLead A H)‖
        ≤ c * H ^ 2 + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 3 := h2
      _ = H ^ 2 * (c + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H) := by ring
  refine ⟨h3, ?_⟩
  have e : S.reachLead A H = (S.halfStepTerm A + S.reachLead A H) - S.halfStepTerm A := by abel
  rw [e, opE_sub]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- **The reach of the coefficients, every scheme** (the paper, `lem:reach`, first statement): a
consistent scheme whose coupling and coefficients of the samples act through the outputs has, for
`H > 0`, a `Z ∈ reach Θ` with `‖X - U - H² (½ A_ς A + Z)‖ ≤ √(card κ) C₃ H³` and
`‖Z‖ ≤ c + ‖½ A_ς A‖ + √(card κ) C₃ H`. -/
theorem Consistent.exists_reach [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hH : 0 < H) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) :
    ∃ Z ∈ S.reach Θ,
      ‖opE (S.X - U - H ^ 2 • (S.halfStepTerm A + Z))‖ ≤
          Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 3 ∧
        ‖opE Z‖ ≤ c + ‖opE (S.halfStepTerm A)‖ +
          Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H :=
  ⟨S.reachLead A H, h.reachLead_mem hΘ hAΘ hGΘ, h.norm_sub_reachLead_le hH.ne',
    (h.norm_reachLead_le hH).2⟩

/-! ### Every element of the reach is reached -/

variable (S)

/-- **The scheme that reaches `Z`** (the paper, `lem:reach`, second statement): on the subsystems,
partners and stages of `S`, the local maps `F = e^{H A₀} + H² Y`, `Y` the block diagonal of `Z`,
and the coefficients of the samples of the zero-order hold plus `H²` times the coupling part of
`Z`, the new samples from the subsystems of an earlier stage, the old ones from the others.
`X = (Σ_{k < B} N^k) (F + M)` solves `X = F + M + N X` (`N^B = 0`). -/
noncomputable def reachScheme (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (hZ : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → Z p q = 0) (H : ℝ) :
    HeldScheme n κ where
  sub := S.sub
  partner := S.partner
  stage := S.stage
  F := NormedSpace.exp (H • S.blockDiag A) + H ^ 2 • S.blockDiag Z
  N := S.zohNew A H + H ^ 2 • S.couplingNew Z
  M := S.zohOld A H + H ^ 2 • S.couplingOld Z
  X := (∑ k ∈ Finset.range S.stageBound, (S.zohNew A H + H ^ 2 • S.couplingNew Z) ^ k) *
    (NormedSpace.exp (H • S.blockDiag A) + H ^ 2 • S.blockDiag Z +
      (S.zohOld A H + H ^ 2 • S.couplingOld Z))
  hF := fun p q h => by
    rw [Matrix.add_apply, Matrix.smul_apply, S.blockDiag_apply, ite_eq_right h, smul_zero,
      add_zero]
    exact S.exp_apply_eq_zero_of_block
      (fun p q h => by rw [Matrix.smul_apply, S.blockDiag_apply, ite_eq_right h, smul_zero]) h
  hN := fun p q h => by
    rw [Matrix.add_apply, S.zohNew_apply_eq_zero hA H h, Matrix.smul_apply, S.couplingNew_apply]
    by_cases hs : S.stage (S.sub q) < S.stage (S.sub p)
    · have hnp : ¬ S.partner (S.sub p) (S.sub q) := fun hp => h ⟨hp, hs⟩
      have hne : S.sub p ≠ S.sub q := fun e => by rw [e] at hs; exact lt_irrefl _ hs
      rw [ite_eq_left hs, S.coupling_apply, ite_eq_right hne, hZ p q hne hnp, smul_zero,
        zero_add]
    · rw [ite_eq_right hs, smul_zero, zero_add]
  hM := fun p q h => by
    rw [Matrix.add_apply, S.zohOld_apply_eq_zero hA H h, Matrix.smul_apply, S.couplingOld_apply]
    by_cases hs : S.stage (S.sub q) < S.stage (S.sub p)
    · rw [ite_eq_left hs, smul_zero, zero_add]
    · have hnp : ¬ S.partner (S.sub p) (S.sub q) := fun hp => h ⟨hp, hs⟩
      rw [ite_eq_right hs, S.coupling_apply]
      by_cases hne : S.sub p = S.sub q
      · rw [ite_eq_left hne, smul_zero, zero_add]
      · rw [ite_eq_right hne, hZ p q hne hnp, smul_zero, zero_add]
  hX := add_mul_geom_sum_mul (S.pow_stageBound_eq_zero fun p q h => by
    simp [zohNew, couplingNew, h]) _

variable {S}
variable {A : Matrix (Fin n) (Fin n) ℝ}
  {hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0}
  {Z : Matrix (Fin n) (Fin n) ℝ}
  {hZ : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → Z p q = 0} {H : ℝ}

/-- The local maps of the scheme that reaches `Z`: `F = e^{H A₀} + H² Y`. -/
theorem reachScheme_F :
    (S.reachScheme A hA Z hZ H).F = NormedSpace.exp (H • S.blockDiag A) + H ^ 2 • S.blockDiag Z :=
  rfl

/-- The coefficients of the samples of the scheme that reaches `Z`: `G C = G° C + H² A_c(Z)`. -/
theorem reachScheme_samples :
    (S.reachScheme A hA Z hZ H).M + (S.reachScheme A hA Z hZ H).N =
      S.zohCoupling A H + H ^ 2 • S.coupling Z := by
  show S.zohOld A H + H ^ 2 • S.couplingOld Z + (S.zohNew A H + H ^ 2 • S.couplingNew Z) = _
  rw [← S.zohOld_add_zohNew A H, ← S.couplingOld_add_couplingNew Z, smul_add]
  abel

/-- **The coefficients of the samples act through the outputs** if the coupling does and
`Z ∈ reach Θ`: `(M + N) Θ = 0`. -/
theorem reachScheme_samples_mul_eq_zero {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hAΘ : S.coupling A * Θ = 0) (hZΘ : S.coupling Z * Θ = 0) :
    ((S.reachScheme A hA Z hZ H).M + (S.reachScheme A hA Z hZ H).N) * Θ = 0 := by
  rw [reachScheme_samples, Matrix.add_mul, zohCoupling, Matrix.mul_assoc, hAΘ, Matrix.mul_zero,
    Matrix.smul_mul, hZΘ, smul_zero, add_zero]

/-- **The two brackets of the scheme that reaches `Z`** are those of the zero-order hold plus
`H² Z`. -/
theorem reachScheme_brackets :
    ((S.reachScheme A hA Z hZ H).F - 1 - H • (S.reachScheme A hA Z hZ H).blockDiag A -
        (H ^ 2 / 2) • ((S.reachScheme A hA Z hZ H).blockDiag A *
          (S.reachScheme A hA Z hZ H).blockDiag A)) +
      ((S.reachScheme A hA Z hZ H).M + (S.reachScheme A hA Z hZ H).N -
        H • (S.reachScheme A hA Z hZ H).coupling A -
        (H ^ 2 / 2) • ((S.reachScheme A hA Z hZ H).blockDiag A *
          (S.reachScheme A hA Z hZ H).coupling A)) =
      ((NormedSpace.exp (H • S.blockDiag A) - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
        (S.zohCoupling A H - H • S.coupling A -
          (H ^ 2 / 2) • (S.blockDiag A * S.coupling A))) + H ^ 2 • Z := by
  rw [reachScheme_samples, reachScheme_F]
  have e : H ^ 2 • Z = H ^ 2 • S.blockDiag Z + H ^ 2 • S.coupling Z := by
    rw [← smul_add, S.blockDiag_add_coupling]
  rw [e]
  show NormedSpace.exp (H • S.blockDiag A) + H ^ 2 • S.blockDiag Z - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A) +
      (S.zohCoupling A H + H ^ 2 • S.coupling Z - H • S.coupling A -
        (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) = _
  abel

/-- The constant of the reaction with the constants of the scheme that reaches `Z`: for
`α ≤ β` and `e^{Hα} ≤ 4/3`, `C₃ ≤ (7 + 74σ + 81σ²) β³`. -/
theorem reactionC_reach_le {σ α β H : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hE : Real.exp (H * α) ≤ 4 / 3) :
    reactionC (3 * σ * β) (9 * β) ((6 + 27 * σ) * β ^ 2) α H ≤
      (7 + 74 * σ + 81 * σ ^ 2) * β ^ 3 := by
  have hβ : 0 ≤ β := hα.trans hαβ
  have hE0 : 0 ≤ Real.exp (H * α) := Real.exp_nonneg _
  have h2 : α ^ 2 * Real.exp (H * α) ≤ β ^ 2 * (4 / 3) :=
    mul_le_mul (pow_le_pow_left₀ hα hαβ 2) hE hE0 (by positivity)
  have h3 : α ^ 3 * Real.exp (H * α) ≤ β ^ 3 * (4 / 3) :=
    mul_le_mul (pow_le_pow_left₀ hα hαβ 3) hE hE0 (by positivity)
  have k1 : ((6 + 27 * σ) * β ^ 2 + 3 * σ * β * (9 * β) + α ^ 2 / 2 * Real.exp (H * α)) * α ≤
      ((6 + 54 * σ) * β ^ 2 + 2 / 3 * β ^ 2) * β := by
    refine mul_le_mul ?_ hαβ hα (by positivity)
    linarith
  have k2 : 3 * σ * β * ((6 + 27 * σ) * β ^ 2 + α ^ 2 / 2 * Real.exp (H * α)) ≤
      3 * σ * β * ((6 + 27 * σ) * β ^ 2 + 2 / 3 * β ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have k3 : α ^ 3 / 6 * Real.exp (H * α) ≤ 2 / 9 * β ^ 3 := by linarith
  have hb3 : 0 ≤ β ^ 3 := pow_nonneg hβ 3
  unfold reactionC reactionConst couplingConst
  linarith

/-- **The scheme that reaches `Z` is consistent** (the paper, `lem:reach`: "the standing assumptions
hold"). For `‖A‖ ≤ β`, `‖Z‖ ≤ β²`, `0 ≤ H`, `H β ≤ 1/4` and `σ H β ≤ 1/6`, `σ = √(card κ)`:
`‖N‖ ≤ 3σβ H`, `‖X - 1‖ ≤ 9β H`, `‖X - e^{HA}‖ ≤ (6 + 27σ) β² H²`. -/
theorem reachScheme_consistent [Fintype κ] {β : ℝ} (hH : 0 ≤ H) (hAβ : ‖opE A‖ ≤ β)
    (hZβ : ‖opE Z‖ ≤ β ^ 2) (hβH : H * β ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6) :
    (S.reachScheme A hA Z hZ H).Consistent A (NormedSpace.exp (H • A)) H
      (3 * Real.sqrt (Fintype.card κ) * β) (9 * β)
      ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) := by
  set σ := Real.sqrt (Fintype.card κ) with hσdef
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hα : 0 ≤ ‖opE A‖ := norm_nonneg _
  have hβ : 0 ≤ β := hα.trans hAβ
  have hAH : H * ‖opE A‖ ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hAβ hH).trans hβH
  obtain ⟨h0, hγ, hx, hE₀⟩ := S.norm_parts_le A hH hAH
  have hE : Real.exp (H * ‖opE A‖) ≤ 4 / 3 := (Real.exp_le_exp.2 hAH).trans exp_quarter_le
  have hα2 : ‖opE A‖ ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hα hAβ 2
  set R := S.reachScheme A hA Z hZ H with hR
  have eF : R.F = NormedSpace.exp (H • S.blockDiag A) + H ^ 2 • S.blockDiag Z := rfl
  have eN : R.N = S.zohNew A H + H ^ 2 • S.couplingNew Z := rfl
  have eMN : R.M + R.N = S.zohCoupling A H + H ^ 2 • S.coupling Z := reachScheme_samples
  have nsm : ∀ T : Matrix (Fin n) (Fin n) ℝ, ‖opE (H ^ 2 • T)‖ = H ^ 2 * ‖opE T‖ := fun T => by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
  -- the parts of `Z`
  have hZ0 : ‖opE (S.blockDiag Z)‖ ≤ β ^ 2 := (S.norm_opE_blockDiag_le Z).trans hZβ
  have hZc : ‖opE (S.coupling Z)‖ ≤ 2 * β ^ 2 := by
    have := S.norm_opE_coupling_le_two Z
    linarith
  have hZn : ‖opE (S.couplingNew Z)‖ ≤ σ * (2 * β ^ 2) :=
    (S.norm_opE_couplingNew_le Z).trans (mul_le_mul_of_nonneg_left hZc hσ0)
  have hq : H ^ 2 * β ^ 2 ≤ 1 / 4 * (β * H) := by
    have := mul_le_mul_of_nonneg_left hβH (mul_nonneg hβ hH)
    linarith
  -- the coefficients of the zero-order hold
  have hF1 := (S.norm_zoh_local_samples_le A hH hAH).1
  have hG := (S.norm_zoh_local_samples_le A hH hAH).2
  have hAHβ : ‖opE A‖ * H ≤ β * H := mul_le_mul_of_nonneg_right hAβ hH
  have hNz : ‖opE (S.zohNew A H)‖ ≤ σ * (7 / 3 * ‖opE A‖ * H) :=
    (S.norm_opE_zohNew_le A H).trans (mul_le_mul_of_nonneg_left hG hσ0)
  have hσq : σ * (H ^ 2 * β ^ 2) ≤ σ * (1 / 4 * (β * H)) := mul_le_mul_of_nonneg_left hq hσ0
  have hσA : σ * (‖opE A‖ * H) ≤ σ * (β * H) := mul_le_mul_of_nonneg_left hAHβ hσ0
  have hβH0 : 0 ≤ β * H := mul_nonneg hβ hH
  have hσβH : 0 ≤ σ * (β * H) := mul_nonneg hσ0 hβH0
  -- the new samples
  have hN : ‖opE R.N‖ ≤ 3 * σ * β * H := by
    rw [eN, opE_add]
    refine (norm_add_le _ _).trans ?_
    rw [nsm]
    have := mul_le_mul_of_nonneg_left hZn (sq_nonneg H)
    linarith
  have hN2 : ‖opE R.N‖ ≤ 1 / 2 := by linarith
  -- the local maps and the samples
  have hFm1 : ‖opE (R.F - 1)‖ ≤ 19 / 12 * β * H := by
    have e : R.F - 1 = (NormedSpace.exp (H • S.blockDiag A) - 1) + H ^ 2 • S.blockDiag Z := by
      rw [eF]
      abel
    rw [e, opE_add]
    refine (norm_add_le _ _).trans ?_
    rw [nsm]
    have := mul_le_mul_of_nonneg_left hZ0 (sq_nonneg H)
    linarith
  have hMN : ‖opE (R.M + R.N)‖ ≤ 17 / 6 * β * H := by
    rw [eMN, opE_add]
    refine (norm_add_le _ _).trans ?_
    rw [nsm]
    have := mul_le_mul_of_nonneg_left hZc (sq_nonneg H)
    linarith
  have hX1 : ‖opE (R.X - 1)‖ ≤ 9 * β * H := by
    have h := R.norm_X_sub_one_le hN2
    linarith
  -- the one-step error
  have hXU : ‖opE (R.X - NormedSpace.exp (H • A))‖ ≤ (6 + 27 * σ) * β ^ 2 * H ^ 2 := by
    have h := R.norm_X_sub_step_le (S.blockDiag A) (S.coupling A) (NormedSpace.exp (H • A)) H
    rw [S.blockDiag_add_coupling] at h
    have t1 : ‖opE (NormedSpace.exp (H • S.blockDiag A) - (1 + H • S.blockDiag A))‖ ≤
        2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by
      refine (norm_opE_exp_sub_linear_le (S.blockDiag A) hH).trans ?_
      calc ‖opE (S.blockDiag A)‖ ^ 2 / 2 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 2
          ≤ ‖opE A‖ ^ 2 / 2 * (4 / 3) * H ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul
              (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h0 2) zero_le_two)
              hE₀ (Real.exp_nonneg _) (by positivity)) (by positivity)
        _ = 2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by ring
    have t2 : ‖opE (S.zohCoupling A H - H • S.coupling A)‖ ≤
        10 / 9 * ‖opE A‖ ^ 2 * H ^ 2 := by
      refine (S.norm_opE_zohCoupling_sub_le A hH hx).trans ?_
      have h5 : ‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖ ≤ ‖opE A‖ * (2 * ‖opE A‖) :=
        mul_le_mul h0 hγ (norm_nonneg _) hα
      have h6 := mul_le_mul_of_nonneg_right h5 (sq_nonneg H)
      linarith
    have t4 : ‖opE (NormedSpace.exp (H • A) - (1 + H • A))‖ ≤ 2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by
      refine (norm_opE_exp_sub_linear_le A hH).trans ?_
      calc ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2
          ≤ ‖opE A‖ ^ 2 / 2 * (4 / 3) * H ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity))
              (by positivity)
        _ = 2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by ring
    have u1 : ‖opE (R.F - (1 + H • S.blockDiag A))‖ ≤ 2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 +
        H ^ 2 * β ^ 2 := by
      have e : R.F - (1 + H • S.blockDiag A) =
          (NormedSpace.exp (H • S.blockDiag A) - (1 + H • S.blockDiag A)) +
            H ^ 2 • S.blockDiag Z := by
        rw [eF]
        abel
      rw [e, opE_add]
      refine (norm_add_le _ _).trans (add_le_add t1 ?_)
      rw [nsm]
      exact mul_le_mul_of_nonneg_left hZ0 (sq_nonneg H)
    have u2 : ‖opE (R.M + R.N - H • S.coupling A)‖ ≤ 10 / 9 * ‖opE A‖ ^ 2 * H ^ 2 +
        H ^ 2 * (2 * β ^ 2) := by
      have e : R.M + R.N - H • S.coupling A =
          (S.zohCoupling A H - H • S.coupling A) + H ^ 2 • S.coupling Z := by
        rw [eMN]
        abel
      rw [e, opE_add]
      refine (norm_add_le _ _).trans (add_le_add t2 ?_)
      rw [nsm]
      exact mul_le_mul_of_nonneg_left hZc (sq_nonneg H)
    have u3 : ‖opE R.N‖ * ‖opE (R.X - 1)‖ ≤ 3 * σ * β * H * (9 * β * H) :=
      mul_le_mul hN hX1 (norm_nonneg _) (by positivity)
    have hα2H : ‖opE A‖ ^ 2 * H ^ 2 ≤ β ^ 2 * H ^ 2 := mul_le_mul_of_nonneg_right hα2 (sq_nonneg H)
    have p0 : 0 ≤ β ^ 2 * H ^ 2 := by positivity
    linarith
  refine ⟨hH, rfl, hA, ?_, ?_, ?_⟩
  · exact hN.trans_eq (by ring)
  · exact hX1.trans_eq (by ring)
  · exact hXU.trans_eq (by ring)

/-- The constant of the scheme that reaches `Z`, `(1 + 7σ + 74σ² + 81σ³) β³`. -/
noncomputable def reachK (σ β : ℝ) : ℝ := (1 + 7 * σ + 74 * σ ^ 2 + 81 * σ ^ 3) * β ^ 3

/-- **The scheme that reaches `Z` has the expansion with this `Z`** (the paper, `lem:reach`, second
statement, with eq. `eq:reach`). For `‖A‖ ≤ β`, `‖Z‖ ≤ β²`, `0 ≤ H`, `H β ≤ 1/4` and
`σ H β ≤ 1/6`, `σ = √(card κ)`, in any order of execution:
`‖X - e^{HA} - H² (½ A_ς A + Z)‖ ≤ (1 + 7σ + 74σ² + 81σ³) β³ H³`. -/
theorem norm_reachScheme_sub_le [Fintype κ] {β : ℝ} (hH : 0 ≤ H) (hAβ : ‖opE A‖ ≤ β)
    (hZβ : ‖opE Z‖ ≤ β ^ 2) (hβH : H * β ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6) :
    ‖opE ((S.reachScheme A hA Z hZ H).X - NormedSpace.exp (H • A) -
        H ^ 2 • (S.halfStepTerm A + Z))‖ ≤
      reachK (Real.sqrt (Fintype.card κ)) β * H ^ 3 := by
  have hc := reachScheme_consistent (hA := hA) (hZ := hZ) hH hAβ hZβ hβH hσ
  have h1 := hc.norm_half_step_le
  have h2 := S.norm_zoh_brackets_le A hH
  have hα : 0 ≤ ‖opE A‖ := norm_nonneg _
  have hAH : H * ‖opE A‖ ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hAβ hH).trans hβH
  obtain ⟨hE, hZC, -⟩ := S.zoh_taylor_constants_le A hH hAH
  have hR := reactionC_reach_le (Real.sqrt_nonneg (Fintype.card κ)) hα hAβ hE
  have e : (S.reachScheme A hA Z hZ H).X - NormedSpace.exp (H • A) -
      H ^ 2 • (S.halfStepTerm A + Z) =
      ((S.reachScheme A hA Z hZ H).X - NormedSpace.exp (H • A) -
        (S.reachScheme A hA Z hZ H).halfStepLead A H) +
      ((NormedSpace.exp (H • S.blockDiag A) - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
        (S.zohCoupling A H - H • S.coupling A -
          (H ^ 2 / 2) • (S.blockDiag A * S.coupling A))) := by
    rw [halfStepLead, reachScheme_brackets]
    show _ = _ - (_ + H ^ 2 • Z + (H ^ 2 / 2) • (S.signedCoupling A * A)) + _
    rw [halfStepTerm, smul_add, smul_smul, show H ^ 2 * (1 / 2 : ℝ) = H ^ 2 / 2 by ring]
    abel
  rw [e, opE_add]
  refine (norm_add_le _ _).trans ?_
  have hβ : 0 ≤ β := hα.trans hAβ
  have hσ0 : 0 ≤ Real.sqrt (Fintype.card κ) := Real.sqrt_nonneg _
  have hα3 : ‖opE A‖ ^ 3 ≤ β ^ 3 := pow_le_pow_left₀ hα hAβ 3
  have hH3 : 0 ≤ H ^ 3 := pow_nonneg hH 3
  have k1 := mul_le_mul_of_nonneg_left hR hσ0
  have k2 : Real.sqrt (Fintype.card κ) *
      reactionC (3 * Real.sqrt (Fintype.card κ) * β) (9 * β)
        ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ H +
      zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H ≤
      reachK (Real.sqrt (Fintype.card κ)) β := by
    unfold reachK
    linarith [pow_nonneg hβ 3]
  have k3 := mul_le_mul_of_nonneg_right k2 hH3
  linarith

/-- **The reach of the coefficients, every element is reached** (the paper, `lem:reach`, second
statement). For `Z ∈ reach Θ`, `A` without blocks between subsystems that are not partners and
with `A_c Θ = 0`, `‖A‖ ≤ β`, `‖Z‖ ≤ β²`, `0 ≤ H`, `H β ≤ 1/4`, `σ H β ≤ 1/6`: there is a scheme on
the subsystems, partners and stages of `S` with `F = e^{H A₀} + H² Y` (`Y` block diagonal),
coefficients of the samples `G°C + H² A_c(Z)` that act through the outputs, consistent with the
constants `3σβ`, `9β`, `(6 + 27σ) β²`, and `‖X - e^{HA} - H² (½ A_ς A + Z)‖ ≤ reachK σ β H³`. -/
theorem exists_reachScheme [Fintype κ]
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hZΘ : Z ∈ S.reach Θ)
    (hAΘ : S.coupling A * Θ = 0) {β : ℝ} (hH : 0 ≤ H) (hAβ : ‖opE A‖ ≤ β)
    (hZβ : ‖opE Z‖ ≤ β ^ 2) (hβH : H * β ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6) :
    ∃ R : HeldScheme n κ, R.sub = S.sub ∧ R.partner = S.partner ∧ R.stage = S.stage ∧
      R.F = NormedSpace.exp (H • S.blockDiag A) + H ^ 2 • S.blockDiag Z ∧
      R.M + R.N = S.zohCoupling A H + H ^ 2 • S.coupling Z ∧ (R.M + R.N) * Θ = 0 ∧
      R.Consistent A (NormedSpace.exp (H • A)) H (3 * Real.sqrt (Fintype.card κ) * β) (9 * β)
        ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ∧
      ‖opE (R.X - NormedSpace.exp (H • A) - H ^ 2 • (S.halfStepTerm A + Z))‖ ≤
        reachK (Real.sqrt (Fintype.card κ)) β * H ^ 3 :=
  ⟨S.reachScheme A hA Z hZΘ.1 H, rfl, rfl, rfl, rfl, reachScheme_samples,
    reachScheme_samples_mul_eq_zero hAΘ hZΘ.2,
    reachScheme_consistent hH hAβ hZβ hβH hσ, norm_reachScheme_sub_le hH hAβ hZβ hβH hσ⟩

end HeldScheme

end CoSimFoundations
