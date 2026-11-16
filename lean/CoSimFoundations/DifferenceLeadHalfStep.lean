/-
The half-step relation, the total numerical damping and the two parts between non-partners, for
the difference itself (the paper, Theorem `thm:half` with eq. `eq:halfstep`, Definition
`def:props` (iii) with eq. `eq:negdamping`, Corollary `cor:blocks` (a) with eq. `eq:parts`).

**Paper.** For a consistent family of holds, `Δ = (X - U)/H + O(H²)`; hence every statement on the
one-step error `X - U` up to `O(H³)` is a statement on the difference `Δ = Ã - A` up to `O(H²)`:
`Δ = (1/H) [(F - e^{H A₀}) + (G - G°) C] + ½H A_ς A + O(H²)`, the total numerical damping
`ν = -tr Δ`, and between subsystems `i ≠ j` that are not partners
`[Δ_R]_ij = -¼H Σ_k (ς_ik + ς_jk) A_ik A_kj + O(H²)`,
`[Δ_J]_ij = ¼H Σ_k (ς_ik - ς_jk) A_ik A_kj + O(H²)`.

**What is formalised.** `DifferenceLead` proves the passage a priori: for `H > 0`, `b H ≤ 1/3`,
`H ‖A‖ ≤ 1/4`, `‖Δ - H⁻¹ • (X - U)‖ ≤ K H²`, `K = diffLeadC b c ‖A‖ = 3/2 · c · max b (4/3 ‖A‖)`,
with `Ã = modifiedSystem H X = H⁻¹ • log X` and `Δ = difference A H X`. Here it is combined with
the one-step statements of `HalfStep`, `LegRule` and `ForcedParts` for a consistent scheme with
one held sample (`S.Consistent A U H a b c`), in any order of execution. All remainders are in the
constants `a`, `b`, `c` of consistency and `‖A‖` alone; `C₃ = reactionC a b c ‖A‖ H`,
`C = forcedC a b c ‖A‖ H`, `κ` the type of the subsystems, `n` the number of states.

* The scheme forms of `DifferenceLead`: `Consistent.exp_smul_modifiedSystem`,
  `Consistent.norm_modifiedSystem_le` (`‖Ã‖ ≤ 3/2 · b`), `Consistent.norm_smul_difference_sub_le`,
  `Consistent.norm_difference_sub_le`, `Consistent.norm_difference_le` (`‖Δ‖ ≤ 3/2 · c H`).
* **The half-step relation for the difference** (`Consistent.norm_difference_half_step_le`):
    `‖Δ - H⁻¹ • [(F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c)] - (H/2) • A_ς A‖`
    `≤ (K + √(card κ) C₃) H²`.
  If the two brackets are of third order, `‖…‖ ≤ e H³` (the zero-order hold), then
    `‖Δ - (H/2) • A_ς A‖ ≤ (K + √(card κ) C₃ + e) H²`  (`Consistent.norm_difference_sub_half_le`),
  which is eq. `eq:halfstep` in matrix form. That the brackets of the zero-order hold are of third
  order is not proved here (the library has no coefficients of the zero-order hold in this
  module's imports).
* **The total numerical damping** `ν = -tr Δ`, if no subsystem is its own partner
  (`Consistent.abs_numDamping_half_step_le`, `Consistent.abs_numDamping_partner_weights_le`):
    `|ν + H⁻¹ tr (F - 1 - H A₀ - ½H² A₀²) + (H/2) tr (A_ς A)| ≤ n (K + C₃) H²`,
  and with exact local maps `F = exp (H A₀)`
    `|ν + (H/2) tr (A_ς A)| ≤ n (K + C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H²`.
  (`tr (A_ς A)` for links with a kind is `trace_signedCoupling_mul_kind` of `LegRule`.)
* **Between subsystems that are not partners** (`x` supported on `s`, `y` on `t ≠ s`):
    `|⟪x, Δ y⟫ - (H/2) ⟪x, A_ς A y⟫| ≤ (K + C₃) H² ‖x‖ ‖y‖`      (`Consistent.difference_forced`),
  and with skew coupling (`A q p = -A p q` between different subsystems), for the numerical
  dissipation `Δ_R = -sym Δ` (`numDissipation`) and the numerical interconnection `Δ_J = skew Δ`
  (`numInterconnection`):
    `|⟪x, Δ_R y⟫ + (H/4) ⟪x, A (ς_s + ς_t) A y⟫| ≤ (K + C) H² ‖x‖ ‖y‖`,
    `|⟪x, Δ_J y⟫ - (H/4) ⟪x, A (ς_s - ς_t) A y⟫| ≤ (K + C) H² ‖x‖ ‖y‖`
  (`Consistent.numDissipation_block`, `Consistent.numInterconnection_block`): eq. `eq:parts` as a
  statement on the blocks, since `⟪x, A ς_u A y⟫ = xᵀ (Σ_k ς_uk A_sk A_kt) y`.
-/
import CoSimFoundations.DifferenceLead
import CoSimFoundations.HalfStep
import CoSimFoundations.LegRule

open NormedSpace Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-- `H⁻¹ · (H²/2) = H/2`. -/
theorem inv_mul_sq_half {H : ℝ} (hH : H ≠ 0) : H⁻¹ * (H ^ 2 / 2) = H / 2 := by
  rw [sq, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hH, one_mul]

/-- **The numerical interconnection** `Δ_J = skew Δ`, `Δ = Ã - A`, of a co-simulation with the
modified system `Ã` of a monolithic system `A` (the paper, Proposition `prop:basis`). -/
noncomputable def numInterconnection (A At : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • ((At - A) - (At - A)ᵀ)

/-- `Δ = Δ_J - Δ_R` (the paper, eq. `eq:split`). -/
theorem numInterconnection_sub_numDissipation (A At : Matrix (Fin n) (Fin n) ℝ) :
    numInterconnection A At - numDissipation A At = At - A := by
  rw [numInterconnection, numDissipation, sub_neg_eq_add, ← smul_add]
  have e : At - A - (At - A)ᵀ + (At - A + (At - A)ᵀ) = (2 : ℝ) • (At - A) := by
    rw [two_smul]
    abel
  rw [e, smul_smul]
  norm_num

/-- The matrix element of the numerical dissipation: `⟪x, Δ_R y⟫ = -½ (⟪x, Δ y⟫ + ⟪y, Δ x⟫)`. -/
theorem inner_numDissipation (A At : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (numDissipation A At) y⟫ =
      -(1 / 2) * (⟪x, opE (At - A) y⟫ + ⟪y, opE (At - A) x⟫) := by
  rw [numDissipation, ← neg_smul, inner_opE_smul, inner_opE_add,
    ← inner_opE_transpose (At - A) x y]

/-- The matrix element of the numerical interconnection:
`⟪x, Δ_J y⟫ = ½ (⟪x, Δ y⟫ - ⟪y, Δ x⟫)`. -/
theorem inner_numInterconnection (A At : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (numInterconnection A At) y⟫ =
      1 / 2 * (⟪x, opE (At - A) y⟫ - ⟪y, opE (At - A) x⟫) := by
  rw [numInterconnection, inner_opE_smul, inner_opE_sub (At - A),
    ← inner_opE_transpose (At - A) x y]

namespace HeldScheme

section Passage

variable {κ : Type*} {S : HeldScheme n κ} {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- **A consistent scheme has a modified system for small steps:** `exp (H • Ã) = X` for
`Ã = H⁻¹ • log X`, `H > 0` and `b H ≤ 1/3`. -/
theorem Consistent.exp_smul_modifiedSystem (h : S.Consistent A U H a b c) (hH : 0 < H)
    (hbH : b * H ≤ 1 / 3) : exp (H • modifiedSystem H S.X) = S.X :=
  CoSimFoundations.exp_smul_modifiedSystem hH.ne' (lt_of_le_of_lt (h.hb.trans hbH) (by norm_num))

/-- **A priori bound on the modified system of a consistent scheme:** `‖Ã‖ ≤ 3/2 · b` for
`H > 0` and `b H ≤ 1/3`. -/
theorem Consistent.norm_modifiedSystem_le (h : S.Consistent A U H a b c) (hH : 0 < H)
    (hbH : b * H ≤ 1 / 3) : ‖opE (modifiedSystem H S.X)‖ ≤ 3 / 2 * b :=
  norm_opE_modifiedSystem_le hH h.hb hbH

/-- **The a priori passage for a consistent scheme, one step:** `‖H • Δ - (X - U)‖ ≤ K H³`,
`K = 3/2 · c · max b (4/3 ‖A‖)`, for `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`. -/
theorem Consistent.norm_smul_difference_sub_le (h : S.Consistent A U H a b c) (hH : 0 < H)
    (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (H • difference A H S.X - (S.X - U))‖ ≤ diffLeadC b c ‖opE A‖ * H ^ 3 :=
  norm_opE_smul_difference_sub_le hH h.hU h.hb h.hc hbH hAH

/-- **The difference of a consistent scheme is its one-step error divided by the macro step, up
to `K H²`** (the paper, Theorem `thm:half`: `Δ = (X - U)/H + O(H²)`):
`‖Δ - H⁻¹ • (X - U)‖ ≤ K H²` for `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`. -/
theorem Consistent.norm_difference_sub_le (h : S.Consistent A U H a b c) (hH : 0 < H)
    (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (difference A H S.X - H⁻¹ • (S.X - U))‖ ≤ diffLeadC b c ‖opE A‖ * H ^ 2 :=
  norm_opE_difference_sub_le hH h.hU h.hb h.hc hbH hAH

/-- **The difference of a consistent scheme is of first order:** `‖Δ‖ ≤ (c + K H) H` and
`‖Δ‖ ≤ 3/2 · c H`, for `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`. -/
theorem Consistent.norm_difference_le (h : S.Consistent A U H a b c) (hH : 0 < H)
    (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (difference A H S.X)‖ ≤ (c + diffLeadC b c ‖opE A‖ * H) * H ∧
      ‖opE (difference A H S.X)‖ ≤ 3 / 2 * c * H :=
  ⟨norm_opE_difference_le hH h.hU h.hb h.hc hbH hAH,
    norm_opE_difference_le' hH h.hU h.hb h.hc hbH hAH⟩

/-- **The two parts of the difference between non-partners, numerical dissipation** (the paper,
Corollary `cor:blocks` (a), eq. `eq:parts`). For a consistent scheme with skew coupling,
`H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, subsystems `s ≠ t` that are not partners, `x` supported on
`s` and `y` on `t`:
`|⟪x, Δ_R y⟫ + (H/4) ⟪x, A (ς_s + ς_t) A y⟫| ≤ (K + C) H² ‖x‖ ‖y‖`, `C = forcedC a b c ‖A‖ H`. -/
theorem Consistent.numDissipation_block (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (numDissipation A (modifiedSystem H S.X)) y⟫ +
        H / 4 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫| ≤
      (diffLeadC b c ‖opE A‖ + forcedC a b c ‖opE A‖ H) * H ^ 2 * (‖x‖ * ‖y‖) := by
  have h1 := abs_le.1 (abs_inner_difference_sub_le hH h.hU h.hb h.hc hbH hAH x y)
  have h2 := abs_le.1 (abs_inner_difference_sub_le hH h.hU h.hb h.hc hbH hAH y x)
  rw [mul_comm ‖y‖ ‖x‖] at h2
  have h3 : |H⁻¹ * (⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫ -
      H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫)| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 2 * (‖x‖ * ‖y‖) := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hH), inv_mul_le_iff₀ hH]
    exact (h.forced_sym hskew hst hnp hnp' hx hy).trans_eq (by ring)
  rw [mul_sub, mul_add, ← mul_assoc, inv_mul_sq_half hH.ne'] at h3
  have h4 := abs_le.1 h3
  rw [inner_numDissipation, abs_le]
  change -((diffLeadC b c ‖opE A‖ + forcedC a b c ‖opE A‖ H) * H ^ 2 * (‖x‖ * ‖y‖)) ≤
      -(1 / 2) * (⟪x, opE (difference A H S.X) y⟫ + ⟪y, opE (difference A H S.X) x⟫) +
        H / 4 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫ ∧
    -(1 / 2) * (⟪x, opE (difference A H S.X) y⟫ + ⟪y, opE (difference A H S.X) x⟫) +
        H / 4 * ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫ ≤
      (diffLeadC b c ‖opE A‖ + forcedC a b c ‖opE A‖ H) * H ^ 2 * (‖x‖ * ‖y‖)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2]

/-- **The two parts of the difference between non-partners, numerical interconnection** (the paper,
Corollary `cor:blocks` (a), eq. `eq:parts`). Under the hypotheses of
`Consistent.numDissipation_block`:
`|⟪x, Δ_J y⟫ - (H/4) ⟪x, A (ς_s - ς_t) A y⟫| ≤ (K + C) H² ‖x‖ ‖y‖`, `C = forcedC a b c ‖A‖ H`. -/
theorem Consistent.numInterconnection_block (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (numInterconnection A (modifiedSystem H S.X)) y⟫ -
        H / 4 * ⟪x, opE (A * (S.sgn s - S.sgn t) * A) y⟫| ≤
      (diffLeadC b c ‖opE A‖ + forcedC a b c ‖opE A‖ H) * H ^ 2 * (‖x‖ * ‖y‖) := by
  have h1 := abs_le.1 (abs_inner_difference_sub_le hH h.hU h.hb h.hc hbH hAH x y)
  have h2 := abs_le.1 (abs_inner_difference_sub_le hH h.hU h.hb h.hc hbH hAH y x)
  rw [mul_comm ‖y‖ ‖x‖] at h2
  have h3 : |H⁻¹ * (⟪x, opE (S.X - U) y⟫ - ⟪y, opE (S.X - U) x⟫ -
      H ^ 2 / 2 * ⟪x, opE (A * (S.sgn s - S.sgn t) * A) y⟫)| ≤
      2 * forcedC a b c ‖opE A‖ H * H ^ 2 * (‖x‖ * ‖y‖) := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hH), inv_mul_le_iff₀ hH]
    exact (h.forced_antisym hskew hst hnp hnp' hx hy).trans_eq (by ring)
  rw [mul_sub, mul_sub, ← mul_assoc, inv_mul_sq_half hH.ne'] at h3
  have h4 := abs_le.1 h3
  rw [inner_numInterconnection, abs_le]
  change -((diffLeadC b c ‖opE A‖ + forcedC a b c ‖opE A‖ H) * H ^ 2 * (‖x‖ * ‖y‖)) ≤
      1 / 2 * (⟪x, opE (difference A H S.X) y⟫ - ⟪y, opE (difference A H S.X) x⟫) -
        H / 4 * ⟪x, opE (A * (S.sgn s - S.sgn t) * A) y⟫ ∧
    1 / 2 * (⟪x, opE (difference A H S.X) y⟫ - ⟪y, opE (difference A H S.X) x⟫) -
        H / 4 * ⟪x, opE (A * (S.sgn s - S.sgn t) * A) y⟫ ≤
      (diffLeadC b c ‖opE A‖ + forcedC a b c ‖opE A‖ H) * H ^ 2 * (‖x‖ * ‖y‖)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2]

end Passage

section HalfStep

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- The leading term of `X - U` divided by the macro step:
`H⁻¹ • halfStepLead = H⁻¹ • (the two brackets) + (H/2) • A_ς A`. -/
theorem halfStepLead_inv_smul (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : H ≠ 0) :
    H⁻¹ • S.halfStepLead A H =
      H⁻¹ • ((S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
        (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A))) +
      (H / 2) • (S.signedCoupling A * A) := by
  rw [halfStepLead, smul_add, smul_smul, inv_mul_sq_half hH]

variable {S} {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- The half-step relation for the difference, with the leading term of `HalfStep`:
`‖Δ - H⁻¹ • halfStepLead‖ ≤ (K + √(card κ) C₃) H²`. -/
theorem Consistent.norm_difference_sub_halfStepLead_le [Fintype κ]
    (h : S.Consistent A U H a b c) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (difference A H S.X - H⁻¹ • S.halfStepLead A H)‖ ≤
      (diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H) *
        H ^ 2 := by
  have e : difference A H S.X - H⁻¹ • S.halfStepLead A H =
      (difference A H S.X - H⁻¹ • (S.X - U)) + H⁻¹ • (S.X - U - S.halfStepLead A H) := by
    rw [smul_sub H⁻¹ (S.X - U)]
    abel
  have h1 := h.norm_difference_sub_le hH hbH hAH
  have h2 : ‖opE (H⁻¹ • (S.X - U - S.halfStepLead A H))‖ ≤
      Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 2 := by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le), inv_mul_le_iff₀ hH]
    exact h.norm_half_step_le.trans_eq (by ring)
  rw [e, opE_add]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- **The half-step relation for the difference** (the paper, Theorem `thm:half`, eq. `eq:half`
divided by `H`, with the a priori passage). For a consistent scheme with one held sample, in any
order of execution, `H > 0`, `b H ≤ 1/3` and `H ‖A‖ ≤ 1/4`:
`‖Δ - H⁻¹ • [(F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c)] - (H/2) • A_ς A‖`
`≤ (K + √(card κ) C₃) H²`, `K = diffLeadC b c ‖A‖`, `C₃ = reactionC a b c ‖A‖ H`. -/
theorem Consistent.norm_difference_half_step_le [Fintype κ] (h : S.Consistent A U H a b c)
    (hH : 0 < H) (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (difference A H S.X -
        H⁻¹ • ((S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
          (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A))) -
        (H / 2) • (S.signedCoupling A * A))‖ ≤
      (diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H) *
        H ^ 2 := by
  have h1 := h.norm_difference_sub_halfStepLead_le hH hbH hAH
  rwa [S.halfStepLead_inv_smul A hH.ne', ← sub_sub] at h1

/-- **The modified system of a hold whose two brackets are of third order** (the paper, eq.
`eq:halfstep` in matrix form: the zero-order hold). If in addition
`‖(F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c)‖ ≤ e H³`, then
`‖Δ - (H/2) • A_ς A‖ ≤ (K + √(card κ) C₃ + e) H²`: the modified system is the monolithic system
with every partner output shifted by half a macro step, up to the order `H²`. -/
theorem Consistent.norm_difference_sub_half_le [Fintype κ] {e : ℝ}
    (h : S.Consistent A U H a b c) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (he : ‖opE ((S.F - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
      (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)))‖ ≤
      e * H ^ 3) :
    ‖opE (difference A H S.X - (H / 2) • (S.signedCoupling A * A))‖ ≤
      (diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H + e) *
        H ^ 2 := by
  have h1 := h.norm_difference_half_step_le hH hbH hAH
  have h2 : ‖opE (H⁻¹ • ((S.F - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
      (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A))))‖ ≤
      e * H ^ 2 := by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le), inv_mul_le_iff₀ hH]
    exact he.trans_eq (by ring)
  have h3 := (norm_add_le _ _).trans (add_le_add h1 h2)
  rw [← opE_add] at h3
  refine le_of_eq_of_le (congrArg (fun T => ‖opE T‖) ?_) (h3.trans_eq (by ring))
  abel

/-- **Between subsystems that are not partners, the difference is the half-step term** (the paper,
Corollary `cor:blocks` (a), eq. `eq:forced` divided by `H`). For `H > 0`, `b H ≤ 1/3`,
`H ‖A‖ ≤ 1/4`, `x` supported on `s` and `y` on `t ≠ s`, not a partner of `s`:
`|⟪x, Δ y⟫ - (H/2) ⟪x, A_ς A y⟫| ≤ (K + C₃) H² ‖x‖ ‖y‖`. -/
theorem Consistent.difference_forced (h : S.Consistent A U H a b c) (hH : 0 < H)
    (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (difference A H S.X) y⟫ - H / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫| ≤
      (diffLeadC b c ‖opE A‖ + reactionC a b c ‖opE A‖ H) * H ^ 2 * (‖x‖ * ‖y‖) := by
  have h1 := abs_le.1 (abs_inner_difference_sub_le hH h.hU h.hb h.hc hbH hAH x y)
  have h3 : |H⁻¹ * (⟪x, opE (S.X - U) y⟫ -
      H ^ 2 / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫)| ≤
      reactionC a b c ‖opE A‖ H * H ^ 2 * (‖x‖ * ‖y‖) := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hH), inv_mul_le_iff₀ hH]
    exact (h.half_step_forced hst hnp hx hy).trans_eq (by ring)
  rw [mul_sub, ← mul_assoc, inv_mul_sq_half hH.ne'] at h3
  have h4 := abs_le.1 h3
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h4.1, h4.2]

/-- **The total numerical damping of a consistent scheme** (the paper, Definition `def:props` (iii),
`ν = -tr Δ`, and the trace of eq. `eq:half`). If no subsystem is its own partner, `H > 0`,
`b H ≤ 1/3` and `H ‖A‖ ≤ 1/4`, in any order of execution and for every coupling:
`|ν + H⁻¹ tr (F - 1 - H A₀ - ½H² A₀²) + (H/2) tr (A_ς A)| ≤ n (K + C₃) H²`. -/
theorem Consistent.abs_numDamping_half_step_le (h : S.Consistent A U H a b c)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p)) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    |numDamping A H S.X +
        H⁻¹ * Matrix.trace (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
        H / 2 * Matrix.trace (S.signedCoupling A * A)| ≤
      (n : ℝ) * (diffLeadC b c ‖opE A‖ + reactionC a b c ‖opE A‖ H) * H ^ 2 := by
  have h1 := abs_le.1 (abs_numDamping_add_trace_le hH h.hU h.hb h.hc hbH hAH)
  have h3 : |H⁻¹ * (Matrix.trace (S.X - U) -
      Matrix.trace (S.F - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) -
      H ^ 2 / 2 * Matrix.trace (S.signedCoupling A * A))| ≤
      (n : ℝ) * reactionC a b c ‖opE A‖ H * H ^ 2 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hH), inv_mul_le_iff₀ hH]
    exact (h.half_step_trace hself).trans_eq (by ring)
  rw [mul_sub, mul_sub, ← mul_assoc, inv_mul_sq_half hH.ne'] at h3
  have h4 := abs_le.1 h3
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h4.1, h4.2]

/-- **The total numerical damping with partner weights only** (the paper, eq. `eq:negdamping`, as a
statement on `ν = -tr Δ`). If no subsystem is its own partner and the local maps are exact,
`F = exp (H A₀)`, then for `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, in any order of execution and for
every coupling: `|ν + (H/2) tr (A_ς A)| ≤ n (K + C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H²`. The coefficients
of the partner samples do not enter. -/
theorem Consistent.abs_numDamping_partner_weights_le (h : S.Consistent A U H a b c)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hF : S.F = exp (H • S.blockDiag A)) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    |numDamping A H S.X + H / 2 * Matrix.trace (S.signedCoupling A * A)| ≤
      (n : ℝ) * (diffLeadC b c ‖opE A‖ + reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 := by
  have h1 := abs_le.1 (abs_numDamping_add_trace_le hH h.hU h.hb h.hc hbH hAH)
  have h3 : |H⁻¹ * (Matrix.trace (S.X - U) -
      H ^ 2 / 2 * Matrix.trace (S.signedCoupling A * A))| ≤
      (n : ℝ) * (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hH), inv_mul_le_iff₀ hH]
    exact (h.trace_partner_weights hself hF).trans_eq (by ring)
  rw [mul_sub, ← mul_assoc, inv_mul_sq_half hH.ne'] at h3
  have h4 := abs_le.1 h3
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h4.1, h4.2]

end HalfStep

end HeldScheme

end CoSimFoundations
