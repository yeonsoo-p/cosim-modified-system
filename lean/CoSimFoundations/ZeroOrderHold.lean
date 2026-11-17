/-
The zero-order hold is a consistent scheme, with explicit constants; its one-step map and its
modified system without a hypothesis of consistency (the paper, Section `sec:half`, the
definition of a consistent family of holds, and Theorem `thm:half` with eqs. `eq:half`,
`eq:halfstep`: "For the zero-order hold the first two terms vanish, and its modified system is,
up to terms of the order `H²`, …").

`HalfStepZOH` defines the zero-order hold as a scheme, `S.zoh A hA H` (`F = e^{H A₀}`, old samples
`zohOld`, new samples `zohNew`, together `G°C = (∫₀ᴴ e^{s A₀} ds) A_c`), and proves its
statements under the hypothesis `(S.zoh A hA H).Consistent A U H a b c`. Here the hypothesis is
proved. Notation: `α = ‖A‖`, `α₀ = ‖A₀‖`, `γ = ‖A_c‖` (spectral norms `‖opE ·‖`),
`σ = √(card κ)`, `κ` the type of the subsystems.

1. **Norms of the parts** (`norm_opE_blockDiag_le`, `norm_opE_coupling_le_two`): the
   block-diagonal part is a pinching, `α₀ ≤ α` (`⟪x, A₀ y⟫ = Σ_s ⟪x_s, A y_s⟫` and
   Cauchy-Schwarz over the subsystems), hence `γ ≤ 2α`.
   **Coefficients of the hold** for `H ≥ 0`, `H α₀ ≤ 1/4` (`norm_opE_zohCoupling_sub_le`,
   `norm_opE_zohCoupling_le`): `‖G°C - H A_c‖ ≤ 5/9 · α₀ γ H²`, `‖G°C‖ ≤ 7/6 · γ H`.
   **New samples** (`norm_opE_zohNew_le`): `‖zohNew‖ ≤ σ ‖G°C‖`. In the rows of a subsystem `s`,
   `zohNew = G°C · early_s`; the factor `σ` is the price of cutting a matrix along the stages
   (the spectral norm of a triangular truncation is not bounded by the norm of the matrix).
   **Any scheme with one held sample** (`norm_X_sub_one_le`, `norm_X_sub_step_le`): if
   `‖N‖ ≤ 1/2`, then `‖X - 1‖ ≤ 2 (‖F - 1‖ + ‖M + N‖)`, and for `A = A₀ + A_c`
   `‖X - U‖ ≤ ‖F - 1 - H A₀‖ + ‖M + N - H A_c‖ + ‖N‖ ‖X - 1‖ + ‖U - 1 - H A‖`
   (both from `X = F + M + N X`).
   **The zero-order hold is consistent** (`zoh_consistent`): for `0 ≤ H`, `H α ≤ 1/4` and
   `σ H α ≤ 1/6`, `(S.zoh A hA H).Consistent A (e^{HA}) H a b c`, that is `‖N‖ ≤ a H`,
   `‖X - 1‖ ≤ b H`, `‖X - e^{HA}‖ ≤ c H²`, with
     `a = 3 σ α` (`zohConsA`),  `b = 8 α` (`zohConsB`),  `c = 3 (1 + 6σ) α²` (`zohConsC`).
   The paper's definition also has `F = 1 + O(H)` and `G = O(H)`:
   `‖F - 1‖ ≤ 4/3 · α H`, `‖M + N‖ ≤ 7/3 · α H` for `H α ≤ 1/4` (`norm_zoh_local_samples_le`).
   (`zoh_consistent_of_new_le` has any `σ ≥ 0` with `‖zohNew‖ ≤ σ ‖G°C‖`. If there is a state,
   `H α ≤ σ H α`, `mul_norm_le_sqrt_card_mul`, so that `σ H α ≤ 1/6` implies `H α ≤ 1/6`.)
   Hence `norm_zoh_sub_le` of `HalfStepZOH` without its hypothesis (`norm_zoh_step_sub_le`):
     `‖X - e^{HA} - ½H² A_ς A‖ ≤ (2/3 + 4σ + 53σ² + 54σ³) α³ H³`   (`zohStepK`).

2. **Equation (halfstep)** (`norm_zoh_difference_sub_half_le`): for `0 < H`, `H α ≤ 1/24` (so
   that `b H ≤ 1/3`, the range of `DifferenceLead`) and `σ H α ≤ 1/6`, the difference
   `Δ = Ã - A` of the zero-order hold obeys
     `‖Δ - (H/2) A_ς A‖ ≤ (37 + 220σ + 53σ² + 54σ³) α³ H²`   (`zohDiffK`).
   The two brackets of `Consistent.norm_difference_sub_half_le` are the Taylor remainders of
   `e^{H A₀}` and of `G°C` (`norm_zoh_brackets_le`, from `norm_exp_blockDiag_bracket_le` and
   `norm_zohCoupling_bracket_le`).

The constants in `α` and `σ` alone come from `e^{H α} ≤ e^{1/4} ≤ 4/3`, `α₀ ≤ α`, `γ ≤ 2α`
(`reactionC_zohCons_le`, `zohCons_constants_le`, `zoh_taylor_constants_le`). The total numerical
damping and the staggered readout of the zero-order hold are in `ZeroOrderHoldDamping`.
-/
import CoSimFoundations.HalfStepZOH
import CoSimFoundations.DifferenceLeadHalfStep

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

namespace HeldScheme

/-! ### The constants -/

/-- The constant `a` of the consistency of the zero-order hold, `‖N‖ ≤ a H`: `a = 3 σ α`,
`σ = √(card κ)`, `α = ‖A‖`. -/
noncomputable def zohConsA (σ α : ℝ) : ℝ := 3 * σ * α

/-- The constant `b` of the consistency of the zero-order hold, `‖X - 1‖ ≤ b H`: `b = 8 α`. -/
noncomputable def zohConsB (α : ℝ) : ℝ := 8 * α

/-- The constant `c` of the consistency of the zero-order hold, `‖X - U‖ ≤ c H²`:
`c = 3 (1 + 6σ) α²`. -/
noncomputable def zohConsC (σ α : ℝ) : ℝ := 3 * (1 + 6 * σ) * α ^ 2

/-- The constant of the one-step map of the zero-order hold,
`‖X - U - ½H² A_ς A‖ ≤ zohStepK σ α · H³`: `(2/3 + 4σ + 53σ² + 54σ³) α³`. -/
noncomputable def zohStepK (σ α : ℝ) : ℝ := (2 / 3 + 4 * σ + 53 * σ ^ 2 + 54 * σ ^ 3) * α ^ 3

/-- The constant of the difference of the zero-order hold,
`‖Δ - (H/2) A_ς A‖ ≤ zohDiffK σ α · H²`: `(37 + 220σ + 53σ² + 54σ³) α³`. -/
noncomputable def zohDiffK (σ α : ℝ) : ℝ := (37 + 220 * σ + 53 * σ ^ 2 + 54 * σ ^ 3) * α ^ 3

/-- The constant of the total numerical damping of the zero-order hold,
`|ν + (H/2) tr (A_ς A)| ≤ n · zohDampK σ α · H²`: `(41 + 269σ + 54σ²) α³`. -/
noncomputable def zohDampK (σ α : ℝ) : ℝ := (41 + 269 * σ + 54 * σ ^ 2) * α ^ 3

/-- The constant `C₃` of the reaction with the constants of the zero-order hold, for
`e^{Hα} ≤ 4/3`: `C₃ ≤ (35/9 + 53σ + 54σ²) α³`. -/
theorem reactionC_zohCons_le {σ α H : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hE : Real.exp (H * α) ≤ 4 / 3) :
    reactionC (zohConsA σ α) (zohConsB α) (zohConsC σ α) α H ≤
      (35 / 9 + 53 * σ + 54 * σ ^ 2) * α ^ 3 := by
  have h1 : α ^ 3 * Real.exp (H * α) ≤ α ^ 3 * (4 / 3) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have h2 : σ * α ^ 3 * Real.exp (H * α) ≤ σ * α ^ 3 * (4 / 3) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  unfold reactionC reactionConst couplingConst zohConsA zohConsB zohConsC
  linarith

/-- The three constants of the zero-order hold bound the constants of `HalfStepZOH` and
`DifferenceLeadHalfStep`: with `C₃ = reactionC a b c α H`, `K = diffLeadC b c α`, `e^{Hα} ≤ 4/3`,
a bound `Z ≤ 2/3 · α³` of the two Taylor brackets and a bound `W ≤ 2/9 · α³` of the local one,
`σ C₃ + Z ≤ zohStepK`, `K + σ C₃ + Z ≤ zohDiffK` and `K + C₃ + W ≤ zohDampK`. -/
theorem zohCons_constants_le {σ α H Z W : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hE : Real.exp (H * α) ≤ 4 / 3) (hZ : Z ≤ 2 / 3 * α ^ 3) (hW : W ≤ 2 / 9 * α ^ 3) :
    (σ * reactionC (zohConsA σ α) (zohConsB α) (zohConsC σ α) α H + Z ≤ zohStepK σ α) ∧
      (diffLeadC (zohConsB α) (zohConsC σ α) α +
        σ * reactionC (zohConsA σ α) (zohConsB α) (zohConsC σ α) α H + Z ≤ zohDiffK σ α) ∧
      (diffLeadC (zohConsB α) (zohConsC σ α) α +
        reactionC (zohConsA σ α) (zohConsB α) (zohConsC σ α) α H + W ≤ zohDampK σ α) := by
  have hR := reactionC_zohCons_le hσ hα hE
  have hD : diffLeadC (zohConsB α) (zohConsC σ α) α = 36 * (1 + 6 * σ) * α ^ 3 := by
    unfold diffLeadC zohConsB zohConsC
    rw [max_eq_left (by linarith)]
    ring
  have hσR := mul_le_mul_of_nonneg_left hR hσ
  have p1 : 0 ≤ α ^ 3 := by positivity
  have p2 : 0 ≤ σ * α ^ 3 := by positivity
  rw [hD]
  unfold zohStepK zohDiffK zohDampK
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- For `H ‖A‖ ≤ 1/24`: `H ‖A‖ ≤ 1/4` and `b H ≤ 1/3` with the constant `b = 8 ‖A‖` of the
zero-order hold. -/
theorem zohConsB_mul_le {α H : ℝ} (h : H * α ≤ 1 / 24) :
    H * α ≤ 1 / 4 ∧ zohConsB α * H ≤ 1 / 3 := by
  unfold zohConsB
  constructor <;> linarith

/-! ### Every scheme with one held sample -/

section General

variable {κ : Type*} (S : HeldScheme n κ)

/-- **The one-step map near the identity.** For every scheme with one held sample, if
`‖N‖ ≤ 1/2`, then `‖X - 1‖ ≤ 2 (‖F - 1‖ + ‖M + N‖)`: from
`X - 1 = (F - 1) + (M + N) + N (X - 1)`. -/
theorem norm_X_sub_one_le (hN : ‖opE S.N‖ ≤ 1 / 2) :
    ‖opE (S.X - 1)‖ ≤ 2 * (‖opE (S.F - 1)‖ + ‖opE (S.M + S.N)‖) := by
  have e : S.X - 1 = (S.F - 1) + (S.M + S.N) + S.N * (S.X - 1) :=
    calc S.X - 1 = (S.F + S.M + S.N * S.X) - 1 := by rw [← S.hX]
      _ = (S.F - 1) + (S.M + S.N) + S.N * (S.X - 1) := by
        rw [mul_sub, mul_one]
        abel
  have h := norm_add₃_le (a := opE (S.F - 1)) (b := opE (S.M + S.N))
    (c := opE (S.N * (S.X - 1)))
  rw [← opE_add, ← opE_add, ← e] at h
  have h1 := norm_opE_mul_le S.N (S.X - 1)
  have h2 := mul_le_mul_of_nonneg_right hN (norm_nonneg (opE (S.X - 1)))
  linarith

/-- **The one-step error from the parts.** For every scheme with one held sample, matrices `A₀`,
`A_c` and `U`:
`‖X - U‖ ≤ ‖F - (1 + H A₀)‖ + ‖M + N - H A_c‖ + ‖N‖ ‖X - 1‖ + ‖U - (1 + H (A₀ + A_c))‖`. -/
theorem norm_X_sub_step_le (A₀ Ac U : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    ‖opE (S.X - U)‖ ≤ ‖opE (S.F - (1 + H • A₀))‖ + ‖opE (S.M + S.N - H • Ac)‖ +
      ‖opE S.N‖ * ‖opE (S.X - 1)‖ + ‖opE (U - (1 + H • (A₀ + Ac)))‖ := by
  have e : S.X - U = (S.F - (1 + H • A₀)) + (S.M + S.N - H • Ac) + S.N * (S.X - 1) -
      (U - (1 + H • (A₀ + Ac))) :=
    calc S.X - U = (S.F + S.M + S.N * S.X) - U := by rw [← S.hX]
      _ = (S.F - (1 + H • A₀)) + (S.M + S.N - H • Ac) + S.N * (S.X - 1) -
          (U - (1 + H • (A₀ + Ac))) := by
        rw [mul_sub, mul_one, smul_add]
        abel
  have h := norm_sub_le (opE ((S.F - (1 + H • A₀)) + (S.M + S.N - H • Ac) + S.N * (S.X - 1)))
    (opE (U - (1 + H • (A₀ + Ac))))
  rw [← opE_sub, ← e] at h
  have h3 := norm_add₃_le (a := opE (S.F - (1 + H • A₀))) (b := opE (S.M + S.N - H • Ac))
    (c := opE (S.N * (S.X - 1)))
  rw [← opE_add, ← opE_add] at h3
  have h1 := norm_opE_mul_le S.N (S.X - 1)
  linarith

include S in
/-- If there is a state, there is a subsystem: `H ‖A‖ ≤ √(card κ) · H ‖A‖` for `H ≥ 0` (without
states both sides vanish). So the condition `√(card κ) · H ‖A‖ ≤ r` implies `H ‖A‖ ≤ r`. -/
theorem mul_norm_le_sqrt_card_mul [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ}
    (hH : 0 ≤ H) : H * ‖opE A‖ ≤ Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hA0 : opE A = 0 := by
      rw [Subsingleton.elim A 0]
      exact map_zero _
    rw [hA0, norm_zero, mul_zero, mul_zero]
  · have hc : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.2 ⟨S.sub ⟨0, hpos⟩⟩
    have h1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card κ) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hc
    exact le_mul_of_one_le_left (mul_nonneg hH (norm_nonneg _)) h1

end General

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The norms of the parts of `A` -/

/-- The matrix element of the block-diagonal part, subsystem by subsystem:
`⟪x, A₀ y⟫ = Σ_s ⟪x_s, A y_s⟫`. -/
theorem inner_blockDiag_eq_sum [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.blockDiag A) y⟫ = ∑ s, ⟪opE (S.mask s) x, opE A (opE (S.mask s) y)⟫ := by
  rw [S.inner_eq_sum_parts x (opE (S.blockDiag A) y)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← opE_mul_apply]
  refine inner_opE_congr_row (S.opE_mask_support s x) y fun p q hp => ?_
  have e : (A * S.mask s) p q = A p q * (if S.sub q = s then 1 else 0) := by
    rw [mask, Matrix.mul_diagonal]
  rw [e, S.blockDiag_apply, hp]
  by_cases hq : S.sub q = s
  · rw [ite_eq_left hq.symm, ite_eq_left hq, mul_one]
  · rw [ite_eq_right fun e' => hq e'.symm, ite_eq_right hq, mul_zero]

/-- **The block-diagonal part is not larger than the matrix:** `‖A₀‖ ≤ ‖A‖` in the spectral norm
(a pinching; Cauchy-Schwarz over the subsystems). -/
theorem norm_opE_blockDiag_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (S.blockDiag A)‖ ≤ ‖opE A‖ := by
  refine norm_opE_le_of_abs_inner_le (norm_nonneg _) fun x y => ?_
  rw [S.inner_blockDiag_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ s ∈ (Finset.univ : Finset κ),
      |⟪opE (S.mask s) x, opE A (opE (S.mask s) y)⟫| ≤
        ‖opE A‖ * (‖opE (S.mask s) x‖ * ‖opE (S.mask s) y‖) :=
    fun s _ => abs_inner_opE_le A _ _
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset κ)
    (fun s => ‖opE (S.mask s) x‖) (fun s => ‖opE (S.mask s) y‖)
  rw [S.sum_norm_sq_parts, S.sum_norm_sq_parts, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at h2
  exact h2

/-- **The coupling part is at most twice the matrix:** `‖A_c‖ ≤ 2 ‖A‖`. -/
theorem norm_opE_coupling_le_two [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (S.coupling A)‖ ≤ 2 * ‖opE A‖ := by
  have h1 := S.norm_opE_coupling_le A
  have h2 := S.norm_opE_blockDiag_le A
  linarith

/-- **The parts of `A` in `‖A‖` alone:** `‖A₀‖ ≤ ‖A‖`, `‖A_c‖ ≤ 2 ‖A‖` and, for `H ≥ 0` and
`H ‖A‖ ≤ 1/4`, `H ‖A₀‖ ≤ 1/4` and `e^{H‖A₀‖} ≤ 4/3`. -/
theorem norm_parts_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (S.blockDiag A)‖ ≤ ‖opE A‖ ∧ ‖opE (S.coupling A)‖ ≤ 2 * ‖opE A‖ ∧
      H * ‖opE (S.blockDiag A)‖ ≤ 1 / 4 ∧ Real.exp (H * ‖opE (S.blockDiag A)‖) ≤ 4 / 3 := by
  have h0 : ‖opE (S.blockDiag A)‖ ≤ ‖opE A‖ := S.norm_opE_blockDiag_le A
  have hx : H * ‖opE (S.blockDiag A)‖ ≤ 1 / 4 := (mul_le_mul_of_nonneg_left h0 hH).trans hAH
  exact ⟨h0, S.norm_opE_coupling_le_two A, hx, (Real.exp_le_exp.2 hx).trans exp_quarter_le⟩

/-! ### The coefficients of the zero-order hold -/

/-- **The coefficients of the zero-order hold to first order:** for `H ≥ 0` and `H ‖A₀‖ ≤ 1/4`,
`‖G°C - H A_c‖ ≤ 5/9 · ‖A₀‖ ‖A_c‖ H²`. -/
theorem norm_opE_zohCoupling_sub_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hx : H * ‖opE (S.blockDiag A)‖ ≤ 1 / 4) :
    ‖opE (S.zohCoupling A H - H • S.coupling A)‖ ≤
      5 / 9 * ‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖ * H ^ 2 := by
  have hE : Real.exp (H * ‖opE (S.blockDiag A)‖) ≤ 4 / 3 :=
    (Real.exp_le_exp.2 hx).trans exp_quarter_le
  have h1 := S.norm_zohCoupling_bracket_le A hH
  have h2 : ‖opE ((H ^ 2 / 2) • (S.blockDiag A * S.coupling A))‖ ≤
      H ^ 2 / 2 * (‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖) := by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg (by positivity), opE_mul]
    exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
  have h3 : H * ‖opE (S.blockDiag A)‖ * Real.exp (H * ‖opE (S.blockDiag A)‖) ≤
      1 / 4 * (4 / 3) := mul_le_mul hx hE (Real.exp_nonneg _) (by norm_num)
  have h4 : ‖opE (S.blockDiag A)‖ ^ 2 / 6 * ‖opE (S.coupling A)‖ *
      Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 ≤
      ‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖ * H ^ 2 / 18 :=
    calc ‖opE (S.blockDiag A)‖ ^ 2 / 6 * ‖opE (S.coupling A)‖ *
          Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3
        = ‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖ * H ^ 2 / 6 *
          (H * ‖opE (S.blockDiag A)‖ * Real.exp (H * ‖opE (S.blockDiag A)‖)) := by ring
      _ ≤ ‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖ * H ^ 2 / 6 * (1 / 4 * (4 / 3)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖ * H ^ 2 / 18 := by ring
  have h5 := norm_add_le
    (opE (S.zohCoupling A H - H • S.coupling A -
      (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)))
    (opE ((H ^ 2 / 2) • (S.blockDiag A * S.coupling A)))
  rw [← opE_add, sub_add_cancel] at h5
  linarith

/-- **The size of the coefficients of the zero-order hold:** for `H ≥ 0` and `H ‖A₀‖ ≤ 1/4`,
`‖G°C‖ ≤ 7/6 · ‖A_c‖ H`. -/
theorem norm_opE_zohCoupling_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hx : H * ‖opE (S.blockDiag A)‖ ≤ 1 / 4) :
    ‖opE (S.zohCoupling A H)‖ ≤ 7 / 6 * ‖opE (S.coupling A)‖ * H := by
  have h1 := S.norm_opE_zohCoupling_sub_le A hH hx
  have h2 : ‖opE (H • S.coupling A)‖ = H * ‖opE (S.coupling A)‖ := by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg hH]
  have h3 := norm_add_le (opE (S.zohCoupling A H - H • S.coupling A)) (opE (H • S.coupling A))
  rw [← opE_add, sub_add_cancel] at h3
  have h4 : ‖opE (S.coupling A)‖ * H * (H * ‖opE (S.blockDiag A)‖) ≤
      ‖opE (S.coupling A)‖ * H * (1 / 4) := mul_le_mul_of_nonneg_left hx (by positivity)
  have p : 0 ≤ ‖opE (S.coupling A)‖ * H := by positivity
  linarith

/-- **The coefficients of the new samples:** `‖zohNew‖ ≤ √(card κ) ‖G°C‖`. In the rows of a
subsystem `s` the part of `G°C` on the new samples is `G°C` times the mask of the stages before
`s`. -/
theorem norm_opE_zohNew_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    ‖opE (S.zohNew A H)‖ ≤ Real.sqrt (Fintype.card κ) * ‖opE (S.zohCoupling A H)‖ := by
  refine S.norm_opE_le_of_rows (norm_nonneg _) fun s x hx y => ?_
  have e : ⟪x, opE (S.zohNew A H) y⟫ = ⟪x, opE (S.zohCoupling A H * S.early s) y⟫ := by
    refine inner_opE_congr_row hx y fun p q hp => ?_
    have e' : (S.zohCoupling A H * S.early s) p q =
        S.zohCoupling A H p q * (if S.stage (S.sub q) < S.stage s then 1 else 0) := by
      rw [early, Matrix.mul_diagonal]
    rw [e', ← hp]
    by_cases hs : S.stage (S.sub q) < S.stage (S.sub p) <;> simp [zohNew, hs]
  rw [e]
  exact (abs_inner_opE_le _ x y).trans (mul_le_mul_of_nonneg_right
    (norm_opE_mul_le_of_norm_le_one _ (S.norm_opE_early_le s)) (by positivity))

/-- **The two Taylor brackets of the zero-order hold are of third order:** for `H ≥ 0`,
`‖(e^{H A₀} - 1 - H A₀ - ½H² A₀²) + (G°C - H A_c - ½H² A₀ A_c)‖ ≤ zohC ‖A₀‖ ‖A_c‖ H · H³`. -/
theorem norm_zoh_brackets_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE ((NormedSpace.exp (H • S.blockDiag A) - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
      (S.zohCoupling A H - H • S.coupling A -
        (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)))‖ ≤
      zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H * H ^ 3 := by
  rw [opE_add]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (S.norm_exp_blockDiag_bracket_le A hH)
    (S.norm_zohCoupling_bracket_le A hH)).trans_eq ?_
  rw [zohC]
  ring

/-- The exponentials and the Taylor constants of the zero-order hold in `‖A‖` alone: for
`H ≥ 0` and `H ‖A‖ ≤ 1/4`, `e^{H‖A‖} ≤ 4/3`, `zohC ‖A₀‖ ‖A_c‖ H ≤ 2/3 · ‖A‖³` and
`‖A₀‖³/6 · e^{H‖A₀‖} ≤ 2/9 · ‖A‖³`. -/
theorem zoh_taylor_constants_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    Real.exp (H * ‖opE A‖) ≤ 4 / 3 ∧
      zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H ≤ 2 / 3 * ‖opE A‖ ^ 3 ∧
      ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) ≤
        2 / 9 * ‖opE A‖ ^ 3 := by
  obtain ⟨h0, hγ, -, hE₀⟩ := S.norm_parts_le A hH hAH
  have h3 : ‖opE (S.blockDiag A)‖ ^ 3 ≤ ‖opE A‖ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h0 3
  have h2 : ‖opE (S.blockDiag A)‖ ^ 2 * ‖opE (S.coupling A)‖ ≤ ‖opE A‖ ^ 2 * (2 * ‖opE A‖) :=
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h0 2) hγ (norm_nonneg _) (by positivity)
  refine ⟨(Real.exp_le_exp.2 hAH).trans exp_quarter_le, ?_, ?_⟩
  · rw [zohC]
    calc (‖opE (S.blockDiag A)‖ ^ 3 / 6 + ‖opE (S.blockDiag A)‖ ^ 2 / 6 * ‖opE (S.coupling A)‖) *
          Real.exp (H * ‖opE (S.blockDiag A)‖)
        ≤ ‖opE A‖ ^ 3 / 2 * (4 / 3) :=
          mul_le_mul (by linarith) hE₀ (Real.exp_nonneg _) (by positivity)
      _ = 2 / 3 * ‖opE A‖ ^ 3 := by ring
  · calc ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)
        ≤ ‖opE A‖ ^ 3 / 6 * (4 / 3) :=
          mul_le_mul (by linarith) hE₀ (Real.exp_nonneg _) (by positivity)
      _ = 2 / 9 * ‖opE A‖ ^ 3 := by ring

/-- **The constants of the zero-order hold in `σ` and `‖A‖` alone:** for `H ≥ 0`, `H ‖A‖ ≤ 1/4`
and `σ ≥ 0`, the three bounds of `zohCons_constants_le` hold with the Taylor constants of the
zero-order hold, `Z = zohC ‖A₀‖ ‖A_c‖ H` and `W = ‖A₀‖³/6 · e^{H‖A₀‖}`. -/
theorem zoh_constants_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) {H σ : ℝ} (hH : 0 ≤ H)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (hσ : 0 ≤ σ) :
    (σ * reactionC (zohConsA σ ‖opE A‖) (zohConsB ‖opE A‖) (zohConsC σ ‖opE A‖) ‖opE A‖ H +
        zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H ≤ zohStepK σ ‖opE A‖) ∧
      (diffLeadC (zohConsB ‖opE A‖) (zohConsC σ ‖opE A‖) ‖opE A‖ +
        σ * reactionC (zohConsA σ ‖opE A‖) (zohConsB ‖opE A‖) (zohConsC σ ‖opE A‖) ‖opE A‖ H +
        zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H ≤ zohDiffK σ ‖opE A‖) ∧
      (diffLeadC (zohConsB ‖opE A‖) (zohConsC σ ‖opE A‖) ‖opE A‖ +
        reactionC (zohConsA σ ‖opE A‖) (zohConsB ‖opE A‖) (zohConsC σ ‖opE A‖) ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) ≤
          zohDampK σ ‖opE A‖) := by
  obtain ⟨h1, h2, h3⟩ := S.zoh_taylor_constants_le A hH hAH
  exact zohCons_constants_le hσ (norm_nonneg _) h1 h2 h3

/-! ### The zero-order hold is consistent -/

/-- **The local maps and the coefficients of the samples of the zero-order hold are `1 + O(H)`
and `O(H)`** (the paper, Section `sec:half`: "`F = I + O(H)`, `G = O(H)`"). For `0 ≤ H` and
`H ‖A‖ ≤ 1/4`: `‖e^{H A₀} - 1‖ ≤ 4/3 · ‖A‖ H` and `‖G°C‖ ≤ 7/3 · ‖A‖ H`. -/
theorem norm_zoh_local_samples_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ}
    (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (NormedSpace.exp (H • S.blockDiag A) - 1)‖ ≤ 4 / 3 * ‖opE A‖ * H ∧
      ‖opE (S.zohCoupling A H)‖ ≤ 7 / 3 * ‖opE A‖ * H := by
  obtain ⟨h0, hγ, hx, hE₀⟩ := S.norm_parts_le A hH hAH
  constructor
  · refine (norm_opE_exp_sub_one_le (S.blockDiag A) hH).trans ?_
    calc ‖opE (S.blockDiag A)‖ * Real.exp (H * ‖opE (S.blockDiag A)‖) * H
        ≤ ‖opE A‖ * (4 / 3) * H :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h0 hE₀ (Real.exp_nonneg _) (norm_nonneg _)) hH
      _ = 4 / 3 * ‖opE A‖ * H := by ring
  · have h1 := S.norm_opE_zohCoupling_le A hH hx
    have h2 := mul_le_mul_of_nonneg_right hγ hH
    linarith

/-- **The zero-order hold is consistent, for any bound of the cut along the stages.** Let
`‖zohNew‖ ≤ σ ‖G°C‖` (`σ = √(card κ)` always does, `norm_opE_zohNew_le`). For `0 ≤ H`,
`H ‖A‖ ≤ 1/4` and `σ H ‖A‖ ≤ 1/6` the zero-order hold `S.zoh A hA H` is consistent with
`‖N‖ ≤ 3σ‖A‖ · H`, `‖X - 1‖ ≤ 8‖A‖ · H`, `‖X - e^{HA}‖ ≤ 3 (1 + 6σ) ‖A‖² · H²`. -/
theorem zoh_consistent_of_new_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H σ : ℝ}
    (hH : 0 ≤ H) (hσ0 : 0 ≤ σ)
    (hnew : ‖opE (S.zohNew A H)‖ ≤ σ * ‖opE (S.zohCoupling A H)‖)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (hσ : σ * (H * ‖opE A‖) ≤ 1 / 6) :
    (S.zoh A hA H).Consistent A (NormedSpace.exp (H • A)) H (zohConsA σ ‖opE A‖)
      (zohConsB ‖opE A‖) (zohConsC σ ‖opE A‖) := by
  have hα : 0 ≤ ‖opE A‖ := norm_nonneg _
  obtain ⟨h0, hγ, hx, hE₀⟩ := S.norm_parts_le A hH hAH
  have hE : Real.exp (H * ‖opE A‖) ≤ 4 / 3 := (Real.exp_le_exp.2 hAH).trans exp_quarter_le
  have eF : (S.zoh A hA H).F = NormedSpace.exp (H • S.blockDiag A) := rfl
  have eN : (S.zoh A hA H).N = S.zohNew A H := rfl
  have eMN : (S.zoh A hA H).M + (S.zoh A hA H).N = S.zohCoupling A H :=
    S.zohOld_add_zohNew A H
  -- the local maps and the coefficients of the samples
  have hF1 := (S.norm_zoh_local_samples_le A hH hAH).1
  have hG := (S.norm_zoh_local_samples_le A hH hAH).2
  have hN : ‖opE (S.zohNew A H)‖ ≤ 7 / 3 * σ * ‖opE A‖ * H := by
    have h2 := mul_le_mul_of_nonneg_left hG hσ0
    linarith
  have hN2 : ‖opE (S.zoh A hA H).N‖ ≤ 1 / 2 := by
    rw [eN]
    linarith
  -- the one-step map
  have hX1 : ‖opE ((S.zoh A hA H).X - 1)‖ ≤ 22 / 3 * ‖opE A‖ * H := by
    have h := (S.zoh A hA H).norm_X_sub_one_le hN2
    rw [eMN, eF] at h
    linarith
  have hXU : ‖opE ((S.zoh A hA H).X - NormedSpace.exp (H • A))‖ ≤
      (22 / 9 + 154 / 9 * σ) * ‖opE A‖ ^ 2 * H ^ 2 := by
    have h := (S.zoh A hA H).norm_X_sub_step_le (S.blockDiag A) (S.coupling A)
      (NormedSpace.exp (H • A)) H
    rw [S.blockDiag_add_coupling, eMN, eN, eF] at h
    have t1 : ‖opE (NormedSpace.exp (H • S.blockDiag A) - (1 + H • S.blockDiag A))‖ ≤
        2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by
      refine (norm_opE_exp_sub_linear_le (S.blockDiag A) hH).trans ?_
      calc ‖opE (S.blockDiag A)‖ ^ 2 / 2 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 2
          ≤ ‖opE A‖ ^ 2 / 2 * (4 / 3) * H ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul
              (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h0 2) zero_le_two) hE₀
              (Real.exp_nonneg _) (by positivity)) (by positivity)
        _ = 2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by ring
    have t2 : ‖opE (S.zohCoupling A H - H • S.coupling A)‖ ≤
        10 / 9 * ‖opE A‖ ^ 2 * H ^ 2 := by
      refine (S.norm_opE_zohCoupling_sub_le A hH hx).trans ?_
      have h5 : ‖opE (S.blockDiag A)‖ * ‖opE (S.coupling A)‖ ≤ ‖opE A‖ * (2 * ‖opE A‖) :=
        mul_le_mul h0 hγ (norm_nonneg _) hα
      have h6 := mul_le_mul_of_nonneg_right h5 (sq_nonneg H)
      linarith
    have t3 : ‖opE (S.zohNew A H)‖ * ‖opE ((S.zoh A hA H).X - 1)‖ ≤
        154 / 9 * σ * ‖opE A‖ ^ 2 * H ^ 2 :=
      (mul_le_mul hN hX1 (norm_nonneg _) (by positivity)).trans_eq (by ring)
    have t4 : ‖opE (NormedSpace.exp (H • A) - (1 + H • A))‖ ≤ 2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by
      refine (norm_opE_exp_sub_linear_le A hH).trans ?_
      calc ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2
          ≤ ‖opE A‖ ^ 2 / 2 * (4 / 3) * H ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity))
              (by positivity)
        _ = 2 / 3 * ‖opE A‖ ^ 2 * H ^ 2 := by ring
    linarith
  have p0 : 0 ≤ ‖opE A‖ * H := by positivity
  have p1 : 0 ≤ σ * ‖opE A‖ * H := by positivity
  have p2 : 0 ≤ ‖opE A‖ ^ 2 * H ^ 2 := by positivity
  have p3 : 0 ≤ σ * ‖opE A‖ ^ 2 * H ^ 2 := by positivity
  refine ⟨hH, rfl, hA, ?_, ?_, ?_⟩
  · rw [eN]
    unfold zohConsA
    linarith
  · unfold zohConsB
    linarith
  · unfold zohConsC
    linarith

/-- **The zero-order hold is consistent, with explicit constants** (the paper, Theorem `thm:half`:
"for the zero-order hold"). For `0 ≤ H`, `H ‖A‖ ≤ 1/4` and `√(card κ) · H ‖A‖ ≤ 1/6`, the
zero-order hold `S.zoh A hA H`, in any order of execution, is consistent with the monolithic step
`e^{HA}`: `‖N‖ ≤ a H`, `‖X - 1‖ ≤ b H`, `‖X - e^{HA}‖ ≤ c H²` with `a = 3σ‖A‖`, `b = 8‖A‖`,
`c = 3 (1 + 6σ) ‖A‖²`, `σ = √(card κ)`. -/
theorem zoh_consistent [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    (S.zoh A hA H).Consistent A (NormedSpace.exp (H • A)) H
      (zohConsA (Real.sqrt (Fintype.card κ)) ‖opE A‖) (zohConsB ‖opE A‖)
      (zohConsC (Real.sqrt (Fintype.card κ)) ‖opE A‖) :=
  S.zoh_consistent_of_new_le hA hH (Real.sqrt_nonneg _) (S.norm_opE_zohNew_le A H) hAH hσ

/-- **The one-step map of the zero-order hold, without a hypothesis of consistency** (the paper,
Theorem `thm:half`, eq. `eq:half` for the zero-order hold). For `0 ≤ H`, `H ‖A‖ ≤ 1/4` and
`√(card κ) · H ‖A‖ ≤ 1/6`, in any order of execution:
`‖X - e^{HA} - ½H² A_ς A‖ ≤ (2/3 + 4σ + 53σ² + 54σ³) ‖A‖³ · H³`, `σ = √(card κ)`. -/
theorem norm_zoh_step_sub_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    ‖opE ((S.zoh A hA H).X - NormedSpace.exp (H • A) -
        (H ^ 2 / 2) • (S.signedCoupling A * A))‖ ≤
      zohStepK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 3 := by
  have hc := S.zoh_consistent hA hH hAH hσ
  refine (norm_zoh_sub_le hc).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact (S.zoh_constants_le A hH hAH (Real.sqrt_nonneg _)).1

/-! ### Equation (halfstep) for the zero-order hold -/

/-- **The modified system of the zero-order hold** (the paper, Theorem `thm:half`, eq. `eq:halfstep`
in matrix form). For `0 < H`, `H ‖A‖ ≤ 1/24` and `√(card κ) · H ‖A‖ ≤ 1/6`, in any order of
execution, the difference `Δ = Ã - A` of the zero-order hold obeys
`‖Δ - (H/2) A_ς A‖ ≤ (37 + 220σ + 53σ² + 54σ³) ‖A‖³ · H²`, `σ = √(card κ)`: the modified system
is the monolithic system with every partner output shifted by half a macro step, up to the order
`H²`. -/
theorem norm_zoh_difference_sub_half_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    ‖opE (difference A H (S.zoh A hA H).X - (H / 2) • (S.signedCoupling A * A))‖ ≤
      zohDiffK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 2 := by
  obtain ⟨hAH4, hbH⟩ := zohConsB_mul_le hAH
  have hc := S.zoh_consistent hA hH.le hAH4 hσ
  have he := S.norm_zoh_brackets_le A hH.le
  rw [← S.zohOld_add_zohNew A H] at he
  have h := hc.norm_difference_sub_half_le hH hbH hAH4 he
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact (S.zoh_constants_le A hH.le hAH4 (Real.sqrt_nonneg _)).2.1

end HeldScheme

end CoSimFoundations
