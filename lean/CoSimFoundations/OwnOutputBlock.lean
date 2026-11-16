/-
The reaction from the own output: the conclusion of Corollary 7.2 (`cor:own`) of the the paper,
`Π_i (X - U) Π_iᵀ = O(H³)`, with an explicit constant.

Setting of `ReactionDiag` and `ForcedNorm`: a `HeldScheme` with `S.Consistent A U H a b c`,
spectral norms `‖opE ·‖`, `blk s T = mask_s T mask_s` the diagonal block `s` of a matrix `T`
padded with zeros, `osgn s` the diagonal matrix of the signs `ς_sk` on the other subsystems
(`0` on `s`), `C₃ = reactionC a b c ‖A‖ H`, `A_s = blk s A`.

The reaction (`Consistent.reaction_diag`) is
`Π_s (X - U) Π_sᵀ = F_s - e^{H A_s} + ½H² Σ_k ς_sk A_sk A_ks + r_s`, `‖r_s‖ ≤ (C₃ + τ_s) H³`,
`τ_s = ‖A_s‖³/6 · e^{H‖A_s‖}`; the block `s` of `A osgn_s A` is `Σ_k ς_sk A_sk A_ks`, and with
`A_sk = -A_ksᵀ` (`hskew`) it is `-Σ_k ς_sk A_ksᵀ A_ks`, the block of `-Aᵀ osgn_s A`
(`osgn_skew_apply`).

1. **The conclusion from the local coefficient** (`Consistent.own_output_block`,
   `Consistent.own_output_block_skew`). If
     `‖Π_s (F - (e^{H A_s} + ½H² Σ_k ς_sk A_ksᵀ A_ks)) Π_sᵀ‖ ≤ d H³`
   (in the first form, without `hskew`: `F - e^{H A_s} + ½H² A osgn_s A`), then
     `‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + τ_s + d) H³`.

2. **The realisation by a local gain** (`Consistent.own_output_local_gain`,
   `Consistent.own_output_gain_block`). If the block `s` of `F` is the block of
   `exp (H (A_s + E))` with `‖E‖ ≤ κ₁ H` and `H E = ½H² Σ_k ς_sk A_ksᵀ A_ks` on the block, then
   the hypothesis of 1 holds with `d = κ₁ (‖A_s‖ + κ₁ H) e^{H (‖A_s‖ + κ₁ H)}` (`ownGainConst`),
   by `‖exp (H Ã) - exp (H A) - H (Ã - A)‖ ≤ H² ‖Ã - A‖ m e^{H m}`
   (`norm_exp_smul_sub_exp_smul_sub_le`, `ForcedParts.lean`). For the gain of the paper,
   `E = (H/2) Σ_k ς_sk A_ksᵀ A_ks = B_s K_s B_sᵀ` (`own_output_gain`, `ReactionGain.lean`),
   `κ₁ = ‖A‖² / 2`.

3. **The realisation by a constant weight on the own output**
   (`Consistent.own_output_weight`, `Consistent.own_output_weight_integral`). If the block `s`
   of `F` is the block of `e^{H A_s} + Φ E` with `‖Φ - H‖ ≤ φ H²`, then the hypothesis of 1 holds
   with `d = φ κ₁`. For `Φ = ∫₀^H e^{(H - τ) A_s} dτ`, the response of the subsystem to an input
   that is held over the macro step, `φ = ‖A_s‖/2 · e^{H‖A_s‖}`: by the moment formula
   (`Phi.lean`) the integral is `H φ₁(H A_s)`, and `‖φ₁(Z) - 1‖ ≤ ‖Z‖/2 · e^{‖Z‖}`
   (`norm_phi_one_sub_one_le`).

The paper states the corollary for "a consistent family of holds" with `O(H³)`; here the family is
one scheme at one macro step `H ≥ 0` with the constants of `HeldScheme.Consistent`, that no
subsystem is its own partner is the hypothesis `hnp`, and the two realisations are stated through
the block `s` of `F`.
-/
import CoSimFoundations.ForcedNorm
import CoSimFoundations.Phi

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

variable {n : ℕ}

/-- The transpose of a matrix has the same spectral norm (one inequality). -/
theorem norm_opE_transpose_le (T : Matrix (Fin n) (Fin n) ℝ) : ‖opE Tᵀ‖ ≤ ‖opE T‖ := by
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg _) fun u v hu hv => ?_
  have h1 := abs_inner_opE_le T u v
  rw [hu, hv, mul_one, mul_one] at h1
  rw [RCLike.re_to_real, real_inner_comm, inner_opE_transpose, Matrix.transpose_transpose]
  exact (le_abs_self _).trans h1

end OneStep

open OneStep

variable {n : ℕ}

/-- The constant of the realisation by a local gain: `κ₁ (α_s + κ₁ H) e^{H (α_s + κ₁ H)}`, with
`‖E‖ ≤ κ₁ H` and `α_s = ‖A_s‖`. -/
noncomputable def ownGainConst (κ₁ αs H : ℝ) : ℝ :=
  κ₁ * (αs + κ₁ * H) * Real.exp (H * (αs + κ₁ * H))

section PhiOne

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The first φ-function near one:** `‖φ₁(Z) - 1‖ ≤ ‖Z‖/2 · e^{‖Z‖}`, with
`φ₁(Z) = Σ_j Z^j / (j + 1)!`. -/
theorem norm_phi_one_sub_one_le (Z : 𝔸) : ‖phi 1 Z - 1‖ ≤ ‖Z‖ / 2 * Real.exp ‖Z‖ := by
  have hf : HasSum (fun j : ℕ => (((j + 1).factorial : ℕ) : ℝ)⁻¹ • Z ^ j) (phi 1 Z) :=
    (summable_phi 1 Z).hasSum
  have htail := (hasSum_nat_add_iff' 1).2 hf
  have hsum : ∑ i ∈ Finset.range 1, (((i + 1).factorial : ℕ) : ℝ)⁻¹ • Z ^ i = 1 := by
    simp
  rw [hsum] at htail
  have hg : HasSum (fun j : ℕ => ‖Z‖ / 2 * (‖Z‖ ^ j / (j.factorial : ℝ)))
      (‖Z‖ / 2 * Real.exp ‖Z‖) := by
    have h : HasSum (fun i : ℕ => ‖Z‖ ^ i / (i.factorial : ℝ)) (Real.exp ‖Z‖) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp ‖Z‖
    exact h.mul_left _
  refine htail.norm_le_of_bounded hg fun j => ?_
  rw [norm_smul, norm_inv, Real.norm_natCast]
  have hp : ‖Z ^ (j + 1)‖ ≤ ‖Z‖ ^ (j + 1) := norm_pow_le' Z (Nat.succ_pos j)
  have hfact : ((j + 1 + 1).factorial : ℝ) =
      ((j : ℝ) + 2) * (((j : ℝ) + 1) * (j.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hfpos : (0 : ℝ) < ((j + 1 + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1 + 1)
  have hF : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hY : 0 ≤ ‖Z‖ ^ (j + 1) := by positivity
  have hR : ((j + 1 + 1).factorial : ℝ) * (‖Z‖ / 2 * (‖Z‖ ^ j / (j.factorial : ℝ))) =
      ((j : ℝ) + 2) * ((j : ℝ) + 1) / 2 * ‖Z‖ ^ (j + 1) := by
    rw [hfact, pow_succ]
    field_simp
  rw [inv_mul_le_iff₀ hfpos, hR]
  refine hp.trans ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) ^ 2 + 3 * j) hY]

/-- **The response to a held input:** `∫₀^H e^{(H - τ) Z} dτ = H φ₁(H Z)` (the moment formula of
`Phi.lean` for the moment `0`), hence `‖∫₀^H e^{(H - τ) Z} dτ - H‖ ≤ ‖Z‖/2 · e^{H‖Z‖} H²`. -/
theorem norm_integral_exp_sub_le (Z : 𝔸) {H : ℝ} (hH : 0 ≤ H) :
    ‖(∫ τ in (0 : ℝ)..H, NormedSpace.exp ((H - τ) • Z)) - H • (1 : 𝔸)‖ ≤
      ‖Z‖ / 2 * Real.exp (H * ‖Z‖) * H ^ 2 := by
  have hm := moment_formula Z H 0
  simp only [pow_zero, one_smul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, one_mul]
    at hm
  rw [hm, ← smul_sub, norm_smul, Real.norm_of_nonneg hH]
  have h1 := norm_phi_one_sub_one_le (H • Z)
  rw [norm_smul, Real.norm_of_nonneg hH] at h1
  exact (mul_le_mul_of_nonneg_left h1 hH).trans_eq (by ring)

end PhiOne

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- The diagonal block is the block between a subsystem and itself. -/
theorem cblock_self (s : κ) (T : Matrix (Fin n) (Fin n) ℝ) : S.cblock s s T = S.blk s T := rfl

/-- The signs of the other subsystems form a diagonal matrix of spectral norm at most one. -/
theorem norm_opE_osgn_le (s : κ) : ‖opE (S.osgn s)‖ ≤ 1 :=
  norm_opE_diagonal_le _ zero_le_one fun i => by
    by_cases h1 : S.sub i = s
    · simp [h1]
    · by_cases h2 : S.stage (S.sub i) < S.stage s <;> simp [sg, h1, h2]

/-- With `A_sk = -A_ksᵀ` between different subsystems, the rows of `s` of `A osgn_s A` are minus
the rows of `Aᵀ osgn_s A`: `Σ_k ς_sk A_sk A_ks = -Σ_k ς_sk A_ksᵀ A_ks`. -/
theorem osgn_skew_apply {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s : κ} {p : Fin n} (hp : S.sub p = s)
    (q : Fin n) : (A * S.osgn s * A) p q = -(Aᵀ * S.osgn s * A) p q := by
  have e1 : (A * S.osgn s * A) p q =
      ∑ r, A p r * (if S.sub r = s then 0 else S.sg s (S.sub r)) * A r q :=
    mul_diagonal_mul_apply A A _ p q
  have e2 : (Aᵀ * S.osgn s * A) p q =
      ∑ r, Aᵀ p r * (if S.sub r = s then 0 else S.sg s (S.sub r)) * A r q :=
    mul_diagonal_mul_apply Aᵀ A _ p q
  rw [e1, e2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = s
  · rw [ite_eq_left hr]
    ring
  · have e : A r p = -A p r := hskew p r (by rw [hp]; exact fun e' => hr e'.symm)
    rw [Matrix.transpose_apply, e]
    ring

/-- The matrix `Σ_k ς_sk A_ksᵀ A_ks` of the reaction is of the size of `‖A‖²`. -/
theorem norm_opE_blk_transpose_osgn_le (A : Matrix (Fin n) (Fin n) ℝ) (s : κ) :
    ‖opE (S.blk s (Aᵀ * S.osgn s * A))‖ ≤ ‖opE A‖ ^ 2 := by
  have h1 : ‖opE (Aᵀ * S.osgn s * A)‖ ≤ ‖opE A‖ * 1 * ‖opE A‖ := by
    rw [opE_mul, opE_mul]
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (norm_mul_le _ _).trans
      (mul_le_mul (norm_opE_transpose_le A) (S.norm_opE_osgn_le s) (norm_nonneg _) (norm_nonneg _))
  have h2 := S.norm_opE_blk_le s (Aᵀ * S.osgn s * A)
  have e : ‖opE A‖ * 1 * ‖opE A‖ = ‖opE A‖ ^ 2 := by ring
  linarith

variable {S}

/-! ### The conclusion from the local coefficient -/

/-- **The diagonal block from the local coefficient.** For a consistent scheme with one held
sample, in any order of execution, and a subsystem `s` that is not its own partner: if the local
coefficient supplies the reaction up to third order,
`‖Π_s (F - e^{H A_s} + ½H² A osgn_s A) Π_sᵀ‖ ≤ d H³`, then
`‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖} + d) H³`, `C₃ = reactionC a b c ‖A‖ H`. No
symmetry of the coupling is assumed. -/
theorem Consistent.own_output_block {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} (hnp : ¬ S.partner s s) {d : ℝ}
    (hF : ‖opE (S.blk s (S.F - NormedSpace.exp (H • S.blk s A) +
      (H ^ 2 / 2) • (A * S.osgn s * A)))‖ ≤ d * H ^ 3) :
    ‖opE (S.blk s (S.X - U))‖ ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) + d) * H ^ 3 := by
  have hH := h.hH
  have hd : 0 ≤ d * H ^ 3 := (norm_nonneg _).trans hF
  have hC := h.reaction_bound_nonneg
  have hT : 0 ≤ ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) * H ^ 3 := by
    positivity
  have e : (reactionC a b c ‖opE A‖ H +
      ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) + d) * H ^ 3 =
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖)) * H ^ 3 + d * H ^ 3 := by
    ring
  have hK : 0 ≤ (reactionC a b c ‖opE A‖ H +
      ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) + d) * H ^ 3 := by
    rw [e]
    linarith
  rw [← S.cblock_self]
  refine (S.norm_opE_cblock_le_iff s s (S.X - U) hK).2 fun x y hx hy => ?_
  have h1 := h.reaction_diag hnp hx hy
  have h2 := S.abs_inner_le_norm_cblock (S.F - NormedSpace.exp (H • S.blk s A) +
    (H ^ 2 / 2) • (A * S.osgn s * A)) hx hy
  rw [S.cblock_self, inner_opE_add, inner_opE_smul] at h2
  have h3 := h2.trans (mul_le_mul_of_nonneg_right hF (by positivity : (0 : ℝ) ≤ ‖x‖ * ‖y‖))
  rw [e, add_mul]
  rw [abs_le] at h1 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]

/-- **The conclusion of Corollary 7.2** (`cor:own`), from the local coefficient. For a consistent
scheme with `A_sk = -A_ksᵀ` between different subsystems and a subsystem `s` that is not its own
partner: if `‖Π_s (F - (e^{H A_s} + ½H² Σ_k ς_sk A_ksᵀ A_ks)) Π_sᵀ‖ ≤ d H³`, then
`‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖} + d) H³`. The block `s` of `Aᵀ osgn_s A` is
`Σ_k ς_sk A_ksᵀ A_ks`. -/
theorem Consistent.own_output_block_skew {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s) {d : ℝ}
    (hF : ‖opE (S.blk s (S.F - (NormedSpace.exp (H • S.blk s A) +
      (H ^ 2 / 2) • (Aᵀ * S.osgn s * A))))‖ ≤ d * H ^ 3) :
    ‖opE (S.blk s (S.X - U))‖ ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) + d) * H ^ 3 := by
  refine h.own_output_block hnp ?_
  have e : S.blk s (S.F - NormedSpace.exp (H • S.blk s A) + (H ^ 2 / 2) • (A * S.osgn s * A)) =
      S.blk s (S.F - (NormedSpace.exp (H • S.blk s A) + (H ^ 2 / 2) • (Aᵀ * S.osgn s * A))) := by
    refine S.cblock_congr fun p q hp _ => ?_
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [S.osgn_skew_apply hskew hp q]
    ring
  rw [e]
  exact hF

/-! ### The realisation by a local gain -/

/-- **The local coefficient of a local gain.** If the block `s` of `F` is the block of
`exp (H (A_s + E))`, `‖E‖ ≤ κ₁ H`, and `H E = -½H² A osgn_s A` on the block `s`, then
`‖Π_s (F - e^{H A_s} + ½H² A osgn_s A) Π_sᵀ‖ ≤ κ₁ (‖A_s‖ + κ₁ H) e^{H (‖A_s‖ + κ₁ H)} H³`. -/
theorem norm_local_gain_block_le (S : HeldScheme n κ) {A E : Matrix (Fin n) (Fin n) ℝ}
    {H κ₁ : ℝ} (hH : 0 ≤ H) {s : κ} (hE : ‖opE E‖ ≤ κ₁ * H)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s →
      S.F p q = NormedSpace.exp (H • (S.blk s A + E)) p q)
    (hgain : ∀ p q, S.sub p = s → S.sub q = s →
      H * E p q = -(H ^ 2 / 2) * (A * S.osgn s * A) p q) :
    ‖opE (S.blk s (S.F - NormedSpace.exp (H • S.blk s A) +
      (H ^ 2 / 2) • (A * S.osgn s * A)))‖ ≤ ownGainConst κ₁ ‖opE (S.blk s A)‖ H * H ^ 3 := by
  have hκ : 0 ≤ κ₁ * H := (norm_nonneg _).trans hE
  have hAt : ‖opE (S.blk s A + E)‖ ≤ ‖opE (S.blk s A)‖ + κ₁ * H := by
    rw [opE_add]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hE)
  have hA' : ‖opE (S.blk s A)‖ ≤ ‖opE (S.blk s A)‖ + κ₁ * H := by linarith
  have hn : ‖opE (NormedSpace.exp (H • (S.blk s A + E)) - NormedSpace.exp (H • S.blk s A) -
      H • (S.blk s A + E - S.blk s A))‖ ≤
      H ^ 2 * ‖opE (S.blk s A + E - S.blk s A)‖ * (‖opE (S.blk s A)‖ + κ₁ * H) *
        Real.exp (H * (‖opE (S.blk s A)‖ + κ₁ * H)) := by
    rw [opE_sub, opE_sub, opE_exp, opE_exp, opE_smul, opE_smul, opE_smul, opE_sub]
    exact norm_exp_smul_sub_exp_smul_sub_le (opE (S.blk s A + E)) (opE (S.blk s A)) hH hAt hA'
  rw [add_sub_cancel_left] at hn
  have e : S.blk s (S.F - NormedSpace.exp (H • S.blk s A) + (H ^ 2 / 2) • (A * S.osgn s * A)) =
      S.blk s (NormedSpace.exp (H • (S.blk s A + E)) - NormedSpace.exp (H • S.blk s A) -
        H • E) := by
    refine S.cblock_congr fun p q hp hq => ?_
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hFs p q hp hq]
    linear_combination hgain p q hp hq
  rw [e]
  refine (S.norm_opE_blk_le s _).trans (hn.trans ?_)
  have h1 : H ^ 2 * ‖opE E‖ ≤ H ^ 2 * (κ₁ * H) := mul_le_mul_of_nonneg_left hE (sq_nonneg H)
  have h2 : 0 ≤ (‖opE (S.blk s A)‖ + κ₁ * H) * Real.exp (H * (‖opE (S.blk s A)‖ + κ₁ * H)) := by
    positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  unfold ownGainConst
  linarith

/-- **Corollary 7.2, realisation by a local gain** (general gain). For a consistent scheme and a
subsystem `s` that is not its own partner: if the block `s` of `F` is the block of
`exp (H (A_s + E))` with `‖E‖ ≤ κ₁ H` and `H E = -½H² Σ_k ς_sk A_sk A_ks` on the block `s`, then
`‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖} + κ₁ (‖A_s‖ + κ₁ H) e^{H (‖A_s‖ + κ₁ H)}) H³`. -/
theorem Consistent.own_output_local_gain {A U E : Matrix (Fin n) (Fin n) ℝ} {H a b c κ₁ : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} (hnp : ¬ S.partner s s) (hE : ‖opE E‖ ≤ κ₁ * H)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s →
      S.F p q = NormedSpace.exp (H • (S.blk s A + E)) p q)
    (hgain : ∀ p q, S.sub p = s → S.sub q = s →
      H * E p q = -(H ^ 2 / 2) * (A * S.osgn s * A) p q) :
    ‖opE (S.blk s (S.X - U))‖ ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) +
        ownGainConst κ₁ ‖opE (S.blk s A)‖ H) * H ^ 3 :=
  h.own_output_block hnp (S.norm_local_gain_block_le h.hH hE hFs hgain)

/-- **Corollary 7.2 (`cor:own`), realisation by the local gain of the paper.** For a consistent
scheme with `A_sk = -A_ksᵀ` between different subsystems and a subsystem `s` that is not its own
partner: if the block `s` of `F` is the block of `exp (H (A_s + E_s))` with
`E_s = (H/2) Σ_k ς_sk A_ksᵀ A_ks` (which is `B_s K_s B_sᵀ` by `own_output_gain`), then
`‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖} + κ₁ (‖A_s‖ + κ₁ H) e^{H (‖A_s‖ + κ₁ H)}) H³`
with `κ₁ = ‖A‖² / 2`. -/
theorem Consistent.own_output_gain_block {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q =
      NormedSpace.exp (H • (S.blk s A + (H / 2) • S.blk s (Aᵀ * S.osgn s * A))) p q) :
    ‖opE (S.blk s (S.X - U))‖ ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) +
        ownGainConst (‖opE A‖ ^ 2 / 2) ‖opE (S.blk s A)‖ H) * H ^ 3 := by
  have hH := h.hH
  refine h.own_output_local_gain hnp ?_ hFs fun p q hp hq => ?_
  · rw [opE_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left (S.norm_opE_blk_transpose_osgn_le A s)
      (by positivity : (0 : ℝ) ≤ H / 2)
    linarith
  · rw [Matrix.smul_apply, smul_eq_mul, S.blk_apply, ite_eq_left hp, ite_eq_left hq,
      S.osgn_skew_apply hskew hp q]
    ring

/-! ### The realisation by a constant weight on the own output -/

/-- **The local coefficient of a weight on the own output.** If the block `s` of `F` is the block
of `e^{H A_s} + Φ E`, `‖Φ - H‖ ≤ φ H²`, `‖E‖ ≤ κ₁ H`, and `H E = -½H² A osgn_s A` on the block
`s`, then `‖Π_s (F - e^{H A_s} + ½H² A osgn_s A) Π_sᵀ‖ ≤ φ κ₁ H³`. -/
theorem norm_own_weight_block_le (S : HeldScheme n κ) {A E Φ : Matrix (Fin n) (Fin n) ℝ}
    {H κ₁ φ : ℝ} {s : κ} (hE : ‖opE E‖ ≤ κ₁ * H) (hΦ : ‖opE (Φ - H • 1)‖ ≤ φ * H ^ 2)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s →
      S.F p q = (NormedSpace.exp (H • S.blk s A) + Φ * E) p q)
    (hgain : ∀ p q, S.sub p = s → S.sub q = s →
      H * E p q = -(H ^ 2 / 2) * (A * S.osgn s * A) p q) :
    ‖opE (S.blk s (S.F - NormedSpace.exp (H • S.blk s A) +
      (H ^ 2 / 2) • (A * S.osgn s * A)))‖ ≤ φ * κ₁ * H ^ 3 := by
  have hφ : 0 ≤ φ * H ^ 2 := (norm_nonneg _).trans hΦ
  have e : S.blk s (S.F - NormedSpace.exp (H • S.blk s A) + (H ^ 2 / 2) • (A * S.osgn s * A)) =
      S.blk s (Φ * E - H • E) := by
    refine S.cblock_congr fun p q hp hq => ?_
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hFs p q hp hq, Matrix.add_apply]
    linear_combination hgain p q hp hq
  have e2 : Φ * E - H • E = (Φ - H • 1) * E := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [e, e2]
  refine (S.norm_opE_blk_le s _).trans ?_
  rw [opE_mul]
  exact ((norm_mul_le _ _).trans (mul_le_mul hΦ hE (norm_nonneg _) hφ)).trans_eq (by ring)

/-- **Corollary 7.2, realisation by a weight on the own output** (general weight and general
response `Φ`). For a consistent scheme and a subsystem `s` that is not its own partner: if the
block `s` of `F` is the block of `e^{H A_s} + Φ E` with `‖Φ - H‖ ≤ φ H²`, `‖E‖ ≤ κ₁ H` and
`H E = -½H² Σ_k ς_sk A_sk A_ks` on the block `s`, then
`‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖} + φ κ₁) H³`. -/
theorem Consistent.own_output_weight {A U E Φ : Matrix (Fin n) (Fin n) ℝ} {H a b c κ₁ φ : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} (hnp : ¬ S.partner s s) (hE : ‖opE E‖ ≤ κ₁ * H)
    (hΦ : ‖opE (Φ - H • 1)‖ ≤ φ * H ^ 2)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s →
      S.F p q = (NormedSpace.exp (H • S.blk s A) + Φ * E) p q)
    (hgain : ∀ p q, S.sub p = s → S.sub q = s →
      H * E p q = -(H ^ 2 / 2) * (A * S.osgn s * A) p q) :
    ‖opE (S.blk s (S.X - U))‖ ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) + φ * κ₁) * H ^ 3 :=
  h.own_output_block hnp (S.norm_own_weight_block_le hE hΦ hFs hgain)

/-- **Corollary 7.2, realisation by a constant weight on the own output, with the response of the
subsystem.** As `Consistent.own_output_weight`, with `Φ = ∫₀^H e^{(H - τ) A_s} dτ` (as operators),
the response of the subsystem to an input held over the macro step:
`‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖} + ‖A_s‖/2 e^{H‖A_s‖} κ₁) H³`. -/
theorem Consistent.own_output_weight_integral {A U E Φ : Matrix (Fin n) (Fin n) ℝ}
    {H a b c κ₁ : ℝ} (h : S.Consistent A U H a b c) {s : κ} (hnp : ¬ S.partner s s)
    (hE : ‖opE E‖ ≤ κ₁ * H)
    (hΦ : opE Φ = ∫ τ in (0 : ℝ)..H, NormedSpace.exp ((H - τ) • opE (S.blk s A)))
    (hFs : ∀ p q, S.sub p = s → S.sub q = s →
      S.F p q = (NormedSpace.exp (H • S.blk s A) + Φ * E) p q)
    (hgain : ∀ p q, S.sub p = s → S.sub q = s →
      H * E p q = -(H ^ 2 / 2) * (A * S.osgn s * A) p q) :
    ‖opE (S.blk s (S.X - U))‖ ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) +
        ‖opE (S.blk s A)‖ / 2 * Real.exp (H * ‖opE (S.blk s A)‖) * κ₁) * H ^ 3 := by
  refine h.own_output_weight hnp hE ?_ hFs hgain
  rw [opE_sub, opE_smul, opE_one, hΦ]
  exact norm_integral_exp_sub_le (opE (S.blk s A)) h.hH

/-- **Corollary 7.2 (`cor:own`), realisation by the constant weight of the paper on the own
output.** For a consistent scheme with `A_sk = -A_ksᵀ` between different subsystems and a
subsystem `s` that is not its own partner: if the block `s` of `F` is the block of
`e^{H A_s} + (∫₀^H e^{(H - τ) A_s} dτ) E_s` with `E_s = (H/2) Σ_k ς_sk A_ksᵀ A_ks`
(`= B_s K_s B_sᵀ`), then
`‖Π_s (X - U) Π_sᵀ‖ ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖} + ‖A_s‖ ‖A‖²/4 e^{H‖A_s‖}) H³`. -/
theorem Consistent.own_output_weight_block {A U Φ : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hΦ : opE Φ = ∫ τ in (0 : ℝ)..H, NormedSpace.exp ((H - τ) • opE (S.blk s A)))
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q =
      (NormedSpace.exp (H • S.blk s A) + Φ * ((H / 2) • S.blk s (Aᵀ * S.osgn s * A))) p q) :
    ‖opE (S.blk s (S.X - U))‖ ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) +
        ‖opE (S.blk s A)‖ / 2 * Real.exp (H * ‖opE (S.blk s A)‖) * (‖opE A‖ ^ 2 / 2)) *
          H ^ 3 := by
  have hH := h.hH
  refine h.own_output_weight_integral hnp ?_ hΦ hFs fun p q hp hq => ?_
  · rw [opE_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left (S.norm_opE_blk_transpose_osgn_le A s)
      (by positivity : (0 : ℝ) ≤ H / 2)
    linarith
  · rw [Matrix.smul_apply, smul_eq_mul, S.blk_apply, ite_eq_left hp, ite_eq_left hq,
      S.osgn_skew_apply hskew hp q]
    ring

end HeldScheme

end CoSimFoundations
