/-
The zero-order hold is the monolithic flow in staggered clocks, up to the third order (the
paper, Section `sec:half`):
  `X T = T U + O(H³)`,   `X = T U T⁻¹ + O(H³)`,
`U = e^{HA}`, `X` the one-step map of the zero-order hold, and `T` the matrix whose rows of
subsystem `s` are those of `e^{½ q_s H A}` for offsets `q` (`q_s - q_t = ς_st` for partners,
`Offsets`).

**Setting.** `P = diag(q)` (`offsetP`), `A_ς = P A - A P` (`signedCoupling_eq_commutator`),
`|q_s| ≤ ρ`, `α = ‖A‖`, `σ = √(card κ)`, spectral norms, `0 ≤ H`.

**The identity** (`offset_conj_ring`). In a ring, if `L B - B L = -W`, then
  `X T - T U = [U - 1 - L, B] + [U - 1, T - 1 - B] + W (T - 1) + (X - U - W) T`.
Here `L = H A`, `B = ½H P A`, `W = ½H² A_ς A`, and `L B - B L = ½H² (A P A - P A A) = -W`.

**The bounds** (`norm_offset_conj_le`, `norm_offsetT_sub_le`, `norm_zoh_mul_offsetT_sub_le`).
  `‖U - 1 - HA‖ ≤ ½α² e^{Hα} H²`,  `‖U - 1‖ ≤ α e^{Hα} H`,  `‖B‖ ≤ ½H ρ α`,  `‖W‖ ≤ ρ α² H²`,
  `‖T - 1 - B‖ ≤ σ · ½α² e^{½ρHα} (½ρH)²`  (rows of `s`: those of `e^Z - 1 - Z`, `Z = ½ q_s H A`),
  `‖X - U - W‖ ≤ zohStepK σ α · H³`  (`norm_zoh_step_sub_le`, for `Hα ≤ 1/4`, `σHα ≤ 1/6`).
Together, with `t₁ = ½ρα + ⅛ σ ρ² α² H e^{½ρHα}` (`offsetT1`, `‖T - 1‖ ≤ H t₁`):
  `‖X T - T U‖ ≤ offsetK · H³`,
  `offsetK = ½ρα³ e^{Hα} + ¼σρ²α³ e^{Hα} e^{½ρHα} + ρα² t₁ + zohStepK σ α (1 + H t₁)`.

**The conjugacy** (`isUnit_det_offsetT`, `norm_zoh_sub_conj_le`). If `H t₁ < 1`, `T` is
invertible, `‖T⁻¹‖ ≤ 1 / (1 - H t₁)`, and `‖X - T U T⁻¹‖ ≤ offsetK · H³ / (1 - H t₁)`.

**A constant free of `H`** (`offsetK_le`, `norm_zoh_mul_offsetT_sub_le_num`). If also `ρHα ≤ 1/2`,
  `offsetK ≤ (⅔ρ + ½ρ² + (19/36) σρ²) α³ + zohStepK σ α (5/4 + σ/24)`   (`offsetKNum`).
-/
import CoSimFoundations.Offsets

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

/-- **The identity behind the staggered clocks.** In a ring, if `L B - B L = -W`, then
`X T - T U = [U - 1 - L, B] + [U - 1, T - 1 - B] + W (T - 1) + (X - U - W) T`. -/
theorem offset_conj_ring {R : Type*} [Ring R] (X U T B L W : R) (hW : L * B - B * L = -W) :
    X * T - T * U = (U - 1 - L) * B - B * (U - 1 - L) +
      ((U - 1) * (T - 1 - B) - (T - 1 - B) * (U - 1)) + W * (T - 1) + (X - U - W) * T := by
  have key : (U - 1 - L) * B - B * (U - 1 - L) +
      ((U - 1) * (T - 1 - B) - (T - 1 - B) * (U - 1)) + W * (T - 1) + (X - U - W) * T =
      X * T - T * U - (L * B - B * L) - W := by
    noncomm_ring
  rw [key, hW]
  abel

/-- **The bound behind the staggered clocks,** in a normed ring with `‖1‖ ≤ 1`: if
`L B - B L = -W`, `‖U - 1 - L‖ ≤ u₂`, `‖B‖ ≤ b`, `‖U - 1‖ ≤ u₁`, `‖T - 1 - B‖ ≤ r`, `‖W‖ ≤ w`
and `‖X - U - W‖ ≤ x`, then
`‖X T - T U‖ ≤ 2 u₂ b + 2 u₁ r + w (b + r) + x (1 + (b + r))`. -/
theorem norm_offset_conj_le {𝔸 : Type*} [NormedRing 𝔸] (h1 : ‖(1 : 𝔸)‖ ≤ 1)
    {X U T B L W : 𝔸} (hW : L * B - B * L = -W) {u₂ b u₁ r w x : ℝ}
    (hu₂ : ‖U - 1 - L‖ ≤ u₂) (hb : ‖B‖ ≤ b) (hu₁ : ‖U - 1‖ ≤ u₁) (hr : ‖T - 1 - B‖ ≤ r)
    (hw : ‖W‖ ≤ w) (hx : ‖X - U - W‖ ≤ x) :
    ‖X * T - T * U‖ ≤ 2 * (u₂ * b) + 2 * (u₁ * r) + w * (b + r) + x * (1 + (b + r)) := by
  have ht : ‖T - 1‖ ≤ b + r := by
    have h := norm_add_le (T - 1 - B) B
    rw [sub_add_cancel] at h
    linarith
  have hT : ‖T‖ ≤ 1 + (b + r) := by
    have h := norm_add_le (1 : 𝔸) (T - 1)
    rw [add_sub_cancel] at h
    linarith
  have p1 : ‖(U - 1 - L) * B‖ ≤ u₂ * b :=
    (norm_mul_le _ _).trans (mul_le_mul hu₂ hb (norm_nonneg _) ((norm_nonneg _).trans hu₂))
  have p2 : ‖B * (U - 1 - L)‖ ≤ b * u₂ :=
    (norm_mul_le _ _).trans (mul_le_mul hb hu₂ (norm_nonneg _) ((norm_nonneg _).trans hb))
  have p3 : ‖(U - 1) * (T - 1 - B)‖ ≤ u₁ * r :=
    (norm_mul_le _ _).trans (mul_le_mul hu₁ hr (norm_nonneg _) ((norm_nonneg _).trans hu₁))
  have p4 : ‖(T - 1 - B) * (U - 1)‖ ≤ r * u₁ :=
    (norm_mul_le _ _).trans (mul_le_mul hr hu₁ (norm_nonneg _) ((norm_nonneg _).trans hr))
  have p5 : ‖W * (T - 1)‖ ≤ w * (b + r) :=
    (norm_mul_le _ _).trans (mul_le_mul hw ht (norm_nonneg _) ((norm_nonneg _).trans hw))
  have p6 : ‖(X - U - W) * T‖ ≤ x * (1 + (b + r)) :=
    (norm_mul_le _ _).trans (mul_le_mul hx hT (norm_nonneg _) ((norm_nonneg _).trans hx))
  rw [offset_conj_ring X U T B L W hW]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))) le_rfl)) le_rfl).trans ?_
  linarith

/-- The constant of `‖T - 1‖ ≤ H t₁`: `t₁ = ½ρα + ⅛ σ ρ² α² H e^{½ρHα}`. -/
noncomputable def offsetT1 (σ α ρ H : ℝ) : ℝ :=
  ρ * α / 2 + σ * ρ ^ 2 * α ^ 2 * H / 8 * Real.exp (ρ * H / 2 * α)

/-- The constant of the staggered clocks, `‖X T - T U‖ ≤ offsetK · H³`:
`½ρα³ e^{Hα} + ¼σρ²α³ e^{Hα} e^{½ρHα} + ρα² t₁ + zohStepK σ α (1 + H t₁)`. -/
noncomputable def offsetK (σ α ρ H : ℝ) : ℝ :=
  ρ * α ^ 3 / 2 * Real.exp (H * α) +
    σ * ρ ^ 2 * α ^ 3 / 4 * Real.exp (H * α) * Real.exp (ρ * H / 2 * α) +
    ρ * α ^ 2 * offsetT1 σ α ρ H + HeldScheme.zohStepK σ α * (1 + H * offsetT1 σ α ρ H)

/-- The constant of the staggered clocks for `H α ≤ 1/4` and `ρ H α ≤ 1/2`, free of `H`:
`(⅔ρ + ½ρ² + (19/36) σρ²) α³ + zohStepK σ α (5/4 + σ/24)`. -/
noncomputable def offsetKNum (σ α ρ : ℝ) : ℝ :=
  (2 / 3 * ρ + ρ ^ 2 / 2 + 19 / 36 * σ * ρ ^ 2) * α ^ 3 +
    HeldScheme.zohStepK σ α * (5 / 4 + σ / 24)

/-- For `H α ≤ 1/4` and `ρ H α ≤ 1/2`: `offsetK σ α ρ H ≤ offsetKNum σ α ρ`. -/
theorem offsetK_le {σ α ρ H : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hρ : 0 ≤ ρ) (hH : 0 ≤ H)
    (hAH : H * α ≤ 1 / 4) (hρH : ρ * (H * α) ≤ 1 / 2) :
    offsetK σ α ρ H ≤ offsetKNum σ α ρ := by
  have hE1 : Real.exp (H * α) ≤ 4 / 3 := (Real.exp_le_exp.2 hAH).trans exp_quarter_le
  have hE2 : Real.exp (ρ * H / 2 * α) ≤ 4 / 3 := by
    refine (Real.exp_le_exp.2 ?_).trans exp_quarter_le
    have e : ρ * H / 2 * α = ρ * (H * α) / 2 := by ring
    linarith
  have hE2' := Real.exp_nonneg (ρ * H / 2 * α)
  have hx0 : 0 ≤ ρ * (H * α) := by positivity
  have hK0 : 0 ≤ HeldScheme.zohStepK σ α := by
    unfold HeldScheme.zohStepK
    positivity
  have t1 : ρ * α ^ 3 / 2 * Real.exp (H * α) ≤ ρ * α ^ 3 / 2 * (4 / 3) :=
    mul_le_mul_of_nonneg_left hE1 (by positivity)
  have hEE : Real.exp (H * α) * Real.exp (ρ * H / 2 * α) ≤ 4 / 3 * (4 / 3) :=
    mul_le_mul hE1 hE2 hE2' (by norm_num)
  have t2 : σ * ρ ^ 2 * α ^ 3 / 4 * (Real.exp (H * α) * Real.exp (ρ * H / 2 * α)) ≤
      σ * ρ ^ 2 * α ^ 3 / 4 * (4 / 3 * (4 / 3)) :=
    mul_le_mul_of_nonneg_left hEE (by positivity)
  have hxE : ρ * (H * α) * Real.exp (ρ * H / 2 * α) ≤ 1 / 2 * (4 / 3) :=
    mul_le_mul hρH hE2 hE2' (by norm_num)
  have hT1 : offsetT1 σ α ρ H ≤ ρ * α / 2 + σ * ρ * α / 12 := by
    have h := mul_le_mul_of_nonneg_left hxE (show 0 ≤ σ * ρ * α / 8 by positivity)
    have e : σ * ρ ^ 2 * α ^ 2 * H / 8 * Real.exp (ρ * H / 2 * α) =
        σ * ρ * α / 8 * (ρ * (H * α) * Real.exp (ρ * H / 2 * α)) := by ring
    rw [offsetT1, e]
    linarith
  have hHT1 : H * offsetT1 σ α ρ H ≤ 1 / 4 + σ / 24 := by
    have h1 : (ρ * (H * α)) * (ρ * (H * α) * Real.exp (ρ * H / 2 * α)) ≤
        1 / 2 * (1 / 2 * (4 / 3)) :=
      mul_le_mul hρH hxE (mul_nonneg hx0 hE2') (by norm_num)
    have h := mul_le_mul_of_nonneg_left h1 (show 0 ≤ σ / 8 by positivity)
    have e : H * offsetT1 σ α ρ H = ρ * (H * α) / 2 +
        σ / 8 * ((ρ * (H * α)) * (ρ * (H * α) * Real.exp (ρ * H / 2 * α))) := by
      rw [offsetT1]
      ring
    rw [e]
    linarith
  have t3 : ρ * α ^ 2 * offsetT1 σ α ρ H ≤ ρ * α ^ 2 * (ρ * α / 2 + σ * ρ * α / 12) :=
    mul_le_mul_of_nonneg_left hT1 (by positivity)
  have t4 : HeldScheme.zohStepK σ α * (1 + H * offsetT1 σ α ρ H) ≤
      HeldScheme.zohStepK σ α * (5 / 4 + σ / 24) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  rw [offsetK, offsetKNum, mul_assoc (σ * ρ ^ 2 * α ^ 3 / 4)]
  linarith

namespace HeldScheme

open OneStep

variable {n : ℕ} {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- **The staggered clocks:** the matrix whose rows of subsystem `s` are the rows of
`e^{½ q_s H A}`. -/
noncomputable def offsetT (q : κ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun r c => NormedSpace.exp ((q (S.sub r) * H / 2) • A) r c

/-- The offsets are bounded by `ρ` in the spectral norm: `‖P‖ ≤ ρ`. -/
theorem norm_opE_offsetP_le {q : κ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ s, |q s| ≤ ρ) :
    ‖opE (S.offsetP q)‖ ≤ ρ :=
  norm_opE_diagonal_le _ hρ0 fun r => hρ (S.sub r)

/-- **`T = 1 + ½H P A` up to the second order:**
`‖T - 1 - ½H P A‖ ≤ σ · ½α² e^{½ρHα} (½ρH)²`, `σ = √(card κ)`, for `|q_s| ≤ ρ` and `H ≥ 0`. -/
theorem norm_offsetT_sub_le [Fintype κ] {q : κ → ℝ} {ρ : ℝ} (hρ : ∀ s, |q s| ≤ ρ)
    (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE (S.offsetT q A H - 1 - (H / 2) • (S.offsetP q * A))‖ ≤
      Real.sqrt (Fintype.card κ) *
        (‖opE A‖ ^ 2 / 2 * Real.exp (ρ * H / 2 * ‖opE A‖) * (ρ * H / 2) ^ 2) := by
  refine S.norm_opE_le_of_rows (by positivity) fun s x hx y => ?_
  have e : ⟪x, opE (S.offsetT q A H - 1 - (H / 2) • (S.offsetP q * A)) y⟫ =
      ⟪x, opE (NormedSpace.exp ((q s * H / 2) • A) - (1 + (q s * H / 2) • A)) y⟫ := by
    refine inner_opE_congr_row hx y fun r c hr => ?_
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, offsetT,
      Matrix.of_apply, offsetP, Matrix.diagonal_mul, hr]
    ring
  have hc : |q s * H / 2| ≤ ρ * H / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hH, abs_two]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hρ s) hH) zero_le_two
  rw [e]
  refine (abs_inner_opE_le _ x y).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [opE_sub, opE_exp, opE_add, opE_one, opE_smul]
  refine (norm_exp_sub_linear_le ((q s * H / 2) • opE A)).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  calc (|q s * H / 2| * ‖opE A‖) ^ 2 / 2 * Real.exp (|q s * H / 2| * ‖opE A‖)
      ≤ (ρ * H / 2 * ‖opE A‖) ^ 2 / 2 * Real.exp (ρ * H / 2 * ‖opE A‖) := by gcongr
    _ = ‖opE A‖ ^ 2 / 2 * Real.exp (ρ * H / 2 * ‖opE A‖) * (ρ * H / 2) ^ 2 := by ring

/-- `‖½H P A‖ ≤ ½H ρ ‖A‖`. -/
theorem norm_half_smul_offsetP_mul_le {q : κ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ s, |q s| ≤ ρ)
    (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE ((H / 2) • (S.offsetP q * A))‖ ≤ H / 2 * (ρ * ‖opE A‖) := by
  rw [opE_smul, opE_mul, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (S.norm_opE_offsetP_le hρ0 hρ) (norm_nonneg _))) (by positivity)

/-- **`‖T - 1‖ ≤ H t₁`,** `t₁ = ½ρα + ⅛ σ ρ² α² H e^{½ρHα}` (`offsetT1`). -/
theorem norm_offsetT_sub_one_le [Fintype κ] {q : κ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ s, |q s| ≤ ρ) (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE (S.offsetT q A H - 1)‖ ≤
      H * offsetT1 (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H := by
  have h1 := S.norm_offsetT_sub_le hρ A hH
  have h2 := S.norm_half_smul_offsetP_mul_le hρ0 hρ A hH
  have h3 := norm_add_le (opE (S.offsetT q A H - 1 - (H / 2) • (S.offsetP q * A)))
    (opE ((H / 2) • (S.offsetP q * A)))
  rw [← opE_add, sub_add_cancel] at h3
  refine (h3.trans (add_le_add h1 h2)).trans_eq ?_
  rw [offsetT1]
  ring


/-- `‖A_ς‖ ≤ 2 ρ ‖A‖` for offsets bounded by `ρ`. -/
theorem norm_opE_signedCoupling_le_offset {q : κ → ℝ} (hq : S.IsOffset q) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ s, |q s| ≤ ρ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) :
    ‖opE (S.signedCoupling A)‖ ≤ 2 * ρ * ‖opE A‖ := by
  have hP := S.norm_opE_offsetP_le hρ0 hρ
  rw [S.signedCoupling_eq_commutator hq hA, opE_sub, opE_mul, opE_mul]
  have h1 : ‖opE (S.offsetP q) * opE A‖ ≤ ρ * ‖opE A‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have h2 : ‖opE A * opE (S.offsetP q)‖ ≤ ‖opE A‖ * ρ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
  have h3 := norm_sub_le (opE (S.offsetP q) * opE A) (opE A * opE (S.offsetP q))
  linarith

/-- **The zero-order hold is the monolithic flow in staggered clocks, up to the third order.**
Let `q` be offsets of the subsystems (`q_s - q_t = ς_st` for partners) with `|q_s| ≤ ρ`, `T` the
matrix whose rows of subsystem `s` are those of `e^{½ q_s H A}`, and `X` the one-step map of the
zero-order hold. For `0 ≤ H`, `H ‖A‖ ≤ 1/4` and `√(card κ) · H ‖A‖ ≤ 1/6`:
`‖X T - T e^{HA}‖ ≤ offsetK σ ‖A‖ ρ H · H³`, `σ = √(card κ)`. -/
theorem norm_zoh_mul_offsetT_sub_le [Fintype κ] {q : κ → ℝ} (hq : S.IsOffset q) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ s, |q s| ≤ ρ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    ‖opE ((S.zoh A hA H).X * S.offsetT q A H - S.offsetT q A H * NormedSpace.exp (H • A))‖ ≤
      offsetK (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H * H ^ 3 := by
  have hWm : (H • A) * ((H / 2) • (S.offsetP q * A)) - ((H / 2) • (S.offsetP q * A)) * (H • A) =
      -((H ^ 2 / 2) • (S.signedCoupling A * A)) := by
    rw [S.signedCoupling_eq_commutator hq hA]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, Matrix.mul_assoc]
    module
  have hW : opE (H • A) * opE ((H / 2) • (S.offsetP q * A)) -
      opE ((H / 2) • (S.offsetP q * A)) * opE (H • A) =
      -opE ((H ^ 2 / 2) • (S.signedCoupling A * A)) := by
    rw [← opE_mul, ← opE_mul, ← opE_sub, hWm]
    exact map_neg _ _
  have hu₂ : ‖opE (NormedSpace.exp (H • A)) - 1 - opE (H • A)‖ ≤
      ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2 := by
    rw [opE_exp, opE_smul, sub_sub]
    exact norm_exp_smul_sub_linear_le (opE A) hH
  have hb := S.norm_half_smul_offsetP_mul_le hρ0 hρ A hH
  have hu₁ : ‖opE (NormedSpace.exp (H • A)) - 1‖ ≤ ‖opE A‖ * Real.exp (H * ‖opE A‖) * H := by
    rw [opE_exp, opE_smul]
    exact norm_exp_smul_sub_one_le (opE A) hH
  have hr := S.norm_offsetT_sub_le hρ A hH
  rw [opE_sub, opE_sub, opE_one] at hr
  have hw : ‖opE ((H ^ 2 / 2) • (S.signedCoupling A * A))‖ ≤
      H ^ 2 / 2 * (2 * ρ * ‖opE A‖ * ‖opE A‖) := by
    rw [opE_smul, opE_mul, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (S.norm_opE_signedCoupling_le_offset hq hρ0 hρ hA) (norm_nonneg _))) (by positivity)
  have hx := S.norm_zoh_step_sub_le hA hH hAH hσ
  rw [opE_sub, opE_sub] at hx
  rw [opE_sub, opE_mul, opE_mul]
  refine (norm_offset_conj_le ContinuousLinearMap.norm_id_le hW hu₂ hb hu₁ hr hw hx).trans_eq ?_
  rw [offsetK, offsetT1]
  ring

/-- **The staggered clocks with a constant free of `H`:** in the setting of
`norm_zoh_mul_offsetT_sub_le`, if in addition `ρ H ‖A‖ ≤ 1/2`, then
`‖X T - T e^{HA}‖ ≤ ((⅔ρ + ½ρ² + (19/36) σρ²) ‖A‖³ + zohStepK σ ‖A‖ (5/4 + σ/24)) · H³`. -/
theorem norm_zoh_mul_offsetT_sub_le_num [Fintype κ] {q : κ → ℝ} (hq : S.IsOffset q) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ s, |q s| ≤ ρ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6)
    (hρH : ρ * (H * ‖opE A‖) ≤ 1 / 2) :
    ‖opE ((S.zoh A hA H).X * S.offsetT q A H - S.offsetT q A H * NormedSpace.exp (H • A))‖ ≤
      offsetKNum (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ * H ^ 3 :=
  (S.norm_zoh_mul_offsetT_sub_le hq hρ0 hρ hA hH hAH hσ).trans
    (mul_le_mul_of_nonneg_right
      (offsetK_le (Real.sqrt_nonneg _) (norm_nonneg _) hρ0 hH hAH hρH) (by positivity))

/-- **`T` is invertible for a small macro step:** if `H t₁ < 1` (`t₁ = offsetT1`), then
`det T` is a unit. -/
theorem isUnit_det_offsetT [Fintype κ] {q : κ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ s, |q s| ≤ ρ)
    (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (ht : H * offsetT1 (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H < 1) :
    IsUnit (S.offsetT q A H).det := by
  have h1 := S.norm_offsetT_sub_one_le hρ0 hρ A hH
  have h2 : ‖1 - opE (S.offsetT q A H)‖ < 1 := by
    rw [norm_sub_rev, ← opE_one, ← opE_sub]
    exact h1.trans_lt ht
  have h3 := isUnit_one_sub_of_norm_lt_one h2
  rw [sub_sub_cancel] at h3
  have h4 := h3.map (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm
  rw [StarAlgEquiv.symm_apply_apply] at h4
  exact (Matrix.isUnit_iff_isUnit_det _).1 h4

/-- **The zero-order hold is conjugate to the monolithic flow up to the third order:** in the
setting of `norm_zoh_mul_offsetT_sub_le`, if `H t₁ < 1` (`t₁ = offsetT1`), then
`‖X - T e^{HA} T⁻¹‖ ≤ offsetK σ ‖A‖ ρ H · H³ / (1 - H t₁)`. -/
theorem norm_zoh_sub_conj_le [Fintype κ] {q : κ → ℝ} (hq : S.IsOffset q) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ s, |q s| ≤ ρ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6)
    (ht : H * offsetT1 (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H < 1) :
    ‖opE ((S.zoh A hA H).X -
        S.offsetT q A H * NormedSpace.exp (H • A) * (S.offsetT q A H)⁻¹)‖ ≤
      offsetK (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H * H ^ 3 /
        (1 - H * offsetT1 (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H) := by
  have hdet := S.isUnit_det_offsetT hρ0 hρ A hH ht
  have hTi : (S.offsetT q A H)⁻¹ * S.offsetT q A H = 1 := Matrix.nonsing_inv_mul _ hdet
  have hTi' : S.offsetT q A H * (S.offsetT q A H)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h1 := S.norm_offsetT_sub_one_le hρ0 hρ A hH
  have hpos : 0 < 1 - H * offsetT1 (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H := by linarith
  have hinv : ‖opE (S.offsetT q A H)⁻¹‖ ≤
      1 / (1 - H * offsetT1 (Real.sqrt (Fintype.card κ)) ‖opE A‖ ρ H) := by
    have e : (S.offsetT q A H)⁻¹ = 1 - (S.offsetT q A H)⁻¹ * (S.offsetT q A H - 1) := by
      rw [mul_sub, hTi, mul_one, sub_sub_cancel]
    have h2 : ‖opE (S.offsetT q A H)⁻¹‖ ≤
        1 + ‖opE (S.offsetT q A H)⁻¹‖ * ‖opE (S.offsetT q A H - 1)‖ := by
      have h3 := norm_sub_le (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (opE (S.offsetT q A H)⁻¹ * opE (S.offsetT q A H - 1))
      rw [← opE_mul, ← opE_one, ← opE_sub, ← e, opE_one, opE_mul] at h3
      have h4 := norm_mul_le (opE (S.offsetT q A H)⁻¹) (opE (S.offsetT q A H - 1))
      have h5 : ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le
      linarith
    have h6 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (opE (S.offsetT q A H)⁻¹))
    rw [le_div_iff₀ hpos]
    linarith
  have hK := S.norm_zoh_mul_offsetT_sub_le hq hρ0 hρ hA hH hAH hσ
  have e : (S.zoh A hA H).X -
      S.offsetT q A H * NormedSpace.exp (H • A) * (S.offsetT q A H)⁻¹ =
      ((S.zoh A hA H).X * S.offsetT q A H - S.offsetT q A H * NormedSpace.exp (H • A)) *
        (S.offsetT q A H)⁻¹ := by
    rw [sub_mul, mul_assoc (S.zoh A hA H).X, hTi', mul_one]
  rw [e, opE_mul, div_eq_mul_one_div]
  exact (norm_mul_le _ _).trans (mul_le_mul hK hinv (norm_nonneg _) ((norm_nonneg _).trans hK))

end HeldScheme

end CoSimFoundations
