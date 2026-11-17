/-
Injection and added damping: the second inequality of Theorem 6.2 (`thm:access`, `eq:access`) of
the the paper, and the identity behind Corollary 6.4 (`cor:own`).

**Theorem 6.2, second inequality.** `D` the defect, `U` the reference step, `X = D ∘ U`, on a
real inner product space; `α = ‖D - 1‖ < 1`; `D'` a left inverse of `D` (`D' ∘ D = 1`); `e` a
unit vector, `g = ⟪e, X e⟫ - ⟪e, U e⟫`. Then (`diag_gain_inv`)

  `-g - α / (1 - α) · ‖X e - e‖ ≤ ‖D'‖ - 1`.

Here `‖D'‖` stands for the paper's `1 / s₋`: for an invertible `D` the smallest singular value is
`s₋ = inf ‖D v‖ / ‖v‖ = 1 / ‖D⁻¹‖`. Three forms are given:
* `diag_gain_inv`: with any left inverse `D'` (no completeness, no finite dimension);
* `diag_gain_inverse`: in a complete space, with `Ring.inverse D`, which is the inverse because
  `α < 1` (Neumann series);
* `diag_gain_smin`: with any `s > 0` such that `s ‖v‖ ≤ ‖D v‖` for all `v` (any lower bound of
  the stretch, in particular `s = s₋`): `-g - α / (1 - α) · ‖X e - e‖ ≤ 1 / s - 1`.
  `le_norm_mul_of_left_inverse` shows that `s = 1 / ‖D'‖` is such a bound.

Proof (the paper's): `D' (X e) = U e`, hence
`⟪e, D' e⟫ - 1 = -g - ⟪e, (D' - 1) (X e - e)⟫`; `D' - 1 = -D' (D - 1)` gives
`‖D'‖ ≤ 1 / (1 - α)` and `‖(D' - 1) v‖ ≤ α / (1 - α) ‖v‖`; and `⟪e, D' e⟫ ≤ ‖D'‖`.
The first inequality of `eq:access` is `diag_gain` in `PairLaws.lean`.

**Corollary 6.4, the identity.** For real matrices `B` (`n × m`), `B_k` (`n_k × m_k`), `L_k`
(`m_k × m`), signs `ς_k`, and the gain `K = (H/2) Σ_k ς_k L_kᵀ B_kᵀ B_k L_k`
(`own_output_gain`):

  `H B K Bᵀ = ½H² Σ_k ς_k A_kᵀ A_k`,   `A_k = B_k L_k Bᵀ`.

With `B = B_i`, `L_k = L_{ki}`, `A_k = A_{ki}` this is the identity
`H B_i K_i B_iᵀ = ½H² Σ_k ς_{ik} A_{ki}ᵀ A_{ki}` of the proof of Corollary 6.4: the gain supplies
the term that the reaction (Proposition 6.1, `ReactionDiag.lean`) leaves in the diagonal block.
Only this identity is formalised here, not the step `F_i - e^{H A_i} = H B_i K_i B_iᵀ + O(H³)` of
the proof.
-/
import CoSimFoundations.PairLaws
import CoSimFoundations.MemoryBound
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Data.Matrix.Mul

open scoped RealInnerProductSpace

namespace CoSimFoundations

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a left inverse `D'` of `D`: `‖D' v - v‖ ≤ ‖D'‖ ‖D - 1‖ ‖v‖`, from
`D' - 1 = -D' (D - 1)`. -/
theorem norm_apply_sub_le_of_left_inverse {D D' : E →L[ℝ] E} (hinv : D' * D = 1) (v : E) :
    ‖D' v - v‖ ≤ ‖D'‖ * ‖D - 1‖ * ‖v‖ := by
  have e : D' v - v = -D' (D v - v) := by
    rw [map_sub, left_inverse_apply hinv, neg_sub]
  have e2 : D v - v = (D - 1) v := by simp
  rw [e, norm_neg, e2]
  calc ‖D' ((D - 1) v)‖ ≤ ‖D'‖ * ‖(D - 1) v‖ := D'.le_opNorm _
    _ ≤ ‖D'‖ * (‖D - 1‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((D - 1).le_opNorm v) (norm_nonneg _)
    _ = ‖D'‖ * ‖D - 1‖ * ‖v‖ := by ring

/-- A left inverse of a map at distance `α < 1` from the identity has norm at most
`1 / (1 - α)`. -/
theorem norm_le_of_left_inverse {D D' : E →L[ℝ] E} (hinv : D' * D = 1) (hα : ‖D - 1‖ < 1) :
    ‖D'‖ ≤ 1 / (1 - ‖D - 1‖) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [ContinuousLinearMap.opNorm_subsingleton]
    exact div_nonneg zero_le_one (sub_pos.2 hα).le
  · exact norm_le_of_mul_eq_one (𝔸 := (E →L[ℝ] E)ᵐᵒᵖ) (D := MulOpposite.op D)
      (D' := MulOpposite.op D') (congrArg MulOpposite.op hinv) hα

/-- For a left inverse `D'` of `D` with `α = ‖D - 1‖ < 1`:
`‖D' v - v‖ ≤ α / (1 - α) ‖v‖`. -/
theorem norm_apply_sub_le_of_left_inverse' {D D' : E →L[ℝ] E} (hinv : D' * D = 1)
    (hα : ‖D - 1‖ < 1) (v : E) : ‖D' v - v‖ ≤ ‖D - 1‖ / (1 - ‖D - 1‖) * ‖v‖ := by
  refine (norm_apply_sub_le_of_left_inverse hinv v).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖D'‖ * ‖D - 1‖ ≤ 1 / (1 - ‖D - 1‖) * ‖D - 1‖ :=
        mul_le_mul_of_nonneg_right (norm_le_of_left_inverse hinv hα) (norm_nonneg _)
    _ = ‖D - 1‖ / (1 - ‖D - 1‖) := by rw [one_div, inv_mul_eq_div]

/-- A left inverse bounds the stretch from below: `‖v‖ ≤ ‖D'‖ ‖D v‖`, so that
`s = 1 / ‖D'‖` satisfies `s ‖v‖ ≤ ‖D v‖` (the smallest singular value is at least `1 / ‖D'‖`). -/
theorem le_norm_mul_of_left_inverse {D D' : E →L[ℝ] E} (hinv : D' * D = 1) (v : E) :
    ‖v‖ ≤ ‖D'‖ * ‖D v‖ := by
  have h := D'.le_opNorm (D v)
  rwa [left_inverse_apply hinv] at h

/-- **Theorem 6.2, second inequality** (added damping). `X = D ∘ U`, `D'` a left inverse of `D`,
`α = ‖D - 1‖ < 1`, `e` a unit vector, `g = ⟪e, X e⟫ - ⟪e, U e⟫`:
`-g - α / (1 - α) · ‖X e - e‖ ≤ ‖D'‖ - 1`, where `‖D'‖ = ‖D⁻¹‖` is the paper's `1 / s₋`. -/
theorem diag_gain_inv (D D' U : E →L[ℝ] E) (hinv : D' * D = 1) (hα : ‖D - 1‖ < 1) {e : E}
    (he : ‖e‖ = 1) :
    -(⟪e, D (U e)⟫ - ⟪e, U e⟫) - ‖D - 1‖ / (1 - ‖D - 1‖) * ‖D (U e) - e‖ ≤ ‖D'‖ - 1 := by
  have h1 : ⟪e, D' e⟫ ≤ ‖D'‖ := by
    have h := (real_inner_le_norm e (D' e)).trans
      (mul_le_mul_of_nonneg_left (D'.le_opNorm e) (norm_nonneg e))
    rwa [he, one_mul, mul_one] at h
  have h2 : D' e = U e - (D (U e) - e) - (D' (D (U e) - e) - (D (U e) - e)) := by
    rw [map_sub, left_inverse_apply hinv]
    abel
  have h3 : ⟪e, D' e⟫ = ⟪e, U e⟫ - ⟪e, D (U e)⟫ + 1 -
      ⟪e, D' (D (U e) - e) - (D (U e) - e)⟫ := by
    have h4 : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    rw [h2, inner_sub_right, inner_sub_right, inner_sub_right, h4]
    simp only [map_sub, left_inverse_apply hinv, inner_sub_right, h4]
    ring
  have h5 : ⟪e, D' (D (U e) - e) - (D (U e) - e)⟫ ≤
      ‖D - 1‖ / (1 - ‖D - 1‖) * ‖D (U e) - e‖ := by
    have h := (real_inner_le_norm e (D' (D (U e) - e) - (D (U e) - e))).trans
      (mul_le_mul_of_nonneg_left
        (norm_apply_sub_le_of_left_inverse' hinv hα (D (U e) - e)) (norm_nonneg e))
    rwa [he, one_mul] at h
  linarith

/-- In a complete space a map at distance less than one from the identity is invertible. -/
theorem isUnit_of_norm_sub_one_lt_one [CompleteSpace E] {D : E →L[ℝ] E} (hα : ‖D - 1‖ < 1) :
    IsUnit D := by
  have h := isUnit_one_sub_of_norm_lt_one (x := 1 - D) (by rwa [norm_sub_rev])
  rwa [sub_sub_cancel] at h

/-- **Theorem 6.2, second inequality, with the inverse.** In a complete space `D` with
`α = ‖D - 1‖ < 1` is invertible, and with `X = D ∘ U`, a unit vector `e` and
`g = ⟪e, X e⟫ - ⟪e, U e⟫`: `-g - α / (1 - α) · ‖X e - e‖ ≤ ‖D⁻¹‖ - 1` (`D⁻¹ = Ring.inverse D`). -/
theorem diag_gain_inverse [CompleteSpace E] (D U : E →L[ℝ] E) (hα : ‖D - 1‖ < 1) {e : E}
    (he : ‖e‖ = 1) :
    -(⟪e, D (U e)⟫ - ⟪e, U e⟫) - ‖D - 1‖ / (1 - ‖D - 1‖) * ‖D (U e) - e‖ ≤
      ‖Ring.inverse D‖ - 1 :=
  diag_gain_inv D (Ring.inverse D) U
    (Ring.inverse_mul_cancel D (isUnit_of_norm_sub_one_lt_one hα)) hα he

/-- A right inverse of a map whose stretch is at least `s > 0` has norm at most `1 / s`. With
`le_norm_mul_of_left_inverse`: the smallest stretch of an invertible `D` is `1 / ‖D⁻¹‖`. -/
theorem norm_le_of_right_inverse {D D' : E →L[ℝ] E} (hr : D * D' = 1) {s : ℝ} (hs : 0 < s)
    (hD : ∀ v, s * ‖v‖ ≤ ‖D v‖) : ‖D'‖ ≤ 1 / s := by
  refine D'.opNorm_le_bound (by positivity) fun w => ?_
  have h2 := hD (D' w)
  rw [left_inverse_apply hr] at h2
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs]
  linarith

/-- **Theorem 6.2, second inequality, with the smallest stretch.** If `D` has a two-sided
inverse and `s > 0` is a lower bound of its stretch, `s ‖v‖ ≤ ‖D v‖` for all `v` (in particular
the smallest singular value `s₋`), then `-g - α / (1 - α) · ‖X e - e‖ ≤ 1 / s - 1`. -/
theorem diag_gain_smin (D D' U : E →L[ℝ] E) (hl : D' * D = 1) (hr : D * D' = 1)
    (hα : ‖D - 1‖ < 1) {e : E} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s)
    (hD : ∀ v, s * ‖v‖ ≤ ‖D v‖) :
    -(⟪e, D (U e)⟫ - ⟪e, U e⟫) - ‖D - 1‖ / (1 - ‖D - 1‖) * ‖D (U e) - e‖ ≤ 1 / s - 1 := by
  have h1 : ‖D'‖ ≤ 1 / s := norm_le_of_right_inverse hr hs hD
  have h3 := diag_gain_inv D D' U hl hα he
  linarith

/-- **Theorem 6.2, second inequality, with the smallest stretch, in a complete space**: no
inverse has to be supplied. If `α = ‖D - 1‖ < 1` and `s > 0` satisfies `s ‖v‖ ≤ ‖D v‖` for all
`v`, then `-g - α / (1 - α) · ‖X e - e‖ ≤ 1 / s - 1`. -/
theorem diag_gain_smin_complete [CompleteSpace E] (D U : E →L[ℝ] E) (hα : ‖D - 1‖ < 1) {e : E}
    (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) (hD : ∀ v, s * ‖v‖ ≤ ‖D v‖) :
    -(⟪e, D (U e)⟫ - ⟪e, U e⟫) - ‖D - 1‖ / (1 - ‖D - 1‖) * ‖D (U e) - e‖ ≤ 1 / s - 1 :=
  diag_gain_smin D (Ring.inverse D) U
    (Ring.inverse_mul_cancel D (isUnit_of_norm_sub_one_lt_one hα))
    (Ring.mul_inverse_cancel D (isUnit_of_norm_sub_one_lt_one hα)) hα he hs hD

end Inverse

section Own

open Matrix

variable {ι n m : Type*} [Fintype n] [Fintype m] {nk mk : ι → Type*} [∀ k, Fintype (nk k)]
  [∀ k, Fintype (mk k)]

/-- **The identity behind Corollary 6.4** (the reaction from the own output). With the gain
`K = (H/2) Σ_k ς_k L_kᵀ B_kᵀ B_k L_k` and `A_k = B_k L_k Bᵀ`:
`H B K Bᵀ = ½H² Σ_k ς_k A_kᵀ A_k`. -/
theorem own_output_gain (P : Finset ι) (ς : ι → ℝ) (H : ℝ) (B : Matrix n m ℝ)
    (Bk : ∀ k, Matrix (nk k) (mk k) ℝ) (Lk : ∀ k, Matrix (mk k) m ℝ) :
    H • (B * ((H / 2) • ∑ k ∈ P, ς k • ((Lk k)ᵀ * (Bk k)ᵀ * Bk k * Lk k)) * Bᵀ) =
      (H ^ 2 / 2) • ∑ k ∈ P, ς k • ((Bk k * Lk k * Bᵀ)ᵀ * (Bk k * Lk k * Bᵀ)) := by
  have e : ∀ k, B * ((Lk k)ᵀ * (Bk k)ᵀ * Bk k * Lk k) * Bᵀ =
      (Bk k * Lk k * Bᵀ)ᵀ * (Bk k * Lk k * Bᵀ) := by
    intro k
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_sum, Matrix.sum_mul]
  have e2 : H * (H / 2) = H ^ 2 / 2 := by ring
  rw [e2]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, e k]

end Own

end CoSimFoundations
