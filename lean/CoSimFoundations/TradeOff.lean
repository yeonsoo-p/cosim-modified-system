/-
The trade-off that the link floor forces between accuracy and energy.

`D` is the one-step defect, `U` the reference step, `X = D ∘ U` the scheme's step, on a real inner
product space (energy coordinates); `α = ‖D - 1‖`, largest stretch `‖D‖`.

Let `e₁`, `e₂` be orthonormal (two stores) between which the scheme moves nothing in either
direction: `⟪e₁, X e₂⟫ = 0` and `⟪e₂, X e₁⟫ = 0` (stores that are not coupled). Put

  `u = ⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫`  (what the reference moves between them, both directions),
  `η = ‖U e₁ - e₁‖ + ‖U e₂ - e₂‖`  (of first order in the macro step).

Then

* `|u| ≤ (‖D‖ - 1) + α (1 + η)`: accuracy and growth of energy cannot both be small;
* if `m ‖x‖ ≤ ‖D x‖` for all `x` (`m` a lower bound of the least stretch), then
  `m² ≤ 1 + α² - 2 (|u| - α (1 + η))`: some state loses energy relative to the reference.

For skew coupling `u = H² [A²]₁₂ + O(H³)`, twice the link floor to leading order. A scheme on the
link floor (`α = |u|/2`) therefore has `‖D‖ - 1 ≳ |u|/2`: it adds energy at the rate of its own
error, and a scheme that adds no energy has `α ≳ |u|`, twice the link floor.

Proof: the symmetric part of `D - 1` has the entry `-u/2` (up to `α η`) between the two stores;
test its quadratic form on `e₁ + e₂` and `e₁ - e₂`.
-/
import CoSimFoundations.Floor

open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- What the scheme's error moves between two stores that it does not connect: the entry of
`D - 1` is minus the entry of `U`, up to `‖D - 1‖ ‖U f - f‖`. -/
theorem abs_inner_sub_one_add_le (D U : E →L[ℝ] E) {e f : E} (he : ‖e‖ = 1)
    (h : ⟪e, D (U f)⟫ = 0) :
    |⟪e, (D - 1) f⟫ + ⟪e, U f⟫| ≤ ‖D - 1‖ * ‖U f - f‖ := by
  have h1 := abs_inner_sub_one_apply_le D he (U f - f)
  have h2 : ⟪e, (D - 1) (U f - f)⟫ = -(⟪e, (D - 1) f⟫ + ⟪e, U f⟫) := by
    have : (D - 1) (U f - f) = D (U f) - U f - (D - 1) f := by
      simp [map_sub]
    rw [this, inner_sub_right, inner_sub_right, h]
    ring
  rw [h2, abs_neg] at h1
  exact h1

section Forms

variable (D : E →L[ℝ] E) {e₁ e₂ : E}

/-- The quadratic form of `D - 1` on `e₁ + e₂` and on `e₁ - e₂`. -/
theorem inner_add_sub_one (e₁ e₂ : E) :
    ⟪e₁ + e₂, (D - 1) (e₁ + e₂)⟫ =
      ⟪e₁, (D - 1) e₁⟫ + ⟪e₂, (D - 1) e₂⟫ + (⟪e₁, (D - 1) e₂⟫ + ⟪e₂, (D - 1) e₁⟫) := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  ring

theorem inner_sub_sub_one (e₁ e₂ : E) :
    ⟪e₁ - e₂, (D - 1) (e₁ - e₂)⟫ =
      ⟪e₁, (D - 1) e₁⟫ + ⟪e₂, (D - 1) e₂⟫ - (⟪e₁, (D - 1) e₂⟫ + ⟪e₂, (D - 1) e₁⟫) := by
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
  ring

/-- `|⟪x, (D - 1) x⟫| ≤ ‖D - 1‖ ‖x‖²`. -/
theorem abs_inner_sub_one_self_le (x : E) : |⟪x, (D - 1) x⟫| ≤ ‖D - 1‖ * ‖x‖ ^ 2 := by
  calc |⟪x, (D - 1) x⟫| ≤ ‖x‖ * ‖(D - 1) x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖D - 1‖ * ‖x‖) := by gcongr; exact (D - 1).le_opNorm x
    _ = ‖D - 1‖ * ‖x‖ ^ 2 := by ring

/-- `⟪x, D x⟫ = ‖x‖² + ⟪x, (D - 1) x⟫ ≤ ‖D‖ ‖x‖²`. -/
theorem sq_add_inner_sub_one_le (x : E) : ‖x‖ ^ 2 + ⟪x, (D - 1) x⟫ ≤ ‖D‖ * ‖x‖ ^ 2 := by
  have h1 : ‖x‖ ^ 2 + ⟪x, (D - 1) x⟫ = ⟪x, D x⟫ := by
    simp [inner_sub_right]
  rw [h1]
  calc ⟪x, D x⟫ ≤ ‖x‖ * ‖D x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖D‖ * ‖x‖) := by gcongr; exact D.le_opNorm x
    _ = ‖D‖ * ‖x‖ ^ 2 := by ring

/-- `‖D x‖² = ‖x‖² + 2 ⟪x, (D - 1) x⟫ + ‖(D - 1) x‖² ≤ ‖x‖² + 2 ⟪x, (D - 1) x⟫ + ‖D - 1‖² ‖x‖²`. -/
theorem norm_sq_apply_le (x : E) :
    ‖D x‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * ⟪x, (D - 1) x⟫ + ‖D - 1‖ ^ 2 * ‖x‖ ^ 2 := by
  have h1 : D x = x + (D - 1) x := by simp
  have h2 : ‖(D - 1) x‖ ^ 2 ≤ ‖D - 1‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((D - 1).le_opNorm x) 2
  rw [h1, norm_add_sq_real]
  linarith

end Forms

/-- The sum and the difference of two orthonormal vectors have squared norm `2`. -/
theorem norm_add_sq_of_orthonormal {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) : ‖e₁ + e₂‖ ^ 2 = 2 ∧ ‖e₁ - e₂‖ ^ 2 = 2 := by
  constructor
  · rw [norm_add_sq_real, h1, h2, h12]; norm_num
  · rw [norm_sub_sq_real, h1, h2, h12]; norm_num

/-- **The link floor forces a trade-off between accuracy and energy.** -/
theorem link_tradeoff (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0) :
    |⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| ≤
      (‖D‖ - 1) + ‖D - 1‖ * (1 + (‖U e₁ - e₁‖ + ‖U e₂ - e₂‖)) := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have r1 := abs_le.1 (abs_inner_sub_one_add_le D U h1 hz1)
  have r2 := abs_le.1 (abs_inner_sub_one_add_le D U h2 hz2)
  have qp := abs_le.1 (abs_inner_sub_one_self_le D (e₁ + e₂))
  have qm := abs_le.1 (abs_inner_sub_one_self_le D (e₁ - e₂))
  have dp := sq_add_inner_sub_one_le D (e₁ + e₂)
  have dm := sq_add_inner_sub_one_le D (e₁ - e₂)
  rw [hp] at qp dp
  rw [hm] at qm dm
  rw [inner_add_sub_one] at qp dp
  rw [inner_sub_sub_one] at qm dm
  rw [abs_le]
  constructor <;> linarith [qp.1, qp.2, qm.1, qm.2, r1.1, r1.2, r2.1, r2.2]

/-- **The other end of the trade-off:** some state loses energy relative to the reference. -/
theorem link_tradeoff_least (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    {m : ℝ} (hm0 : 0 ≤ m) (hmD : ∀ x, m * ‖x‖ ≤ ‖D x‖) :
    m ^ 2 ≤ 1 + ‖D - 1‖ ^ 2 -
      2 * (|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| - ‖D - 1‖ * (1 + (‖U e₁ - e₁‖ + ‖U e₂ - e₂‖))) := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have r1 := abs_le.1 (abs_inner_sub_one_add_le D U h1 hz1)
  have r2 := abs_le.1 (abs_inner_sub_one_add_le D U h2 hz2)
  have qp := abs_le.1 (abs_inner_sub_one_self_le D (e₁ + e₂))
  have qm := abs_le.1 (abs_inner_sub_one_self_le D (e₁ - e₂))
  have np := norm_sq_apply_le D (e₁ + e₂)
  have nm := norm_sq_apply_le D (e₁ - e₂)
  have mp : (m * ‖e₁ + e₂‖) ^ 2 ≤ ‖D (e₁ + e₂)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) (hmD _) 2
  have mm : (m * ‖e₁ - e₂‖) ^ 2 ≤ ‖D (e₁ - e₂)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) (hmD _) 2
  rw [mul_pow, hp] at mp
  rw [mul_pow, hm] at mm
  rw [hp] at qp np
  rw [hm] at qm nm
  rw [inner_add_sub_one] at qp np
  rw [inner_sub_sub_one] at qm nm
  rcases abs_cases (⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫) with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;>
    linarith [qp.1, qp.2, qm.1, qm.2, r1.1, r1.2, r2.1, r2.2]

/-- **Energy cannot be kept in every state.** The largest stretch and a lower bound `m` of the least
stretch are apart by what the reference moves between the two stores:
`(‖D‖ - 1) + (1 - m²)/2 ≥ |u| - α (η + α/2)`. For a scheme with a one-step error of second order
in the macro step the right side is `|u|` to leading order, twice the link floor. -/
theorem link_tradeoff_spread (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    {m : ℝ} (hm0 : 0 ≤ m) (hmD : ∀ x, m * ‖x‖ ≤ ‖D x‖) :
    |⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| -
        ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2) ≤
      (‖D‖ - 1) + (1 - m ^ 2) / 2 := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have r1 := abs_le.1 (abs_inner_sub_one_add_le D U h1 hz1)
  have r2 := abs_le.1 (abs_inner_sub_one_add_le D U h2 hz2)
  have dp := sq_add_inner_sub_one_le D (e₁ + e₂)
  have dm := sq_add_inner_sub_one_le D (e₁ - e₂)
  have np := norm_sq_apply_le D (e₁ + e₂)
  have nm := norm_sq_apply_le D (e₁ - e₂)
  have mp : (m * ‖e₁ + e₂‖) ^ 2 ≤ ‖D (e₁ + e₂)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) (hmD _) 2
  have mm : (m * ‖e₁ - e₂‖) ^ 2 ≤ ‖D (e₁ - e₂)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) (hmD _) 2
  rw [mul_pow, hp] at mp
  rw [mul_pow, hm] at mm
  rw [hp] at dp np
  rw [hm] at dm nm
  rw [inner_add_sub_one] at dp np
  rw [inner_sub_sub_one] at dm nm
  rcases abs_cases (⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫) with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;>
    nlinarith [r1.1, r1.2, r2.1, r2.2, sq_nonneg ‖D - 1‖]

end CoSimFoundations
