/-
Floors of the difference (the paper, Cor 6.4), operator form.

`A` generates the reference, `Ã` the modified system, both operators on a real Hilbert space
(energy coordinates). If the co-simulation step `exp (H • Ã)` sends `f` to a vector with no
component along the unit vector `e` (two stores that are not coupled), then what the reference
sends there is bounded by the difference:

  `|⟪e, exp (H • A) f⟫| ≤ H · (a · ‖Ã - A‖ · b) · ‖exp (H • A) f‖`,

with `a`, `b` bounds for `‖exp (τ • Ã)‖`, `‖exp (-τ • A)‖` on `[0, H]`. Since the left side is
`½ H² |[A²]_{ef}| + O(H³)` for stores two links apart, `‖Ã - A‖` is at least of first order in `H`:
the order barrier. Likewise for the turning floor.
-/
import CoSimFoundations.Floor
import CoSimFoundations.DefectDifference

open NormedSpace
open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Undoing the reference step and applying the defect is the co-simulation step. -/
theorem defect_apply_reference (At A : E →L[ℝ] E) (H : ℝ) (f : E) :
    (exp (H • At) * exp (H • (-A))) (exp (H • A) f) = exp (H • At) f := by
  let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  have h : exp (H • (-A)) * exp (H • A) = 1 := by
    rw [← exp_add_of_commute ((Commute.refl A).neg_left.smul_left H |>.smul_right H), smul_neg,
      neg_add_cancel, exp_zero]
  have h2 : exp (H • (-A)) (exp (H • A) f) = f := by
    have := congrArg (fun T : E →L[ℝ] E => T f) h
    simpa using this
  change exp (H • At) (exp (H • (-A)) (exp (H • A) f)) = exp (H • At) f
  rw [h2]

/-- **Link floor of the difference, from a bound of the defect.** If `‖e‖ = 1`,
`e ⊥ exp (H Ã) f` and `‖exp (H Ã) exp (-H A) - 1‖ ≤ c`, then
`|⟪e, exp (H A) f⟫| ≤ c ‖exp (H A) f‖`. -/
theorem difference_link_floor_of_le (At A : E →L[ℝ] E) {H c : ℝ}
    (hc : ‖exp (H • At) * exp (H • (-A)) - 1‖ ≤ c) {e : E} (he : ‖e‖ = 1) (f : E)
    (h : ⟪e, exp (H • At) f⟫ = 0) : |⟪e, exp (H • A) f⟫| ≤ c * ‖exp (H • A) f‖ :=
  (link_floor (exp (H • At) * exp (H • (-A))) (exp (H • A)) he f
    (by rw [defect_apply_reference]; exact h)).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

/-- **Turning floor of the difference, from a bound of the defect.** If `‖e‖ = 1`,
`0 ≤ ⟪e, exp (H Ã) e⟫` and `‖exp (H Ã) exp (-H A) - 1‖ ≤ c`, then
`-⟪e, exp (H A) e⟫ ≤ c ‖exp (H A) e‖`. -/
theorem difference_turning_floor_of_le (At A : E →L[ℝ] E) {H c : ℝ}
    (hc : ‖exp (H • At) * exp (H • (-A)) - 1‖ ≤ c) {e : E} (he : ‖e‖ = 1)
    (h : 0 ≤ ⟪e, exp (H • At) e⟫) : -⟪e, exp (H • A) e⟫ ≤ c * ‖exp (H • A) e‖ :=
  (turning_floor (exp (H • At) * exp (H • (-A))) (exp (H • A)) he
    (by rw [defect_apply_reference]; exact h)).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

/-- **Link floor of the difference.** -/
theorem difference_link_floor (At A : E →L[ℝ] E) {H a b : ℝ} (hH : 0 ≤ H)
    (ha : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • At)‖ ≤ a) (hb : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • (-A))‖ ≤ b)
    {e : E} (he : ‖e‖ = 1) (f : E) (h : ⟪e, exp (H • At) f⟫ = 0) :
    |⟪e, exp (H • A) f⟫| ≤ H * (a * ‖At - A‖ * b) * ‖exp (H • A) f‖ :=
  difference_link_floor_of_le At A (norm_defect_sub_one_le At A hH ha hb) he f h

/-- **Turning floor of the difference.** -/
theorem difference_turning_floor (At A : E →L[ℝ] E) {H a b : ℝ} (hH : 0 ≤ H)
    (ha : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • At)‖ ≤ a) (hb : ∀ τ ∈ Set.Icc 0 H, ‖exp (τ • (-A))‖ ≤ b)
    {e : E} (he : ‖e‖ = 1) (h : 0 ≤ ⟪e, exp (H • At) e⟫) :
    -⟪e, exp (H • A) e⟫ ≤ H * (a * ‖At - A‖ * b) * ‖exp (H • A) e‖ :=
  difference_turning_floor_of_le At A (norm_defect_sub_one_le At A hH ha hb) he h

end CoSimFoundations
