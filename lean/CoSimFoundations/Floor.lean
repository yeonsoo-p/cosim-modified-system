/-
The accuracy floor of a class of schemes.

`D` is the one-step defect, `U` the reference step, `X = D ∘ U` the scheme's step, all on a real
inner product space (energy coordinates), and `α = ‖D - 1‖`.

* Turning floor. If the scheme keeps the `e`-component of what it makes of `e` non-negative,
  `0 ≤ ⟪e, X e⟫` (for a scalar store with a local gain: `X_ii > 0`), then
  `-⟪e, U e⟫ ≤ α ‖U e‖`: with `θ` the angle between `e` and `U e`, `α ≥ -cos θ`.
* Link floor. If the scheme moves nothing from `f` to `e`, `⟪e, X f⟫ = 0` (stores that are not
  coupled: `X_ij = 0`), then `|⟪e, U f⟫| ≤ α ‖U f‖ ≤ α ‖U‖`.

Both hold for every `D`, so no gains and no weights of the class break them.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component of `(D - 1) v` along a unit vector is at most `‖D - 1‖ ‖v‖` in modulus. -/
theorem abs_inner_sub_one_apply_le (D : E →L[ℝ] E) {e : E} (he : ‖e‖ = 1) (v : E) :
    |⟪e, (D - 1) v⟫| ≤ ‖D - 1‖ * ‖v‖ := by
  calc |⟪e, (D - 1) v⟫| ≤ ‖e‖ * ‖(D - 1) v‖ := abs_real_inner_le_norm _ _
    _ = ‖(D - 1) v‖ := by rw [he, one_mul]
    _ ≤ ‖D - 1‖ * ‖v‖ := (D - 1).le_opNorm v

/-- **Turning floor.** If `0 ≤ ⟪e, D (U e)⟫` for a unit vector `e`, then
`-⟪e, U e⟫ ≤ ‖D - 1‖ ‖U e‖`. -/
theorem turning_floor (D U : E →L[ℝ] E) {e : E} (he : ‖e‖ = 1) (h : 0 ≤ ⟪e, D (U e)⟫) :
    -⟪e, U e⟫ ≤ ‖D - 1‖ * ‖U e‖ := by
  have h1 := abs_inner_sub_one_apply_le D he (U e)
  have h2 : ⟪e, (D - 1) (U e)⟫ = ⟪e, D (U e)⟫ - ⟪e, U e⟫ := by
    simp [inner_sub_right]
  have h3 := le_abs_self ⟪e, (D - 1) (U e)⟫
  linarith

/-- **Link floor.** If `⟪e, D (U f)⟫ = 0` for a unit vector `e`, then
`|⟪e, U f⟫| ≤ ‖D - 1‖ ‖U f‖`. -/
theorem link_floor (D U : E →L[ℝ] E) {e : E} (he : ‖e‖ = 1) (f : E) (h : ⟪e, D (U f)⟫ = 0) :
    |⟪e, U f⟫| ≤ ‖D - 1‖ * ‖U f‖ := by
  have h1 := abs_inner_sub_one_apply_le D he (U f)
  have h2 : ⟪e, (D - 1) (U f)⟫ = -⟪e, U f⟫ := by
    simp [inner_sub_right, h]
  rwa [h2, abs_neg] at h1

/-- **Link floor, in terms of `‖U‖`.** For unit vectors `e`, `f` with `⟪e, D (U f)⟫ = 0`,
`|⟪e, U f⟫| ≤ ‖D - 1‖ ‖U‖`. -/
theorem link_floor_opNorm (D U : E →L[ℝ] E) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (h : ⟪e, D (U f)⟫ = 0) : |⟪e, U f⟫| ≤ ‖D - 1‖ * ‖U‖ := by
  refine (link_floor D U he f h).trans ?_
  have : ‖U f‖ ≤ ‖U‖ := by simpa [hf] using U.le_opNorm f
  gcongr

/-- The sum and the difference of two orthonormal vectors have squared norm `2`. -/
theorem norm_add_sq_of_orthonormal {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) : ‖e₁ + e₂‖ ^ 2 = 2 ∧ ‖e₁ - e₂‖ ^ 2 = 2 := by
  constructor
  · rw [norm_add_sq_real, h1, h2, h12]; norm_num
  · rw [norm_sub_sq_real, h1, h2, h12]; norm_num

end CoSimFoundations
