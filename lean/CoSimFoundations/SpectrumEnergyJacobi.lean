/-
What the laws for every scheme say for a class that moves nothing between two directions: the one-sample Jacobi instance.

`D` the defect, `U` the reference step, `X = D ∘ U`; `e₁`, `e₂` orthonormal with
`⟪e₁, X e₂⟫ = 0 = ⟪e₂, X e₁⟫` (two stores that are not partners; or two directions, each in the
kernel of the other subsystem's output map). `u = ⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫`,
`η = ‖U e₁ - e₁‖ + ‖U e₂ - e₂‖`, `α = ‖D - 1‖`.

* **No energy added and the mean damping kept force a first-order error:** if `‖D‖ ≤ 1` and
  `1 ≤ |det D|`, then `|u| ≤ α (η + α/2)`. Since `|u|` is of second order in the macro step and `η`
  of first order, `α` is of first order: the difference of such a scheme does not vanish with the
  macro step.
* **Without local gains the trace of a Jacobi step does not depend on the weights:**
  `tr X = Σ_i e^{a_i H}`; so the spectrum of the reference, whose trace differs at second order, is
  out of reach.
* **Lossless reference: the energy error accumulates over a run, whatever the spectrum.** `U` an
  isometry with inverse `V`, `D = X ∘ V`; if `‖(Xᵏ)† Xᵏ - 1‖ ≤ ε` for all `k ≤ K`, then
  `K (|u| - α (η + α/2)) ≤ ε (1 + K (1 + ‖X‖) ‖X - 1‖)`. Proof: `D` has the stretches of `X`, so
  the pair trade-off bounds `|u| - α (η + α/2)` by `‖X† X - 1‖`; then `energy_accumulation`.
* **Gauss-Seidel in the order 1-2-3 escapes on the chain of three:** with `c = 2 cos (h/√2) - 1`,
  `s² = 1 - c²`, the product of two plane rotations `X = G₂₃ G₁₂` is orthogonal, has the zero
  `X₁₃ = 0` and the minor `X₂₁ X₃₂ = X₂₂ X₃₁` that the class forces, `det X = 1`, and
  `tr X = 1 + 2 cos (√2 h)`. Not formalized here: that this is the trace of the lossless reference
  step `e^{hA}` (eigenvalues `1`, `e^{± i √2 h}`), that a rotation of `ℝ³` with this trace therefore
  has exactly the spectrum of the reference, and that `X` is realised by a scheme of the class.
-/
import CoSimFoundations.DetStretch
import CoSimFoundations.PairTradeOff
import CoSimFoundations.ScalarStores

open Module
open scoped RealInnerProductSpace InnerProduct

namespace CoSimFoundations

section Pair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **No energy added and the mean damping kept force a first-order one-step error.** -/
theorem first_order_of_no_gain_of_det [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E}
    (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0)
    (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hD : ‖D‖ ≤ 1) (hdet : 1 ≤ |LinearMap.det (D : E →ₗ[ℝ] E)|) :
    |⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| ≤
      ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2) := by
  have h := pair_tradeoff_isometry D U h1 h2 h12
    (isometry_of_opNorm_le_one_of_one_le_abs_det D hD hdet)
  rwa [inner_sub_right, inner_sub_right, hz1, hz2, sub_zero, sub_zero] at h

end Pair

section Run

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **One step changes the energy of a state by at most `‖X† X - 1‖` times it:**
`|‖X y‖² - ‖y‖²| ≤ ‖X† X - 1‖ ‖y‖²`. -/
theorem abs_norm_sq_apply_sub_le (X : E →L[ℝ] E) (y : E) :
    |‖X y‖ ^ 2 - ‖y‖ ^ 2| ≤ ‖X† * X - 1‖ * ‖y‖ ^ 2 := by
  have h : ‖X y‖ ^ 2 - ‖y‖ ^ 2 = ⟪y, (X† * X - 1) y⟫ := by
    rw [sub_apply, one_apply_eq_self, inner_sub_right, mul_apply_eq_comp,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
  rw [h]
  calc |⟪y, (X† * X - 1) y⟫| ≤ ‖y‖ * ‖(X† * X - 1) y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖X† * X - 1‖ * ‖y‖) := by gcongr; exact (X† * X - 1).le_opNorm y
    _ = ‖X† * X - 1‖ * ‖y‖ ^ 2 := by ring

/-- **Lossless reference: what the scheme fails to move between two directions is paid in
energy.** `U` an isometry with inverse `V`, `X` any scheme, `D = X ∘ V` its defect,
`α = ‖D - 1‖`: `|u_X| - α (η + α/2) ≤ ‖X† X - 1‖`, the largest one-step energy error of the
scheme. (`D` has the stretches of `X`, and `pair_tradeoff_sq` applies with
`lo = 1 - ‖X† X - 1‖`, `hi = 1 + ‖X† X - 1‖`.) -/
theorem pair_tradeoff_lossless (X U V : E →L[ℝ] E) (hU : ∀ x, ‖U x‖ = ‖x‖) (hUV : U * V = 1)
    (hVU : V * U = 1) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) :
    |⟪e₁, U e₂ - X e₂⟫ + ⟪e₂, U e₁ - X e₁⟫| -
        ‖X * V - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖X * V - 1‖ / 2) ≤
      ‖X† * X - 1‖ := by
  have hV : ∀ x, ‖V x‖ = ‖x‖ := fun x => by rw [← hU (V x), left_inverse_apply hUV]
  have hDU : ∀ x, (X * V) (U x) = X x := fun x => by
    rw [mul_apply_eq_comp, left_inverse_apply hVU]
  have hbd : ∀ y, |‖(X * V) y‖ ^ 2 - ‖y‖ ^ 2| ≤ ‖X† * X - 1‖ * ‖y‖ ^ 2 := fun y => by
    rw [mul_apply_eq_comp, ← hV y]
    exact abs_norm_sq_apply_sub_le X (V y)
  have hlo : ∀ y, (1 - ‖X† * X - 1‖) * ‖y‖ ^ 2 ≤ ‖(X * V) y‖ ^ 2 := fun y => by
    have h := abs_le.1 (hbd y)
    linarith [h.1]
  have hhi : ∀ y, ‖(X * V) y‖ ^ 2 ≤ (1 + ‖X† * X - 1‖) * ‖y‖ ^ 2 := fun y => by
    have h := abs_le.1 (hbd y)
    linarith [h.2]
  have key := pair_tradeoff_sq (X * V) U h1 h2 h12 hlo hhi
  rw [hDU, hDU] at key
  linarith

/-- **Lossless reference: the energy error accumulates over a run.** If
`‖(Xᵏ)† Xᵏ - 1‖ ≤ ε` for all `k ≤ K`, then `K (|u_X| - α (η + α/2)) ≤ ε (1 + K (1 + ‖X‖) ‖X - 1‖)`:
the energy error over a run is at least `(|u_X| - α (η + α/2)) / ((1 + ‖X‖) ‖X - 1‖ + 1/K)`,
one order in the macro step above the one-step bound. -/
theorem run_energy_lossless_pair (X U V : E →L[ℝ] E) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (hUV : U * V = 1) (hVU : V * U = 1) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) {K : ℕ} {ε : ℝ} (hε : ∀ k ≤ K, ‖(X ^ k)† * X ^ k - 1‖ ≤ ε) :
    K * (|⟪e₁, U e₂ - X e₂⟫ + ⟪e₂, U e₁ - X e₁⟫| -
        ‖X * V - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖X * V - 1‖ / 2)) ≤
      ε * (1 + K * ((1 + ‖X‖) * ‖X - 1‖)) := by
  have h := pair_tradeoff_lossless X U V hU hUV hVU h1 h2 h12
  have hε' : ∀ k ≤ K, ‖star (X ^ k) * X ^ k - 1‖ ≤ ε := fun k hk => by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hε k hk
  have hacc := energy_accumulation X hε'
  rw [ContinuousLinearMap.star_eq_adjoint] at hacc
  calc _ ≤ (K : ℝ) * ‖X† * X - 1‖ := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg K)
    _ ≤ _ := hacc

/-- **Lossless reference, a scheme that moves nothing between two directions: no run keeps the
energy.** If `⟪e₁, X e₂⟫ = 0 = ⟪e₂, X e₁⟫` and `‖(Xᵏ)† Xᵏ - 1‖ ≤ ε` for all `k ≤ K`, then
`K (|u| - α (η + α/2)) ≤ ε (1 + K (1 + ‖X‖) ‖X - 1‖)` with `u = ⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫`,
`α = ‖X ∘ U⁻¹ - 1‖`. Whatever the spectrum of `X`, the energy error over a run is at least
`(|u| - α (η + α/2)) / ((1 + ‖X‖) ‖X - 1‖ + 1/K)`. -/
theorem run_energy_lossless (X U V : E →L[ℝ] E) (hU : ∀ x, ‖U x‖ = ‖x‖) (hUV : U * V = 1)
    (hVU : V * U = 1) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0)
    (hz1 : ⟪e₁, X e₂⟫ = 0) (hz2 : ⟪e₂, X e₁⟫ = 0) {K : ℕ} {ε : ℝ}
    (hε : ∀ k ≤ K, ‖(X ^ k)† * X ^ k - 1‖ ≤ ε) :
    K * (|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| -
        ‖X * V - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖X * V - 1‖ / 2)) ≤
      ε * (1 + K * ((1 + ‖X‖) * ‖X - 1‖)) := by
  have h := run_energy_lossless_pair X U V hU hUV hVU h1 h2 h12 hε
  rwa [inner_sub_right, inner_sub_right, hz1, hz2, sub_zero, sub_zero] at h

end Run

namespace ScalarNet

variable {n : ℕ} (N : ScalarNet n)

/-- **The trace of a Jacobi step does not depend on the weights.** -/
theorem trace_jacobiStep (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    (N.jacobiStep H k w).trace = ∑ i, Real.exp (N.rate k i * H) := by
  simp [Matrix.trace, jacobiStep]

/-- Without local gains the trace is that of the uncoupled stores. -/
theorem trace_jacobiStep_zero_gain (H : ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    (N.jacobiStep H 0 w).trace = ∑ i, Real.exp (N.a i * H) := by
  simp [trace_jacobiStep, rate]

end ScalarNet

section GaussSeidelEscape

open scoped Matrix

/-- The product `G₂₃(φ) G₁₂(φ)` of two plane rotations, `c = cos φ`, `s = sin φ`: the step of a
Gauss-Seidel scheme in the order 1-2-3 on the lossless chain of three. -/
def gsRot (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c, -s, 0; c * s, c ^ 2, -s; s ^ 2, s * c, c]

/-- **The rotation product is orthogonal:** `Xᵀ X = 1` when `s² = 1 - c²`. -/
theorem gsRot_transpose_mul_self {c s : ℝ} (hs : s ^ 2 = 1 - c ^ 2) :
    (gsRot c s)ᵀ * gsRot c s = 1 := by
  have hT : (gsRot c s)ᵀ = !![c, c * s, s ^ 2; -s, c ^ 2, s * c; 0, -s, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hT, gsRot, Matrix.mul_fin_three, Matrix.one_fin_three]
  refine congrArg Matrix.of (Matrix.vec3_eq (Matrix.vec3_eq ?_ ?_ ?_) (Matrix.vec3_eq ?_ ?_ ?_)
    (Matrix.vec3_eq ?_ ?_ ?_))
  · linear_combination (s ^ 2 + 1) * hs
  · linear_combination (c * s) * hs
  · ring
  · linear_combination (c * s) * hs
  · linear_combination (c ^ 2 + 1) * hs
  · ring
  · ring
  · ring
  · linear_combination hs

/-- **The rotation product has the structural zero of the Gauss-Seidel class:** store 1 does not
see store 3 within the step. -/
theorem gsRot_zero (c s : ℝ) : gsRot c s 0 2 = 0 := rfl

/-- **The rotation product satisfies the minor condition of the Gauss-Seidel class 1-2-3:**
`X₂₁ X₃₂ = X₂₂ X₃₁`. -/
theorem gsRot_minor (c s : ℝ) : gsRot c s 1 0 * gsRot c s 2 1 = gsRot c s 1 1 * gsRot c s 2 0 := by
  change c * s * (s * c) = c ^ 2 * s ^ 2
  ring

/-- **The rotation product is a rotation:** `det X = 1` when `s² = 1 - c²`. -/
theorem gsRot_det {c s : ℝ} (hs : s ^ 2 = 1 - c ^ 2) : (gsRot c s).det = 1 := by
  rw [Matrix.det_fin_three]
  change c * c ^ 2 * c - c * -s * (s * c) - -s * (c * s) * c + -s * -s * s ^ 2 +
    0 * (c * s) * (s * c) - 0 * c ^ 2 * s ^ 2 = 1
  linear_combination (c ^ 2 + s ^ 2 + 1) * hs

/-- **The trace of the rotation product is that of the reference:** with
`c = 2 cos (h/√2) - 1`, `tr X = 1 + 2 cos (√2 h)`, the trace of `e^{hA}` for the lossless chain of
three (eigenvalues of `A`: `0`, `± i √2`). With `gsRot_transpose_mul_self` and `gsRot_det`, `X` is a
rotation, whose eigenvalues `1`, `e^{± i θ}` are fixed by `1 + 2 cos θ = tr X`; so `X` has the
spectrum of the reference step (this last step and the trace of `e^{hA}` are not formalized). -/
theorem gsRot_trace {h c : ℝ} (hc : c = 2 * Real.cos (h / Real.sqrt 2) - 1) (s : ℝ) :
    (gsRot c s).trace = 1 + 2 * Real.cos (Real.sqrt 2 * h) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : 2 * (h / Real.sqrt 2) = Real.sqrt 2 * h := by
    rw [mul_div_assoc', div_eq_iff hpos]
    linear_combination (-h) * hs2
  subst hc
  rw [gsRot, Matrix.trace_fin_three_of, ← h2, Real.cos_two_mul]
  ring

end GaussSeidelEscape

end CoSimFoundations
