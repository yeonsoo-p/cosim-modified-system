/-
The determinant against the least stretch, and what an exact mean damping costs.

`T` an operator on a finite-dimensional real inner product space of dimension `n ≥ 1`.

* `|det T| ≤ ‖T v‖ · ‖T‖ⁿ⁻¹` for every unit vector `v` (the determinant is the product of the
  singular values, and the least of them is at most any stretch).
  Proof by reduction to `Region.lean`: if `T` is not invertible, `det T = 0`. Otherwise apply the
  lower bound `‖S‖ · mⁿ⁻¹ ≤ |det S|` of `Region.lean` (`opNorm_mul_pow_le_abs_det`) to `S = T⁻¹`
  with `m = ‖T‖⁻¹` (`‖S y‖ ≥ ‖y‖ / ‖T‖`), and `‖S‖ ≥ ‖S (T v)‖ / ‖T v‖ = 1 / ‖T v‖`.
* If `‖T‖ ≤ 1` and `1 ≤ |det T|`, then `T` is an isometry. For a co-simulation: a scheme that adds
  no energy in any state (`s₊ ≤ 1`) and keeps the mean damping (`det D = 1`) has an orthogonal
  defect.
* **Exact mean damping forces a one-step energy gain.** If the scheme moves nothing between two
  orthonormal directions in either way and `|det D| = 1`, then, with `u`, `η`, `α` as in
  `TradeOff.lean`,

    `|u| - α (η + α/2) ≤ n (‖D‖ - 1)`.

  Proof: `link_tradeoff_spread` gives `(‖D‖ - 1) + (1 - m²)/2 ≥ |u| - α (η + α/2)` for the least
  stretch `m`; the first item gives `1 ≤ m ‖D‖ⁿ⁻¹`, hence `‖D‖ ≥ 1` and
  `1 - m² ≤ 2 (n - 1)(‖D‖ - 1)` (Bernoulli).
-/
import CoSimFoundations.Region
import CoSimFoundations.TradeOff

open Module
open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Bernoulli's inequality for the inverse power: `sᵏ (1 - k (s - 1)) ≤ 1` for `s ≥ 1`. -/
theorem pow_mul_one_sub_mul_le {s : ℝ} (hs : 1 ≤ s) (k : ℕ) :
    s ^ k * (1 - k * (s - 1)) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 1 ≤ s ^ k := one_le_pow₀ hs
    have h0 : 0 ≤ s := by linarith
    have h1 := mul_le_mul_of_nonneg_left ih h0
    have h2 := mul_le_mul_of_nonneg_left hk (mul_nonneg h0 (sub_nonneg.2 hs))
    push_cast
    rw [pow_succ]
    nlinarith [sq_nonneg (s - 1)]

/-- **The determinant is at most any stretch times the largest stretch to the power `n - 1`.** -/
theorem abs_det_le_norm_apply_mul_opNorm_pow [Nontrivial E] (T : E →L[ℝ] E) {v : E}
    (hv : ‖v‖ = 1) :
    |LinearMap.det (T : E →ₗ[ℝ] E)| ≤ ‖T v‖ * ‖T‖ ^ (finrank ℝ E - 1) := by
  by_cases hdet : LinearMap.det (T : E →ₗ[ℝ] E) = 0
  · rw [hdet, abs_zero]
    positivity
  -- the inverse `S` of `T`
  let e : E ≃L[ℝ] E := T.toContinuousLinearEquivOfDetNeZero hdet
  let S : E →L[ℝ] E := e.symm
  have hTS : ∀ y, T (S y) = y := fun y => e.apply_symm_apply y
  have hST : ∀ x, S (T x) = x := fun x => e.symm_apply_apply x
  have hdetST : |LinearMap.det (S : E →ₗ[ℝ] E)| * |LinearMap.det (T : E →ₗ[ℝ] E)| = 1 := by
    rw [← abs_mul, ← LinearMap.det_comp]
    have hid : (S : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E) = LinearMap.id := LinearMap.ext hST
    rw [hid, LinearMap.det_id, abs_one]
  -- `‖S‖ ≥ 1 / ‖T v‖`
  have hSv : 1 ≤ ‖S‖ * ‖T v‖ := by
    have h := S.le_opNorm (T v)
    rwa [hST, hv] at h
  have hTpos : 0 < ‖T‖ := by
    rcases (norm_nonneg T).eq_or_lt with h | h
    · have h0 := T.le_opNorm v
      rw [← h, zero_mul] at h0
      nlinarith [norm_nonneg (T v), norm_nonneg S]
    · exact h
  -- `‖S y‖ ≥ ‖y‖ / ‖T‖`
  have hSlow : ∀ y, ‖T‖⁻¹ * ‖y‖ ≤ ‖S y‖ := by
    intro y
    have h1 := T.le_opNorm (S y)
    rw [hTS] at h1
    rw [inv_mul_le_iff₀ hTpos]
    exact h1
  have hmain := opNorm_mul_pow_le_abs_det S (inv_nonneg.2 hTpos.le) hSlow
  have hinv : (‖T‖⁻¹) ^ (finrank ℝ E - 1) * ‖T‖ ^ (finrank ℝ E - 1) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hTpos.ne', one_pow]
  have ha : 0 ≤ |LinearMap.det (T : E →ₗ[ℝ] E)| := abs_nonneg _
  have hb : 0 ≤ ‖T v‖ * ‖T‖ ^ (finrank ℝ E - 1) := by positivity
  calc |LinearMap.det (T : E →ₗ[ℝ] E)|
      = |LinearMap.det (T : E →ₗ[ℝ] E)| *
          ((‖T‖⁻¹) ^ (finrank ℝ E - 1) * ‖T‖ ^ (finrank ℝ E - 1)) := by rw [hinv, mul_one]
    _ ≤ |LinearMap.det (T : E →ₗ[ℝ] E)| *
          ((‖T‖⁻¹) ^ (finrank ℝ E - 1) * ‖T‖ ^ (finrank ℝ E - 1)) * (‖S‖ * ‖T v‖) :=
        le_mul_of_one_le_right (by positivity) hSv
    _ = (‖S‖ * (‖T‖⁻¹) ^ (finrank ℝ E - 1)) * |LinearMap.det (T : E →ₗ[ℝ] E)| *
          (‖T v‖ * ‖T‖ ^ (finrank ℝ E - 1)) := by ring
    _ ≤ |LinearMap.det (S : E →ₗ[ℝ] E)| * |LinearMap.det (T : E →ₗ[ℝ] E)| *
          (‖T v‖ * ‖T‖ ^ (finrank ℝ E - 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmain ha) hb
    _ = ‖T v‖ * ‖T‖ ^ (finrank ℝ E - 1) := by rw [hdetST, one_mul]

/-- **No energy added and the mean damping kept: the defect is an isometry.** -/
theorem isometry_of_opNorm_le_one_of_one_le_abs_det [Nontrivial E] (T : E →L[ℝ] E)
    (hT : ‖T‖ ≤ 1) (hdet : 1 ≤ |LinearMap.det (T : E →ₗ[ℝ] E)|) (x : E) :
    ‖T x‖ = ‖x‖ := by
  have hunit : ∀ v : E, ‖v‖ = 1 → ‖T v‖ = 1 := by
    intro v hv
    have h1 := abs_det_le_norm_apply_mul_opNorm_pow T hv
    have h2 : ‖T‖ ^ (finrank ℝ E - 1) ≤ 1 := pow_le_one₀ (norm_nonneg T) hT
    have h3 : ‖T v‖ ≤ 1 := (T.le_opNorm v).trans (by rw [hv, mul_one]; exact hT)
    have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (T v))
    linarith
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hv : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx'.ne']
    have h := hunit _ hv
    rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_eq_one₀ hx'.ne'] at h
    exact h.symm

/-- **Exact mean damping forces a one-step energy gain.** -/
theorem gain_of_abs_det_eq_one [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hdet : |LinearMap.det (D : E →ₗ[ℝ] E)| = 1) :
    |⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| -
        ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2) ≤
      (finrank ℝ E : ℝ) * (‖D‖ - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, finrank ℝ E = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := E)).ne'
  obtain ⟨m, ⟨v, hv, hDv⟩, hmD, -, -, hdetle, -⟩ := chain D
  have hm0 : 0 ≤ m := by rw [← hDv]; exact norm_nonneg _
  have hspread := link_tradeoff_spread D U h1 h2 h12 hz1 hz2 hm0 hmD
  have hlow := abs_det_le_norm_apply_mul_opNorm_pow D hv
  rw [hdet, hDv, hk, Nat.add_sub_cancel] at hlow
  rw [hdet, hk] at hdetle
  -- `‖D‖ ≥ 1`
  have hs : 1 ≤ ‖D‖ := (one_le_pow_iff_of_nonneg (norm_nonneg D) (Nat.succ_ne_zero k)).1 hdetle
  -- Bernoulli: `m ≥ ‖D‖⁻ᵏ ≥ 1 - k (‖D‖ - 1)`
  have hB := pow_mul_one_sub_mul_le hs k
  have hpos : 0 < ‖D‖ ^ k := pow_pos (by linarith) k
  have hc : 1 - k * (‖D‖ - 1) ≤ m := by
    refine le_of_mul_le_mul_left ?_ hpos
    linarith
  have hsq : 1 - m ^ 2 ≤ 2 * k * (‖D‖ - 1) := by
    by_cases hc0 : 1 - k * (‖D‖ - 1) ≤ 0
    · nlinarith [sq_nonneg m]
    · have hc0' : 0 < 1 - k * (‖D‖ - 1) := not_le.1 hc0
      nlinarith [mul_le_mul hc hc hc0'.le hm0, sq_nonneg ((k : ℝ) * (‖D‖ - 1))]
  rw [hk]
  push_cast
  linarith

end CoSimFoundations
