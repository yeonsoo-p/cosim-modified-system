/-
One macro step in Jacobi mode: damping against energy gain (the paper, Proposition 5.4
`prop:onestep`, inequalities (27) `eq:pairnu` and (28) `eq:noinj`).

`D` the one-step defect, `U` the reference step, `X = D ∘ U` the scheme's step, on a real inner
product space of dimension `n ≥ 1` (energy coordinates). `e₁`, `e₂` are orthonormal and the scheme
moves nothing between them: `⟪e₁, X e₂⟫ = 0 = ⟪e₂, X e₁⟫`. With

  `u = ⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫`,  `η = ‖U e₁ - e₁‖ + ‖U e₂ - e₂‖`,  `α = ‖D - 1‖`,  `s₊ = ‖D‖`:

* **(27), exponential form, every `D`:**  `|det D| ≤ exp (n (s₊ - 1) - (|u| - α (η + α/2)))`;
* **(27), as printed, `det D ≠ 0`:**  `ln |det D| ≤ n (s₊ - 1) - (|u| - α (η + α/2))`.
  In the paper `ln det D = -H ν` (`ν` the numerical damping), so this is
  `H ν + n (s₊ - 1) ≥ |u| - α (η + α/2)`;
* **(28):** if `s₊ ≤ 1` then `|det D| ≤ exp (-(|u| - α (η + α/2)))`, that is,
  `H ν ≥ |u| - α (η + α/2)`.

Proof of (27), the paper's. Let `m = s₋` be the least stretch of `D`, attained at a unit vector
(`chain`). Then `|det D| ≤ m s₊ⁿ⁻¹` (`abs_det_le_norm_apply_mul_opNorm_pow`), `s₊ ≤ exp (s₊ - 1)`
and `m ≤ exp ((m² - 1)/2)` (both are `1 + x ≤ exp x`), and
`(s₊ - 1) + (1 - m²)/2 ≥ |u| - α (η + α/2)` (`link_tradeoff_spread`). The chain
`ln det D ≤ (n - 1)(s₊ - 1) + (s₋² - 1)/2 ≤ n (s₊ - 1) - |u| + α (η + α/2)` of the paper needs no
further hypothesis: `ln t ≤ t - 1` is used for `t = s₊` and for `t = s₋²`, whatever their size.
What the printed statement needs is `det D ≠ 0` for the logarithm (in the paper `det D > 0`,
because `D = exp (H Ã) exp (-H A)`); the exponential form holds for every `D`.

Proof of (28). `det_sq_le_of_no_gain` (`NoInjection.lean`) gives the sharper
`(det D)² ≤ 1 + α² - 2 (|u| - α η) = 1 - 2 (|u| - α (η + α/2))`, and `1 - 2x ≤ exp (-2x)`.
(28) also follows from (27), because `n (s₊ - 1) ≤ 0`.

The last section states (27) and (28) for the Jacobi schemes of a network of scalar stores
(`ScalarStores.lean`), in the style of `NoInjectionJacobi.lean`: for a step matrix `D * U` and two
stores `i ≠ j` that are not partners, `u = U i j + U j i`.
-/
import CoSimFoundations.NoInjectionJacobi

open Module
open scoped RealInnerProductSpace

namespace CoSimFoundations

/-- `sᵏ ≤ exp (k (s - 1))` for `s ≥ 0`. -/
theorem pow_le_exp_mul_sub_one {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    s ^ k ≤ Real.exp (k * (s - 1)) := by
  have h : s ≤ Real.exp (s - 1) := by
    have := Real.add_one_le_exp (s - 1)
    linarith
  calc s ^ k ≤ Real.exp (s - 1) ^ k := pow_le_pow_left₀ hs h k
    _ = Real.exp (k * (s - 1)) := (Real.exp_nat_mul _ _).symm

/-- `m ≤ exp ((m² - 1)/2)` for `m ≥ 0`. -/
theorem le_exp_sq_sub_one_half {m : ℝ} (hm : 0 ≤ m) : m ≤ Real.exp ((m ^ 2 - 1) / 2) := by
  have h : m ^ 2 ≤ Real.exp ((m ^ 2 - 1) / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    have h1 := Real.add_one_le_exp (m ^ 2 - 1)
    have h2 : ((2 : ℕ) : ℝ) * ((m ^ 2 - 1) / 2) = m ^ 2 - 1 := by push_cast; ring
    rw [h2]
    linarith
  exact (sq_le_sq₀ hm (Real.exp_pos _).le).1 h

/-- If `d² ≤ 1 - 2x` then `|d| ≤ exp (-x)`. -/
theorem abs_le_exp_neg_of_sq_le {d x : ℝ} (h : d ^ 2 ≤ 1 - 2 * x) : |d| ≤ Real.exp (-x) := by
  have h1 : d ^ 2 ≤ Real.exp (-x) ^ 2 := by
    rw [← Real.exp_nat_mul]
    have h2 := Real.add_one_le_exp (((2 : ℕ) : ℝ) * -x)
    push_cast at h2 ⊢
    linarith
  exact abs_le_of_sq_le_sq h1 (Real.exp_pos _).le

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Proposition 5.4, inequality (27), exponential form.** If the scheme with defect `D` moves
nothing between the orthonormal directions `e₁`, `e₂` in either way, then
`|det D| ≤ exp (n (‖D‖ - 1) - (|u| - α (η + α/2)))` with `u = ⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫`,
`η = ‖U e₁ - e₁‖ + ‖U e₂ - e₂‖`, `α = ‖D - 1‖`, `n` the dimension. No hypothesis on `det D`. -/
theorem abs_det_le_exp_pair [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0) :
    |LinearMap.det (D : E →ₗ[ℝ] E)| ≤ Real.exp ((finrank ℝ E : ℝ) * (‖D‖ - 1) -
      (|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| -
        ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2))) := by
  obtain ⟨k, hk⟩ : ∃ k, finrank ℝ E = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := E)).ne'
  obtain ⟨m, ⟨v, hv, hDv⟩, hmD, -, -, -, -⟩ := chain D
  have hm0 : 0 ≤ m := by rw [← hDv]; exact norm_nonneg _
  have hspread := link_tradeoff_spread D U h1 h2 h12 hz1 hz2 hm0 hmD
  have hlow := abs_det_le_norm_apply_mul_opNorm_pow D hv
  rw [hDv, hk, Nat.add_sub_cancel] at hlow
  calc |LinearMap.det (D : E →ₗ[ℝ] E)| ≤ m * ‖D‖ ^ k := hlow
    _ ≤ Real.exp ((m ^ 2 - 1) / 2) * Real.exp (k * (‖D‖ - 1)) :=
        mul_le_mul (le_exp_sq_sub_one_half hm0) (pow_le_exp_mul_sub_one (norm_nonneg D) k)
          (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((m ^ 2 - 1) / 2 + k * (‖D‖ - 1)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
        rw [Real.exp_le_exp, hk]
        push_cast
        linarith

/-- **Proposition 5.4, inequality (27), as printed:** for an invertible defect,
`ln |det D| ≤ n (‖D‖ - 1) - (|u| - α (η + α/2))`. With `ln det D = -H ν` this is
`H ν + n (s₊ - 1) ≥ |u| - α (η + α/2)`. -/
theorem log_abs_det_le_pair [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hdet : LinearMap.det (D : E →ₗ[ℝ] E) ≠ 0) :
    Real.log |LinearMap.det (D : E →ₗ[ℝ] E)| ≤ (finrank ℝ E : ℝ) * (‖D‖ - 1) -
      (|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| -
        ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2)) :=
  (Real.log_le_iff_le_exp (abs_pos.2 hdet)).2 (abs_det_le_exp_pair D U h1 h2 h12 hz1 hz2)

/-- **Proposition 5.4, inequality (28), exponential form.** A scheme that injects no energy over a
step (`‖D‖ ≤ 1`) has `|det D| ≤ exp (-(|u| - α (η + α/2)))`. It is a consequence of the sharper
`det_sq_le_of_no_gain`, `(det D)² ≤ 1 - 2 (|u| - α (η + α/2))`, and of `1 - 2x ≤ exp (-2x)`. -/
theorem abs_det_le_exp_of_no_gain [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hD : ‖D‖ ≤ 1) :
    |LinearMap.det (D : E →ₗ[ℝ] E)| ≤ Real.exp (-(|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| -
      ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2))) := by
  have h := det_sq_le_of_no_gain D U h1 h2 h12 hz1 hz2 hD
  refine abs_le_exp_neg_of_sq_le (h.trans (le_of_eq ?_))
  ring

/-- (28) is also the case `‖D‖ ≤ 1` of (27): the term `n (‖D‖ - 1)` is not positive. -/
theorem abs_det_le_exp_of_no_gain' [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1)
    (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0) (hz2 : ⟪e₂, D (U e₁)⟫ = 0)
    (hD : ‖D‖ ≤ 1) :
    |LinearMap.det (D : E →ₗ[ℝ] E)| ≤ Real.exp (-(|⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| -
      ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2))) := by
  refine (abs_det_le_exp_pair D U h1 h2 h12 hz1 hz2).trans (Real.exp_le_exp.2 ?_)
  have hn : (0 : ℝ) ≤ (finrank ℝ E : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **Proposition 5.4, inequality (28), as printed:** if `‖D‖ ≤ 1` and `det D ≠ 0`, then
`|u| - α (η + α/2) ≤ -ln |det D|` (`= H ν` in the paper). -/
theorem le_neg_log_abs_det_of_no_gain [Nontrivial E] (D U : E →L[ℝ] E) {e₁ e₂ : E}
    (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hz1 : ⟪e₁, D (U e₂)⟫ = 0)
    (hz2 : ⟪e₂, D (U e₁)⟫ = 0) (hD : ‖D‖ ≤ 1) (hdet : LinearMap.det (D : E →ₗ[ℝ] E) ≠ 0) :
    |⟪e₁, U e₂⟫ + ⟪e₂, U e₁⟫| - ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2) ≤
      -Real.log |LinearMap.det (D : E →ₗ[ℝ] E)| := by
  have h := (Real.log_le_iff_le_exp (abs_pos.2 hdet)).2
    (abs_det_le_exp_of_no_gain D U h1 h2 h12 hz1 hz2 hD)
  linarith

end Operator

namespace ScalarNet

variable {n : ℕ} (N : ScalarNet n)

/-- **Inequality (27) for the class.** Every Jacobi scheme with one held sample of a network of
scalar stores, with step matrix `D * U`, and two stores `i ≠ j` that are not partners of each
other: `|det D| ≤ exp (n (‖D‖ - 1) - (|U i j + U j i| - α (η + α/2)))`. -/
theorem pair_damping {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ i j, ¬ N.partner i j → w i j = 0) (D U : Matrix (Fin n) (Fin n) ℝ)
    (hX : N.jacobiStep H k w = D * U) {i j : Fin n} (hij : i ≠ j)
    (hp : ¬ N.partner i j) (hp' : ¬ N.partner j i) :
    |D.det| ≤ Real.exp ((n : ℝ) * (‖opE D‖ - 1) - (|U i j + U j i| - ‖opE D - 1‖ *
      ((‖opE U (unitE i) - unitE i‖ + ‖opE U (unitE j) - unitE j‖) + ‖opE D - 1‖ / 2))) := by
  have hne : unitE i ≠ 0 := by
    intro h0
    have h1 := norm_unitE i
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := nontrivial_of_ne _ _ hne
  have h := abs_det_le_exp_pair (opE D) (opE U) (norm_unitE i) (norm_unitE j)
    (inner_unitE_of_ne hij) (N.inner_unitE_opE_opE_eq_zero hH k w hw D U hX hij hp)
    (N.inner_unitE_opE_opE_eq_zero hH k w hw D U hX hij.symm hp')
  rwa [det_opE, inner_unitE_opE, inner_unitE_opE, finrank_euclideanSpace_fin] at h

/-- **Inequality (27) for the class, as printed:** if `det D ≠ 0`,
`ln |det D| ≤ n (‖D‖ - 1) - (|U i j + U j i| - α (η + α/2))`. -/
theorem pair_damping_log {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ i j, ¬ N.partner i j → w i j = 0) (D U : Matrix (Fin n) (Fin n) ℝ)
    (hX : N.jacobiStep H k w = D * U) {i j : Fin n} (hij : i ≠ j)
    (hp : ¬ N.partner i j) (hp' : ¬ N.partner j i) (hdet : D.det ≠ 0) :
    Real.log |D.det| ≤ (n : ℝ) * (‖opE D‖ - 1) - (|U i j + U j i| - ‖opE D - 1‖ *
      ((‖opE U (unitE i) - unitE i‖ + ‖opE U (unitE j) - unitE j‖) + ‖opE D - 1‖ / 2)) :=
  (Real.log_le_iff_le_exp (abs_pos.2 hdet)).2 (N.pair_damping hH k w hw D U hX hij hp hp')

/-- **Inequality (28) for the class:** a Jacobi scheme that injects no energy over a step,
`‖D‖ ≤ 1`, has `|det D| ≤ exp (-(|U i j + U j i| - α (η + α/2)))`. -/
theorem pair_damping_of_no_gain {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ)
    (w : Matrix (Fin n) (Fin n) ℝ) (hw : ∀ i j, ¬ N.partner i j → w i j = 0)
    (D U : Matrix (Fin n) (Fin n) ℝ) (hX : N.jacobiStep H k w = D * U) {i j : Fin n}
    (hij : i ≠ j) (hp : ¬ N.partner i j) (hp' : ¬ N.partner j i) (hD : ‖opE D‖ ≤ 1) :
    |D.det| ≤ Real.exp (-(|U i j + U j i| - ‖opE D - 1‖ *
      ((‖opE U (unitE i) - unitE i‖ + ‖opE U (unitE j) - unitE j‖) + ‖opE D - 1‖ / 2))) := by
  have h := N.no_injection_costs_damping hH k w hw D U hX hij hp hp' hD
  refine abs_le_exp_neg_of_sq_le (h.trans (le_of_eq ?_))
  ring

end ScalarNet

end CoSimFoundations
