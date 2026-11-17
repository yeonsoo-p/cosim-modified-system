/-
Two laws for every scheme.

**1. The pair trade-off without a zero.** `D` the defect, `U` the reference step, `X = D ∘ U`, on a
real inner product space; `e₁`, `e₂` orthonormal; `m` a lower bound of the least stretch of `D`.
With

  `u_X = ⟪e₁, (U - X) e₂⟫ + ⟪e₂, (U - X) e₁⟫`   (what the scheme fails to move between the two
                                                 directions, both ways),
  `η = ‖U e₁ - e₁‖ + ‖U e₂ - e₂‖`,   `α = ‖D - 1‖`:

  `|u_X| - α (η + α/2) ≤ (‖D‖² - m²)/2`.

No structural zero of `X` is assumed: a class enters only through a lower bound on `|u_X|`. If
`D` is an isometry (no energy gained or lost in any state), then `|u_X| ≤ α (η + α/2)`: such a
scheme has a one-step error of first order.

Proof. With `N = 1 - D`: `u_X = ⟪e₁, N (U e₂)⟫ + ⟪e₂, N (U e₁)⟫`, and
`⟪e₁, N e₂⟫ + ⟪e₂, N e₁⟫ = ⟪N e₁, N e₂⟫ - ⟪D e₁, D e₂⟫` (expand, `⟪e₁, e₂⟫ = 0`). By polarisation
`4 ⟪T e₁, T e₂⟫ = ‖T (e₁ + e₂)‖² - ‖T (e₁ - e₂)‖²`, and `‖e₁ ± e₂‖² = 2`, so
`|⟪D e₁, D e₂⟫| ≤ (‖D‖² - m²)/2` and `|⟪N e₁, N e₂⟫| ≤ α²/2`. The remaining terms
`⟪e₁, N (U e₂ - e₂)⟫`, `⟪e₂, N (U e₁ - e₁)⟫` are at most `α η`.

**2. Energy errors accumulate.** In a normed star algebra (operators with their adjoints), if
`‖(Xᵏ)* Xᵏ - 1‖ ≤ ε` for all `k ≤ K`, then

  `K ‖X* X - 1‖ ≤ ε (1 + K (1 + ‖X‖) ‖X - 1‖)`.

So the energy error over a run is at least `‖X* X - 1‖ / ((1 + ‖X‖) ‖X - 1‖ + 1/K)`: one order in
the macro step larger than the energy error of one step.

Proof. `S = Σ_{k<K} (Xᵏ)* Xᵏ` telescopes: `X* S X - S = (X^K)* X^K - 1`. With
`Π = S - K = Σ_{k<K} ((Xᵏ)* Xᵏ - 1)`, `‖Π‖ ≤ K ε`, and
`K (X* X - 1) = (X* S X - S) - ((X - 1)* Π X + Π (X - 1))`.
-/
import CoSimFoundations.TradeOff
import Mathlib.Analysis.CStarAlgebra.Basic

open scoped RealInnerProductSpace

namespace CoSimFoundations

section Pair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Polarisation: the inner product of the images of two orthonormal vectors is at most half the
spread of the squared stretches. -/
theorem abs_inner_apply_le_half_spread (T : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) {lo hi : ℝ} (hlo : ∀ x, lo * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2)
    (hhi : ∀ x, ‖T x‖ ^ 2 ≤ hi * ‖x‖ ^ 2) :
    |⟪T e₁, T e₂⟫| ≤ (hi - lo) / 2 := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have a1 := hlo (e₁ + e₂)
  have a2 := hhi (e₁ + e₂)
  have b1 := hlo (e₁ - e₂)
  have b2 := hhi (e₁ - e₂)
  rw [hp, map_add, norm_add_sq_real] at a1 a2
  rw [hm, map_sub, norm_sub_sq_real] at b1 b2
  rw [abs_le]
  constructor <;> linarith

/-- **The pair trade-off with two-sided bounds on the squared stretches.** If
`lo ‖x‖² ≤ ‖D x‖² ≤ hi ‖x‖²` for every `x`, then `|u_X| - α (η + α/2) ≤ (hi - lo)/2`, with
`u_X = ⟪e₁, (U - X) e₂⟫ + ⟪e₂, (U - X) e₁⟫`, `X = D ∘ U`. (`pair_tradeoff` is the case
`lo = m²`, `hi = ‖D‖²`.) -/
theorem pair_tradeoff_sq (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) {lo hi : ℝ} (hlo : ∀ x, lo * ‖x‖ ^ 2 ≤ ‖D x‖ ^ 2)
    (hhi : ∀ x, ‖D x‖ ^ 2 ≤ hi * ‖x‖ ^ 2) :
    |⟪e₁, U e₂ - D (U e₂)⟫ + ⟪e₂, U e₁ - D (U e₁)⟫| -
        ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2) ≤
      (hi - lo) / 2 := by
  have key : ⟪e₁, U e₂ - D (U e₂)⟫ + ⟪e₂, U e₁ - D (U e₁)⟫ =
      ⟪(D - 1) e₁, (D - 1) e₂⟫ - ⟪D e₁, D e₂⟫ - ⟪e₁, (D - 1) (U e₂ - e₂)⟫ -
        ⟪e₂, (D - 1) (U e₁ - e₁)⟫ := by
    have c1 : ⟪D e₁, e₂⟫ = ⟪e₂, D e₁⟫ := real_inner_comm _ _
    have c2 : ⟪e₂, e₁⟫ = 0 := by rw [real_inner_comm]; exact h12
    simp only [sub_apply, one_apply_eq_self, map_sub, inner_sub_left, inner_sub_right]
    linarith
  have hlo' : ∀ x, 0 * ‖x‖ ^ 2 ≤ ‖(D - 1) x‖ ^ 2 := fun x => by
    rw [zero_mul]; positivity
  have hD := abs_le.1 (abs_inner_apply_le_half_spread D h1 h2 h12 hlo hhi)
  have hN := abs_le.1
    (abs_inner_apply_le_half_spread (D - 1) h1 h2 h12 hlo' (norm_apply_sq_le (D - 1)))
  have r1 := abs_le.1 (abs_inner_sub_one_apply_le D h1 (U e₂ - e₂))
  have r2 := abs_le.1 (abs_inner_sub_one_apply_le D h2 (U e₁ - e₁))
  rw [key, sub_le_iff_le_add, abs_le]
  constructor <;> linarith [hD.1, hD.2, hN.1, hN.2, r1.1, r1.2, r2.1, r2.2]

/-- **The pair trade-off without a zero.** -/
theorem pair_tradeoff (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) {m : ℝ} (hm0 : 0 ≤ m) (hmD : ∀ x, m * ‖x‖ ≤ ‖D x‖) :
    |⟪e₁, U e₂ - D (U e₂)⟫ + ⟪e₂, U e₁ - D (U e₁)⟫| -
        ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2) ≤
      (‖D‖ ^ 2 - m ^ 2) / 2 :=
  pair_tradeoff_sq D U h1 h2 h12 (sq_mul_norm_sq_le hm0 hmD) (norm_apply_sq_le D)

/-- **A defect that keeps the energy of every state** has a one-step error of first order wherever
the scheme fails to move something between two directions. -/
theorem pair_tradeoff_isometry (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (hiso : ∀ x, ‖D x‖ = ‖x‖) :
    |⟪e₁, U e₂ - D (U e₂)⟫ + ⟪e₂, U e₁ - D (U e₁)⟫| ≤
      ‖D - 1‖ * ((‖U e₁ - e₁‖ + ‖U e₂ - e₂‖) + ‖D - 1‖ / 2) := by
  have h := pair_tradeoff D U h1 h2 h12 zero_le_one (fun x => by rw [one_mul, hiso])
  have hD : ‖D‖ ≤ 1 := D.opNorm_le_bound zero_le_one (fun x => by rw [hiso, one_mul])
  have hD2 : ‖D‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hD
  linarith

end Pair

section Star

variable {A : Type*} [NormedRing A] [StarRing A] [NormedStarGroup A] [NormedAlgebra ℝ A]

/-- The sum of the energies of the powers telescopes. -/
theorem star_mul_sum_mul_sub_sum (X : A) (K : ℕ) :
    star X * (∑ k ∈ Finset.range K, star (X ^ k) * X ^ k) * X -
        ∑ k ∈ Finset.range K, star (X ^ k) * X ^ k =
      star (X ^ K) * X ^ K - 1 := by
  have hg : ∀ k : ℕ,
      star X * (star (X ^ k) * X ^ k) * X = star (X ^ (k + 1)) * X ^ (k + 1) := by
    intro k
    rw [pow_succ, star_mul]
    simp only [mul_assoc]
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [hg]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => star (X ^ k) * X ^ k) K]
  simp

/-- The energy error of one step in terms of the telescoped sum `S` and its defect
`P = S - K`. -/
theorem nsmul_star_mul_sub_one_eq (X S P : A) (K : ℕ) (hP : P = S - K • (1 : A)) :
    K • (star X * X - 1) = (star X * S * X - S) - (star (X - 1) * P * X + P * (X - 1)) := by
  rw [hP, star_sub, star_one, smul_sub]
  noncomm_ring [smul_add, smul_neg]

/-- **Energy errors accumulate.** -/
theorem energy_accumulation (X : A) {K : ℕ} {ε : ℝ}
    (hε : ∀ k ≤ K, ‖star (X ^ k) * X ^ k - 1‖ ≤ ε) :
    (K : ℝ) * ‖star X * X - 1‖ ≤ ε * (1 + K * ((1 + ‖X‖) * ‖X - 1‖)) := by
  have hP : ∑ k ∈ Finset.range K, (star (X ^ k) * X ^ k - 1) =
      ∑ k ∈ Finset.range K, star (X ^ k) * X ^ k - K • (1 : A) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  have hid := nsmul_star_mul_sub_one_eq X _ _ K hP
  rw [star_mul_sum_mul_sub_sum] at hid
  have hPn : ‖∑ k ∈ Finset.range K, (star (X ^ k) * X ^ k - 1)‖ ≤ K * ε := by
    calc ‖∑ k ∈ Finset.range K, (star (X ^ k) * X ^ k - 1)‖
        ≤ ∑ k ∈ Finset.range K, ‖star (X ^ k) * X ^ k - 1‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range K, ε :=
          Finset.sum_le_sum fun k hk => hε k (Finset.mem_range.1 hk).le
      _ = K * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  generalize ∑ k ∈ Finset.range K, (star (X ^ k) * X ^ k - 1) = P at hid hPn
  have hK : ‖K • (star X * X - 1)‖ = K * ‖star X * X - 1‖ := by
    rw [RCLike.norm_nsmul ℝ, nsmul_eq_mul]
  have n1 : ‖star (X - 1) * P * X‖ ≤ ‖X - 1‖ * (K * ε) * ‖X‖ := by
    calc ‖star (X - 1) * P * X‖ ≤ ‖star (X - 1)‖ * ‖P‖ * ‖X‖ := norm_mul₃_le
      _ ≤ ‖X - 1‖ * (K * ε) * ‖X‖ := by rw [norm_star]; gcongr
  have n2 : ‖P * (X - 1)‖ ≤ K * ε * ‖X - 1‖ :=
    (norm_mul_le _ _).trans (by gcongr)
  have hT := hε K le_rfl
  have s1 := norm_sub_le (star (X ^ K) * X ^ K - 1) (star (X - 1) * P * X + P * (X - 1))
  have s2 := norm_add_le (star (X - 1) * P * X) (P * (X - 1))
  rw [← hid, hK] at s1
  linarith

end Star

end CoSimFoundations
