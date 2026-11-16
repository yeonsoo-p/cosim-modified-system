/-
The order barrier (the paper, Cor 6.4, second part), with explicit constants.

1. Taylor remainder of the exponential in a real Banach algebra, for `b ≥ 1`:

     `‖exp Z - Σ_{n < b} Zⁿ / n!‖ ≤ ‖Z‖ᵇ / b! · e^{‖Z‖}`.

2. On a real Hilbert space, for vectors `e`, `f`:

     `|⟪e, exp (H • A) f⟫ - (⟪e, f⟫ + H ⟪e, A f⟫ + ½H² ⟪e, A² f⟫)| ≤ ‖H • A‖³/6 · e^{‖H • A‖} ‖e‖ ‖f‖`.

3. **Order barrier.** Let `e`, `f` be two stores that are two coupling links apart: `⟪e, f⟫ = 0`,
   `⟪e, A f⟫ = 0`. If the co-simulation step `exp (H • Ã)` sends nothing from `f` to `e`
   (`⟪e, exp (H • Ã) f⟫ = 0`), then

     `½H² |⟪e, A² f⟫| ≤ H · κ_H ‖Ã - A‖ · ‖exp (H • A) f‖ + ‖H • A‖³/6 · e^{‖H • A‖} ‖f‖`,

   that is, `‖Ã - A‖ ≥ (½H |[A²]_{ef}| - O(H²)) / (κ_H ‖U f‖)`: the difference is at least of first
   order in the macro step, with the constant `½ |[A²]_{ef}|` of the system.
-/
import CoSimFoundations.LogNorm

open NormedSpace Nat
open scoped RealInnerProductSpace

namespace CoSimFoundations

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Taylor remainder of the exponential.** -/
theorem norm_exp_sub_sum_le (Z : 𝔸) {b : ℕ} (hb : 0 < b) :
    ‖exp Z - ∑ n ∈ Finset.range b, ((n ! : ℝ)⁻¹) • Z ^ n‖ ≤
      ‖Z‖ ^ b / (b ! : ℝ) * Real.exp ‖Z‖ := by
  have hf : HasSum (fun n : ℕ => ((n ! : ℝ)⁻¹) • Z ^ n) (exp Z) :=
    exp_series_hasSum_exp' (𝕂 := ℝ) Z
  have htail := (hasSum_nat_add_iff' b).2 hf
  have hg : HasSum (fun i : ℕ => ‖Z‖ ^ b / (b ! : ℝ) * (‖Z‖ ^ i / (i ! : ℝ)))
      (‖Z‖ ^ b / (b ! : ℝ) * Real.exp ‖Z‖) := by
    have h : HasSum (fun n : ℕ => ‖Z‖ ^ n / (n ! : ℝ)) (Real.exp ‖Z‖) := by
      rw [Real.exp_eq_exp_ℝ]
      exact expSeries_div_hasSum_exp ‖Z‖
    exact h.mul_left _
  refine htail.norm_le_of_bounded hg (fun i => ?_)
  have h1 : ‖Z ^ (i + b)‖ ≤ ‖Z‖ ^ i * ‖Z‖ ^ b := by
    rw [← pow_add]
    exact norm_pow_le' Z (by omega)
  have h2 : (i ! : ℝ) * (b ! : ℝ) ≤ ((i + b)! : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (factorial_pos _) (factorial_mul_factorial_dvd_factorial_add i b)
  have hi : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast factorial_pos i
  have hbf : (0 : ℝ) < (b ! : ℝ) := by exact_mod_cast factorial_pos b
  rw [norm_smul, norm_inv, Real.norm_natCast]
  calc (((i + b)! : ℝ))⁻¹ * ‖Z ^ (i + b)‖
      ≤ ((i ! : ℝ) * (b ! : ℝ))⁻¹ * (‖Z‖ ^ i * ‖Z‖ ^ b) := by gcongr
    _ = ‖Z‖ ^ b / (b ! : ℝ) * (‖Z‖ ^ i / (i ! : ℝ)) := by field_simp

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Second-order expansion of a matrix element of the reference step.** -/
theorem inner_exp_sub_quadratic_le (A : E →L[ℝ] E) (H : ℝ) (e f : E) :
    |⟪e, exp (H • A) f⟫ - (⟪e, f⟫ + H * ⟪e, A f⟫ + H ^ 2 / 2 * ⟪e, A (A f)⟫)| ≤
      ‖H • A‖ ^ 3 / 6 * Real.exp ‖H • A‖ * (‖e‖ * ‖f‖) := by
  have h := norm_exp_sub_sum_le (H • A) (b := 3) (by norm_num)
  have h6 : ((3 ! : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  have hsum : ⟪e, (exp (H • A) - ∑ n ∈ Finset.range 3, ((n ! : ℝ)⁻¹) • (H • A) ^ n) f⟫ =
      ⟪e, exp (H • A) f⟫ - (⟪e, f⟫ + H * ⟪e, A f⟫ + H ^ 2 / 2 * ⟪e, A (A f)⟫) := by
    simp [Finset.sum_range_succ, Nat.factorial, pow_two, inner_sub_right, inner_add_right,
      inner_smul_right]
    ring
  rw [← hsum]
  calc |⟪e, (exp (H • A) - ∑ n ∈ Finset.range 3, ((n ! : ℝ)⁻¹) • (H • A) ^ n) f⟫|
      ≤ ‖e‖ * ‖(exp (H • A) - ∑ n ∈ Finset.range 3, ((n ! : ℝ)⁻¹) • (H • A) ^ n) f‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖exp (H • A) - ∑ n ∈ Finset.range 3, ((n ! : ℝ)⁻¹) • (H • A) ^ n‖ * ‖f‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖e‖ * (‖H • A‖ ^ 3 / 6 * Real.exp ‖H • A‖ * ‖f‖) := by gcongr
    _ = ‖H • A‖ ^ 3 / 6 * Real.exp ‖H • A‖ * (‖e‖ * ‖f‖) := by ring

/-- **The order barrier.** Two stores `e`, `f` two coupling links apart, between which the
co-simulation step sends nothing: the difference is at least of first order in `H`, with the
system constant `½ |⟪e, A² f⟫|`. -/
theorem order_barrier (At A : E →L[ℝ] E) {H c₁ c₂ : ℝ} (hH : 0 ≤ H)
    (hAt : ∀ x, ⟪x, At x⟫ ≤ c₁ * ‖x‖ ^ 2) (hA : ∀ x, -⟪x, A x⟫ ≤ c₂ * ‖x‖ ^ 2)
    {e f : E} (he : ‖e‖ = 1) (hef : ⟪e, f⟫ = 0) (heAf : ⟪e, A f⟫ = 0)
    (h : ⟪e, exp (H • At) f⟫ = 0) :
    H ^ 2 / 2 * |⟪e, A (A f)⟫| ≤
      H * (Real.exp (H * max (c₁ + c₂) 0) * ‖At - A‖) * ‖exp (H • A) f‖ +
        ‖H • A‖ ^ 3 / 6 * Real.exp ‖H • A‖ * ‖f‖ := by
  have h1 := difference_link_floor_kappa At A hH hAt hA he f h
  have h2 := inner_exp_sub_quadratic_le A H e f
  rw [hef, heAf, he, mul_zero, zero_add, zero_add, one_mul] at h2
  have h3 : H ^ 2 / 2 * |⟪e, A (A f)⟫| = |H ^ 2 / 2 * ⟪e, A (A f)⟫| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ H ^ 2 / 2)]
  rw [h3]
  have h4 := abs_sub_abs_le_abs_sub (H ^ 2 / 2 * ⟪e, A (A f)⟫) (⟪e, exp (H • A) f⟫)
  rw [abs_sub_comm] at h4
  linarith

end CoSimFoundations
