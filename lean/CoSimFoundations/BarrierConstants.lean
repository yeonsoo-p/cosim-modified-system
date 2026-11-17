/-
The first-order barrier with its constants (the paper, Theorem 4.7 `thm:barrier`, first display
(19) `eq:barrier`, with its proof).

In a complete real normed algebra with `‖1‖ = 1` let `U = exp (H • A)` be the reference step
(`H ≥ 0`), `X` the one-step map of a scheme, `K ≥ 1` with `K H ‖A‖ ≤ 1/2`, and `c ≤ ‖X - U‖`.
If `‖X ^ k - U ^ k‖ ≤ δ` for all `k ≤ K`, then

  `min (K c / 10) (√(c / 6)) ≤ δ`,

that is, `max_{k ≤ K} ‖X ^ k - U ^ k‖ ≥ min {K c / 10, √(c / 6)}`.

Proof (the paper's).
(a) `‖exp Z - 1‖ ≤ exp ‖Z‖ - 1` (series), hence `‖U ^ k - 1‖ ≤ exp (k H ‖A‖) - 1`, because
    `U ^ k = exp (k • (H • A))`.
(b) With `S_K = Σ_{k < K} U ^ k` and `β = exp (1/2) - 1`: `‖S_K / K - 1‖ ≤ β < 1`, so `S_K / K`
    has an inverse `T'` (Neumann series) with `‖T'‖ ≤ 1 / (1 - β)`, and `S' = T' / K` is a right
    inverse of `S_K` with `‖S'‖ ≤ 1 / ((1 - β) K)`.
(c) `(K - 1) ‖1 - U‖ ≤ K (exp (H ‖A‖) - 1) ≤ exp (K H ‖A‖) - 1 ≤ β` (Bernoulli).
(d) The accumulation law `norm_step_error_le_of_run` (`Accumulation.lean`) gives
    `c ≤ δ (1 + β + K δ) / ((1 - β) K)`; with `exp (1/2) < 1.65`, that is `β < 0.65`:
    `0.35 K c ≤ δ (1.65 + K δ)`.
(e) If `δ < K c / 10` and `δ² < c / 6`, the right side is below `(0.165 + 1/6) K c < 0.35 K c`.

The number `exp (1/2) < 1.65` follows from `exp 1 < 2.7182818286` (Mathlib) and
`1.65² = 2.7225`.
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import CoSimFoundations.Accumulation
import CoSimFoundations.MemoryBound

open NormedSpace
open scoped Nat

namespace CoSimFoundations

/-- `exp (1/2) < 1.65`. -/
theorem exp_half_lt : Real.exp (1 / 2) < 1.65 := by
  by_contra h
  rw [not_lt] at h
  have h1 : (1.65 : ℝ) ^ 2 ≤ Real.exp (1 / 2) ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h3 := Real.exp_one_lt_d9
  rw [h2] at h1
  norm_num at h1 h3
  linarith

/-- Bernoulli for the exponential: `K (exp x - 1) ≤ exp (K x) - 1`. -/
theorem mul_exp_sub_one_le (x : ℝ) (K : ℕ) :
    K * (Real.exp x - 1) ≤ Real.exp (K * x) - 1 := by
  have h := one_add_mul_le_pow (a := Real.exp x - 1) (by linarith [Real.exp_pos x]) K
  rw [add_sub_cancel, ← Real.exp_nat_mul] at h
  linarith

/-- `2 - e^{1/2} > 0.35`: a bound `s ≤ 1 / ((2 - e^{1/2}) K')` gives `s ≤ 1 / (0.35 K')`. -/
theorem le_one_div_of_le_one_div_exp_half {s K' : ℝ} (hK' : 0 < K')
    (hs : s ≤ 1 / ((2 - Real.exp (1 / 2)) * K')) : s ≤ 1 / (0.35 * K') := by
  have he := exp_half_lt
  refine hs.trans (one_div_le_one_div_of_le (by positivity) ?_)
  exact mul_le_mul_of_nonneg_right (by linarith) hK'.le

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp x * exp (-x) = 1`. -/
theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.refl x).neg_right, add_neg_cancel, exp_zero]

/-- `exp (-x) * exp x = 1`. -/
theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  have h := exp_mul_exp_neg (-x)
  rwa [neg_neg] at h

/-- **The exponential near one:** `‖exp Z - 1‖ ≤ exp ‖Z‖ - 1`. -/
theorem norm_exp_sub_one_le_exp_norm (Z : 𝔸) : ‖exp Z - 1‖ ≤ Real.exp ‖Z‖ - 1 := by
  have hf : HasSum (fun n : ℕ => ((n ! : ℝ)⁻¹) • Z ^ n) (exp Z) :=
    exp_series_hasSum_exp' (𝕂 := ℝ) Z
  have htail := (hasSum_nat_add_iff' 1).2 hf
  rw [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    at htail
  have h : HasSum (fun n : ℕ => ‖Z‖ ^ n / (n ! : ℝ)) (Real.exp ‖Z‖) :=
    Real.exp_eq_exp_ℝ ▸ expSeries_div_hasSum_exp ‖Z‖
  have hg := (hasSum_nat_add_iff' 1).2 h
  rw [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hg
  refine htail.norm_le_of_bounded hg (fun i => ?_)
  rw [norm_smul, norm_inv, Real.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' Z (Nat.succ_pos i))
    (inv_nonneg.2 (Nat.cast_nonneg _))

/-- **Step (a):** the powers of the reference step stay near one,
`‖U ^ k - 1‖ ≤ exp (k H ‖A‖) - 1`. -/
theorem norm_exp_smul_pow_sub_one_le (A : 𝔸) {H : ℝ} (hH : 0 ≤ H) (k : ℕ) :
    ‖exp (H • A) ^ k - 1‖ ≤ Real.exp (k * (H * ‖A‖)) - 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_nsmul]
  refine (norm_exp_sub_one_le_exp_norm _).trans ?_
  have h : ‖k • (H • A)‖ ≤ k * (H * ‖A‖) := by
    refine norm_nsmul_le.trans (le_of_eq ?_)
    rw [norm_smul, Real.norm_of_nonneg hH]
  exact sub_le_sub_right (Real.exp_le_exp.2 h) 1

/-- Within a horizon `K H ‖A‖ ≤ 1/2` every power `U ^ k`, `k ≤ K`, of the reference step is
within `β = exp (1/2) - 1` of one. -/
theorem norm_exp_smul_pow_sub_one_le_half (A : 𝔸) {H : ℝ} (hH : 0 ≤ H) {K : ℕ}
    (hKH : K * H * ‖A‖ ≤ 1 / 2) {k : ℕ} (hk : k ≤ K) :
    ‖exp (H • A) ^ k - 1‖ ≤ Real.exp (1 / 2) - 1 := by
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
  have h1 : (k : ℝ) * (H * ‖A‖) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hkK (mul_nonneg hH (norm_nonneg A))).trans
      (by rw [← mul_assoc]; exact hKH)
  exact (norm_exp_smul_pow_sub_one_le A hH k).trans
    (sub_le_sub_right (Real.exp_le_exp.2 h1) 1)

/-- **Step (c):** within a horizon `K H ‖A‖ ≤ 1/2`, `K' ‖U - 1‖ ≤ exp (1/2) - 1` for every
`0 ≤ K' ≤ K`, because `K (exp x - 1) ≤ exp (K x) - 1`. -/
theorem mul_norm_exp_smul_sub_one_le (A : 𝔸) {H : ℝ} (hH : 0 ≤ H) {K : ℕ}
    (hKH : K * H * ‖A‖ ≤ 1 / 2) {K' : ℝ} (hK'0 : 0 ≤ K') (hK' : K' ≤ K) :
    K' * ‖exp (H • A) - 1‖ ≤ Real.exp (1 / 2) - 1 := by
  have h1 : ‖exp (H • A) - 1‖ ≤ Real.exp (H * ‖A‖) - 1 := by
    refine (norm_exp_sub_one_le_exp_norm _).trans (le_of_eq ?_)
    rw [norm_smul, Real.norm_of_nonneg hH]
  have h2 : 0 ≤ Real.exp (H * ‖A‖) - 1 := (norm_nonneg _).trans h1
  have h3 := mul_exp_sub_one_le (H * ‖A‖) K
  have h4 : Real.exp (K * (H * ‖A‖)) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.2 (by rw [← mul_assoc]; exact hKH)
  calc K' * ‖exp (H • A) - 1‖
      ≤ K' * (Real.exp (H * ‖A‖) - 1) := mul_le_mul_of_nonneg_left h1 hK'0
    _ ≤ K * (Real.exp (H * ‖A‖) - 1) := mul_le_mul_of_nonneg_right hK' h2
    _ ≤ Real.exp (1 / 2) - 1 := by linarith

variable [NormOneClass 𝔸]

/-- **Step (b), for any finite sum:** a sum of `n ≥ 1` elements that are each within
`β = exp (1/2) - 1` of one has a right inverse of norm at most `1 / ((2 - exp (1/2)) n)`: the
mean is within `β < 1` of one and has an inverse `T'` with `‖T'‖ ≤ 1 / (1 - β)` (Neumann
series), and `T' / n` is a right inverse of the sum. -/
theorem exists_sum_right_inverse {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (u : ι → 𝔸)
    (hu : ∀ k ∈ s, ‖u k - 1‖ ≤ Real.exp (1 / 2) - 1) :
    ∃ S' : 𝔸, (∑ k ∈ s, u k) * S' = 1 ∧
      ‖S'‖ ≤ 1 / ((2 - Real.exp (1 / 2)) * (s.card : ℝ)) := by
  have hKpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have he := exp_half_lt
  -- the sum is within `n β` of `n`
  have hS : ‖(∑ k ∈ s, u k) - (s.card : ℝ) • (1 : 𝔸)‖ ≤ s.card * (Real.exp (1 / 2) - 1) := by
    have e : (∑ k ∈ s, u k) - (s.card : ℝ) • (1 : 𝔸) = ∑ k ∈ s, (u k - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [e]
    calc ‖∑ k ∈ s, (u k - 1)‖
        ≤ ∑ _k ∈ s, (Real.exp (1 / 2) - 1) := norm_sum_le_of_le _ hu
      _ = s.card * (Real.exp (1 / 2) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the mean `T` is within `β` of one
  have hT : ‖(s.card : ℝ)⁻¹ • (∑ k ∈ s, u k) - 1‖ ≤ Real.exp (1 / 2) - 1 := by
    have e : (s.card : ℝ)⁻¹ • (∑ k ∈ s, u k) - 1 =
        (s.card : ℝ)⁻¹ • ((∑ k ∈ s, u k) - (s.card : ℝ) • (1 : 𝔸)) := by
      rw [smul_sub, inv_smul_smul₀ hKpos.ne']
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hKpos.le, inv_mul_le_iff₀ hKpos]
    exact hS
  have hT1 : ‖(s.card : ℝ)⁻¹ • (∑ k ∈ s, u k) - 1‖ < 1 := by linarith
  obtain ⟨T', hTT', -⟩ := exists_inverse_of_norm_sub_one_lt hT1
  have hT' := norm_le_of_mul_eq_one hTT' hT1
  have hpos : 0 < 2 - Real.exp (1 / 2) := by linarith
  refine ⟨(s.card : ℝ)⁻¹ • T', ?_, ?_⟩
  · rw [mul_smul_comm, ← smul_mul_assoc]
    exact hTT'
  · rw [norm_smul, norm_inv, Real.norm_of_nonneg hKpos.le, one_div, mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right (hT'.trans ?_) (inv_nonneg.2 hKpos.le)
    rw [one_div]
    exact inv_anti₀ hpos (by linarith)

/-- **Step (b):** over a horizon `K H ‖A‖ ≤ 1/2` the sum `S_K = Σ_{k < K} U ^ k` of the powers of
the reference step has a right inverse of norm at most `1 / ((2 - exp (1/2)) K)`. -/
theorem exists_sum_pow_right_inverse (A : 𝔸) {H : ℝ} (hH : 0 ≤ H) {K : ℕ} (hK : 1 ≤ K)
    (hKH : K * H * ‖A‖ ≤ 1 / 2) :
    ∃ S' : 𝔸, (∑ k ∈ Finset.range K, exp (H • A) ^ k) * S' = 1 ∧
      ‖S'‖ ≤ 1 / ((2 - Real.exp (1 / 2)) * K) := by
  have h := exists_sum_right_inverse (Finset.nonempty_range_iff.2 (by omega))
    (fun k => exp (H • A) ^ k)
    fun k hk => norm_exp_smul_pow_sub_one_le_half A hH hKH (Finset.mem_range.1 hk).le
  rwa [Finset.card_range] at h

/-- **Theorem 4.7 (first-order barrier), inequality (19).** Let `U = exp (H • A)`, `K ≥ 1` with
`K H ‖A‖ ≤ 1/2`, and let the one-step map `X` have `‖X - U‖ ≥ c`. If the error stays below `δ`
over `K` steps, `‖X ^ k - U ^ k‖ ≤ δ` for all `k ≤ K`, then `δ ≥ min {K c / 10, √(c / 6)}`. -/
theorem first_order_barrier (A X : 𝔸) {H : ℝ} (hH : 0 ≤ H) {K : ℕ} (hK : 1 ≤ K)
    (hKH : K * H * ‖A‖ ≤ 1 / 2) {c δ : ℝ} (hc : c ≤ ‖X - exp (H • A)‖)
    (hδ : ∀ k ≤ K, ‖X ^ k - exp (H • A) ^ k‖ ≤ δ) :
    min (K * c / 10) (Real.sqrt (c / 6)) ≤ δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (Nat.zero_le _))
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (0 : ℝ) ≤ (K : ℝ) - 1 := by
    rw [sub_nonneg]
    exact_mod_cast hK
  rcases le_or_gt c 0 with hc0 | hc0
  · -- a floor that is not positive says nothing
    have h : (K : ℝ) * c / 10 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hKpos.le hc0) (by norm_num)
    exact (min_le_left _ _).trans (h.trans hδ0)
  have he := exp_half_lt
  obtain ⟨S', hS, hS'⟩ := exists_sum_pow_right_inverse A hH hK hKH
  have hrun := norm_step_error_le_of_run X (exp (H • A)) S' hK hδ hS
  -- step (c)
  have hU : ((K : ℝ) - 1) * ‖1 - exp (H • A)‖ ≤ Real.exp (1 / 2) - 1 := by
    rw [norm_sub_rev]
    exact mul_norm_exp_smul_sub_one_le A hH hKH hK1 (by linarith)
  -- step (d)
  have h1 : 1 + ((K : ℝ) - 1) * (‖1 - exp (H • A)‖ + δ) ≤ 1.65 + K * δ := by
    have h : ((K : ℝ) - 1) * δ ≤ K * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
    rw [mul_add]
    linarith
  have hS'' : ‖S'‖ ≤ 1 / (0.35 * K) := le_one_div_of_le_one_div_exp_half hKpos hS'
  have h2 : c ≤ δ * (1.65 + K * δ) * (1 / (0.35 * K)) :=
    hc.trans (hrun.trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 hδ0) hS'' (norm_nonneg _)
      (mul_nonneg hδ0 (by positivity))))
  have h3 : 0.35 * K * c ≤ δ * (1.65 + K * δ) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)] at h2
    linarith
  -- step (e)
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  obtain ⟨ha, hb⟩ := hlt
  have hb' : δ ^ 2 < c / 6 := (Real.lt_sqrt hδ0).1 hb
  have h4 := mul_lt_mul_of_pos_left hb' hKpos
  have h5 := mul_pos hKpos hc0
  nlinarith

/-- **Theorem 4.7, inequality (19), as a statement about the largest error over the run:**
there is a step `k ≤ K` at which the error is at least `min {K c / 10, √(c / 6)}`. -/
theorem exists_first_order_barrier (A X : 𝔸) {H : ℝ} (hH : 0 ≤ H) {K : ℕ} (hK : 1 ≤ K)
    (hKH : K * H * ‖A‖ ≤ 1 / 2) {c : ℝ} (hc : c ≤ ‖X - exp (H • A)‖) :
    ∃ k ≤ K, min (K * c / 10) (Real.sqrt (c / 6)) ≤ ‖X ^ k - exp (H • A) ^ k‖ := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := K))
    (fun k => ‖X ^ k - exp (H • A) ^ k‖)
  refine ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), ?_⟩
  rw [← hmax]
  refine first_order_barrier A X hH hK hKH hc (fun j hj => ?_)
  exact Finset.le_sup' (fun k => ‖X ^ k - exp (H • A) ^ k‖)
    (Finset.mem_range.2 (Nat.lt_succ_iff.2 hj))

/-- **Theorem 4.7, inequality (19), with the maximum:**
`max_{k ≤ K} ‖X ^ k - U ^ k‖ ≥ min {K c / 10, √(c / 6)}`. -/
theorem first_order_barrier_sup (A X : 𝔸) {H : ℝ} (hH : 0 ≤ H) {K : ℕ} (hK : 1 ≤ K)
    (hKH : K * H * ‖A‖ ≤ 1 / 2) {c : ℝ} (hc : c ≤ ‖X - exp (H • A)‖) :
    min (K * c / 10) (Real.sqrt (c / 6)) ≤
      (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖X ^ k - exp (H • A) ^ k‖) :=
  first_order_barrier A X hH hK hKH hc (fun _ hj =>
    Finset.le_sup' (fun k => ‖X ^ k - exp (H • A) ^ k‖)
      (Finset.mem_range.2 (Nat.lt_succ_iff.2 hj)))

end Algebra

end CoSimFoundations
