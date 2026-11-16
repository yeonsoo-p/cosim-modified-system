/-
Order over a run, in the form of a fraction of the accumulated defect (the paper, Theorem
"order over a run" `thm:runorder`, inequality `eq:runorder`).

**Statement.** A scheme with `l` held samples in any order of execution is the recursion
`(1 - N) x^{k+1} = Σ_{r < l} M r x^{k-r}`, `l - 1 ≤ k < K` (`RunOrder.lean`), with the local
defect `T = (1 - N) U - Σ_{r < l} M r U^{-r}`, `U = exp (H • A)`. Let `1 ≤ l ≤ K`,
`K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ n̄` and `‖M r‖ ≤ m̄` for `1 ≤ r < l`. If `δ` bounds the relative error
`‖x^k - U^k x_0‖ / ‖x_0‖` of the runs of all initial states `x_0 ≠ 0` for all `k ≤ K`, then

  `δ ≥ 0.35 T_K / (b + T_K)`,  `T_K = (K - l + 1) ‖T‖`,  `b = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`.

This is the paper's inequality with its constants and its hypotheses; `0 ≤ H` and `1 ≤ l` are
implicit in the paper. `RunOrder.lean` has the earlier form
`δ ≥ min {0.175, 0.175 T_K / (2.65 (1 + n̄) + m̄ l (l - 1) (1 + ¼ e^{(l-1) H ‖A‖}))}`.

**Proof** (the paper's, with the lemmas of `RunOrder.lean`). The sum `S = Σ_{k=l-1}^{K-1} U^k`
has a right inverse `S'` with `‖S'‖ ≤ 1 / ((2 - e^{1/2}) K')`, `K' = K - l + 1`
(`exists_sum_Ico_pow_right_inverse`). The run of `x_0 = S' v` gives, for every `v`,
`‖T v‖ ≤ δ ‖S'‖ ‖v‖ (b₀ + K' ‖B‖)` with `b₀ = 2 ‖1 - N‖ + 2 Σ_r r ‖M r‖`
(`norm_runDefect_smul_le_of_run`) and `‖B‖ ≤ ‖T‖ + η`,
`η = ‖1 - N‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖U^{-r} - 1‖` (`norm_runBalance_le`). With
`b₀ + K' η ≤ 2.65 (1 + n̄) + m̄ l (l - 1) (1 + ¼ e^{(l-1) H ‖A‖})` (`run_constant_le`) and
`(l - 1) H ‖A‖ ≤ K H ‖A‖ ≤ 1/2` the right side is at most `b` (`run_fraction_constant_le`), so
`0.35 K' ‖T‖ ≤ δ (b + K' ‖T‖)` (`fraction_of_le`). If `b + T_K = 0` the quotient is zero in Lean
and the statement is `0 ≤ δ`.

The three constants of the paper's proof are `run_fraction_constants`:
`2 - e^{1/2} > 0.35`, `1 + e^{1/2} < 2.65`, `1 + ¼ e^{1/2} < 1.42`.

**Forms.** `run_order_fraction`: operators on a real Banach space `E ≠ 0`, an arbitrary (not
necessarily linear) starting procedure, every upper bound `δ` of the relative errors.
`run_order_fraction_isLUB`: the same for the least upper bound `ε_K` of the relative errors, the
paper's "largest value". `exists_run_order_fraction`: for every `c` below the right-hand side
some run has a relative error above `c` at some step `k ≤ K`. `run_order_fraction_linear`: a
linear starting procedure in a Banach algebra with `‖1‖ = 1`.
-/
import CoSimFoundations.RunOrder

open NormedSpace Finset

namespace CoSimFoundations

section Real

/-- The three constants in the paper's proof of `eq:runorder`: `2 - e^{1/2} > 0.35`,
`1 + e^{1/2} < 2.65` and `1 + ¼ e^{1/2} < 1.42`. -/
theorem run_fraction_constants :
    0.35 < 2 - Real.exp (1 / 2) ∧ 1 + Real.exp (1 / 2) < 2.65 ∧
      1 + 1 / 4 * Real.exp (1 / 2) < 1.42 := by
  have h := exp_half_lt
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The last step of the bound: from `t ≤ δ s (b + K' β)` with `s ≤ 1 / (0.35 K')`,
`β ≤ t + η` and `b + K' η ≤ b'` to `0.35 K' t / (b' + K' t) ≤ δ`. -/
theorem fraction_of_le {t δ s b β η b' K' : ℝ} (hδ : 0 ≤ δ) (hK' : 0 < K')
    (hb : 0 ≤ b) (hβ0 : 0 ≤ β) (hs : s ≤ 1 / (0.35 * K')) (hβ : β ≤ t + η)
    (hbb : b + K' * η ≤ b') (h : t ≤ δ * s * (b + K' * β)) :
    0.35 * (K' * t) / (b' + K' * t) ≤ δ := by
  have h1 : b + K' * β ≤ b' + K' * t := by
    have := mul_le_mul_of_nonneg_left hβ hK'.le
    linarith
  have h0 : 0 ≤ b + K' * β := add_nonneg hb (mul_nonneg hK'.le hβ0)
  have h2 : t ≤ δ * (1 / (0.35 * K')) * (b' + K' * t) :=
    h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hs hδ) h1 h0
      (mul_nonneg hδ (by positivity)))
  have h3 : 0.35 * (K' * t) ≤ δ * (b' + K' * t) := by
    rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h2
    linarith
  rcases (h0.trans h1).eq_or_lt with h4 | h4
  · rw [← h4, div_zero]
    exact hδ
  · rw [div_le_iff₀ h4]
    exact h3

end Real

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The reference step has the inverse `exp (-(H • A))`. -/
private theorem exp_neg_mul_exp_self (Z : 𝔸) : exp (-Z) * exp Z = 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.refl Z).neg_left, neg_add_cancel, exp_zero]

variable [NormOneClass 𝔸]

/-- The constant of the paper: with `‖N‖ ≤ n̄`, `‖M r‖ ≤ m̄` for `1 ≤ r < l`, `1 ≤ l ≤ K` and
`K H ‖A‖ ≤ 1/2`, `b₀ + K' η ≤ 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`, where
`b₀ = 2 ‖1 - N‖ + 2 Σ_r r ‖M r‖`, `η = ‖1 - N‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖U^{-r} - 1‖`,
`K' = K - l + 1`. -/
theorem run_fraction_constant_le (A N : 𝔸) (M : ℕ → 𝔸) {H : ℝ} (hH : 0 ≤ H) {l K : ℕ}
    (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {nbar mbar : ℝ} (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) :
    2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * (‖1 - N‖ * ‖exp (H • A) - 1‖ +
          ∑ r ∈ range l, ‖M r‖ * ‖exp (-(H • A)) ^ r - 1‖) ≤
      2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) := by
  refine (run_constant_le A N M hH hl hK hKH hN hM).trans ?_
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlK : (l : ℝ) ≤ K := by exact_mod_cast hK
  have hx : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hKx : (K : ℝ) * (H * ‖A‖) ≤ 1 / 2 := by rw [← mul_assoc]; exact hKH
  have he : Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right (by linarith) hx).trans hKx)
  have hm : 0 ≤ mbar * ((l : ℝ) * (l - 1)) := by
    rcases hl.eq_or_lt with h1 | h1
    · subst h1
      simp
    · exact mul_nonneg ((norm_nonneg _).trans (hM 1 le_rfl h1))
        (mul_nonneg (by linarith) (by linarith))
  have h2 := exp_half_lt
  have h3 : mbar * ((l : ℝ) * (l - 1)) *
      (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) ≤
      mbar * ((l : ℝ) * (l - 1)) * 1.42 :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  linarith

/-- The bound `eq:runorder` from a bound on the local defect: the common last step of the
forms below. -/
theorem run_fraction_of_defect_le (A N : 𝔸) (M : ℕ → 𝔸) {H : ℝ} (hH : 0 ≤ H) {l K : ℕ}
    (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {nbar mbar : ℝ} (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) {δ : ℝ} (hδ : 0 ≤ δ) {S' : 𝔸}
    (hS' : ‖S'‖ ≤ 1 / ((2 - Real.exp (1 / 2)) * ((K : ℝ) - l + 1)))
    (h : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤
      δ * ‖S'‖ * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖)) :
    0.35 * (((K : ℝ) - l + 1) * ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) +
        ((K : ℝ) - l + 1) * ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖) ≤ δ := by
  have hlK : (l : ℝ) ≤ K := by exact_mod_cast hK
  have hK' : (0 : ℝ) < (K : ℝ) - l + 1 := by linarith
  have he := exp_half_lt
  have hconst := run_fraction_constant_le A N M hH hl hK hKH hN hM
  have hb : 0 ≤ 2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ :=
    add_nonneg (by positivity)
      (mul_nonneg (by norm_num) (sum_nonneg fun r _ => by positivity))
  have hs : ‖S'‖ ≤ 1 / (0.35 * ((K : ℝ) - l + 1)) := by
    refine hS'.trans (one_div_le_one_div_of_le (by positivity) ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) hK'.le
  have hβ := norm_runBalance_le N M (exp (H • A)) (exp (-(H • A))) l
  rw [add_assoc] at hβ
  exact fraction_of_le hδ hK' hb (norm_nonneg _) hs hβ hconst h

/-- **Theorem "order over a run", inequality `eq:runorder`, for a linear starting procedure**,
in a Banach algebra with `‖1‖ = 1`: let `X k` be the map from the initial state to the state
after `k` steps, `(1 - N) X (k+1) = Σ_{r<l} M r X (k-r)` for `l - 1 ≤ k < K`, with arbitrary
`X 0, …, X (l-1)`. If `1 ≤ l ≤ K`, `K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ n̄`, `‖M r‖ ≤ m̄` for `1 ≤ r < l`,
and `‖X k - U^k‖ ≤ δ` for all `k ≤ K`, then `δ ≥ 0.35 T_K / (b + T_K)` with
`T_K = (K - l + 1) ‖T‖`, `T = (1 - N) U - Σ_{r<l} M r U^{-r}` and
`b = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`. -/
theorem run_order_fraction_linear (A N : 𝔸) (M : ℕ → 𝔸) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {nbar mbar : ℝ}
    (hN : ‖N‖ ≤ nbar) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (X : ℕ → 𝔸)
    (hX : ∀ k, l - 1 ≤ k → k < K → (1 - N) * X (k + 1) = ∑ r ∈ range l, M r * X (k - r))
    {δ : ℝ} (hδ : ∀ k ≤ K, ‖X k - exp (H • A) ^ k‖ ≤ δ) :
    0.35 * (((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) + ((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) ≤ δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (Nat.zero_le _))
  obtain ⟨S', hS, hS'⟩ := exists_sum_Ico_pow_right_inverse A hH hl hK hKH
  refine run_fraction_of_defect_le A N M hH hl hK hKH hN hM hδ0 hS' ?_
  have hx : ∀ k, l - 1 ≤ k → k < K →
      (1 - N) • (X (k + 1) * S') = ∑ r ∈ range l, M r • (X (k - r) * S') := by
    intro k hk hkK
    simp only [smul_eq_mul, ← mul_assoc]
    rw [hX k hk hkK, sum_mul]
  have hd : ∀ k ≤ K, ‖X k * S' - exp (H • A) ^ k • S' • (1 : 𝔸)‖ ≤ δ * ‖S'‖ := by
    intro k hk
    rw [smul_eq_mul, smul_eq_mul, mul_one, ← sub_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hδ k hk) (norm_nonneg _))
  have h := norm_runDefect_smul_le_of_run (exp_neg_mul_exp_self (H • A)) hl hK hS (1 : 𝔸)
    (fun k => X k * S') hx hd
  rwa [smul_eq_mul, mul_one] at h

end Algebra

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

/-- The local defect is bounded by the errors of the runs: if `S'` is a right inverse of
`Σ_{k=l-1}^{K-1} U^k` and `δ ≥ 0` bounds the relative error of the runs of all initial states
`x_0 ≠ 0` for `k ≤ K`, then `‖T‖ ≤ δ ‖S'‖ (2 ‖1 - N‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) ‖B‖)`. -/
theorem norm_runDefect_le_of_runs (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ}
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖)
    {S' : E →L[ℝ] E} (hS : (∑ k ∈ Ico (l - 1) K, exp (H • A) ^ k) * S' = 1) :
    ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤
      δ * ‖S'‖ * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖) := by
  have hbdd : IsBoundedSMul (E →L[ℝ] E) E :=
    IsBoundedSMul.of_norm_smul_le fun T v => T.le_opNorm v
  have hb : 0 ≤ 2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
      ((K : ℝ) - l + 1) * ‖runBalance N M l‖ := by
    have hlK : (l : ℝ) ≤ K := by exact_mod_cast hK
    have h1 : (0 : ℝ) ≤ ∑ r ∈ range l, (r : ℝ) * ‖M r‖ := sum_nonneg fun r _ => by positivity
    have h2 : 0 ≤ ((K : ℝ) - l + 1) * ‖runBalance N M l‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
    have := norm_nonneg (1 - N)
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hδ0 (norm_nonneg _)) hb) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hx0 : S' v ≠ 0 := by
    intro h0
    have h1 : (∑ k ∈ Ico (l - 1) K, exp (H • A) ^ k) (S' v) = v := by
      rw [← mul_apply_eq_comp, hS, one_apply_eq_self]
    rw [h0, map_zero] at h1
    exact hv h1.symm
  have h := norm_runDefect_smul_le_of_run (V := E) (exp_neg_mul_exp_self (H • A)) hl hK hS v
    (x (S' v)) (hx (S' v) hx0) (hδ (S' v) hx0)
  refine h.trans ?_
  have h3 : δ * ‖S' v‖ ≤ δ * ‖S'‖ * ‖v‖ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (S'.le_opNorm v) hδ0
  calc δ * ‖S' v‖ * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖)
      ≤ δ * ‖S'‖ * ‖v‖ * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖) := mul_le_mul_of_nonneg_right h3 hb
    _ = δ * ‖S'‖ * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖) * ‖v‖ := by ring

/-- **Theorem "order over a run", inequality `eq:runorder`** (the paper, `thm:runorder`). Operators
on a real Banach space `E ≠ 0`. A starting procedure assigns to every initial state `x_0 ≠ 0` a
run `x x_0 k`, `k ≤ K`, with arbitrary starting values and
`(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` for `l - 1 ≤ k < K`; it need not be linear. Let
`1 ≤ l ≤ K`, `K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ n̄` and `‖M r‖ ≤ m̄` for `1 ≤ r < l`. If `δ` bounds the
relative error of all runs, `‖x^k - U^k x_0‖ ≤ δ ‖x_0‖` for all `x_0 ≠ 0` and `k ≤ K`
(`U = exp (H • A)`), then
`δ ≥ 0.35 T_K / (b + T_K)`, `T_K = (K - l + 1) ‖T‖`, `b = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`,
with the local defect `T = (1 - N) U - Σ_{r<l} M r U^{-r}`. This is the paper's statement with
the largest relative error `ε_K` replaced by any upper bound `δ` of the relative errors. -/
theorem run_order_fraction (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {nbar mbar : ℝ}
    (hN : ‖N‖ ≤ nbar) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) + ((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) ≤ δ := by
  have hδ0 : 0 ≤ δ := by
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    have h := (norm_nonneg _).trans (hδ y hy 0 (Nat.zero_le _))
    exact nonneg_of_mul_nonneg_left h (norm_pos_iff.2 hy)
  obtain ⟨S', hS, hS'⟩ := exists_sum_Ico_pow_right_inverse A hH hl hK hKH
  exact run_fraction_of_defect_le A N M hH hl hK hKH hN hM hδ0 hS'
    (norm_runDefect_le_of_runs A N M hl hK x hx hδ0 hδ hS)

/-- **Theorem "order over a run", inequality `eq:runorder`, for the largest relative error**
(the paper, `thm:runorder`, with `ε_K` as in the paper). If `ε` is the least upper bound of the
relative errors `‖x^k - U^k x_0‖ / ‖x_0‖` over the initial states `x_0 ≠ 0` and the steps
`k ≤ K`, then `ε ≥ 0.35 T_K / (b + T_K)`, under the hypotheses of `run_order_fraction`. -/
theorem run_order_fraction_isLUB (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {nbar mbar : ℝ}
    (hN : ‖N‖ ≤ nbar) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {ε : ℝ} (hε : IsLUB {e : ℝ | ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K,
      e = ‖x x0 k - (exp (H • A) ^ k) x0‖ / ‖x0‖} ε) :
    0.35 * (((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) + ((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) ≤ ε := by
  refine run_order_fraction A N M hH hl hK hKH hN hM x hx fun x0 hx0 k hk => ?_
  have h := hε.1 ⟨x0, hx0, k, hk, rfl⟩
  rwa [div_le_iff₀ (norm_pos_iff.2 hx0)] at h

/-- **Theorem "order over a run", inequality `eq:runorder`, as a statement about single runs:**
for every `c` below `0.35 T_K / (b + T_K)` there are an initial state `x_0 ≠ 0` and a step
`k ≤ K` at which the relative error of the run exceeds `c`. -/
theorem exists_run_order_fraction (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {nbar mbar : ℝ}
    (hN : ‖N‖ ≤ nbar) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {c : ℝ} (hc : c < 0.35 * (((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) + ((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖)) :
    ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K, c * ‖x0‖ < ‖x x0 k - (exp (H • A) ^ k) x0‖ := by
  by_contra hne
  have hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ c * ‖x0‖ := by
    intro x0 hx0 k hk
    by_contra hlt
    exact hne ⟨x0, hx0, k, hk, not_le.1 hlt⟩
  exact absurd (run_order_fraction A N M hH hl hK hKH hN hM x hx hδ) (not_le.2 hc)

end Operator

end CoSimFoundations
