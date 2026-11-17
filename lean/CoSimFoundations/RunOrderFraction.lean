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
  obtain ⟨h0, h3⟩ := run_bound_of_le hδ hK' hb hβ0 hs hβ hbb h
  rcases h0.eq_or_lt with h4 | h4
  · rw [← h4, div_zero]
    exact hδ
  · rw [div_le_iff₀ h4]
    exact h3

end Real

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

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
  have hlK : (l : ℝ) ≤ K := by exact_mod_cast hK
  have hx : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hKx : (K : ℝ) * (H * ‖A‖) ≤ 1 / 2 := by rw [← mul_assoc]; exact hKH
  have he : Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right (by linarith) hx).trans hKx)
  have h2 := exp_half_lt
  have h3 : mbar * ((l : ℝ) * (l - 1)) *
      (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) ≤
      mbar * ((l : ℝ) * (l - 1)) * 1.42 :=
    mul_le_mul_of_nonneg_left (by linarith) (bound_mul_pred_nonneg hl hM)
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
  have hK' := run_length_pos hK
  have hb : 0 ≤ 2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ := by positivity
  exact fraction_of_le hδ hK' hb (norm_nonneg _) (le_one_div_of_le_one_div_exp_half hK' hS')
    ((norm_runBalance_le N M (exp (H • A)) (exp (-(H • A))) l).trans_eq (add_assoc _ _ _))
    (run_fraction_constant_le A N M hH hl hK hKH hN hM) h

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
  obtain ⟨S', hS, hS'⟩ := exists_sum_Ico_pow_right_inverse A hH hl hK hKH
  exact run_fraction_of_defect_le A N M hH hl hK hKH hN hM
    ((norm_nonneg _).trans (hδ 0 (Nat.zero_le _))) hS'
    (norm_runDefect_le_of_linear_runs A N M hl hK X hX hδ hS)

end Algebra

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

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
  have hδ0 := relative_error_bound_nonneg hδ
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
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) ≤ ε :=
  run_order_fraction A N M hH hl hK hKH hN hM x hx (relative_error_le_of_isLUB hε)

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
    ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K, c * ‖x0‖ < ‖x x0 k - (exp (H • A) ^ k) x0‖ :=
  exists_relative_error_gt
    (fun _ hδ => run_order_fraction A N M hH hl hK hKH hN hM x hx hδ) hc

end Operator

end CoSimFoundations
