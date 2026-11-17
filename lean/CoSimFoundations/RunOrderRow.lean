/-
The bound over a run for one block row (the paper, Theorem "order over a run" in
the form for the rule of one subsystem).

**Statement.** `E` is the state space (a real Banach space, `E ≠ 0`), `F` the space of the
states of subsystem `i`. `P : E → F` is the projection onto these states (only `‖P‖ ≤ 1` is
used), `N : E → F` the coefficients of the new samples in the rule of `i` and `M r : E → F` the
coefficients of the samples of the age `r`. Only row `i` of the recursion is assumed: for every
initial state `x_0 ≠ 0` a sequence `x^k`, `k ≤ K`, with

  `(P - N) x^{k+1} = Σ_{r < l} M r x^{k-r}`,   `l - 1 ≤ k < K`.

The local defect of the rule is `T_i = (P - N) U - Σ_{r < l} M r U^{-r}`, `U = exp (H • A)`
(`rowDefect`). Let `1 ≤ l ≤ K`, `0 ≤ H`, `K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ n̄`, `‖M r‖ ≤ m̄` for
`1 ≤ r < l`. If `δ` bounds the relative error `‖x^k - U^k x_0‖ / ‖x_0‖` of all these sequences
for all `k ≤ K`, then

  `δ ≥ 0.35 T_K / (b_i + T_K)`,  `T_K = (K - l + 1) ‖T_i‖`,
  `b_i = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`.

For `F = E`, `P = 1` this is `run_order_fraction`. The other rows of the scheme are not used:
the sequences need not come from a scheme.

**Proof** (that of `RunOrder` and `RunOrderFraction`, with every operator replaced by its row).
With `Q = P - N`, `e_k = x^k - U^k x_0` and `B = Q - Σ_r M r` (`rowBalance`):
`T_i U^k x_0 = Σ_r M r e_{k-r} - Q e_{k+1}` (`rowDefect_apply_pow`); the sum over
`l - 1 ≤ k < K` telescopes (`row_accumulation_aux`),

  `T_i Σ_k U^k x_0 = -B Σ_k e_k + Σ_r M r (Σ_{k=l-1-r}^{l-2} e_k - Σ_{k=K-r}^{K-1} e_k)`
      `- Q (e_K - e_{l-1})`,

so `‖T_i Σ_k U^k x_0‖ ≤ d (2 ‖Q‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) ‖B‖)` if `‖e_k‖ ≤ d`
(`norm_row_accumulation_aux_le`), and `‖B‖ ≤ ‖T_i‖ + ‖Q‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖U^{-r} - 1‖`
(`norm_rowBalance_le`). The sum `S = Σ_{k=l-1}^{K-1} U^k` has a right inverse `S'` with
`‖S'‖ ≤ 1 / (0.35 (K - l + 1))` (`exists_sum_Ico_pow_right_inverse`); the sequence of
`x_0 = S' v` gives `‖T_i v‖ ≤ δ ‖S'‖ ‖v‖ (…)` for every `v` (`norm_rowDefect_le_of_runs`), so no
vector on which `T_i` attains its norm is needed. The constant: `‖Q‖ ≤ 1 + n̄` and
`run_fraction_constant_le` (`run_row_constant_le`), then `fraction_of_le`.

**Forms.** `run_order_row` (every upper bound `δ`), `run_order_row_isLUB` (the least upper bound
of the relative errors, the paper's largest relative error), `exists_run_order_row` (a sequence
and a step with a relative error above every `c` below the bound), and `run_order_row_of_le`
(the same with a lower bound `τ ≤ ‖T_i‖` of the local defect in place of `‖T_i‖`).
-/
import CoSimFoundations.RunOrderFraction

open NormedSpace Finset

namespace CoSimFoundations

section Algebraic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The local defect of the rule of one subsystem with `l` held samples:
`T_i = (P - N) U - Σ_{r < l} M r Ui^r`, with `P` the projection onto the states of the
subsystem, `N` the coefficients of the new samples, `M r` those of the samples of the age `r`,
and `Ui` the inverse of the reference step `U`. -/
noncomputable def rowDefect (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) (U Ui : E →L[ℝ] E) (l : ℕ) :
    E →L[ℝ] F :=
  (P - N) ∘L U - ∑ r ∈ range l, M r ∘L (Ui ^ r)

/-- `B = P - N - Σ_{r < l} M r`: what the rule does to a constant sequence. -/
noncomputable def rowBalance (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) (l : ℕ) : E →L[ℝ] F :=
  P - N - ∑ r ∈ range l, M r

/-- The value of the local defect on a vector. -/
theorem rowDefect_apply (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) (U Ui : E →L[ℝ] E) (l : ℕ)
    (v : E) :
    rowDefect P N M U Ui l v = (P - N) (U v) - ∑ r ∈ range l, M r ((Ui ^ r) v) := by
  unfold rowDefect
  rw [_root_.sub_apply, _root_.sum_apply]
  rfl

/-- The value of `B` on a vector. -/
theorem rowBalance_apply (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) (l : ℕ) (v : E) :
    rowBalance P N M l v = (P - N) v - ∑ r ∈ range l, M r v := by
  unfold rowBalance
  rw [_root_.sub_apply, _root_.sum_apply]

/-- One step of the error in the row of the subsystem: the local defect applied to the reference
solution is `T_i U^k x_0 = Σ_r M r e_{k-r} - (P - N) e_{k+1}` with `e_k = x^k - U^k x_0`. -/
theorem rowDefect_apply_pow {P N : E →L[ℝ] F} {M : ℕ → E →L[ℝ] F} {U Ui : E →L[ℝ] E}
    (hU : Ui * U = 1) {l k : ℕ} (hk : l - 1 ≤ k) (x0 : E) (x : ℕ → E)
    (hx : (P - N) (x (k + 1)) = ∑ r ∈ range l, M r (x (k - r))) :
    rowDefect P N M U Ui l ((U ^ k) x0) =
      ∑ r ∈ range l, M r (x (k - r) - (U ^ (k - r)) x0) -
        (P - N) (x (k + 1) - (U ^ (k + 1)) x0) := by
  have h1 : ∀ r ∈ range l, M r ((Ui ^ r) ((U ^ k) x0)) = M r ((U ^ (k - r)) x0) := by
    intro r hr
    have hr' := mem_range.1 hr
    rw [← mul_apply_eq_comp, inv_pow_mul_pow hU (by omega)]
  have h2 : U ((U ^ k) x0) = (U ^ (k + 1)) x0 := by
    rw [← mul_apply_eq_comp, ← pow_succ']
  rw [rowDefect_apply, h2, sum_congr rfl h1, map_sub (P - N), hx]
  simp only [map_sub, sum_sub_distrib]
  abel

/-- The telescoping sum behind the accumulation identity in one row, for sequences `t` in `F`
and `e` in `E` with the one-step relation `t_k = Σ_r M r e_{k-r} - Q e_{k+1}`. -/
theorem row_accumulation_aux (Q : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) (l : ℕ) (t : ℕ → F)
    (e : ℕ → E) :
    ∀ K, l - 1 ≤ K →
      (∀ k, l - 1 ≤ k → k < K → t k = ∑ r ∈ range l, M r (e (k - r)) - Q (e (k + 1))) →
      ∑ k ∈ Ico (l - 1) K, t k =
        -(Q (∑ k ∈ Ico (l - 1) K, e k) - ∑ r ∈ range l, M r (∑ k ∈ Ico (l - 1) K, e k)) +
          ∑ r ∈ range l,
            M r (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K - r) K, e k) -
          Q (e K - e (l - 1)) :=
  accumulation_additive Q M l t e

/-- The bound of the accumulated defect in one row: if `‖e_k‖ ≤ d` for `k ≤ K`, `K ≥ l ≥ 1`,
then `‖Σ_{k=l-1}^{K-1} t_k‖ ≤ d (2 ‖Q‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) ‖Q - Σ_r M r‖)`. -/
theorem norm_row_accumulation_aux_le (Q : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) {l K : ℕ}
    (hl : 1 ≤ l) (hK : l ≤ K) (t : ℕ → F) (e : ℕ → E)
    (h : ∀ k, l - 1 ≤ k → k < K → t k = ∑ r ∈ range l, M r (e (k - r)) - Q (e (k + 1)))
    {d : ℝ} (hd : ∀ k ≤ K, ‖e k‖ ≤ d) :
    ‖∑ k ∈ Ico (l - 1) K, t k‖ ≤
      d * (2 * ‖Q‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖Q - ∑ r ∈ range l, M r‖) := by
  have hβ : ∀ v, ‖Q v - ∑ r ∈ range l, M r v‖ ≤ ‖Q - ∑ r ∈ range l, M r‖ * ‖v‖ := by
    intro v
    have h1 := (Q - ∑ r ∈ range l, M r).le_opNorm v
    rwa [_root_.sub_apply, _root_.sum_apply] at h1
  exact norm_accumulation_additive_le Q M hl hK t e h (norm_nonneg Q)
    (fun r => norm_nonneg (M r)) (norm_nonneg _) Q.le_opNorm (fun r => (M r).le_opNorm) hβ hd

/-- `‖B‖ ≤ ‖T_i‖ + ‖P - N‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖Ui^r - 1‖` for the row of one subsystem. -/
theorem norm_rowBalance_le (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) (U Ui : E →L[ℝ] E) (l : ℕ) :
    ‖rowBalance P N M l‖ ≤ ‖rowDefect P N M U Ui l‖ + ‖P - N‖ * ‖U - 1‖ +
      ∑ r ∈ range l, ‖M r‖ * ‖Ui ^ r - 1‖ := by
  have e : rowBalance P N M l = rowDefect P N M U Ui l - (P - N) ∘L (U - 1) +
      ∑ r ∈ range l, M r ∘L (Ui ^ r - 1) := by
    ext v
    simp only [rowBalance_apply, rowDefect_apply, _root_.add_apply, _root_.sub_apply,
      _root_.sum_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self, map_sub,
      sum_sub_distrib]
    abel
  rw [e]
  have h1 : ‖∑ r ∈ range l, M r ∘L (Ui ^ r - 1)‖ ≤ ∑ r ∈ range l, ‖M r‖ * ‖Ui ^ r - 1‖ :=
    norm_sum_le_of_le _ fun r _ => ContinuousLinearMap.opNorm_comp_le _ _
  have h2 := norm_add_le (rowDefect P N M U Ui l - (P - N) ∘L (U - 1))
    (∑ r ∈ range l, M r ∘L (Ui ^ r - 1))
  have h3 := norm_sub_le (rowDefect P N M U Ui l) ((P - N) ∘L (U - 1))
  have h4 := ContinuousLinearMap.opNorm_comp_le (P - N) (U - 1)
  linarith

end Algebraic

section Constant

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The constant of the row: with `‖Q‖ ≤ 1 + n̄`, `n̄ ≥ 0`, `‖M r‖ ≤ m̄` for `1 ≤ r < l`,
`1 ≤ l ≤ K` and `K H ‖A‖ ≤ 1/2`,
`2 ‖Q‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) (‖Q‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖U^{-r} - 1‖)`
`≤ 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`. -/
theorem run_row_constant_le (A : E →L[ℝ] E) (Q : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) {H : ℝ}
    (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    {nbar mbar : ℝ} (hn : 0 ≤ nbar) (hQ : ‖Q‖ ≤ 1 + nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) :
    2 * ‖Q‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * (‖Q‖ * ‖exp (H • A) - 1‖ +
          ∑ r ∈ range l, ‖M r‖ * ‖exp (-(H • A)) ^ r - 1‖) ≤
      2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) := by
  have hK' : (0 : ℝ) ≤ (K : ℝ) - l + 1 := (run_length_pos hK).le
  -- the same inequality for scalar operators with the norms `1 + n̄` and `‖M r‖`
  have e1 : (1 : E →L[ℝ] E) - (-nbar) • (1 : E →L[ℝ] E) = (1 + nbar) • (1 : E →L[ℝ] E) := by
    rw [neg_smul, sub_neg_eq_add, add_smul, one_smul]
  have n1 : ‖(1 : E →L[ℝ] E) - (-nbar) • (1 : E →L[ℝ] E)‖ = 1 + nbar := by
    rw [e1, norm_smul, norm_one, mul_one, Real.norm_of_nonneg (by linarith)]
  have n2 : ‖(-nbar) • (1 : E →L[ℝ] E)‖ ≤ nbar := by
    rw [norm_smul, norm_one, mul_one, norm_neg, Real.norm_of_nonneg hn]
  have n3 : ∀ r, ‖‖M r‖ • (1 : E →L[ℝ] E)‖ = ‖M r‖ := fun r => by
    rw [norm_smul, norm_one, mul_one, norm_norm]
  have h := run_fraction_constant_le A ((-nbar) • (1 : E →L[ℝ] E))
    (fun r => ‖M r‖ • (1 : E →L[ℝ] E)) hH hl hK hKH n2
    (fun r h1 h2 => (n3 r).le.trans (hM r h1 h2))
  rw [n1] at h
  simp only [n3] at h
  -- monotonicity in `‖Q‖`
  have h1 : 0 ≤ ((K : ℝ) - l + 1) * ‖exp (H • A) - 1‖ := mul_nonneg hK' (norm_nonneg _)
  have h2 : (1 + nbar - ‖Q‖) * (((K : ℝ) - l + 1) * ‖exp (H • A) - 1‖) ≥ 0 :=
    mul_nonneg (by linarith) h1
  nlinarith [h, h2]

/-- The local defect of the row is bounded by the errors of the sequences: if `S'` is a right
inverse of `Σ_{k=l-1}^{K-1} U^k` and `δ ≥ 0` bounds the relative error of the sequences of all
initial states `x_0 ≠ 0` for `k ≤ K`, then
`‖T_i‖ ≤ δ ‖S'‖ (2 ‖P - N‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) ‖B‖)`. -/
theorem norm_rowDefect_le_of_runs (A : E →L[ℝ] E) (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F)
    {H : ℝ} {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖)
    {S' : E →L[ℝ] E} (hS : (∑ k ∈ Ico (l - 1) K, exp (H • A) ^ k) * S' = 1) :
    ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖ ≤
      δ * ‖S'‖ * (2 * ‖P - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖rowBalance P N M l‖) := by
  refine opNorm_le_of_right_inverse hS _ hδ0 (run_factor_nonneg _ M _ hK) fun v hx0 => ?_
  have hSv : (∑ k ∈ Ico (l - 1) K, exp (H • A) ^ k) (S' v) = v := by
    rw [← mul_apply_eq_comp, hS, one_apply_eq_self]
  have hsum : ∑ k ∈ Ico (l - 1) K,
      rowDefect P N M (exp (H • A)) (exp (-(H • A))) l ((exp (H • A) ^ k) (S' v)) =
      rowDefect P N M (exp (H • A)) (exp (-(H • A))) l v := by
    rw [← map_sum, ← _root_.sum_apply, hSv]
  have h := norm_row_accumulation_aux_le (P - N) M hl hK
    (fun k => rowDefect P N M (exp (H • A)) (exp (-(H • A))) l ((exp (H • A) ^ k) (S' v)))
    (fun k => x (S' v) k - (exp (H • A) ^ k) (S' v))
    (fun k hk hkK => rowDefect_apply_pow (exp_neg_mul_exp (H • A)) hk (S' v) (x (S' v))
      (hx (S' v) hx0 k hk hkK))
    (hδ (S' v) hx0)
  rw [hsum] at h
  exact h

end Constant

section Main

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The bound over a run for one block row** (the paper, Theorem "order over a run").
`E ≠ 0` a real Banach space, `F` a normed space, `A : E → E`, and the rule of
subsystem `i`: `P, N, M r : E → F` with `‖P‖ ≤ 1`, `‖N‖ ≤ n̄`, `‖M r‖ ≤ m̄` for `1 ≤ r < l`.
To every initial state `x_0 ≠ 0` let a sequence `x x_0 k`, `k ≤ K`, be assigned with
`(P - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` for `l - 1 ≤ k < K` (row `i` of the recursion only;
arbitrary starting values; the assignment need not be linear). Let `1 ≤ l ≤ K`, `0 ≤ H`,
`K H ‖A‖ ≤ 1/2`. If `‖x^k - U^k x_0‖ ≤ δ ‖x_0‖` for all `x_0 ≠ 0` and `k ≤ K`
(`U = exp (H • A)`), then
`δ ≥ 0.35 T_K / (b_i + T_K)`, `T_K = (K - l + 1) ‖T_i‖`, `b_i = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`,
with the local defect `T_i = (P - N) U - Σ_{r<l} M r U^{-r}` of the rule (`rowDefect`). -/
theorem run_order_row (A : E →L[ℝ] E) (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) {H : ℝ}
    (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    {nbar mbar : ℝ} (hP : ‖P‖ ≤ 1) (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (((K : ℝ) - l + 1) * ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) +
        ((K : ℝ) - l + 1) * ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖) ≤ δ := by
  have hδ0 := relative_error_bound_nonneg hδ
  have hK' := run_length_pos hK
  have hn : 0 ≤ nbar := (norm_nonneg N).trans hN
  have hQ : ‖P - N‖ ≤ 1 + nbar := (norm_sub_le P N).trans (add_le_add hP hN)
  obtain ⟨S', hS, hS'⟩ := exists_sum_Ico_pow_right_inverse A hH hl hK hKH
  have hb : 0 ≤ 2 * ‖P - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ := by positivity
  exact fraction_of_le hδ0 hK' hb (norm_nonneg _) (le_one_div_of_le_one_div_exp_half hK' hS')
    ((norm_rowBalance_le P N M (exp (H • A)) (exp (-(H • A))) l).trans_eq (add_assoc _ _ _))
    (run_row_constant_le A (P - N) M hH hl hK hKH hn hQ hM)
    (norm_rowDefect_le_of_runs A P N M hl hK x hx hδ0 hδ hS)

/-- **The bound over a run for one block row, with a lower bound of the local defect:** in the
setting of `run_order_row`, if `0 ≤ τ ≤ ‖T_i‖`, then
`δ ≥ 0.35 (K - l + 1) τ / (b_i + (K - l + 1) τ)` (the bound is increasing in `‖T_i‖`). -/
theorem run_order_row_of_le (A : E →L[ℝ] E) (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) {H : ℝ}
    (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    {nbar mbar : ℝ} (hP : ‖P‖ ≤ 1) (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖)
    {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖) :
    0.35 * (((K : ℝ) - l + 1) * τ) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) + ((K : ℝ) - l + 1) * τ) ≤ δ := by
  refine le_trans ?_ (run_order_row A P N M hH hl hK hKH hP hN hM x hx hδ)
  have hK' := run_length_pos hK
  have hn : 0 ≤ nbar := (norm_nonneg N).trans hN
  have hm := bound_mul_pred_nonneg hl hM
  have hbpos : 0 < 2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) := by linarith
  have h1 : 0 ≤ ((K : ℝ) - l + 1) * τ := mul_nonneg hK'.le hτ0
  have h2 : ((K : ℝ) - l + 1) * τ ≤
      ((K : ℝ) - l + 1) * ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖ :=
    mul_le_mul_of_nonneg_left hτ hK'.le
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hbpos.le]

/-- **The bound over a run for one block row, for the largest relative error:** if `ε` is the
least upper bound of the relative errors `‖x^k - U^k x_0‖ / ‖x_0‖` over the initial states
`x_0 ≠ 0` and the steps `k ≤ K`, then `ε ≥ 0.35 T_K / (b_i + T_K)`, under the hypotheses of
`run_order_row`. -/
theorem run_order_row_isLUB (A : E →L[ℝ] E) (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) {H : ℝ}
    (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    {nbar mbar : ℝ} (hP : ‖P‖ ≤ 1) (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {ε : ℝ} (hε : IsLUB {e : ℝ | ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K,
      e = ‖x x0 k - (exp (H • A) ^ k) x0‖ / ‖x0‖} ε) :
    0.35 * (((K : ℝ) - l + 1) * ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) +
        ((K : ℝ) - l + 1) * ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖) ≤ ε :=
  run_order_row A P N M hH hl hK hKH hP hN hM x hx (relative_error_le_of_isLUB hε)

/-- **The bound over a run for one block row, as a statement about single sequences:** for every
`c` below `0.35 T_K / (b_i + T_K)` there are an initial state `x_0 ≠ 0` and a step `k ≤ K` at
which the relative error exceeds `c`. -/
theorem exists_run_order_row (A : E →L[ℝ] E) (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F) {H : ℝ}
    (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    {nbar mbar : ℝ} (hP : ‖P‖ ≤ 1) (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {c : ℝ}
    (hc : c < 0.35 * (((K : ℝ) - l + 1) *
        ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖) /
      (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) +
        ((K : ℝ) - l + 1) * ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖)) :
    ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K, c * ‖x0‖ < ‖x x0 k - (exp (H • A) ^ k) x0‖ :=
  exists_relative_error_gt
    (fun _ hδ => run_order_row A P N M hH hl hK hKH hP hN hM x hx hδ) hc

end Main

end CoSimFoundations
