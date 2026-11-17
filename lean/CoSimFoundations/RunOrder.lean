/-
Order over a run with `l` held samples (the paper, Theorem 4.11 `thm:runorder`, inequality
`eq:runorder`).

**Setting.** A scheme with `l` held samples in any order of execution is a multistep recursion

  `(1 - N) x^{k+1} = Σ_{r < l} M r x^{k-r}`,   `l - 1 ≤ k < K`,

with `N` the coefficients of new samples and `M r` those of the samples of age `r`. `U` is the
reference step with inverse `Ui`, `e_k = x^k - U^k x_0` the error of the run assigned to the
initial state `x_0`, and

  `T = (1 - N) U - Σ_{r < l} M r Ui^r`  (local defect, `runDefect`),
  `B = 1 - N - Σ_{r < l} M r`           (`runBalance`).

**Accumulation with memory** (`accumulation_memory`), an identity in a ring acting on a module
(matrices on vectors, operators on a space, an algebra on itself), for `K ≥ l - 1`:

  `T Σ_{k=l-1}^{K-1} U^k x_0 = -B Σ_{k=l-1}^{K-1} e_k
      + Σ_{r<l} M r (Σ_{k=l-1-r}^{l-2} e_k - Σ_{k=K-r}^{K-1} e_k) - (1 - N)(e_K - e_{l-1})`.

Proof: `T U^k x_0 = Σ_r M r e_{k-r} - (1 - N) e_{k+1}` (subtract the recursion of the reference
from that of the scheme); in the sum over `k` the terms telescope (induction on `K`).

**Bounds** (`norm_defect_smul_sum_le`, `norm_runBalance_le`): if `‖e_k‖ ≤ d` for `k ≤ K`, `K ≥ l`,

  `‖T Σ_{k=l-1}^{K-1} U^k x_0‖ ≤ d (2 ‖1 - N‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) ‖B‖)`,
  `‖B‖ ≤ ‖T‖ + ‖1 - N‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖Ui^r - 1‖`.

**The barrier** (`run_order_barrier`, `run_order_barrier_linear`). Let `U = exp (H • A)`,
`1 ≤ l ≤ K`, `K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ ν`, `‖M r‖ ≤ m̄` for `1 ≤ r < l`. If `δ` bounds the relative
error `‖x^k - U^k x_0‖ / ‖x_0‖` of the runs of all initial states `x_0 ≠ 0` for all `k ≤ K`, then

  `δ ≥ min {0.175, 0.175 (K - l + 1) ‖T‖ / (2.65 (1 + ν) + m̄ l (l - 1) (1 + ¼ e^{(l-1) H ‖A‖}))}`.

Proof (the paper's). Every `U^k`, `k < K`, is within `e^{1/2} - 1 < 0.65` of `1`, so
`S = Σ_{k=l-1}^{K-1} U^k` has an inverse `S'` with `‖S'‖ ≤ 1 / (0.35 K')`, `K' = K - l + 1`
(Neumann series). For every `v`, the run of `x_0 = S' v` gives
`‖T v‖ ≤ δ ‖S'‖ ‖v‖ (b + K' ‖B‖)`, hence `‖T‖ ≤ δ (b + K' η + K' ‖T‖) / (0.35 K')`, and for
`δ < 0.175` the term with `‖T‖` on the right is at most half of the left side. The constants:
`K' ‖U - 1‖ ≤ e^{1/2} - 1` (Bernoulli) and
`K' ‖Ui^r - 1‖ ≤ K' r H ‖A‖ e^{r H ‖A‖} ≤ (r/2) e^{r H ‖A‖}`.
The paper takes a unit vector that `T` maps to its norm; here the bound is proved for every `v`,
so that no attainment is needed and the space may have infinite dimension.

**The supremum over initial states** is stated in two equivalent forms: for every bound `δ` on
the relative errors of all runs the inequality holds (`run_order_barrier`); and for every `c`
below the right-hand side there are an initial state `x_0 ≠ 0` and a step `k ≤ K` with
`‖x^k - U^k x_0‖ > c ‖x_0‖` (`exists_run_order_barrier`). The starting procedure is an arbitrary
map from initial states to runs; it need not be linear. For a linear starting procedure
(`x^k = X k x_0`) the statement is `run_order_barrier_linear`, in any Banach algebra.

Not in this file: the second display `eq:orderl` of Theorem 4.11 (it combines `eq:runorder` with
Theorem 4.10, `MemoryLead.lean`, and is stated to leading order).
-/
import CoSimFoundations.BarrierConstants

open NormedSpace Finset

namespace CoSimFoundations

section Ring

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- The local defect of a scheme with `l` held samples: `T = (1 - N) U - Σ_{r < l} M r Ui^r`,
with `Ui` the inverse of the reference step `U`. -/
def runDefect (N : R) (M : ℕ → R) (U Ui : R) (l : ℕ) : R :=
  (1 - N) * U - ∑ r ∈ range l, M r * Ui ^ r

/-- `B = 1 - N - Σ_{r < l} M r`: what the recursion does to a constant sequence. -/
def runBalance (N : R) (M : ℕ → R) (l : ℕ) : R :=
  1 - N - ∑ r ∈ range l, M r

/-- Powers of the inverse cancel powers of the step: `Ui^r U^k = U^(k-r)` for `r ≤ k`. -/
theorem inv_pow_mul_pow {U Ui : R} (hU : Ui * U = 1) {r k : ℕ} (hr : r ≤ k) :
    Ui ^ r * U ^ k = U ^ (k - r) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, pow_mul_pow_eq_one r hU, one_mul]

/-- One step of the error: the local defect applied to the reference solution is
`T U^k x_0 = Σ_r M r e_{k-r} - (1 - N) e_{k+1}` with `e_k = x^k - U^k x_0`. -/
theorem runDefect_smul_pow {N : R} {M : ℕ → R} {U Ui : R} (hU : Ui * U = 1) {l k : ℕ}
    (hk : l - 1 ≤ k) (x0 : V) (x : ℕ → V)
    (hx : (1 - N) • x (k + 1) = ∑ r ∈ range l, M r • x (k - r)) :
    runDefect N M U Ui l • U ^ k • x0 =
      ∑ r ∈ range l, M r • (x (k - r) - U ^ (k - r) • x0) -
        (1 - N) • (x (k + 1) - U ^ (k + 1) • x0) := by
  have h1 : ∀ r ∈ range l, (M r * Ui ^ r) • U ^ k • x0 = M r • U ^ (k - r) • x0 := by
    intro r hr
    have hr' := mem_range.1 hr
    rw [mul_smul, ← mul_smul (Ui ^ r), inv_pow_mul_pow hU (by omega)]
  have h2 : runDefect N M U Ui l • U ^ k • x0 =
      (1 - N) • U ^ (k + 1) • x0 - ∑ r ∈ range l, M r • U ^ (k - r) • x0 := by
    unfold runDefect
    rw [sub_smul, sum_smul, sum_congr rfl h1, mul_smul, ← mul_smul U, ← pow_succ']
  rw [h2, smul_sub (1 - N), hx]
  simp only [smul_sub, sum_sub_distrib]
  abel

/-- A window of `r` terms moved one step to the right. -/
theorem sum_Ico_shift_succ (e : ℕ → V) {K r : ℕ} (hr : r ≤ K) :
    ∑ k ∈ Ico (K + 1 - r) (K + 1), e k = ∑ k ∈ Ico (K - r) K, e k + e K - e (K - r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp
  · have h1 : K + 1 - r = K - r + 1 := by omega
    have h2 : ∑ k ∈ Ico (K - r) (K + 1), e k = ∑ k ∈ Ico (K - r) K, e k + e K :=
      sum_Ico_succ_top (by omega) e
    have h3 : ∑ k ∈ Ico (K - r) (K + 1), e k = e (K - r) + ∑ k ∈ Ico (K - r + 1) (K + 1), e k :=
      sum_eq_sum_Ico_succ_bot (by omega) e
    rw [h1, ← h2, h3]
    abel

/-- **The telescoping sum behind the accumulation identity,** for additive maps `Q`, `M r` from
`E` to `F` and sequences `t` in `F`, `e` in `E` with the one-step relation
`t_k = Σ_r M r e_{k-r} - Q e_{k+1}`:
`Σ_{k=l-1}^{K-1} t_k = -(Q - Σ_r M r) Σ_{k=l-1}^{K-1} e_k
  + Σ_{r<l} M r (Σ_{k=l-1-r}^{l-2} e_k - Σ_{k=K-r}^{K-1} e_k) - Q (e_K - e_{l-1})`. -/
theorem accumulation_additive {E F Φ : Type*} [AddCommGroup E] [AddCommGroup F] [FunLike Φ E F]
    [AddMonoidHomClass Φ E F] (Q : Φ) (M : ℕ → Φ) (l : ℕ) (t : ℕ → F) (e : ℕ → E) :
    ∀ K, l - 1 ≤ K →
      (∀ k, l - 1 ≤ k → k < K → t k = ∑ r ∈ range l, M r (e (k - r)) - Q (e (k + 1))) →
      ∑ k ∈ Ico (l - 1) K, t k =
        -(Q (∑ k ∈ Ico (l - 1) K, e k) - ∑ r ∈ range l, M r (∑ k ∈ Ico (l - 1) K, e k)) +
          ∑ r ∈ range l,
            M r (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K - r) K, e k) -
          Q (e K - e (l - 1)) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro _
    simp
  | succ K hK ih =>
    intro h
    have ih' := ih fun k hk hkK => h k hk (Nat.lt_succ_of_lt hkK)
    have hs := h K hK (Nat.lt_succ_self K)
    have htele : ∀ r ∈ range l,
        M r (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K + 1 - r) (K + 1), e k) =
          M r (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K - r) K, e k) -
            M r (e K) + M r (e (K - r)) := by
      intro r hr
      have hr' := mem_range.1 hr
      rw [sum_Ico_shift_succ e (by omega : r ≤ K)]
      simp only [map_sub, map_add]
      abel
    have e1 : Q (∑ k ∈ Ico (l - 1) K, e k + e K) = Q (∑ k ∈ Ico (l - 1) K, e k) + Q (e K) :=
      map_add Q _ _
    have e2 : ∀ r ∈ range l, M r (∑ k ∈ Ico (l - 1) K, e k + e K) =
        M r (∑ k ∈ Ico (l - 1) K, e k) + M r (e K) := fun r _ => map_add (M r) _ _
    rw [sum_Ico_succ_top hK, sum_Ico_succ_top hK, ih', hs, e1, sum_congr rfl e2,
      sum_congr rfl htele, sum_add_distrib, sum_add_distrib, sum_sub_distrib,
      map_sub Q (e (K + 1)), map_sub Q (e K)]
    abel

/-- The telescoping sum behind the accumulation identity, for any sequences `u`, `e` that
satisfy the one-step relation `T u_k = Σ_r M r e_{k-r} - (1 - N) e_{k+1}`. -/
theorem accumulation_memory_aux (N : R) (M : ℕ → R) (T : R) (l : ℕ) (u e : ℕ → V) :
    ∀ K, l - 1 ≤ K →
      (∀ k, l - 1 ≤ k → k < K →
        T • u k = ∑ r ∈ range l, M r • e (k - r) - (1 - N) • e (k + 1)) →
      T • ∑ k ∈ Ico (l - 1) K, u k =
        -(runBalance N M l • ∑ k ∈ Ico (l - 1) K, e k) +
          ∑ r ∈ range l,
            M r • (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K - r) K, e k) -
          (1 - N) • (e K - e (l - 1)) := by
  intro K hK h
  have hB : runBalance N M l • ∑ k ∈ Ico (l - 1) K, e k =
      (1 - N) • ∑ k ∈ Ico (l - 1) K, e k - ∑ r ∈ range l, M r • ∑ k ∈ Ico (l - 1) K, e k := by
    unfold runBalance
    rw [sub_smul, sum_smul]
  rw [smul_sum, hB]
  exact accumulation_additive (DistribSMul.toAddMonoidHom V (1 - N))
    (fun r => DistribSMul.toAddMonoidHom V (M r)) l (fun k => T • u k) e K hK h

/-- **Accumulation with memory** (report, Proposition "accumulation with memory", identity
(accmem); the first display in the proof of Theorem 4.11). For a sequence with
`(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` for `l - 1 ≤ k < K` and `e_k = x^k - U^k x_0`:
`T Σ_{k=l-1}^{K-1} U^k x_0 = -B Σ_{k=l-1}^{K-1} e_k
  + Σ_{r<l} M r (Σ_{k=l-1-r}^{l-2} e_k - Σ_{k=K-r}^{K-1} e_k) - (1 - N)(e_K - e_{l-1})`.
The term `r = 0` of the middle sum is zero. -/
theorem accumulation_memory {N : R} {M : ℕ → R} {U Ui : R} (hU : Ui * U = 1) {l K : ℕ}
    (hK : l - 1 ≤ K) (x0 : V) (x : ℕ → V)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) • x (k + 1) = ∑ r ∈ range l, M r • x (k - r)) :
    runDefect N M U Ui l • ∑ k ∈ Ico (l - 1) K, U ^ k • x0 =
      -(runBalance N M l • ∑ k ∈ Ico (l - 1) K, (x k - U ^ k • x0)) +
        ∑ r ∈ range l,
          M r • (∑ k ∈ Ico (l - 1 - r) (l - 1), (x k - U ^ k • x0) -
            ∑ k ∈ Ico (K - r) K, (x k - U ^ k • x0)) -
        (1 - N) • ((x K - U ^ K • x0) - (x (l - 1) - U ^ (l - 1) • x0)) :=
  accumulation_memory_aux N M (runDefect N M U Ui l) l (fun k => U ^ k • x0)
    (fun k => x k - U ^ k • x0) K hK
    (fun k hk hkK => runDefect_smul_pow hU hk x0 x (hx k hk hkK))

end Ring

section Length

/-- The number of the steps `l - 1, …, K - 1` of a run after its starting values, as a real
number: `K - l + 1`. -/
theorem cast_run_length {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) :
    ((K - (l - 1) : ℕ) : ℝ) = (K : ℝ) - l + 1 := by
  rw [Nat.cast_sub (by omega), Nat.cast_sub hl]
  push_cast
  ring

/-- The number `K - l + 1` of the steps of a run after its starting values is positive for
`l ≤ K`. -/
theorem run_length_pos {l K : ℕ} (hK : l ≤ K) : (0 : ℝ) < (K : ℝ) - l + 1 := by
  have hlK : (l : ℝ) ≤ K := by exact_mod_cast hK
  linarith

/-- The factor `b + K' ‖B‖` of the bounds over a run is not negative:
`0 ≤ 2 ‖q‖ + 2 Σ_r r ‖m_r‖ + (K - l + 1) ‖β‖` for `l ≤ K`. -/
theorem run_factor_nonneg {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
    [NormedAddCommGroup V₃] (q : V₁) (m : ℕ → V₂) (β : V₃) {l K : ℕ} (hK : l ≤ K) :
    0 ≤ 2 * ‖q‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖m r‖ + ((K : ℝ) - l + 1) * ‖β‖ := by
  have hK' := run_length_pos hK
  positivity

/-- `m̄ l (l - 1) ≥ 0` if `m̄` bounds the norms of the `M r` with `1 ≤ r < l`. -/
theorem bound_mul_pred_nonneg {V : Type*} [NormedAddCommGroup V] {M : ℕ → V} {l : ℕ}
    (hl : 1 ≤ l) {mbar : ℝ} (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) :
    0 ≤ mbar * ((l : ℝ) * (l - 1)) := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  rcases Nat.lt_or_ge 1 l with h | h
  · exact mul_nonneg ((norm_nonneg _).trans (hM 1 le_rfl h))
      (mul_nonneg (by linarith) (by linarith))
  · have h1 : l = 1 := by omega
    rw [h1]
    simp

end Length

section Normed

variable {R V : Type*} [NormedRing R] [NormedAddCommGroup V] [Module R V] [IsBoundedSMul R V]

/-- A sum of `b - a` terms of size at most `d`. -/
theorem norm_sum_Ico_le (e : ℕ → V) {a b K : ℕ} {d : ℝ} (hb : b ≤ K + 1)
    (hd : ∀ k ≤ K, ‖e k‖ ≤ d) : ‖∑ k ∈ Ico a b, e k‖ ≤ ((b - a : ℕ) : ℝ) * d :=
  calc ‖∑ k ∈ Ico a b, e k‖ ≤ ∑ _k ∈ Ico a b, d :=
        norm_sum_le_of_le _ fun k hk => hd k (by have := (mem_Ico.1 hk).2; omega)
    _ = ((b - a : ℕ) : ℝ) * d := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- **The bound of the accumulated defect,** for additive maps `Q`, `M r` from `E` to `F` with
`‖Q v‖ ≤ q ‖v‖`, `‖M r v‖ ≤ m_r ‖v‖`, `‖Q v - Σ_r M r v‖ ≤ β ‖v‖` and sequences with the one-step
relation `t_k = Σ_r M r e_{k-r} - Q e_{k+1}`: if `‖e_k‖ ≤ d` for `k ≤ K`, `K ≥ l ≥ 1`, then
`‖Σ_{k=l-1}^{K-1} t_k‖ ≤ d (2 q + 2 Σ_r r m_r + (K - l + 1) β)`. -/
theorem norm_accumulation_additive_le {E F Φ : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [FunLike Φ E F] [AddMonoidHomClass Φ E F] (Q : Φ) (M : ℕ → Φ)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (t : ℕ → F) (e : ℕ → E)
    (h : ∀ k, l - 1 ≤ k → k < K → t k = ∑ r ∈ range l, M r (e (k - r)) - Q (e (k + 1)))
    {q β : ℝ} {m : ℕ → ℝ} (hq0 : 0 ≤ q) (hm0 : ∀ r, 0 ≤ m r) (hβ0 : 0 ≤ β)
    (hq : ∀ v, ‖Q v‖ ≤ q * ‖v‖) (hm : ∀ r v, ‖M r v‖ ≤ m r * ‖v‖)
    (hβ : ∀ v, ‖Q v - ∑ r ∈ range l, M r v‖ ≤ β * ‖v‖)
    {d : ℝ} (hd : ∀ k ≤ K, ‖e k‖ ≤ d) :
    ‖∑ k ∈ Ico (l - 1) K, t k‖ ≤
      d * (2 * q + 2 * ∑ r ∈ range l, (r : ℝ) * m r + ((K : ℝ) - l + 1) * β) := by
  rw [accumulation_additive Q M l t e K (by omega) h]
  have h1 : ‖Q (∑ k ∈ Ico (l - 1) K, e k) - ∑ r ∈ range l, M r (∑ k ∈ Ico (l - 1) K, e k)‖ ≤
      β * (((K : ℝ) - l + 1) * d) := by
    refine (hβ _).trans (mul_le_mul_of_nonneg_left ?_ hβ0)
    have h' := norm_sum_Ico_le e (a := l - 1) (b := K) (K := K) (by omega) hd
    rwa [cast_run_length hl hK] at h'
  have h2 : ‖∑ r ∈ range l,
      M r (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K - r) K, e k)‖ ≤
      ∑ r ∈ range l, m r * (2 * ((r : ℝ) * d)) := by
    refine norm_sum_le_of_le _ fun r hr => ?_
    have hr' := mem_range.1 hr
    refine (hm r _).trans (mul_le_mul_of_nonneg_left ?_ (hm0 r))
    have ha := norm_sum_Ico_le e (a := l - 1 - r) (b := l - 1) (K := K) (by omega) hd
    have hb := norm_sum_Ico_le e (a := K - r) (b := K) (K := K) (by omega) hd
    have hca : l - 1 - (l - 1 - r) = r := by omega
    have hcb : K - (K - r) = r := by omega
    rw [hca] at ha
    rw [hcb] at hb
    exact (norm_sub_le _ _).trans (by linarith)
  have h3 : ‖Q (e K - e (l - 1))‖ ≤ q * (2 * d) := by
    refine (hq _).trans (mul_le_mul_of_nonneg_left ?_ hq0)
    exact (norm_sub_le _ _).trans (by linarith [hd K le_rfl, hd (l - 1) (by omega)])
  have h4 : ∑ r ∈ range l, m r * (2 * ((r : ℝ) * d)) =
      d * (2 * ∑ r ∈ range l, (r : ℝ) * m r) := by
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun r _ => by ring
  have h5 := norm_sub_le
    (-(Q (∑ k ∈ Ico (l - 1) K, e k) - ∑ r ∈ range l, M r (∑ k ∈ Ico (l - 1) K, e k)) +
      ∑ r ∈ range l, M r (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K - r) K, e k))
    (Q (e K - e (l - 1)))
  have h6 := norm_add_le
    (-(Q (∑ k ∈ Ico (l - 1) K, e k) - ∑ r ∈ range l, M r (∑ k ∈ Ico (l - 1) K, e k)))
    (∑ r ∈ range l, M r (∑ k ∈ Ico (l - 1 - r) (l - 1), e k - ∑ k ∈ Ico (K - r) K, e k))
  rw [norm_neg] at h6
  rw [h4] at h2
  linarith

/-- The bound behind (accmembound), for sequences with the one-step relation. -/
theorem norm_accumulation_memory_aux_le (N : R) (M : ℕ → R) (T : R) {l K : ℕ} (hl : 1 ≤ l)
    (hK : l ≤ K) (u e : ℕ → V)
    (h : ∀ k, l - 1 ≤ k → k < K →
      T • u k = ∑ r ∈ range l, M r • e (k - r) - (1 - N) • e (k + 1))
    {d : ℝ} (hd : ∀ k ≤ K, ‖e k‖ ≤ d) :
    ‖T • ∑ k ∈ Ico (l - 1) K, u k‖ ≤
      d * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖) := by
  have hB : ∀ v : V, ‖(1 - N) • v - ∑ r ∈ range l, M r • v‖ ≤ ‖runBalance N M l‖ * ‖v‖ := by
    intro v
    rw [← sum_smul, ← sub_smul]
    exact norm_smul_le (runBalance N M l) v
  rw [smul_sum]
  exact norm_accumulation_additive_le (DistribSMul.toAddMonoidHom V (1 - N))
    (fun r => DistribSMul.toAddMonoidHom V (M r)) hl hK (fun k => T • u k) e h
    (norm_nonneg (1 - N)) (fun r => norm_nonneg (M r)) (norm_nonneg (runBalance N M l))
    (norm_smul_le (1 - N)) (fun r => norm_smul_le (M r)) hB hd

/-- **The bound (accmembound)** (second display in the proof of Theorem 4.11): if the errors
`e_k = x^k - U^k x_0` of a run are at most `d` for `k ≤ K`, `K ≥ l ≥ 1`, then
`‖T Σ_{k=l-1}^{K-1} U^k x_0‖ ≤ d (2 ‖1 - N‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) ‖B‖)`. -/
theorem norm_defect_smul_sum_le {N : R} {M : ℕ → R} {U Ui : R} (hU : Ui * U = 1) {l K : ℕ}
    (hl : 1 ≤ l) (hK : l ≤ K) (x0 : V) (x : ℕ → V)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) • x (k + 1) = ∑ r ∈ range l, M r • x (k - r))
    {d : ℝ} (hd : ∀ k ≤ K, ‖x k - U ^ k • x0‖ ≤ d) :
    ‖runDefect N M U Ui l • ∑ k ∈ Ico (l - 1) K, U ^ k • x0‖ ≤
      d * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖) :=
  norm_accumulation_memory_aux_le N M (runDefect N M U Ui l) hl hK (fun k => U ^ k • x0)
    (fun k => x k - U ^ k • x0)
    (fun k hk hkK => runDefect_smul_pow hU hk x0 x (hx k hk hkK)) hd

/-- **The bound (Bbound)** (third display in the proof of Theorem 4.11):
`‖B‖ ≤ ‖T‖ + ‖1 - N‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖Ui^r - 1‖`. -/
theorem norm_runBalance_le (N : R) (M : ℕ → R) (U Ui : R) (l : ℕ) :
    ‖runBalance N M l‖ ≤ ‖runDefect N M U Ui l‖ + ‖1 - N‖ * ‖U - 1‖ +
      ∑ r ∈ range l, ‖M r‖ * ‖Ui ^ r - 1‖ := by
  have e : runBalance N M l = runDefect N M U Ui l - (1 - N) * (U - 1) +
      ∑ r ∈ range l, M r * (Ui ^ r - 1) := by
    unfold runBalance runDefect
    simp only [mul_sub, mul_one, sum_sub_distrib]
    abel
  rw [e]
  have h1 : ‖∑ r ∈ range l, M r * (Ui ^ r - 1)‖ ≤ ∑ r ∈ range l, ‖M r‖ * ‖Ui ^ r - 1‖ :=
    norm_sum_le_of_le _ fun r _ => norm_mul_le _ _
  have h2 := norm_add_le (runDefect N M U Ui l - (1 - N) * (U - 1))
    (∑ r ∈ range l, M r * (Ui ^ r - 1))
  have h3 := norm_sub_le (runDefect N M U Ui l) ((1 - N) * (U - 1))
  have h4 := norm_mul_le (1 - N) (U - 1)
  linarith

/-- If the sum of the reference's powers over the run has a right inverse `S'`, the local defect
on any vector `v` is bounded by the errors of the run that starts at `x_0 = S' v`. -/
theorem norm_runDefect_smul_le_of_run {N : R} {M : ℕ → R} {U Ui : R} (hU : Ui * U = 1)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) {S' : R} (hS : (∑ k ∈ Ico (l - 1) K, U ^ k) * S' = 1)
    (v : V) (x : ℕ → V)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) • x (k + 1) = ∑ r ∈ range l, M r • x (k - r))
    {d : ℝ} (hd : ∀ k ≤ K, ‖x k - U ^ k • S' • v‖ ≤ d) :
    ‖runDefect N M U Ui l • v‖ ≤
      d * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖) := by
  have h := norm_defect_smul_sum_le hU hl hK (S' • v) x hx hd
  rwa [← sum_smul, ← mul_smul _ S', hS, one_smul] at h

end Normed

section Real

/-- `e^y - 1 ≤ y e^y`. -/
theorem exp_sub_one_le_mul_exp (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have h2 := mul_le_mul_of_nonneg_right h (Real.exp_pos y).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  linarith

/-- `Σ_{r < l} r = l (l - 1) / 2`. -/
theorem sum_range_cast_id (l : ℕ) : ∑ r ∈ range l, (r : ℝ) = (l : ℝ) * (l - 1) / 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The common step of the bounds over a run: from `t ≤ δ s (b + K' β)` with
`s ≤ 1 / (0.35 K')`, `β ≤ t + η` and `b + K' η ≤ b'` to `0.35 K' t ≤ δ (b' + K' t)`, with
`b' + K' t ≥ 0`. -/
theorem run_bound_of_le {t δ s b β η b' K' : ℝ} (hδ : 0 ≤ δ) (hK' : 0 < K') (hb : 0 ≤ b)
    (hβ0 : 0 ≤ β) (hs : s ≤ 1 / (0.35 * K')) (hβ : β ≤ t + η) (hbb : b + K' * η ≤ b')
    (h : t ≤ δ * s * (b + K' * β)) :
    0 ≤ b' + K' * t ∧ 0.35 * (K' * t) ≤ δ * (b' + K' * t) := by
  have h1 : b + K' * β ≤ b' + K' * t := by
    have := mul_le_mul_of_nonneg_left hβ hK'.le
    linarith
  have h0 : 0 ≤ b + K' * β := add_nonneg hb (mul_nonneg hK'.le hβ0)
  have h2 : t ≤ δ * (1 / (0.35 * K')) * (b' + K' * t) :=
    h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hs hδ) h1 h0
      (mul_nonneg hδ (by positivity)))
  refine ⟨h0.trans h1, ?_⟩
  rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h2
  linarith

/-- The last step of the barrier: from `t ≤ δ s (b + K' β)` with `s ≤ 1 / (0.35 K')`,
`β ≤ t + η` and `b + K' η ≤ b'` to `min {0.175, 0.175 K' t / b'} ≤ δ`. -/
theorem barrier_of_le {t δ s b β η b' K' : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hK' : 0 < K')
    (hb : 0 ≤ b) (hβ0 : 0 ≤ β) (hb' : 0 < b') (hs : s ≤ 1 / (0.35 * K')) (hβ : β ≤ t + η)
    (hbb : b + K' * η ≤ b') (h : t ≤ δ * s * (b + K' * β)) :
    min 0.175 (0.175 * K' * t / b') ≤ δ := by
  obtain ⟨-, h3⟩ := run_bound_of_le hδ hK' hb hβ0 hs hβ hbb h
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  obtain ⟨ha, hc⟩ := hlt
  rw [lt_div_iff₀ hb'] at hc
  have h4 : δ * (K' * t) ≤ 0.175 * (K' * t) :=
    mul_le_mul_of_nonneg_right ha.le (mul_nonneg hK'.le ht)
  linarith

/-- The step and the system are not trivial over a horizon that passes `1/2`: `H ≥ 0`, `a ≥ 0`
and `(K + 1) H a > 1/2` give `H > 0` and `a > 0`. -/
theorem pos_of_half_lt_horizon {H a : ℝ} {K : ℕ} (hH : 0 ≤ H) (ha : 0 ≤ a)
    (hK1 : 1 / 2 < (K + 1) * H * a) : 0 < H ∧ 0 < a := by
  refine ⟨lt_of_le_of_ne hH fun h => ?_, lt_of_le_of_ne ha fun h => ?_⟩ <;>
    (rw [← h] at hK1; norm_num at hK1)

/-- `2 l x ≤ 1` with `l ≥ 1` and `x ≥ 0` gives `x ≤ 1/2`. -/
theorem le_half_of_two_mul_le {x : ℝ} {l : ℕ} (hl : 1 ≤ l) (hx0 : 0 ≤ x)
    (hlx : 2 * l * x ≤ 1) : x ≤ 1 / 2 := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have := mul_le_mul_of_nonneg_right hl1 hx0
  linarith

/-- A run over a horizon that passes `1/2` is longer than its starting values: `2 l H a ≤ 1`
and `(K + 1) H a > 1/2` give `l ≤ K`. -/
theorem le_of_half_lt_horizon {H a : ℝ} {l K : ℕ} (hx0 : 0 ≤ H * a)
    (hlx : 2 * l * (H * a) ≤ 1) (hK1 : 1 / 2 < (K + 1) * H * a) : l ≤ K := by
  by_contra h
  have h1 : (K : ℝ) + 1 ≤ l := by exact_mod_cast not_le.1 h
  have h2 : ((K : ℝ) + 1) * (H * a) ≤ l * (H * a) := mul_le_mul_of_nonneg_right h1 hx0
  linarith

/-- The length `K'` of a run is not negative: `x > 0`, `2 l x ≤ 1` and `(1 - 2 l x) / 2 ≤ K' x`
give `K' ≥ 0`. -/
theorem run_length_nonneg_of_le {x Kp lr : ℝ} (hx : 0 < x) (hlx : 2 * lr * x ≤ 1)
    (hKp : (1 - 2 * lr * x) / 2 ≤ Kp * x) : 0 ≤ Kp := by
  by_contra h
  have := mul_neg_of_neg_of_pos (not_le.1 h) hx
  linarith

end Real

section RelativeError

variable {E : Type*} [NormedAddCommGroup E] {K : ℕ} {e : E → ℕ → E}

/-- A bound `δ` of the relative errors `‖e_k‖ / ‖x_0‖` of the runs of all initial states
`x_0 ≠ 0` of a space `E ≠ 0` is not negative. -/
theorem relative_error_bound_nonneg [Nontrivial E] {δ : ℝ}
    (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖e x0 k‖ ≤ δ * ‖x0‖) : 0 ≤ δ := by
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have h := (norm_nonneg _).trans (hδ y hy 0 (Nat.zero_le _))
  exact nonneg_of_mul_nonneg_left h (norm_pos_iff.2 hy)

/-- The least upper bound of the relative errors `‖e_k‖ / ‖x_0‖` over the initial states
`x_0 ≠ 0` and the steps `k ≤ K` bounds the error of every run: `‖e_k‖ ≤ ε ‖x_0‖`. -/
theorem relative_error_le_of_isLUB {ε : ℝ}
    (hε : IsLUB {r : ℝ | ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K, r = ‖e x0 k‖ / ‖x0‖} ε) :
    ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖e x0 k‖ ≤ ε * ‖x0‖ := by
  intro x0 hx0 k hk
  have h := hε.1 ⟨x0, hx0, k, hk, rfl⟩
  rwa [div_le_iff₀ (norm_pos_iff.2 hx0)] at h

/-- **From every bound to a single run:** if every bound `δ` of the relative errors of the runs
is at least `b`, then for every `c < b` there are an initial state `x_0 ≠ 0` and a step `k ≤ K`
at which the relative error exceeds `c`. -/
theorem exists_relative_error_gt {b c : ℝ}
    (hb : ∀ δ, (∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖e x0 k‖ ≤ δ * ‖x0‖) → b ≤ δ) (hc : c < b) :
    ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K, c * ‖x0‖ < ‖e x0 k‖ := by
  by_contra hne
  refine absurd (hb c fun x0 hx0 k hk => ?_) (not_le.2 hc)
  by_contra hlt
  exact hne ⟨x0, hx0, k, hk, not_le.1 hlt⟩

end RelativeError

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The powers of the inverse of the reference step stay near one, relative to the length
`K'` of a run with `K' H ‖A‖ ≤ 1/2`: `K' ‖Ui^r - 1‖ ≤ (r/2) e^{r H ‖A‖}`. -/
theorem mul_norm_exp_neg_pow_sub_one_le (A : 𝔸) {H : ℝ} (hH : 0 ≤ H) {K' : ℝ} (hK' : 0 ≤ K')
    (hKH : K' * (H * ‖A‖) ≤ 1 / 2) (r : ℕ) :
    K' * ‖exp (-(H • A)) ^ r - 1‖ ≤ (r : ℝ) / 2 * Real.exp (r * (H * ‖A‖)) := by
  have hx : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have h1 : ‖exp (-(H • A)) ^ r - 1‖ ≤ Real.exp (r * (H * ‖A‖)) - 1 := by
    have h := norm_exp_smul_pow_sub_one_le (-A) hH r
    rwa [smul_neg, norm_neg] at h
  have h2 := exp_sub_one_le_mul_exp (r * (H * ‖A‖))
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h3 : K' * ((r : ℝ) * (H * ‖A‖) * Real.exp (r * (H * ‖A‖))) ≤
      (r : ℝ) / 2 * Real.exp (r * (H * ‖A‖)) := by
    have h := mul_le_mul_of_nonneg_right hKH (mul_nonneg hr (Real.exp_pos (r * (H * ‖A‖))).le)
    linarith
  exact (mul_le_mul_of_nonneg_left (h1.trans h2) hK').trans h3

/-- The local defect is bounded by the errors of a linear starting procedure: if `S'` is a right
inverse of `Σ_{k=l-1}^{K-1} U^k` and `‖X k - U^k‖ ≤ δ` for `k ≤ K`, then
`‖T‖ ≤ δ ‖S'‖ (2 ‖1 - N‖ + 2 Σ_r r ‖M r‖ + (K - l + 1) ‖B‖)`. -/
theorem norm_runDefect_le_of_linear_runs (A N : 𝔸) (M : ℕ → 𝔸) {H : ℝ} {l K : ℕ} (hl : 1 ≤ l)
    (hK : l ≤ K) (X : ℕ → 𝔸)
    (hX : ∀ k, l - 1 ≤ k → k < K → (1 - N) * X (k + 1) = ∑ r ∈ range l, M r * X (k - r))
    {δ : ℝ} (hδ : ∀ k ≤ K, ‖X k - exp (H • A) ^ k‖ ≤ δ) {S' : 𝔸}
    (hS : (∑ k ∈ Ico (l - 1) K, exp (H • A) ^ k) * S' = 1) :
    ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤
      δ * ‖S'‖ * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖) := by
  have hx : ∀ k, l - 1 ≤ k → k < K →
      (1 - N) • (X (k + 1) * S') = ∑ r ∈ range l, M r • (X (k - r) * S') := by
    intro k hk hkK
    simp only [smul_eq_mul, ← mul_assoc]
    rw [hX k hk hkK, sum_mul]
  have hd : ∀ k ≤ K, ‖X k * S' - exp (H • A) ^ k • S' • (1 : 𝔸)‖ ≤ δ * ‖S'‖ := by
    intro k hk
    rw [smul_eq_mul, smul_eq_mul, mul_one, ← sub_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hδ k hk) (norm_nonneg _))
  have h := norm_runDefect_smul_le_of_run (exp_neg_mul_exp (H • A)) hl hK hS (1 : 𝔸)
    (fun k => X k * S') hx hd
  rwa [smul_eq_mul, mul_one] at h

variable [NormOneClass 𝔸]

/-- Over a horizon `K H ‖A‖ ≤ 1/2` the sum `Σ_{k=l-1}^{K-1} U^k` of the powers of the reference
step has a right inverse of norm at most `1 / ((2 - e^{1/2}) (K - l + 1))`. -/
theorem exists_sum_Ico_pow_right_inverse (A : 𝔸) {H : ℝ} (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l)
    (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) :
    ∃ S' : 𝔸, (∑ k ∈ Ico (l - 1) K, exp (H • A) ^ k) * S' = 1 ∧
      ‖S'‖ ≤ 1 / ((2 - Real.exp (1 / 2)) * ((K : ℝ) - l + 1)) := by
  have h := exists_sum_right_inverse (nonempty_Ico.2 (by omega : l - 1 < K))
    (fun k => exp (H • A) ^ k)
    fun k hk => norm_exp_smul_pow_sub_one_le_half A hH hKH (mem_Ico.1 hk).2.le
  rwa [Nat.card_Ico, cast_run_length hl hK] at h

/-- The constant of the barrier: with `‖N‖ ≤ ν` and `‖M r‖ ≤ m̄` for `1 ≤ r < l`,
`b + K' η ≤ 2.65 (1 + ν) + m̄ l (l - 1) (1 + ¼ e^{(l-1) H ‖A‖})`, where
`b = 2 ‖1 - N‖ + 2 Σ_r r ‖M r‖`, `η = ‖1 - N‖ ‖U - 1‖ + Σ_r ‖M r‖ ‖Ui^r - 1‖`, `K' = K - l + 1`. -/
theorem run_constant_le (A N : 𝔸) (M : ℕ → 𝔸) {H : ℝ} (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l)
    (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {ν mbar : ℝ} (hN : ‖N‖ ≤ ν)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) :
    2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * (‖1 - N‖ * ‖exp (H • A) - 1‖ +
          ∑ r ∈ range l, ‖M r‖ * ‖exp (-(H • A)) ^ r - 1‖) ≤
      2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hK'0 : (0 : ℝ) ≤ (K : ℝ) - l + 1 := (run_length_pos hK).le
  have hx : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hKx : (K : ℝ) * (H * ‖A‖) ≤ 1 / 2 := by rw [← mul_assoc]; exact hKH
  have hK'x : ((K : ℝ) - l + 1) * (H * ‖A‖) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) hx).trans hKx
  have he := exp_half_lt
  -- (c1)
  have c1 : ‖1 - N‖ ≤ 1 + ν := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have c1' : 0 ≤ 1 + ν := (norm_nonneg _).trans c1
  -- (c2)
  have c2 : ((K : ℝ) - l + 1) * ‖exp (H • A) - 1‖ ≤ 0.65 :=
    (mul_norm_exp_smul_sub_one_le A hH hKH hK'0 (by linarith)).trans (by linarith)
  -- (c4)
  have c4 : ∑ r ∈ range l, (r : ℝ) * ‖M r‖ ≤ mbar * ((l : ℝ) * (l - 1)) / 2 := by
    have h : ∑ r ∈ range l, (r : ℝ) * ‖M r‖ ≤ ∑ r ∈ range l, (r : ℝ) * mbar := by
      refine sum_le_sum fun r hr => ?_
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp
      · exact mul_le_mul_of_nonneg_left (hM r hr0 (mem_range.1 hr)) (Nat.cast_nonneg r)
    rw [← sum_mul, sum_range_cast_id] at h
    linarith
  -- (c5)
  have c5 : ((K : ℝ) - l + 1) * ∑ r ∈ range l, ‖M r‖ * ‖exp (-(H • A)) ^ r - 1‖ ≤
      mbar * ((l : ℝ) * (l - 1)) / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) := by
    have h : ∀ r ∈ range l, ((K : ℝ) - l + 1) * (‖M r‖ * ‖exp (-(H • A)) ^ r - 1‖) ≤
        (r : ℝ) * (mbar / 2 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) := by
      intro r hr
      have hr' := mem_range.1 hr
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp
      · have hm := hM r hr0 hr'
        have hm0 : 0 ≤ mbar := (norm_nonneg _).trans hm
        have h1 := mul_norm_exp_neg_pow_sub_one_le A hH hK'0 hK'x r
        have hrl : (r : ℝ) ≤ (l : ℝ) - 1 := by
          have : (r : ℝ) + 1 ≤ l := by exact_mod_cast hr'
          linarith
        have h2 : Real.exp (r * (H * ‖A‖)) ≤ Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hrl hx)
        have h3 : ((K : ℝ) - l + 1) * ‖exp (-(H • A)) ^ r - 1‖ ≤
            (r : ℝ) / 2 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        calc ((K : ℝ) - l + 1) * (‖M r‖ * ‖exp (-(H • A)) ^ r - 1‖)
            = ‖M r‖ * (((K : ℝ) - l + 1) * ‖exp (-(H • A)) ^ r - 1‖) := by ring
          _ ≤ mbar * ((r : ℝ) / 2 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) :=
              mul_le_mul hm h3 (mul_nonneg hK'0 (norm_nonneg _)) hm0
          _ = (r : ℝ) * (mbar / 2 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) := by ring
    have h' := sum_le_sum h
    rw [← mul_sum, ← sum_mul, sum_range_cast_id] at h'
    linarith
  have c6 : ((K : ℝ) - l + 1) * (‖1 - N‖ * ‖exp (H • A) - 1‖) ≤ (1 + ν) * 0.65 := by
    calc ((K : ℝ) - l + 1) * (‖1 - N‖ * ‖exp (H • A) - 1‖)
        = ‖1 - N‖ * (((K : ℝ) - l + 1) * ‖exp (H • A) - 1‖) := by ring
      _ ≤ (1 + ν) * 0.65 := mul_le_mul c1 c2 (mul_nonneg hK'0 (norm_nonneg _)) c1'
  rw [mul_add]
  linarith

/-- The barrier from a bound on the local defect: the common last step of the two forms. -/
theorem run_barrier_of_defect_le (A N : 𝔸) (M : ℕ → 𝔸) {H : ℝ} (hH : 0 ≤ H) {l K : ℕ}
    (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {ν mbar : ℝ} (hN : ‖N‖ ≤ ν)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) {δ : ℝ} (hδ : 0 ≤ δ) {S' : 𝔸}
    (hS' : ‖S'‖ ≤ 1 / ((2 - Real.exp (1 / 2)) * ((K : ℝ) - l + 1)))
    (h : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤
      δ * ‖S'‖ * (2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ +
        ((K : ℝ) - l + 1) * ‖runBalance N M l‖)) :
    min 0.175 (0.175 * ((K : ℝ) - l + 1) *
        ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ /
      (2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))))) ≤ δ := by
  have hK' := run_length_pos hK
  have hconst := run_constant_le A N M hH hl hK hKH hN hM
  have hb : 0 ≤ 2 * ‖1 - N‖ + 2 * ∑ r ∈ range l, (r : ℝ) * ‖M r‖ := by positivity
  have hη : 0 ≤ ‖1 - N‖ * ‖exp (H • A) - 1‖ +
      ∑ r ∈ range l, ‖M r‖ * ‖exp (-(H • A)) ^ r - 1‖ := by positivity
  have hb'0 : 0 ≤ 2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
      (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) :=
    (add_nonneg hb (mul_nonneg hK'.le hη)).trans hconst
  rcases hb'0.eq_or_lt with hb' | hb'
  · rw [← hb', div_zero]
    exact (min_le_right _ _).trans hδ
  exact barrier_of_le (norm_nonneg _) hδ hK' hb (norm_nonneg _) hb'
    (le_one_div_of_le_one_div_exp_half hK' hS')
    ((norm_runBalance_le N M (exp (H • A)) (exp (-(H • A))) l).trans_eq (add_assoc _ _ _))
    hconst h

/-- **Theorem 4.11 (order over a run), inequality `eq:runorder`, for a linear starting
procedure**, in a Banach algebra with `‖1‖ = 1`: let `X k` be the map from the initial state to
the state after `k` steps, `(1 - N) X (k+1) = Σ_{r<l} M r X (k-r)` for `l - 1 ≤ k < K`, with
arbitrary `X 0, …, X (l-1)`. If `1 ≤ l ≤ K`, `K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ ν`, `‖M r‖ ≤ m̄` for
`1 ≤ r < l`, and `‖X k - U^k‖ ≤ δ` for all `k ≤ K`, then
`δ ≥ min {0.175, 0.175 (K-l+1) ‖T‖ / (2.65 (1+ν) + m̄ l (l-1) (1 + ¼ e^{(l-1) H ‖A‖}))}` with
`T = (1 - N) U - Σ_{r<l} M r U^{-r}`. -/
theorem run_order_barrier_linear (A N : 𝔸) (M : ℕ → 𝔸) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {ν mbar : ℝ}
    (hN : ‖N‖ ≤ ν) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (X : ℕ → 𝔸)
    (hX : ∀ k, l - 1 ≤ k → k < K → (1 - N) * X (k + 1) = ∑ r ∈ range l, M r * X (k - r))
    {δ : ℝ} (hδ : ∀ k ≤ K, ‖X k - exp (H • A) ^ k‖ ≤ δ) :
    min 0.175 (0.175 * ((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ /
      (2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))))) ≤ δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (Nat.zero_le _))
  obtain ⟨S', hS, hS'⟩ := exists_sum_Ico_pow_right_inverse A hH hl hK hKH
  exact run_barrier_of_defect_le A N M hH hl hK hKH hN hM hδ0 hS'
    (norm_runDefect_le_of_linear_runs A N M hl hK X hX hδ hS)

end Algebra

section Operator

/-- **A bound of an operator through a right inverse:** if `S S' = 1`, `δ, b ≥ 0` and
`‖T v‖ ≤ δ ‖S' v‖ b` for every `v` with `S' v ≠ 0`, then `‖T‖ ≤ δ ‖S'‖ b`. -/
theorem opNorm_le_of_right_inverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S S' : E →L[ℝ] E} (hS : S * S' = 1)
    (T : E →L[ℝ] F) {δ b : ℝ} (hδ0 : 0 ≤ δ) (hb : 0 ≤ b)
    (h : ∀ v, S' v ≠ 0 → ‖T v‖ ≤ δ * ‖S' v‖ * b) : ‖T‖ ≤ δ * ‖S'‖ * b := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hδ0 (norm_nonneg _)) hb)
    fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hx0 : S' v ≠ 0 := by
    intro h0
    have h1 : S (S' v) = v := by rw [← mul_apply_eq_comp, hS, one_apply_eq_self]
    rw [h0, map_zero] at h1
    exact hv h1.symm
  refine (h v hx0).trans ?_
  have h3 : δ * ‖S' v‖ ≤ δ * ‖S'‖ * ‖v‖ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (S'.le_opNorm v) hδ0
  calc δ * ‖S' v‖ * b ≤ δ * ‖S'‖ * ‖v‖ * b := mul_le_mul_of_nonneg_right h3 hb
    _ = δ * ‖S'‖ * b * ‖v‖ := by ring

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
  exact opNorm_le_of_right_inverse hS _ hδ0 (run_factor_nonneg _ M _ hK) fun v hx0 =>
    norm_runDefect_smul_le_of_run (V := E) (exp_neg_mul_exp (H • A)) hl hK hS v
      (x (S' v)) (hx (S' v) hx0) (hδ (S' v) hx0)

/-- **Theorem 4.11 (order over a run), inequality `eq:runorder`.** Operators on a real Banach
space `E ≠ 0`. A starting procedure assigns to every initial state `x_0 ≠ 0` a run `x x_0 k`,
`k ≤ K`, with arbitrary starting values and `(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` for
`l - 1 ≤ k < K`; it need not be linear. Let `1 ≤ l ≤ K`, `K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ ν` and
`‖M r‖ ≤ m̄` for `1 ≤ r < l`. If `δ` bounds the relative error of all runs,
`‖x^k - U^k x_0‖ ≤ δ ‖x_0‖` for all `x_0 ≠ 0` and `k ≤ K` (`U = exp (H • A)`), then
`δ ≥ min {0.175, 0.175 (K-l+1) ‖T‖ / (2.65 (1+ν) + m̄ l (l-1) (1 + ¼ e^{(l-1) H ‖A‖}))}` with
`T = (1 - N) U - Σ_{r<l} M r U^{-r}`. This is the paper's statement with the largest relative
error `ε_K` replaced by any upper bound `δ` of the relative errors. -/
theorem run_order_barrier (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {ν mbar : ℝ}
    (hN : ‖N‖ ≤ ν) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    min 0.175 (0.175 * ((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ /
      (2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))))) ≤ δ := by
  have hδ0 := relative_error_bound_nonneg hδ
  obtain ⟨S', hS, hS'⟩ := exists_sum_Ico_pow_right_inverse A hH hl hK hKH
  exact run_barrier_of_defect_le A N M hH hl hK hKH hN hM hδ0 hS'
    (norm_runDefect_le_of_runs A N M hl hK x hx hδ0 hδ hS)

/-- **Theorem 4.11, inequality `eq:runorder`, as a statement about the largest relative error:**
for every `c` below the right-hand side there are an initial state `x_0 ≠ 0` and a step `k ≤ K`
at which the relative error of the run exceeds `c`. -/
theorem exists_run_order_barrier (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {ν mbar : ℝ}
    (hN : ‖N‖ ≤ ν) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {c : ℝ} (hc : c < min 0.175 (0.175 * ((K : ℝ) - l + 1) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ /
      (2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖)))))) :
    ∃ x0, x0 ≠ 0 ∧ ∃ k ≤ K, c * ‖x0‖ < ‖x x0 k - (exp (H • A) ^ k) x0‖ :=
  exists_relative_error_gt
    (fun _ hδ => run_order_barrier A N M hH hl hK hKH hN hM x hx hδ) hc

end Operator

end CoSimFoundations
