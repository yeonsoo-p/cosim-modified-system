/-
The order barrier as one statement (the paper): a scheme with `l` held samples has,
over an interval of the length `1/(2‖A‖)`, a relative
error of at least `0.35 λ H^l / (5.3 ‖A‖) (1 - O(H))`, for every rule of the subsystem and in
every order of execution, where the shown maps are independent.

**Setting.** That of `LeadingValueScheme` and `BoundedCoefficients` for one subsystem `i`:
`P : E → F` the projection onto its states (`‖P‖ ≤ 1`), the coupling row
`P ∘ A = Ai ∘ P + Σ_{j ∈ J} L j ∘ C j` over its partners `j ∈ J` with outputs `C j`, the samples
of partner `j` at the nodes `σ_j - q`, `q < l` (`schemeNodes`, `σ_j = 0` if the samples of `j`
are old, `σ_j = 1` if its newest sample is that of the new instant; `σ_j ≤ 1`), and a bounded
right inverse `R` of the stack `N₀` of `P` and of the maps `C j A^p`, `p < l` (`stackedDeriv`;
independence). A rule of the subsystem is a coefficient `Fi` on its own state and coefficients
`G (j, q)` on the samples; row `i` of the scheme is

  `P x^{k+1} = Fi P x^k + Σ_{j, q} G (j, q) C j x^{k + σ_j - q}`,   `l - 1 ≤ k < K`.

**Statement** (`order_barrier_all`, `order_barrier_all_floor`; `order_barrier_all_scheme` for
the partners and stages of `VisibilityConverse`). Let `0 < H ≤ 1`, `H ‖Ai‖ ≤ 1`,
`c₁ H ‖R‖ ≤ 1/2` (`c₁ = kernelConst`), `l ≥ 1`, and let `K` be the number of steps of the interval
`1/(2‖A‖)` (`K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`, or `K = ⌊1/(2 H ‖A‖)⌋`). For every rule `(Fi, G)`
and every family of sequences that satisfy row `i`, every `δ` that bounds the relative errors
`‖x^k - U^k x_0‖ / ‖x_0‖`, `k ≤ K`, satisfies

  `δ ≥ 0.35 (λ H^l - κ H^{l+1}) / (5.3 ‖A‖)`,
  `λ = ‖Σ_j γ_l^{σ_j} L j C j A^l | 𝒱^0‖`   (`orderBarrierLead`, the norm of
                                              `leading_value_nodes`),
  `κ = c₄ + λ (2 l ‖A‖ + (c₃ (1 + λ) + λ / (2 ‖A‖)) / 2.65)`   (`orderBarrierRem`),
  `c₄ = c₂ + 4 ‖R‖ c₁ ‖D‖`   (`orderBarrierDefect`, the remainder of `leading_value_nodes`),
  `c₃ = (Σ_{j,q} K_{jq}) (2.65 + 1.42 l (l - 1))`   (`orderBarrierCoef`, `K_{jq} = coefConst`,
                                                     the constants of `norm_coeff_comp_le`).

The constant `5.3 = 2 · 2.65` of the paper comes out.

**Proof.** (0) The row of the rule is a row `(P - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` with
`N = Σ_{q < σ_j} G (j, q) C j` (`ruleNew`) and
`M r = [r = 0] Fi P + Σ_{q = r + σ_j} G (j, q) C j` (`ruleOld`; `row_of_rule`), and its local
defect `rowDefect` is the local defect `𝒯 = ruleDefect` of the rule (`rowDefect_rule`). The own
coefficient `Fi` sits in `M 0`, which `run_order_row` does not bound.
(1) `run_order_row`: `δ ≥ 0.35 K' t / (b + K' t)`, `t = ‖𝒯‖`, `K' = K - l + 1`,
`b = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`.
(2) `norm_coeff_comp_le_scheme` bounds `‖G (j, q) ∘ C j‖ ≤ K_{jq} (H + t / H^{l-1})`; these are
the norms that enter `‖N‖` and `‖M r‖`, `r ≥ 1` (`norm_ruleNew_le`, `norm_ruleOld_le`: sums of
the `G (j, q) ∘ C j`, no further factor), so that `b = 2.65 + c₃ H + c₃ t / H^{l-1}`.
(3) `t ↦ K' t / (β + γ t + K' t)` increases (`run_fraction_mono`), and
`t ≥ f ≥ λ H^{l+1} - c₄ H^{l+2}` (`visBound_le_norm_rule`, `leading_value_nodes`).
(4) With `K' H ‖A‖ ∈ [(1 - 2 l H ‖A‖)/2, 1/2]` the denominator is at most
`2.65 + (c₃ (1 + λ) + λ/(2‖A‖)) H` and the numerator at least
`(1 - 2 l H ‖A‖)(λ H^l - c₄ H^{l+1}) / (2 ‖A‖)` (`barrier_all_arith`).

No smallness beyond the hypotheses of the three cited theorems is assumed: where
`2 l H ‖A‖ > 1` the right-hand side is not positive.
-/
import CoSimFoundations.RunOrderRow
import CoSimFoundations.BoundedCoefficients

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Real

/-- The bound over a run increases with the local defect, also when the constant `b` grows with
it: for `β, γ, K' ≥ 0` and `0 ≤ τ ≤ t`,
`K' τ / (β + γ τ + K' τ) ≤ K' t / (β + γ t + K' t)`. -/
theorem run_fraction_mono {t τ β γ Kp : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hK : 0 ≤ Kp)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ t) :
    Kp * τ / (β + γ * τ + Kp * τ) ≤ Kp * t / (β + γ * t + Kp * t) := by
  have ht0 : 0 ≤ t := hτ0.trans hτ
  have hD1 : 0 ≤ β + γ * τ + Kp * τ := by positivity
  have hD2 : β + γ * τ + Kp * τ ≤ β + γ * t + Kp * t := by
    nlinarith [mul_le_mul_of_nonneg_left hτ hγ, mul_le_mul_of_nonneg_left hτ hK]
  rcases hD1.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact div_nonneg (mul_nonneg hK ht0) (hD1.trans hD2)
  · rw [div_le_div_iff₀ hpos (hpos.trans_le hD2)]
    nlinarith [mul_le_mul_of_nonneg_left hτ (mul_nonneg hK hβ)]

/-- The numerator of the barrier is at most `λ H^l (1 - 2 l H a)`. -/
theorem barrier_numerator_le {lam c4 rest Hl H a lr : ℝ} (hlam : 0 ≤ lam) (hc4 : 0 ≤ c4)
    (hrest : 0 ≤ rest) (hHl0 : 0 ≤ Hl) (hH : 0 ≤ H) :
    lam * Hl - (c4 + lam * (2 * lr * a + rest)) * (Hl * H) ≤
      lam * Hl * (1 - 2 * lr * (H * a)) := by
  have h1 := mul_nonneg hc4 (mul_nonneg hHl0 hH)
  have h2 := mul_nonneg (mul_nonneg hlam hrest) (mul_nonneg hHl0 hH)
  nlinarith [h1, h2]

/-- `H · H^l / H^{l-1} = H²` for `l ≥ 1`. -/
theorem inv_pow_pred_mul {H : ℝ} (hH : 0 < H) {l : ℕ} (hl : 1 ≤ l) :
    (H ^ (l - 1))⁻¹ * (H * H ^ l) = H * H := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hm : H ^ m ≠ 0 := (pow_pos hH m).ne'
  rw [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- **The arithmetic of the order barrier.** From the bound over a run at the lower bound
`τ = H (λ H^l - c₄ H^{l+1})` of the local defect (`hbar`; `i` stands for `1 / H^{l-1}`, `Hl` for
`H^l`, `a` for `‖A‖`, `lr` for `l`, `Kp` for `K - l + 1`) and the length of the run (`hKp`,
`hKp2`) to `δ ≥ 0.35 (λ H^l - κ H^{l+1}) / (5.3 a)`,
`κ = c₄ + λ (2 l a + (c₃ (1 + λ) + λ / (2 a)) / 2.65)`. -/
theorem barrier_all_arith {lam c4 c3 H Hl a lr Kp i δ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1)
    (ha : 0 < a) (hlr : 1 ≤ lr) (hlam : 0 ≤ lam) (hc4 : 0 ≤ c4) (hc3 : 0 ≤ c3)
    (hHl0 : 0 ≤ Hl) (hHl : Hl ≤ H) (hi : 0 ≤ i) (hiH : i * (H * Hl) ≤ H * H)
    (hKp : (1 - 2 * lr * (H * a)) / 2 ≤ Kp * (H * a)) (hKp2 : Kp * (H * a) ≤ 1 / 2)
    (hδ0 : 0 ≤ δ)
    (hbar : 0.35 * (Kp * (H * (lam * Hl - c4 * (Hl * H)))) /
      (2.65 + c3 * H + c3 * i * (H * (lam * Hl - c4 * (Hl * H))) +
        Kp * (H * (lam * Hl - c4 * (Hl * H)))) ≤ δ) :
    0.35 * (lam * Hl -
        (c4 + lam * (2 * lr * a + (c3 * (1 + lam) + lam / (2 * a)) / 2.65)) * (Hl * H)) /
      (5.3 * a) ≤ δ := by
  have hx : 0 < H * a := mul_pos hH ha
  have hd : 0 < 5.3 * a := by positivity
  have hlr0 : 0 ≤ lr := by linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = lam / (2 * a) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    rw [he]
    positivity
  have hea : a * e = lam / 2 := by
    rw [he]
    field_simp
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = lam * Hl - c4 * (Hl * H) := ⟨_, rfl⟩
  rw [← hY] at hbar
  rw [← he]
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (c3 * (1 + lam) + e) * H := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by
    rw [hε]
    positivity
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 * lr * (H * a) + ε / 2.65 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hnum : lam * Hl - (c4 + lam * (2 * lr * a + (c3 * (1 + lam) + e) / 2.65)) * (Hl * H) =
      Y - lam * Hl * u := by
    rw [hY, hu, hε]
    ring
  rw [hnum]
  rcases le_or_gt (Y - lam * Hl * u) 0 with hQ | hQ
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hQ) hd.le).trans hδ0
  have hlH : 0 ≤ lam * Hl := mul_nonneg hlam hHl0
  have hYle : Y ≤ lam * Hl := by
    rw [hY]
    linarith [mul_nonneg hc4 (mul_nonneg hHl0 hH.le)]
  have hY0 : 0 < Y := by linarith [mul_nonneg hlH hu0]
  have hQY : Y - lam * Hl * u ≤ Y - Y * u := by
    linarith [mul_le_mul_of_nonneg_right hYle hu0]
  have h1u : 0 < 1 - u := by
    by_contra h
    have h1 : Y * (1 - u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hY0.le (not_lt.1 h)
    linarith
  have hlx : 2 * lr * (H * a) ≤ 1 := by
    have h1 : 0 ≤ ε / 2.65 := by positivity
    rw [hu] at h1u
    linarith
  have hKp0 := run_length_nonneg_of_le hx hlx hKp
  have han : a * (Kp * (H * Y)) = Kp * (H * a) * Y := by ring
  have hn_lo : 2.65 * (1 - 2 * lr * (H * a)) * Y ≤ 5.3 * a * (Kp * (H * Y)) := by
    have h1 := mul_le_mul_of_nonneg_right hKp hY0.le
    linarith
  have hn_hi : Kp * (H * Y) ≤ e * Hl := by
    have h1 : Kp * (H * a) * Y ≤ 1 / 2 * Y := mul_le_mul_of_nonneg_right hKp2 hY0.le
    have h3 : a * (e * Hl) = lam / 2 * Hl := by rw [← mul_assoc, hea]
    have h2 : a * (Kp * (H * Y)) ≤ a * (e * Hl) := by
      rw [han, h3]
      linarith
    exact le_of_mul_le_mul_left h2 ha
  have hiτ : c3 * i * (H * Y) ≤ c3 * lam * H := by
    have h1 : i * (H * Y) ≤ i * (H * (lam * Hl)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYle hH.le) hi
    have h2 : i * (H * (lam * Hl)) = lam * (i * (H * Hl)) := by ring
    have h3 : lam * (i * (H * Hl)) ≤ lam * (H * H) := mul_le_mul_of_nonneg_left hiH hlam
    have h4 : lam * (H * H) ≤ lam * H := by
      nlinarith [mul_nonneg (mul_nonneg hlam hH.le) (sub_nonneg.2 hH1)]
    have h5 : i * (H * Y) ≤ lam * H := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 hc3
    linarith
  have hD : 2.65 + c3 * H + c3 * i * (H * Y) + Kp * (H * Y) ≤ 2.65 + ε := by
    have h1 : e * Hl ≤ e * H := mul_le_mul_of_nonneg_left hHl he0
    rw [hε]
    linarith
  have hDpos : 0 < 2.65 + c3 * H + c3 * i * (H * Y) + Kp * (H * Y) := by positivity
  have hkey : (Y - Y * u) * (2.65 + ε) ≤ 2.65 * (1 - 2 * lr * (H * a)) * Y := by
    have h2 : 0 ≤ Y * u * ε := by positivity
    have h1 : (Y - Y * u) * (2.65 + ε) = 2.65 * (1 - 2 * lr * (H * a)) * Y - Y * u * ε := by
      rw [hu]
      ring
    linarith
  have hmain : (Y - lam * Hl * u) * (2.65 + c3 * H + c3 * i * (H * Y) + Kp * (H * Y)) ≤
      5.3 * a * (Kp * (H * Y)) :=
    calc (Y - lam * Hl * u) * (2.65 + c3 * H + c3 * i * (H * Y) + Kp * (H * Y))
        ≤ (Y - lam * Hl * u) * (2.65 + ε) := mul_le_mul_of_nonneg_left hD hQ.le
      _ ≤ (Y - Y * u) * (2.65 + ε) := mul_le_mul_of_nonneg_right hQY (by linarith)
      _ ≤ 2.65 * (1 - 2 * lr * (H * a)) * Y := hkey
      _ ≤ 5.3 * a * (Kp * (H * Y)) := hn_lo
  refine le_trans ?_ hbar
  rw [div_le_div_iff₀ hd hDpos]
  linarith

end Real

section Rule

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {J : Type*} [Fintype J] {Y : J → Type*} [∀ j, NormedAddCommGroup (Y j)]
  [∀ j, NormedSpace ℝ (Y j)] [∀ j, CompleteSpace (Y j)] {l : ℕ}

/-! ### The row of a rule -/

/-- The coefficients of the new samples in the row of a rule: the sample `(j, q)` is at the
instant `t_{k + σ_j - q}`, which is the new instant `t_{k+1}` for `q < σ_j`. -/
noncomputable def ruleNew (σ : J → ℕ) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F)
    (C : ∀ j, E →L[ℝ] Y j) : E →L[ℝ] F :=
  ∑ k : J × Fin l, if (k.2 : ℕ) < σ k.1 then G k ∘L C k.1 else 0

/-- The coefficients of the state of the age `r` in the row of a rule: the own state for `r = 0`
and the samples `(j, q)` with `q = r + σ_j`. -/
noncomputable def ruleOld (σ : J → ℕ) (P : E →L[ℝ] F) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (r : ℕ) : E →L[ℝ] F :=
  (if r = 0 then Fi ∘L P else 0) +
    ∑ k : J × Fin l, if (k.2 : ℕ) = r + σ k.1 then G k ∘L C k.1 else 0

/-- The coefficients of the new samples on a state. -/
theorem ruleNew_apply (σ : J → ℕ) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (v : E) :
    ruleNew σ G C v = ∑ k : J × Fin l, if (k.2 : ℕ) < σ k.1 then G k (C k.1 v) else 0 := by
  unfold ruleNew
  rw [_root_.sum_apply]
  refine sum_congr rfl fun k _ => ?_
  by_cases h : (k.2 : ℕ) < σ k.1
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- The coefficients of the state of the age `r` on a state. -/
theorem ruleOld_apply (σ : J → ℕ) (P : E →L[ℝ] F) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (r : ℕ) (v : E) :
    ruleOld σ P Fi G C r v = (if r = 0 then Fi (P v) else 0) +
      ∑ k : J × Fin l, if (k.2 : ℕ) = r + σ k.1 then G k (C k.1 v) else 0 := by
  unfold ruleOld
  rw [_root_.add_apply, _root_.sum_apply]
  have h1 : (if r = 0 then Fi ∘L P else 0) v = if r = 0 then Fi (P v) else 0 := by
    by_cases h : r = 0
    · rw [ite_eq_left h, ite_eq_left h]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
      rfl
  rw [h1]
  refine congrArg _ (sum_congr rfl fun k _ => ?_)
  by_cases h : (k.2 : ℕ) = r + σ k.1
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- **The row of a rule, sample by sample.** If `w (j, q)` is the state at the instant of the
sample `(j, q)`: `top` for `q < σ_j` and `past (q - σ_j)` otherwise, then
`N top + Σ_{r<l} M r (past r) = Fi P (past 0) + Σ_{j,q} G (j, q) C j (w (j, q))`. -/
theorem ruleNew_add_sum_ruleOld (σ : J → ℕ) (P : E →L[ℝ] F) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (hl : 1 ≤ l) (top : E)
    (past : ℕ → E) (w : J × Fin l → E)
    (hnew : ∀ k : J × Fin l, (k.2 : ℕ) < σ k.1 → w k = top)
    (hold : ∀ k : J × Fin l, σ k.1 ≤ (k.2 : ℕ) → w k = past ((k.2 : ℕ) - σ k.1)) :
    ruleNew σ G C top + ∑ r ∈ range l, ruleOld σ P Fi G C r (past r) =
      Fi (P (past 0)) + ∑ k : J × Fin l, G k (C k.1 (w k)) := by
  have h1 : ∑ r ∈ range l, (if r = 0 then Fi (P (past r)) else 0) = Fi (P (past 0)) := by
    rw [Finset.sum_ite_eq' (range l) 0 fun r => Fi (P (past r)),
      ite_eq_left (mem_range.2 (by omega : 0 < l))]
  have h2 : ∀ k : J × Fin l,
      ∑ r ∈ range l, (if (k.2 : ℕ) = r + σ k.1 then G k (C k.1 (past r)) else 0) =
        if σ k.1 ≤ (k.2 : ℕ) then G k (C k.1 (past ((k.2 : ℕ) - σ k.1))) else 0 := by
    intro k
    have hk := k.2.2
    by_cases h : σ k.1 ≤ (k.2 : ℕ)
    · have e : (k.2 : ℕ) = (k.2 : ℕ) - σ k.1 + σ k.1 := by omega
      rw [ite_eq_left h, Finset.sum_eq_single ((k.2 : ℕ) - σ k.1), ite_eq_left e]
      · intro r _ hr
        have e' : ¬ (k.2 : ℕ) = r + σ k.1 := by omega
        rw [ite_eq_right e']
      · intro hnot
        exact absurd (mem_range.2 (by omega)) hnot
    · rw [ite_eq_right h]
      refine sum_eq_zero fun r _ => ?_
      have e' : ¬ (k.2 : ℕ) = r + σ k.1 := by omega
      rw [ite_eq_right e']
  simp only [ruleNew_apply, ruleOld_apply]
  rw [sum_add_distrib, h1, sum_comm, sum_congr rfl fun k _ => h2 k, add_left_comm,
    ← sum_add_distrib]
  refine congrArg _ (sum_congr rfl fun k _ => ?_)
  by_cases h : (k.2 : ℕ) < σ k.1
  · have h' : ¬ σ k.1 ≤ (k.2 : ℕ) := by omega
    rw [ite_eq_left h, ite_eq_right h', add_zero, hnew k h]
  · have h' : σ k.1 ≤ (k.2 : ℕ) := by omega
    rw [ite_eq_right h, ite_eq_left h', zero_add, hold k h']

/-- **The local defect of the row of a rule is the local defect of the rule:** for the nodes
`σ_j - q` with `σ_j ≤ 1`, `(P - N) U - Σ_{r<l} M r U^{-r} = P U - Fi P - Σ_{j,q} G (j,q) C j
U^{σ_j - q}`. -/
theorem rowDefect_rule (σ : J → ℕ) (hσ : ∀ j, σ j ≤ 1) (hl : 1 ≤ l) (P : E →L[ℝ] F)
    (Fi : F →L[ℝ] F) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (A : E →L[ℝ] E) (H : ℝ) :
    rowDefect P (ruleNew σ G C) (ruleOld σ P Fi G C) (exp (H • A)) (exp (-(H • A))) l =
      ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l := by
  ext v
  have hUU := exp_mul_exp_neg (H • A)
  have hnew : ∀ k : J × Fin l, (k.2 : ℕ) < σ k.1 →
      (exp (H • A) ^ σ k.1 * exp (-(H • A)) ^ (k.2 : ℕ)) v = exp (H • A) v := by
    intro k h
    have h1 : σ k.1 = 1 := by have := hσ k.1; omega
    have h0 : (k.2 : ℕ) = 0 := by omega
    rw [h1, h0, pow_one, pow_zero, mul_one]
  have hold : ∀ k : J × Fin l, σ k.1 ≤ (k.2 : ℕ) →
      (exp (H • A) ^ σ k.1 * exp (-(H • A)) ^ (k.2 : ℕ)) v =
        (exp (-(H • A)) ^ ((k.2 : ℕ) - σ k.1)) v := by
    intro k h
    rw [inv_pow_mul_pow (U := exp (-(H • A))) (Ui := exp (H • A)) hUU h]
  have hbk := ruleNew_add_sum_ruleOld σ P Fi G C hl (exp (H • A) v)
    (fun r => (exp (-(H • A)) ^ r) v)
    (fun k => (exp (H • A) ^ σ k.1 * exp (-(H • A)) ^ (k.2 : ℕ)) v) hnew hold
  have hns : ∀ k : J × Fin l, nodeSample C A H (fun j => schemeNodes (σ j) l) k v =
      C k.1 ((exp (H • A) ^ σ k.1 * exp (-(H • A)) ^ (k.2 : ℕ)) v) := fun k =>
    congrArg (fun T : E →L[ℝ] Y k.1 => T v) (nodeSample_scheme C A H σ k.1 k.2)
  have hR : ruleDefect P Fi G C A H (fun j => schemeNodes (σ j) l) v =
      P (exp (H • A) v) - Fi (P v) -
        ∑ k : J × Fin l, G k (C k.1 ((exp (H • A) ^ σ k.1 * exp (-(H • A)) ^ (k.2 : ℕ)) v)) := by
    unfold ruleDefect
    simp only [_root_.sub_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply, hns]
  rw [rowDefect_apply, _root_.sub_apply, sub_sub, hbk, hR, pow_zero, one_apply_eq_self, sub_sub]

/-- **Row `i` of the scheme as a row of the recursion:** a sequence with
`P x^{k+1} = Fi P x^k + Σ_{j,q} G (j,q) C j x^{k + σ_j - q}` satisfies
`(P - N) x^{k+1} = Σ_{r<l} M r x^{k-r}`, for `σ_j ≤ 1` (natural subtraction in the indices). -/
theorem row_of_rule (σ : J → ℕ) (hσ : ∀ j, σ j ≤ 1) (hl : 1 ≤ l) (P : E →L[ℝ] F)
    (Fi : F →L[ℝ] F) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (k : ℕ)
    (x : ℕ → E)
    (hx : P (x (k + 1)) = Fi (P (x k)) +
      ∑ k' : J × Fin l, G k' (C k'.1 (x (k + σ k'.1 - (k'.2 : ℕ))))) :
    (P - ruleNew σ G C) (x (k + 1)) = ∑ r ∈ range l, ruleOld σ P Fi G C r (x (k - r)) := by
  have hnew : ∀ k' : J × Fin l, (k'.2 : ℕ) < σ k'.1 →
      x (k + σ k'.1 - (k'.2 : ℕ)) = x (k + 1) := by
    intro k' h
    have := hσ k'.1
    exact congrArg x (by omega)
  have hold : ∀ k' : J × Fin l, σ k'.1 ≤ (k'.2 : ℕ) →
      x (k + σ k'.1 - (k'.2 : ℕ)) = x (k - ((k'.2 : ℕ) - σ k'.1)) := by
    intro k' h
    exact congrArg x (by omega)
  have hbk := ruleNew_add_sum_ruleOld σ P Fi G C hl (x (k + 1)) (fun r => x (k - r))
    (fun k' => x (k + σ k'.1 - (k'.2 : ℕ))) hnew hold
  rw [_root_.sub_apply, sub_eq_iff_eq_add', hbk, Nat.sub_zero]
  exact hx

/-- The coefficients of the new samples are bounded by the sum of the `‖G (j, q) ∘ C j‖`. -/
theorem norm_ruleNew_le (σ : J → ℕ) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F)
    (C : ∀ j, E →L[ℝ] Y j) : ‖ruleNew σ G C‖ ≤ ∑ k : J × Fin l, ‖G k ∘L C k.1‖ := by
  unfold ruleNew
  refine norm_sum_le_of_le _ fun k _ => ?_
  by_cases h : (k.2 : ℕ) < σ k.1
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, norm_zero]
    exact norm_nonneg _

/-- The coefficients of the state of an age `r ≥ 1` are bounded by the sum of the
`‖G (j, q) ∘ C j‖`: the own coefficient `Fi` enters for `r = 0` only. -/
theorem norm_ruleOld_le (σ : J → ℕ) (P : E →L[ℝ] F) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) {r : ℕ} (hr : 1 ≤ r) :
    ‖ruleOld σ P Fi G C r‖ ≤ ∑ k : J × Fin l, ‖G k ∘L C k.1‖ := by
  have hr0 : ¬ r = 0 := by omega
  unfold ruleOld
  rw [ite_eq_right hr0, zero_add]
  refine norm_sum_le_of_le _ fun k _ => ?_
  by_cases h : (k.2 : ℕ) = r + σ k.1
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, norm_zero]
    exact norm_nonneg _

/-! ### The constants -/

/-- `λ = ‖Σ_j γ_l^{σ_j} L j C j A^l | 𝒱^0‖`: the leading value of the visibility bound divided by
`H^{l+1}` (`leading_value_nodes` for the nodes `σ_j - q`). -/
noncomputable def orderBarrierLead (P : E →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) (A : E →L[ℝ] E) (σ : J → ℕ) (l : ℕ) : ℝ :=
  restrNorm (leadingMap L C A (fun j => schemeGamma (σ j) l) l)
    (unseen P (ContinuousLinearMap.pi C) A l)

/-- `c₄ = c₂ + 4 ρ c₁ ‖D‖`: the remainder of `leading_value_nodes` for the nodes `σ_j - q`, `ρ`
the norm of the right inverse. -/
noncomputable def orderBarrierDefect (A : E →L[ℝ] E) (Ai : F →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) (σ : J → ℕ) (l : ℕ) (ρ : ℝ) : ℝ :=
  defectConst A Ai C L (fun j => schemeNodes (σ j) l) (fun j => schemeWeights (σ j) l) +
    4 * ρ * kernelConst A C (fun j => schemeNodes (σ j) l) (fun j => schemeWeights (σ j) l) *
      ‖leadingMap L C A (fun j => schemeGamma (σ j) l) l‖

/-- `c₃ = (Σ_{j,q} K_{jq}) (2.65 + 1.42 l (l - 1))`, `K_{jq} = coefConst`: the constant `b` of
the bound over a run is at most `2.65 + c₃ (H + ‖𝒯‖ / H^{l-1})`. -/
noncomputable def orderBarrierCoef (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) (σ : J → ℕ) (l : ℕ) (ρ : ℝ) : ℝ :=
  (∑ k : J × Fin l, coefConst A C L (fun j => schemeNodes (σ j) l)
    (fun j => schemeWeights (σ j) l) ρ k.1 k.2) * (2.65 + 1.42 * ((l : ℝ) * (l - 1)))

/-- `κ = c₄ + λ (2 l ‖A‖ + (c₃ (1 + λ) + λ / (2 ‖A‖)) / 2.65)`: the remainder of the order
barrier. -/
noncomputable def orderBarrierRem (P : E →L[ℝ] F) (A : E →L[ℝ] E) (Ai : F →L[ℝ] F)
    (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F) (σ : J → ℕ) (l : ℕ) (ρ : ℝ) : ℝ :=
  orderBarrierDefect A Ai C L σ l ρ + orderBarrierLead P C L A σ l *
    (2 * (l : ℝ) * ‖A‖ + (orderBarrierCoef A C L σ l ρ * (1 + orderBarrierLead P C L A σ l) +
      orderBarrierLead P C L A σ l / (2 * ‖A‖)) / 2.65)

/-- The constant of the bound of a coefficient is not negative. -/
theorem coefConst_nonneg_of_nonneg (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (j : J) (q : Fin l) : 0 ≤ coefConst A C L x W ρ j q := by
  have h1 := coefBase_nonneg A C L x W
  unfold coefConst
  exact mul_nonneg (norm_nonneg _) (sum_nonneg fun p _ => by positivity)

/-- `c₃ ≥ 0`. -/
theorem orderBarrierCoef_nonneg (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (σ : J → ℕ) {l : ℕ} (hl : 1 ≤ l) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ≤ orderBarrierCoef A C L σ l ρ := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : 0 ≤ (l : ℝ) * (l - 1) := mul_nonneg (by linarith) (by linarith)
  unfold orderBarrierCoef
  exact mul_nonneg (sum_nonneg fun k _ => coefConst_nonneg_of_nonneg A C L _ _ hρ k.1 k.2)
    (by linarith)

/-- `c₄ ≥ 0`. -/
theorem orderBarrierDefect_nonneg (A : E →L[ℝ] E) (Ai : F →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) (σ : J → ℕ) (l : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ≤ orderBarrierDefect A Ai C L σ l ρ := by
  have h1 := defectConst_nonneg A Ai C L (fun j => schemeNodes (σ j) l)
    (fun j => schemeWeights (σ j) l)
  have h2 := kernelConst_nonneg A C (fun j => schemeNodes (σ j) l)
    (fun j => schemeWeights (σ j) l)
  unfold orderBarrierDefect
  positivity

/-! ### The order barrier -/

variable {P : E →L[ℝ] F} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {C : ∀ j, E →L[ℝ] Y j}
  {L : ∀ j, Y j →L[ℝ] F}

/-- **The order barrier, as one statement**. Subsystem `i`: projection `P`,
`‖P‖ ≤ 1`, coupling row `P ∘ A = Ai ∘ P + Σ_j L j ∘ C j`, the samples of partner `j` at the nodes
`σ_j - q`, `q < l`, `σ_j ≤ 1`, and a right inverse `R` of the stack of `P` and of the maps
`C j A^p`, `p < l`. Let `0 < H ≤ 1`, `H ‖Ai‖ ≤ 1`, `c₁ H ‖R‖ ≤ 1/2`, `l ≥ 1`, and
`K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`. For every rule `(Fi, G)` and every family of sequences `x x_0`
(`x_0 ≠ 0`) that satisfy row `i` of the scheme,
`P x^{k+1} = Fi P x^k + Σ_{j,q} G (j,q) C j x^{k + σ_j - q}` for `l - 1 ≤ k < K`, every `δ` with
`‖x^k - U^k x_0‖ ≤ δ ‖x_0‖` for all `x_0 ≠ 0`, `k ≤ K` (`U = exp (H • A)`) satisfies
`δ ≥ 0.35 (λ H^l - κ H^{l+1}) / (5.3 ‖A‖)`, `λ = orderBarrierLead`, `κ = orderBarrierRem`. -/
theorem order_barrier_all (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (σ : J → ℕ) (hσ : ∀ j, σ j ≤ 1) {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C (fun j => schemeNodes (σ j) l) (fun j => schemeWeights (σ j) l) *
      H * ‖R‖ ≤ 1 / 2) (hl : 1 ≤ l) {K : ℕ} (hKH : K * H * ‖A‖ ≤ 1 / 2)
    (hK1 : 1 / 2 < (K + 1) * H * ‖A‖) (Fi : F →L[ℝ] F) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F)
    (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      P (x x0 (k + 1)) = Fi (P (x x0 k)) +
        ∑ k' : J × Fin l, G k' (C k'.1 (x x0 (k + σ k'.1 - (k'.2 : ℕ)))))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (orderBarrierLead P C L A σ l * H ^ l -
        orderBarrierRem P A Ai C L σ l ‖R‖ * H ^ (l + 1)) / (5.3 * ‖A‖) ≤ δ := by
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH.le hA0
  have hApos : 0 < ‖A‖ := (pos_of_half_lt_horizon hH.le hA0 hK1).2
  have : Nontrivial E := by
    by_contra hne
    rw [not_nontrivial_iff_subsingleton] at hne
    have h0 : A = 0 := Subsingleton.elim _ _
    rw [h0, norm_zero] at hApos
    exact lt_irrefl _ hApos
  have hδ0 := relative_error_bound_nonneg hδ
  have hρ : 0 ≤ ‖R‖ := norm_nonneg R
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlam0 : 0 ≤ orderBarrierLead P C L A σ l := restrNorm_nonneg _ _
  have hc40 := orderBarrierDefect_nonneg A Ai C L σ l hρ
  have hc30 := orderBarrierCoef_nonneg A C L σ hl hρ
  have hHl0 : 0 ≤ H ^ l := pow_nonneg hH.le l
  have hd : 0 < 5.3 * ‖A‖ := by positivity
  have hrest : 0 ≤ (orderBarrierCoef A C L σ l ‖R‖ * (1 + orderBarrierLead P C L A σ l) +
      orderBarrierLead P C L A σ l / (2 * ‖A‖)) / 2.65 :=
    div_nonneg (add_nonneg (mul_nonneg hc30 (by linarith))
      (div_nonneg hlam0 (by positivity))) (by norm_num)
  unfold orderBarrierRem
  rw [pow_succ H l]
  rcases le_or_gt (orderBarrierLead P C L A σ l * H ^ l -
      (orderBarrierDefect A Ai C L σ l ‖R‖ + orderBarrierLead P C L A σ l *
        (2 * (l : ℝ) * ‖A‖ + (orderBarrierCoef A C L σ l ‖R‖ *
          (1 + orderBarrierLead P C L A σ l) +
          orderBarrierLead P C L A σ l / (2 * ‖A‖)) / 2.65)) * (H ^ l * H)) 0 with hQ | hQ
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hQ) hd.le).trans hδ0
  -- where the bound is positive, the run is longer than the starting values
  have hnum := barrier_numerator_le (lr := (l : ℝ)) (a := ‖A‖) hlam0 hc40 hrest hHl0 hH.le
  have hlx : 2 * (l : ℝ) * (H * ‖A‖) ≤ 1 := by
    by_contra h
    have h2 : orderBarrierLead P C L A σ l * H ^ l * (1 - 2 * (l : ℝ) * (H * ‖A‖)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hlam0 hHl0) (by linarith [not_le.1 h])
    linarith
  have hx1 : H * ‖A‖ ≤ 1 := (le_half_of_two_mul_le hl hx0 hlx).trans (by norm_num)
  have hK : l ≤ K := le_of_half_lt_horizon hx0 hlx hK1
  have hlK : (l : ℝ) ≤ K := by exact_mod_cast hK
  -- (0) the row of the rule and its local defect
  have hdef := rowDefect_rule σ hσ hl P Fi G C A H
  -- (2) the coefficients
  have hcoef : ∀ k : J × Fin l, ‖G k ∘L C k.1‖ ≤
      coefConst A C L (fun j => schemeNodes (σ j) l) (fun j => schemeWeights (σ j) l) ‖R‖
        k.1 k.2 * (H + ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ / H ^ (l - 1)) :=
    fun k => norm_coeff_comp_le_scheme hA hP σ hR hH hH1 hx1 hHAi hsmall Fi G k.1 k.2
  have hsum : ∑ k : J × Fin l, ‖G k ∘L C k.1‖ ≤
      (∑ k : J × Fin l, coefConst A C L (fun j => schemeNodes (σ j) l)
        (fun j => schemeWeights (σ j) l) ‖R‖ k.1 k.2) *
        (H + ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ / H ^ (l - 1)) := by
    rw [sum_mul]
    exact sum_le_sum fun k _ => hcoef k
  have hN := (norm_ruleNew_le σ G C).trans hsum
  have hM : ∀ r, 1 ≤ r → r < l → ‖ruleOld σ P Fi G C r‖ ≤
      (∑ k : J × Fin l, coefConst A C L (fun j => schemeNodes (σ j) l)
        (fun j => schemeWeights (σ j) l) ‖R‖ k.1 k.2) *
        (H + ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ / H ^ (l - 1)) :=
    fun r h1 _ => (norm_ruleOld_le σ P Fi G C h1).trans hsum
  -- (1) the bound over a run for the row
  have hbar := run_order_row A P (ruleNew σ G C) (ruleOld σ P Fi G C) hH.le hl hK hKH hP hN hM
    x (fun x0 hx0' k hk hkK => row_of_rule σ hσ hl P Fi G C k (x x0) (hx x0 hx0' k hk hkK)) hδ
  rw [hdef] at hbar
  -- (3) the local defect is at least the leading value
  have hf := visBound_le_norm_rule P (exp (H • A))
    (nodeSample C A H fun j => schemeNodes (σ j) l) Fi G
  have hlead : -(orderBarrierDefect A Ai C L σ l ‖R‖ * H ^ (l + 2)) ≤
      visBound P (exp (H • A)) (nodeSample C A H fun j => schemeNodes (σ j) l) -
        H ^ (l + 1) * orderBarrierLead P C L A σ l :=
    (abs_le.1 (leading_value_nodes hA hP (x := fun j => schemeNodes (σ j) l)
      (W := fun j => schemeWeights (σ j) l) (fun j => schemeWeights_mul (σ j) l) hR hH hx1 hHAi
      hsmall)).1
  have e1 : H ^ (l + 1) = H ^ l * H := pow_succ H l
  have e2 : H ^ (l + 2) = H ^ l * H * H := by rw [pow_succ, pow_succ]
  rw [e1, e2] at hlead
  have hτ : H * (orderBarrierLead P C L A σ l * H ^ l -
      orderBarrierDefect A Ai C L σ l ‖R‖ * (H ^ l * H)) ≤
      ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ := by
    have hf' : visBound P (exp (H • A)) (nodeSample C A H fun j => schemeNodes (σ j) l) ≤
        ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ := hf
    linarith
  have hY0 : 0 ≤ orderBarrierLead P C L A σ l * H ^ l -
      orderBarrierDefect A Ai C L σ l ‖R‖ * (H ^ l * H) := by
    have h0 : (0 : ℝ) ≤ 2 * (l : ℝ) * ‖A‖ := mul_nonneg (by linarith) hA0
    have h1 := mul_nonneg (mul_nonneg hlam0 (add_nonneg h0 hrest)) (mul_nonneg hHl0 hH.le)
    linarith
  have hτ0 : 0 ≤ H * (orderBarrierLead P C L A σ l * H ^ l -
      orderBarrierDefect A Ai C L σ l ‖R‖ * (H ^ l * H)) := mul_nonneg hH.le hY0
  -- the monotone step
  have hi : 0 ≤ (H ^ (l - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hH.le _)
  have hKp0 : (0 : ℝ) ≤ (K : ℝ) - l + 1 := by linarith
  have hmono := run_fraction_mono (β := 2.65 + orderBarrierCoef A C L σ l ‖R‖ * H)
    (γ := orderBarrierCoef A C L σ l ‖R‖ * (H ^ (l - 1))⁻¹) (Kp := (K : ℝ) - l + 1)
    (add_nonneg (by norm_num) (mul_nonneg hc30 hH.le)) (mul_nonneg hc30 hi) hKp0 hτ0 hτ
  have hden : 2.65 * (1 + (∑ k : J × Fin l, coefConst A C L (fun j => schemeNodes (σ j) l)
        (fun j => schemeWeights (σ j) l) ‖R‖ k.1 k.2) *
        (H + ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ / H ^ (l - 1))) +
      1.42 * ((∑ k : J × Fin l, coefConst A C L (fun j => schemeNodes (σ j) l)
        (fun j => schemeWeights (σ j) l) ‖R‖ k.1 k.2) *
        (H + ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ / H ^ (l - 1))) *
        ((l : ℝ) * (l - 1)) +
      ((K : ℝ) - l + 1) * ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ =
      2.65 + orderBarrierCoef A C L σ l ‖R‖ * H +
        orderBarrierCoef A C L σ l ‖R‖ * (H ^ (l - 1))⁻¹ *
          ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ +
        ((K : ℝ) - l + 1) * ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ := by
    unfold orderBarrierCoef
    rw [div_eq_mul_inv]
    ring
  rw [hden, mul_div_assoc] at hbar
  have hbar2 : 0.35 * (((K : ℝ) - l + 1) * (H * (orderBarrierLead P C L A σ l * H ^ l -
        orderBarrierDefect A Ai C L σ l ‖R‖ * (H ^ l * H)))) /
      (2.65 + orderBarrierCoef A C L σ l ‖R‖ * H +
        orderBarrierCoef A C L σ l ‖R‖ * (H ^ (l - 1))⁻¹ *
          (H * (orderBarrierLead P C L A σ l * H ^ l -
            orderBarrierDefect A Ai C L σ l ‖R‖ * (H ^ l * H))) +
        ((K : ℝ) - l + 1) * (H * (orderBarrierLead P C L A σ l * H ^ l -
          orderBarrierDefect A Ai C L σ l ‖R‖ * (H ^ l * H)))) ≤ δ := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hmono (by norm_num)).trans hbar
  -- (4) the arithmetic
  have hHl : H ^ l ≤ H := pow_le_of_le_one hH.le hH1 (by omega)
  have hKp : (1 - 2 * (l : ℝ) * (H * ‖A‖)) / 2 ≤ ((K : ℝ) - l + 1) * (H * ‖A‖) := by linarith
  have hKp2 : ((K : ℝ) - l + 1) * (H * ‖A‖) ≤ 1 / 2 := by
    have := mul_nonneg (sub_nonneg.2 hl1) hx0
    linarith
  exact barrier_all_arith hH hH1 hApos hl1 hlam0 hc40 hc30 hHl0 hHl hi
    (inv_pow_pred_mul hH hl).le hKp hKp2 hδ0 hbar2

/-- **The order barrier over the interval `1/(2‖A‖)`:** `order_barrier_all` for
`K = ⌊1/(2 H ‖A‖)⌋`, `A ≠ 0`. -/
theorem order_barrier_all_floor (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (σ : J → ℕ) (hσ : ∀ j, σ j ≤ 1) {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hA0 : A ≠ 0) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C (fun j => schemeNodes (σ j) l) (fun j => schemeWeights (σ j) l) *
      H * ‖R‖ ≤ 1 / 2) (hl : 1 ≤ l) (Fi : F →L[ℝ] F) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F)
    (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < ⌊1 / (2 * H * ‖A‖)⌋₊ →
      P (x x0 (k + 1)) = Fi (P (x x0 k)) +
        ∑ k' : J × Fin l, G k' (C k'.1 (x x0 (k + σ k'.1 - (k'.2 : ℕ)))))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊1 / (2 * H * ‖A‖)⌋₊,
      ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (orderBarrierLead P C L A σ l * H ^ l -
        orderBarrierRem P A Ai C L σ l ‖R‖ * H ^ (l + 1)) / (5.3 * ‖A‖) ≤ δ := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.2 hA0
  have hy : 0 < 2 * H * ‖A‖ := by positivity
  have h1 : ((⌊1 / (2 * H * ‖A‖)⌋₊ : ℕ) : ℝ) ≤ 1 / (2 * H * ‖A‖) :=
    Nat.floor_le (by positivity)
  have h2 : 1 / (2 * H * ‖A‖) < ((⌊1 / (2 * H * ‖A‖)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hy] at h1
  rw [div_lt_iff₀ hy] at h2
  exact order_barrier_all hA hP σ hσ hR hH hH1 hHAi hsmall hl (by linarith) (by linarith) Fi G
    x hx hδ

end Rule

section Scheme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, CompleteSpace (Es i)]
  {Yo : ι → Type*} [∀ j, NormedAddCommGroup (Yo j)] [∀ j, NormedSpace ℝ (Yo j)]
  [∀ j, CompleteSpace (Yo j)]

/-- **The order barrier for subsystem `i` of a scheme with `l` held samples, in every order of
execution** (setting of `leading_value_scheme` and `VisibilityConverse`): projections `Pr`,
outputs `c j ∘ Pr j`, stages `stage`, the partners `j ∈ 𝒫(i)` of `i` and
`σ_ij = newSample stage i j` (`1` if `j` runs at an earlier stage than `i`, else `0`). This is
`order_barrier_all` for `J = 𝒫(i)`: for every rule `(Fi, G)` of subsystem `i` and every family
of sequences with
`Pr i x^{k+1} = Fi (Pr i x^k) + Σ_{j ∈ 𝒫(i), q < l} G (j,q) (c j (Pr j x^{k + σ_ij - q}))`,
every bound `δ` of the relative errors over `k ≤ K` satisfies
`δ ≥ 0.35 (λ H^l - κ H^{l+1}) / (5.3 ‖A‖)`. -/
theorem order_barrier_all_scheme (Pr : ∀ i, E →L[ℝ] Es i) (c : ∀ j, Es j →L[ℝ] Yo j)
    (A : E →L[ℝ] E) (stage : ι → ℕ) (partner : ι → ι → Prop) [DecidableRel partner] {l : ℕ}
    (i : ι) (Ai : Es i →L[ℝ] Es i) (L : ∀ j : {j // partner i j}, Yo j →L[ℝ] Es i)
    (hA : Pr i ∘L A = Ai ∘L Pr i + ∑ j : {j // partner i j}, L j ∘L (c j ∘L Pr j))
    (hP : ‖Pr i‖ ≤ 1)
    {R : Es i × (∀ k : {j // partner i j} × Fin l, Yo k.1) →L[ℝ] E}
    (hR : stackedDeriv (Pr i) (fun j : {j // partner i j} => c j ∘L Pr j) A l ∘L R =
      ContinuousLinearMap.id ℝ (Es i × (∀ k : {j // partner i j} × Fin l, Yo k.1)))
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A (fun j : {j // partner i j} => c j ∘L Pr j)
      (fun j => schemeNodes (newSample stage i j) l)
      (fun j => schemeWeights (newSample stage i j) l) * H * ‖R‖ ≤ 1 / 2)
    (hl : 1 ≤ l) {K : ℕ} (hKH : K * H * ‖A‖ ≤ 1 / 2) (hK1 : 1 / 2 < (K + 1) * H * ‖A‖)
    (Fi : Es i →L[ℝ] Es i) (G : ∀ k : {j // partner i j} × Fin l, Yo k.1 →L[ℝ] Es i)
    (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      Pr i (x x0 (k + 1)) = Fi (Pr i (x x0 k)) +
        ∑ k' : {j // partner i j} × Fin l,
          G k' (c k'.1 (Pr k'.1 (x x0 (k + newSample stage i k'.1 - (k'.2 : ℕ))))))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (orderBarrierLead (Pr i) (fun j : {j // partner i j} => c j ∘L Pr j) L A
          (fun j => newSample stage i j) l * H ^ l -
        orderBarrierRem (Pr i) A Ai (fun j : {j // partner i j} => c j ∘L Pr j) L
          (fun j => newSample stage i j) l ‖R‖ * H ^ (l + 1)) / (5.3 * ‖A‖) ≤ δ := by
  have hσ : ∀ j : {j // partner i j}, newSample stage i j ≤ 1 := fun j => by
    unfold newSample
    split_ifs <;> omega
  exact order_barrier_all hA hP (fun j : {j // partner i j} => newSample stage i j) hσ hR hH hH1
    hHAi hsmall hl hKH hK1 Fi G x hx hδ

end Scheme

end CoSimFoundations
