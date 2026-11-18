/-
The least error over a run with `l` held samples from any linear start.

**Setting**, that of `LeastRunMemory` and `LeastRunMemoryReached`. A linear start
`x^q = U^q x_0 + H^l s_q x_0 + O(H^{l+1})`, `q < l`, with `‖s_q‖ ≤ s`, the start errors of the
slots at the order `H^l` and different from slot to slot.

**Accumulation from the last slot** (`run_accumulation_late`). If the slots `q < l - 1` are within
`σ₀ H^l` of the comparison run and the slot `l - 1` within `σ H^{l+1}`, the error is
`H^l ψ(kH) + O(H^{l+1})` for `l - 1 ≤ k ≤ K`: the older slots enter the next `l - 1` steps only
through the coefficients `M q = O(H)`, `q ≥ 1`, a forcing of the size `O(H^{l+1})` over at most
`2l - 2` steps (`sum_range_ite_lt_le`). The comparison start is `S = U^{-(l-1)} s_{l-1}`
(`start_slot_le`): `e^{(l-1)HA} S = s_{l-1}`.

**Every rule** (`least_memory_le_start`). For the Jacobi schemes with `l` old samples and bounded
weights, every start of this form gives relative errors at least `H^l g° - C H^{l+1}`,
`g° = min_{Z ∈ 𝒵_l, S} sup_{0≤t≤T} ‖e^{tA} S - Φ_t(D⁰ + Z)‖`, with `C`
independent of the rule, of the start and of `H`. The errors at the steps `k < l - 1` are not
used: the grid from `l - 1` on sees the supremum up to `l H` (`leadMax_le_of_grid`).
-/
import CoSimFoundations.LeastRunMemoryReached

open NormedSpace Finset

namespace CoSimFoundations

section Late

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `Σ_{j<k} [j < m] c ≤ m c` for `c ≥ 0`. -/
theorem sum_range_ite_lt_le (k m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ j ∈ range k, (if j < m then c else 0) ≤ m * c := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc
  have h : (range k).filter (· < m) ⊆ range m := fun j hj => mem_range.2 (mem_filter.1 hj).2
  have h2 := card_le_card h
  rw [card_range] at h2
  exact_mod_cast h2

/-- The constant of the accumulation from the last slot,
`(σ + 4 l² b σ₀ + 2 T₀ R₀ e^{T₀ α}) e^{2 (l+1) b T₀}`. -/
noncomputable def leadConstLate (α : ℝ) (l : ℕ) (b c₁ δ s σ σ₀ T₀ : ℝ) : ℝ :=
  (σ + 4 * (l : ℝ) ^ 2 * b * σ₀ + 2 * T₀ * leadRes α l b c₁ δ s T₀ * Real.exp (T₀ * α)) *
    Real.exp (2 * (l + 1) * b * T₀)

theorem leadConstLate_nonneg {α : ℝ} (l : ℕ) {b c₁ δ s σ σ₀ T₀ : ℝ} (hα : 0 ≤ α) (hb : 0 ≤ b)
    (hc₁ : 0 ≤ c₁) (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hσ : 0 ≤ σ) (hσ₀ : 0 ≤ σ₀) (hT₀ : 0 ≤ T₀) :
    0 ≤ leadConstLate α l b c₁ δ s σ σ₀ T₀ := by
  have := leadRes_nonneg l hα hb hc₁ hδ hs hT₀ (b := b)
  unfold leadConstLate
  positivity

/-- **Accumulation from the last start slot**. Under the hypotheses of
`run_accumulation`, but with the start slots `q < l - 1` only within `σ₀ H^l ‖x_0‖` of the
comparison run `U^q x_0 + H^l ψ(qH) x_0` and the slot `l - 1` within `σ H^{l+1} ‖x_0‖`: for every
`l - 1 ≤ k ≤ K`, `‖x^k - U^k x_0 - H^l ψ(kH) x_0‖ ≤ C H^{l+1} ‖x_0‖`, `C = leadConstLate`. -/
theorem run_accumulation_late (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) (D S : E →L[ℝ] E)
    {H b c₁ δ s σ σ₀ T₀ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hb : 0 ≤ b) (hbH : b * H ≤ 1 / 2)
    (hσ : 0 ≤ σ) (hσ₀ : 0 ≤ σ₀) {l K : ℕ} (hl : 1 ≤ l) (hKT : (K : ℝ) * H ≤ T₀)
    (hN : ‖N‖ ≤ b * H) (hM0 : ‖M 0 - 1‖ ≤ b * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (hT : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l - H ^ (l + 1) • D‖ ≤
      c₁ * H ^ (l + 2))
    (hD : ‖D‖ ≤ δ) (hS : ‖S‖ ≤ s) (x0 : E) (x : ℕ → E)
    (hstart0 : ∀ q < l - 1,
      ‖x q - (exp (H • A) ^ q) x0 - H ^ l • runLead A S D (q * H) x0‖ ≤ σ₀ * H ^ l * ‖x0‖)
    (hstart : ‖x (l - 1) - (exp (H • A) ^ (l - 1)) x0 -
      H ^ l • runLead A S D (((l - 1 : ℕ) : ℝ) * H) x0‖ ≤ σ * H ^ (l + 1) * ‖x0‖)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) (x (k + 1)) = ∑ q ∈ range l, M q (x (k - q))) :
    ∀ k, l - 1 ≤ k → k ≤ K →
      ‖x k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0‖ ≤
        leadConstLate ‖A‖ l b c₁ δ s σ σ₀ T₀ * H ^ (l + 1) * ‖x0‖ := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  set e : ℕ → E := fun k => x k - leadRun A S D H l k x0 with he
  have hek : ∀ k, e k = x k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0 := by
    intro k
    simp only [he, leadRun_eq, _root_.add_apply, _root_.smul_apply]
    abel
  have hrec : ∀ k, l - 1 ≤ k → k < K → (1 - N) (e (k + 1)) =
      ∑ q ∈ range l, M q (e (k - q)) + -(recResid N M l k (leadRun A S D H l) x0) := by
    intro k hk hkK
    have h := hx k hk hkK
    simp only [he, recResid, map_sub, _root_.sub_apply, mul_apply_eq_comp, _root_.sum_apply,
      sum_sub_distrib, one_apply_eq_self] at h ⊢
    linear_combination (norm := module) h
  -- the error with the older slots removed
  set e' : ℕ → E := fun k => if k < l - 1 then 0 else e k with he'
  have he'k : ∀ k, l - 1 ≤ k → e' k = e k := fun k hk => by
    simp only [he', ite_eq_right (not_lt.2 hk)]
  set extra : ℕ → E := fun k => ∑ q ∈ range l, M q (e (k - q) - e' (k - q)) with hextra
  have hrec' : ∀ k, l - 1 ≤ k → k < K → (1 - N) (e' (k + 1)) =
      ∑ q ∈ range l, M q (e' (k - q)) +
        (-(recResid N M l k (leadRun A S D H l) x0) + extra k) := by
    intro k hk hkK
    rw [he'k (k + 1) (by omega), hrec k hk hkK]
    simp only [hextra, map_sub, sum_sub_distrib]
    abel
  have hα0 := norm_nonneg A
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hD
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hS
  have hc₁ : 0 ≤ c₁ := by
    have h := (norm_nonneg _).trans hT
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hT₀ : 0 ≤ T₀ := le_trans (by positivity) hKT
  have hR0 := leadRes_nonneg l hα0 hb hc₁ hδ0 hs0 hT₀ (b := b)
  set ρ : ℝ := leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 2) * ‖x0‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set ρx : ℝ := l * b * σ₀ * H ^ (l + 1) * ‖x0‖ with hρx
  have hρx0 : 0 ≤ ρx := by positivity
  have hextra_le : ∀ k, l - 1 ≤ k → ‖extra k‖ ≤ if k < 2 * l - 2 then ρx else 0 := by
    intro k hk
    split_ifs with hk2
    · refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ q ∈ range l, ‖M q (e (k - q) - e' (k - q))‖ ≤
          b * H * (σ₀ * H ^ l * ‖x0‖) := by
        intro q hq
        have hql := mem_range.1 hq
        by_cases hkq : k - q < l - 1
        · have hq1 : 1 ≤ q := by omega
          have hdiff : e (k - q) - e' (k - q) = e (k - q) := by
            simp only [he', ite_eq_left hkq, sub_zero]
          rw [hdiff]
          refine ((M q).le_opNorm _).trans
            (mul_le_mul (hM q hq1 hql) ?_ (norm_nonneg _) (by positivity))
          rw [hek]
          exact hstart0 (k - q) hkq
        · have hdiff : e (k - q) - e' (k - q) = 0 := by
            simp only [he', ite_eq_right hkq, sub_self]
          rw [hdiff, map_zero, norm_zero]
          positivity
      refine (sum_le_sum hterm).trans (le_of_eq ?_)
      rw [sum_const, card_range, nsmul_eq_mul, hρx]
      ring
    · have hz : extra k = 0 := by
        refine sum_eq_zero fun q hq => ?_
        have hql := mem_range.1 hq
        have hkq : ¬ (k - q < l - 1) := by omega
        simp only [he', ite_eq_right hkq, sub_self, map_zero]
      rw [hz, norm_zero]
  set ρ' : ℕ → ℝ := fun k => ρ + (if k < 2 * l - 2 then ρx else 0) with hρ'
  have hρ'0 : ∀ k, 0 ≤ ρ' k := fun k => by
    simp only [hρ']
    split_ifs <;> positivity
  have hres : ∀ k, l - 1 ≤ k → k < K →
      ‖-(recResid N M l k (leadRun A S D H l) x0) + extra k‖ ≤ ρ' k := by
    intro k hk hkK
    have hkT : (k : ℝ) * H ≤ T₀ :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkK.le) hH.le) hKT
    have h2 := norm_recResid_leadRun_le h1 A S D N M hH hH1 hb hl hk hkT hN hM hT hD hS
    have h3 : ‖-(recResid N M l k (leadRun A S D H l) x0)‖ ≤ ρ := by
      rw [norm_neg]
      exact ((recResid N M l k (leadRun A S D H l)).le_opNorm x0).trans
        (mul_le_mul_of_nonneg_right h2 (norm_nonneg x0))
    exact (norm_add_le _ _).trans (add_le_add h3 (hextra_le k hk))
  have hstart' : ∀ k < l, ‖e' k‖ ≤ σ * H ^ (l + 1) * ‖x0‖ := by
    intro k hk
    by_cases hk1 : k < l - 1
    · simp only [he', ite_eq_left hk1, norm_zero]
      positivity
    · have hkl : k = l - 1 := by omega
      rw [he'k k (by omega), hek, hkl]
      exact hstart
  have hstab := run_stab_le N M hH.le hb hbH hl hN hM0 hM e' _ ρ' hstart' hρ'0 hres hrec'
  intro k hk hkK
  rw [← hek, ← he'k k hk]
  refine (hstab k hkK).trans ?_
  have hsum : ∑ j ∈ range k, ρ' j ≤ (k : ℝ) * ρ + 2 * l * ρx := by
    simp only [hρ', sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    have h2 := sum_range_ite_lt_le k (2 * l - 2) hρx0
    have h3 : ((2 * l - 2 : ℕ) : ℝ) ≤ 2 * l := by
      have : 2 * l - 2 ≤ 2 * l := Nat.sub_le _ _
      exact_mod_cast this
    have h4 : ((2 * l - 2 : ℕ) : ℝ) * ρx ≤ 2 * l * ρx := mul_le_mul_of_nonneg_right h3 hρx0
    linarith
  have hkT : (k : ℝ) * H ≤ T₀ :=
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkK) hH.le) hKT
  have hc := one_add_pow_le_exp_run hb hH.le l hkT
  have hkρ : (k : ℝ) * ρ ≤
      T₀ * leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 1) * ‖x0‖ := by
    have e2 : (k : ℝ) * ρ = ((k : ℝ) * H) *
        (leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 1) * ‖x0‖) := by
      rw [hρ]
      ring
    rw [e2]
    have : 0 ≤ leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 1) * ‖x0‖ := by
      positivity
    calc (k : ℝ) * H * (leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 1) * ‖x0‖)
        ≤ T₀ * (leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 1) * ‖x0‖) :=
          mul_le_mul_of_nonneg_right hkT this
      _ = _ := by ring
  have hbase : 0 ≤ σ * H ^ (l + 1) * ‖x0‖ + 2 * ∑ j ∈ range k, ρ' j :=
    add_nonneg (by positivity) (mul_nonneg zero_le_two (sum_nonneg fun j _ => hρ'0 j))
  have h5 : σ * H ^ (l + 1) * ‖x0‖ + 2 * ∑ j ∈ range k, ρ' j ≤
      (σ + 4 * (l : ℝ) ^ 2 * b * σ₀ +
        2 * T₀ * leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖)) * H ^ (l + 1) * ‖x0‖ := by
    have e3 : (σ + 4 * (l : ℝ) ^ 2 * b * σ₀ +
        2 * T₀ * leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖)) * H ^ (l + 1) * ‖x0‖ =
        σ * H ^ (l + 1) * ‖x0‖ + 2 * (2 * l * ρx) +
          2 * (T₀ * leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 1) * ‖x0‖) := by
      rw [hρx]
      ring
    rw [e3]
    linarith
  calc (σ * H ^ (l + 1) * ‖x0‖ + 2 * ∑ j ∈ range k, ρ' j) * (1 + 2 * (l + 1) * b * H) ^ k
      ≤ (σ * H ^ (l + 1) * ‖x0‖ + 2 * ∑ j ∈ range k, ρ' j) *
          Real.exp (2 * (l + 1) * b * T₀) := mul_le_mul_of_nonneg_left hc hbase
    _ ≤ (σ + 4 * (l : ℝ) ^ 2 * b * σ₀ +
          2 * T₀ * leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖)) * H ^ (l + 1) * ‖x0‖ *
          Real.exp (2 * (l + 1) * b * T₀) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = leadConstLate ‖A‖ l b c₁ δ s σ σ₀ T₀ * H ^ (l + 1) * ‖x0‖ := by
        unfold leadConstLate
        ring

/-- **A linear start and its comparison run** (only `s_{l-1}` persists). Let
`‖x^q - U^q x_0 - H^l s_q x_0‖ ≤ σ H^{l+1} ‖x_0‖` and `‖s_q‖ ≤ s₀` for `q < l`, `0 ≤ H ≤ 1`,
`‖D‖ ≤ δ`, and `S = U^{-(l-1)} s_{l-1}`. Then `‖S‖ ≤ e^{l‖A‖} s₀`, the slot `l - 1` is within
`(σ + l e^{l‖A‖} δ) H^{l+1} ‖x_0‖` of `U^{l-1} x_0 + H^l ψ((l-1)H) x_0`, and the slots `q < l - 1`
within `(σ + s₀ + e^{2l‖A‖} s₀ + l e^{l‖A‖} δ) H^l ‖x_0‖` of `U^q x_0 + H^l ψ(qH) x_0`. -/
theorem start_slot_le (A D : E →L[ℝ] E) (sq : ℕ → E →L[ℝ] E) {H δ σ s₀ : ℝ} (hH : 0 ≤ H)
    (hσ0 : 0 ≤ σ)
    (hH1 : H ≤ 1) (hD : ‖D‖ ≤ δ) {l : ℕ} (hl : 1 ≤ l) (hs : ∀ q < l, ‖sq q‖ ≤ s₀)
    (x0 : E) (y : ℕ → E)
    (hy : ∀ q < l, ‖y q - (exp (H • A) ^ q) x0 - H ^ l • sq q x0‖ ≤ σ * H ^ (l + 1) * ‖x0‖) :
    ‖exp (-(H • A)) ^ (l - 1) * sq (l - 1)‖ ≤ Real.exp (l * ‖A‖) * s₀ ∧
    ‖y (l - 1) - (exp (H • A) ^ (l - 1)) x0 -
        H ^ l • runLead A (exp (-(H • A)) ^ (l - 1) * sq (l - 1)) D (((l - 1 : ℕ) : ℝ) * H) x0‖ ≤
      (σ + l * Real.exp (l * ‖A‖) * δ) * H ^ (l + 1) * ‖x0‖ ∧
    ∀ q < l - 1,
      ‖y q - (exp (H • A) ^ q) x0 -
          H ^ l • runLead A (exp (-(H • A)) ^ (l - 1) * sq (l - 1)) D (q * H) x0‖ ≤
        (σ + s₀ + Real.exp (2 * l * ‖A‖) * s₀ + l * Real.exp (l * ‖A‖) * δ) * H ^ l * ‖x0‖ := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hα0 := norm_nonneg A
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hD
  have hs₀ : 0 ≤ s₀ := (norm_nonneg _).trans (hs 0 (by omega))
  set S := exp (-(H • A)) ^ (l - 1) * sq (l - 1) with hSdef
  have hEl : ∀ q : ℕ, q ≤ l → Real.exp (q * H * ‖A‖) ≤ Real.exp (l * ‖A‖) := by
    intro q hq
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hα0)
    have h2 : (q : ℝ) ≤ l := by exact_mod_cast hq
    calc (q : ℝ) * H ≤ q * 1 := mul_le_mul_of_nonneg_left hH1 (Nat.cast_nonneg q)
      _ ≤ l := by rw [mul_one]; exact h2
  have hSn : ‖S‖ ≤ Real.exp (l * ‖A‖) * s₀ :=
    (norm_mul_le _ _).trans (mul_le_mul ((norm_exp_neg_pow_le h1 A hH (l - 1)).trans
      (hEl _ (Nat.sub_le l 1))) (hs (l - 1) (by omega)) (norm_nonneg _) (by positivity))
  have hUS : exp (H • A) ^ (l - 1) * S = sq (l - 1) := by
    have hU : exp (H • A) * exp (-(H • A)) = 1 := exp_mul_exp_neg (H • A)
    rw [hSdef, ← mul_assoc, pow_mul_pow_eq_one (l - 1) hU, one_mul]
  refine ⟨hSn, ?_, fun q hq => ?_⟩
  · refine start_lead_le A S D hH hH1 hD (by omega : l - 1 < l) x0 (y (l - 1)) ?_
    rw [hUS]
    exact hy (l - 1) (by omega)
  · have hql : q < l := by omega
    have e : y q - (exp (H • A) ^ q) x0 - H ^ l • runLead A S D (q * H) x0 =
        (y q - (exp (H • A) ^ q) x0 - H ^ l • sq q x0) +
          H ^ l • (sq q x0 - (exp (H • A) ^ q * S) x0 + runPhi A D (q * H) x0) := by
      rw [runLead, exp_natCast_mul_smul, _root_.sub_apply, smul_add, smul_sub, smul_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have hUq : ‖exp (H • A) ^ q‖ ≤ Real.exp (l * ‖A‖) :=
      (norm_exp_pow_le h1 A hH q).trans (hEl q hql.le)
    have hq0 : 0 ≤ (q : ℝ) * H := by positivity
    have hΦ : ‖runPhi A D (q * H)‖ ≤ l * Real.exp (l * ‖A‖) * δ := by
      refine (norm_runPhi_le h1 A D hq0).trans ?_
      have h2 : (q : ℝ) * H ≤ l := by
        calc (q : ℝ) * H ≤ q * 1 := mul_le_mul_of_nonneg_left hH1 (Nat.cast_nonneg q)
          _ ≤ l := by rw [mul_one]; exact_mod_cast hql.le
      have h3 := hEl q hql.le
      gcongr
    have hUS' : ‖exp (H • A) ^ q * S‖ ≤ Real.exp (2 * l * ‖A‖) * s₀ := by
      have e2 : Real.exp (2 * l * ‖A‖) = Real.exp (l * ‖A‖) * Real.exp (l * ‖A‖) := by
        rw [← Real.exp_add]
        ring_nf
      rw [e2, mul_assoc]
      exact (norm_mul_le _ _).trans (mul_le_mul hUq hSn (norm_nonneg _) (by positivity))
    have hin : ‖sq q x0 - (exp (H • A) ^ q * S) x0 + runPhi A D (q * H) x0‖ ≤
        (s₀ + Real.exp (2 * l * ‖A‖) * s₀ + l * Real.exp (l * ‖A‖) * δ) * ‖x0‖ := by
      have h2 := ((sq q).le_opNorm x0).trans (mul_le_mul_of_nonneg_right (hs q hql)
        (norm_nonneg x0))
      have h3 := ((exp (H • A) ^ q * S).le_opNorm x0).trans
        (mul_le_mul_of_nonneg_right hUS' (norm_nonneg x0))
      have h4 := ((runPhi A D (q * H)).le_opNorm x0).trans
        (mul_le_mul_of_nonneg_right hΦ (norm_nonneg x0))
      have h5 := norm_add_le (sq q x0 - (exp (H • A) ^ q * S) x0) (runPhi A D (q * H) x0)
      have h6 := norm_sub_le (sq q x0) ((exp (H • A) ^ q * S) x0)
      have e3 : (s₀ + Real.exp (2 * l * ‖A‖) * s₀ + l * Real.exp (l * ‖A‖) * δ) * ‖x0‖ =
          s₀ * ‖x0‖ + Real.exp (2 * l * ‖A‖) * s₀ * ‖x0‖ +
            l * Real.exp (l * ‖A‖) * δ * ‖x0‖ := by ring
      rw [e3]
      linarith
    have hHl : 0 ≤ H ^ l := by positivity
    have h7 : ‖H ^ l • (sq q x0 - (exp (H • A) ^ q * S) x0 + runPhi A D (q * H) x0)‖ ≤
        (s₀ + Real.exp (2 * l * ‖A‖) * s₀ + l * Real.exp (l * ‖A‖) * δ) * H ^ l * ‖x0‖ := by
      rw [norm_smul, Real.norm_of_nonneg hHl]
      calc H ^ l * ‖sq q x0 - (exp (H • A) ^ q * S) x0 + runPhi A D (q * H) x0‖
          ≤ H ^ l * ((s₀ + Real.exp (2 * l * ‖A‖) * s₀ + l * Real.exp (l * ‖A‖) * δ) * ‖x0‖) :=
            mul_le_mul_of_nonneg_left hin hHl
        _ = _ := by ring
    have h8 : σ * H ^ (l + 1) * ‖x0‖ ≤ σ * H ^ l * ‖x0‖ := by
      have h9 : H ^ (l + 1) ≤ H ^ l := pow_le_pow_of_le_one hH hH1 (by omega)
      gcongr
    have e4 : (σ + s₀ + Real.exp (2 * l * ‖A‖) * s₀ + l * Real.exp (l * ‖A‖) * δ) * H ^ l *
        ‖x0‖ = σ * H ^ l * ‖x0‖ +
          (s₀ + Real.exp (2 * l * ‖A‖) * s₀ + l * Real.exp (l * ‖A‖) * δ) * H ^ l * ‖x0‖ := by
      ring
    rw [e4]
    linarith [hy q hql]

end Late

section LowerStart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, FiniteDimensional ℝ (Es i)]
  {Gs : ι → Type*} [∀ i, NormedAddCommGroup (Gs i)] [∀ i, NormedSpace ℝ (Gs i)]
  [∀ i, FiniteDimensional ℝ (Gs i)]
  {Pr : ∀ i, E →L[ℝ] Es i} {Em : ∀ i, Es i →L[ℝ] E} {C : ∀ i, E →L[ℝ] Gs i}
  {A : E →L[ℝ] E} {Ai : ∀ i, Es i →L[ℝ] Es i} {L : ∀ i, Gs i →L[ℝ] Es i}

/-- **Steps 1 and 2 for a rule with a small defect, from any linear start**: the start
`x^q = U^q x_0 + H^l s_q x_0 + O(H^{l+1})`, `‖s_q‖ ≤ s`, and `g₀` a lower bound of `F` over
`𝒵_l` and all start errors. The relative errors are at least `H^l g₀ - C H^{l+1}`. -/
theorem lower_of_small_defect_start [Nontrivial E]
    (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) {T : ℝ} (hT : 0 < T) {g₀ : ℝ}
    (hg₀ : ∀ Z ∈ hiddenRows Pr C A l, ∀ S : E →L[ℝ] E,
      g₀ ≤ leadMax A S (forcedLead Em C A L l + Z) T)
    {w s σ M₀ b H : ℝ} (hw : 0 ≤ w) (hs : 0 ≤ s) (hσ : 0 ≤ σ) (hM₀ : 0 ≤ M₀) (hH : 0 < H)
    (hH1 : H ≤ 1) (hx1 : H * ‖A‖ ≤ 1) (hbH : b * H ≤ 1 / 2) (hlH : 2 * l * H ≤ T)
    (hb : ‖A‖ * Real.exp ‖A‖ + l * ((∑ i, ‖Em i‖) * w) * Real.exp (l * ‖A‖) + M₀ +
      (∑ i, ‖Em i‖) * w ≤ b)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i)
    (hg : ∀ i r, 1 ≤ r → r < l → ‖g i r ∘L C i‖ ≤ w * H)
    (hsmall : ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l‖ ≤
      M₀ * H ^ (l + 1))
    (sq : ℕ → E →L[ℝ] E) (hsq : ∀ q < l, ‖sq q‖ ≤ s) (x : E → ℕ → E)
    (hstart : ∀ x0, ∀ q < l,
      ‖x x0 q - (exp (H • A) ^ q) x0 - H ^ l • sq q x0‖ ≤ σ * H ^ (l + 1) * ‖x0‖)
    (hx : ∀ x0, ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
      x x0 (k + 1) = ∑ q ∈ range l, jacobiM Pr Em C Fi g q (x x0 (k - q)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊T / H⌋₊, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    H ^ l * g₀ -
      (leadConstLate ‖A‖ l b
          (∑ i, ‖Em i‖ * (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
            memC2 l * w * ‖A‖ ^ (l + 1)))
          (‖forcedLead Em C A L l‖ + ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖)))
          (Real.exp (l * ‖A‖) * s)
          (σ + l * Real.exp (l * ‖A‖) *
            (‖forcedLead Em C A L l‖ + ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖))))
          (σ + s + Real.exp (2 * l * ‖A‖) * s + l * Real.exp (l * ‖A‖) *
            (‖forcedLead Em C A L l‖ + ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖))))
          T +
        l * leadLip ‖A‖ (Real.exp (l * ‖A‖) * s)
          (‖forcedLead Em C A L l‖ + ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖))) T) *
        H ^ (l + 1) ≤ δ := by
  have hα0 := norm_nonneg A
  obtain ⟨Z, hZ, hDn, hTZ, hM0, hMr⟩ := small_defect_class hdec hPEi hPE hA hP hl hw hM₀ hH hH1
    hx1 hb Fi g hg hsmall (L := L)
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
      memC2 l * w * ‖A‖ ^ (l + 1) := ⟨_, rfl⟩
  obtain ⟨δb, hδb⟩ : ∃ δb, δb = ‖forcedLead Em C A L l‖ +
      ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖)) := ⟨_, rfl⟩
  rw [← hκ, ← hδb]
  rw [← hκ] at hTZ
  rw [← hδb] at hDn
  have hκ0 : 0 ≤ κ := by
    have := memB_nonneg l
    have := memC1_nonneg l
    have := memC2_nonneg l
    rw [hκ]
    positivity
  have hc₁0 : 0 ≤ ∑ i, ‖Em i‖ * κ := sum_nonneg fun i _ => by positivity
  have hδb0 : 0 ≤ δb := (norm_nonneg _).trans hDn
  have hb0 : 0 ≤ b := le_trans (by positivity) hb
  set s' := Real.exp (l * ‖A‖) * s with hs'
  have hs'0 : 0 ≤ s' := by positivity
  set σ' := σ + l * Real.exp (l * ‖A‖) * δb with hσ'
  have hσ'0 : 0 ≤ σ' := by positivity
  set σ₀ := σ + s + Real.exp (2 * l * ‖A‖) * s + l * Real.exp (l * ‖A‖) * δb with hσ₀
  have hσ₀0 : 0 ≤ σ₀ := by positivity
  obtain ⟨D, hD⟩ : ∃ D, D = forcedLead Em C A L l + Z := ⟨_, rfl⟩
  rw [← hD] at hTZ hDn
  obtain ⟨M, hM⟩ : ∃ M, M = jacobiM Pr Em C Fi g := ⟨_, rfl⟩
  rw [← hM] at hTZ hx hM0 hMr
  set S := exp (-(H • A)) ^ (l - 1) * sq (l - 1) with hS
  have hKT : (⌊T / H⌋₊ : ℝ) * H ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hH.le)
    rwa [le_div_iff₀ hH] at this
  have hslot := fun x0 => start_slot_le A D sq hH.le hσ hH1 hDn hl hsq x0 (x x0) (hstart x0)
  have hSn : ‖S‖ ≤ s' := (hslot 0).1
  have hacc : ∀ x0, ∀ k, l - 1 ≤ k → k ≤ ⌊T / H⌋₊ →
      ‖x x0 k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0‖ ≤
        leadConstLate ‖A‖ l b (∑ i, ‖Em i‖ * κ) δb s' σ' σ₀ T * H ^ (l + 1) * ‖x0‖ := by
    intro x0
    obtain ⟨-, hlast, hold⟩ := hslot x0
    have hrec : ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
        (1 - (0 : E →L[ℝ] E)) (x x0 (k + 1)) = ∑ q ∈ range l, M q (x x0 (k - q)) :=
      fun k hk hkK => by
        rw [sub_zero, one_apply_eq_self]
        exact hx x0 k hk hkK
    exact run_accumulation_late A 0 M D S hH hH1 hb0 hbH hσ'0 hσ₀0 hl hKT
      (by rw [norm_zero]; positivity) hM0 hMr hTZ hDn hSn x0 (x x0) hold hlast hrec
  have hjT : ((l - 1 : ℕ) : ℝ) * H ≤ T := by
    have h2 : ((l - 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast Nat.sub_le l 1
    have h3 : (0 : ℝ) ≤ l * H := by positivity
    nlinarith
  have hlow := leadMax_le_of_runs A S D hH
    (leadConstLate_nonneg l hα0 hb0 hc₁0 hδb0 hs'0 hσ'0 hσ₀0 hT.le) (l := l) (j := l - 1)
    hjT x (fun x0 k hjk hk => hacc x0 k hjk hk) hδ
  have hLip : leadLip ‖A‖ ‖S‖ ‖D‖ T ≤ leadLip ‖A‖ s' δb T := leadLip_le hα0 hT.le hSn hDn
  have hgZ := hg₀ Z hZ S
  rw [← hD] at hgZ
  have h2 : H ^ l * g₀ ≤ H ^ l * leadMax A S D T :=
    mul_le_mul_of_nonneg_left hgZ (by positivity)
  have hl1 : ((l - 1 : ℕ) : ℝ) + 1 = l := by
    rw [Nat.cast_sub hl]
    push_cast
    ring
  have h3 : (leadConstLate ‖A‖ l b (∑ i, ‖Em i‖ * κ) δb s' σ' σ₀ T +
      (((l - 1 : ℕ) : ℝ) + 1) * leadLip ‖A‖ ‖S‖ ‖D‖ T) * H ^ (l + 1) ≤
      (leadConstLate ‖A‖ l b (∑ i, ‖Em i‖ * κ) δb s' σ' σ₀ T +
        l * leadLip ‖A‖ s' δb T) * H ^ (l + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hl1]
    have := mul_le_mul_of_nonneg_left hLip (Nat.cast_nonneg l)
    linarith
  linarith

/-- **The least error over a run from any linear start, every rule** (lower
bound), for the Jacobi schemes with `l` old
samples and bounded weights `‖g i r ∘ C i‖ ≤ w H` (`1 ≤ r < l`). Let `g₀` be a lower bound of
`F(Z, S) = sup_{0≤t≤T} ‖e^{tA} S - Φ_t(D⁰ + Z)‖` over `Z ∈ 𝒵_l` and all `S`. For every
`w, s, σ ≥ 0` there are `C, H₀` such that for `0 < H ≤ H₀`, every such rule and every run from a
linear start `‖x^q - U^q x_0 - H^l s_q x_0‖ ≤ σ H^{l+1} ‖x_0‖` with `‖s_q‖ ≤ s` (`q < l`; the
start errors of the slots differ at the order `H^l`): if `δ` bounds the relative errors for
`k ≤ ⌊T/H⌋`, then `δ ≥ H^l g₀ - C H^{l+1}`. -/
theorem least_memory_le_start [Nontrivial E]
    (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) {T : ℝ} (hT : 0 < T) (hTA : T * ‖A‖ ≤ 1 / 2) {g₀ : ℝ}
    (hg₀ : ∀ Z ∈ hiddenRows Pr C A l, ∀ S : E →L[ℝ] E,
      g₀ ≤ leadMax A S (forcedLead Em C A L l + Z) T)
    {w s σ : ℝ} (hw : 0 ≤ w) (hs : 0 ≤ s) (hσ : 0 ≤ σ) :
    ∃ Cl H₀ : ℝ, 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
      ∀ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
      (∀ i r, 1 ≤ r → r < l → ‖g i r ∘L C i‖ ≤ w * H) →
      ∀ sq : ℕ → E →L[ℝ] E, (∀ q < l, ‖sq q‖ ≤ s) → ∀ x : E → ℕ → E,
      (∀ x0, ∀ q < l, ‖x x0 q - (exp (H • A) ^ q) x0 - H ^ l • sq q x0‖ ≤
        σ * H ^ (l + 1) * ‖x0‖) →
      (∀ x0, ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
        x x0 (k + 1) = ∑ q ∈ range l, jacobiM Pr Em C Fi g q (x x0 (k - q))) →
      ∀ δ : ℝ, (∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊T / H⌋₊, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) →
      H ^ l * g₀ - Cl * H ^ (l + 1) ≤ δ := by
  have hα0 := norm_nonneg A
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ i, ‖Em i‖ := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact sum_nonneg fun i _ => norm_nonneg _
  obtain ⟨gp, hgp⟩ : ∃ gp, gp = max g₀ 0 := ⟨_, rfl⟩
  have hgp0 : 0 ≤ gp := by rw [hgp]; exact le_max_right _ _
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ = 35 * (gp + 1) / T := ⟨_, rfl⟩
  have hM₀0 : 0 ≤ M₀ := by rw [hM₀]; positivity
  obtain ⟨b, hb⟩ : ∃ b, b = ‖A‖ * Real.exp ‖A‖ + l * (W * w) * Real.exp (l * ‖A‖) + M₀ +
      W * w := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  obtain ⟨δb, hδb⟩ : ∃ δb, δb = ‖forcedLead Em C A L l‖ +
      ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖)) := ⟨_, rfl⟩
  have hδb0 : 0 ≤ δb := by rw [hδb]; positivity
  obtain ⟨Cl, hCl⟩ : ∃ Cl, Cl = leadConstLate ‖A‖ l b
      (∑ i, ‖Em i‖ * (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
        memC2 l * w * ‖A‖ ^ (l + 1))) δb (Real.exp (l * ‖A‖) * s)
      (σ + l * Real.exp (l * ‖A‖) * δb)
      (σ + s + Real.exp (2 * l * ‖A‖) * s + l * Real.exp (l * ‖A‖) * δb) T +
      l * leadLip ‖A‖ (Real.exp (l * ‖A‖) * s) δb T := ⟨_, rfl⟩
  have hCl0 : 0 ≤ Cl := by
    have := memB_nonneg l
    have := memC1_nonneg l
    have := memC2_nonneg l
    rw [hCl]
    exact add_nonneg (leadConstLate_nonneg l hα0 hb0 (sum_nonneg fun i _ => by positivity)
      hδb0 (by positivity) (by positivity) (by positivity) hT.le)
      (mul_nonneg (Nat.cast_nonneg l) (leadLip_nonneg hα0 (by positivity) hδb0 hT.le))
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  refine ⟨Cl, min (min (1 / (1 + ‖A‖ + 2 * b)) (T / (2 * l)))
      (min (0.35 / (1.42 * (W * w) * l ^ 2 + 1)) (0.175 / (gp + 1))),
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)),
    fun H hH hHH₀ Fi g hg sq hsq x hstart hx δ hδ => ?_⟩
  have hHa : H * (1 + ‖A‖ + 2 * b) ≤ 1 := by
    have h := hHH₀.trans ((min_le_left _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hHb : 2 * l * H ≤ T := by
    have h := hHH₀.trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hHc : (1.42 * (W * w) * l ^ 2 + 1) * H ≤ 0.35 := by
    have h := hHH₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hHd : (gp + 1) * H ≤ 0.175 := by
    have h := hHH₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hH1 : H ≤ 1 :=
    (le_mul_of_one_le_right hH.le (by linarith : (1 : ℝ) ≤ 1 + ‖A‖ + 2 * b)).trans hHa
  have hx1 : H * ‖A‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith : ‖A‖ ≤ 1 + ‖A‖ + 2 * b) hH.le).trans hHa
  have hbH : b * H ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left (by linarith : 2 * b ≤ 1 + ‖A‖ + 2 * b) hH.le
    linarith
  have hδ0 : 0 ≤ δ := relative_error_bound_nonneg hδ
  have hgoal : H ^ l * g₀ ≤ H ^ l * gp :=
    mul_le_mul_of_nonneg_left (by rw [hgp]; exact le_max_left _ _) (by positivity)
  have hCH : 0 ≤ Cl * H ^ (l + 1) := by positivity
  rcases lt_or_ge (M₀ * H ^ (l + 1))
      ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l‖ with hbig | hsmall
  · have hm : 1.42 * (W * w * H) * (l : ℝ) ^ 2 ≤ 0.35 := by
      have : 0 ≤ H := hH.le
      nlinarith
    have hMr : ∀ r, 1 ≤ r → r < l → ‖jacobiM Pr Em C Fi g r‖ ≤ W * w * H := by
      intro r hr1 hrl
      refine (norm_jacobiM_le _ _ hr1).trans ?_
      rw [hW, sum_mul, sum_mul]
      refine sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hg i r hr1 hrl) (norm_nonneg _)
    rw [hM₀] at hbig
    have h := lower_of_large_defect A (jacobiM Pr Em C Fi g) hH hH1 hT hTA hl hHb hgp0 hHd
      (by positivity) hm hMr hbig x hx hδ
    linarith
  · have h := lower_of_small_defect_start hdec hPEi hPE hA hP hl hT hg₀ hw hs hσ hM₀0 hH hH1
      hx1 hbH hHb (by rw [← hW, hb]) Fi g hg hsmall sq hsq x hstart hx hδ
    rw [← hδb, ← hCl] at h
    exact h

end LowerStart

end CoSimFoundations
