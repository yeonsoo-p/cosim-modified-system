/-
The largest order of convergence with bounded weights, in every case (the paper).

**Paper.** Let `f^w(H)` be the least local defect over the rules with weights bounded by `w`
(coefficients of the samples of instants other than `t_k` at most `w H`) and
`p^w = sup {p : f^w = O(H^p)}`. The largest order of convergence of these rules is `p^w - 1`:
(a) a rule of the class with `ε_K = O(H^q)` has, by Lemma A.1, a defect `O(H^{q+1})`, so
`f^w = O(H^{q+1})`; (b) the rule that attains `f^w = O(H^p)` has bounded weights and converges
with the order `p - 1`.

**Setting**, that of `RunOrder` and `OrderReached`: the recursion
`(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}`, `U = exp (H A)`, the local defect
`𝒯 = (1 - N) U - Σ_{r<l} M r U^{-r}` (`runDefect`). A rule is given by its coefficients
`ρ = (N, m)`, `m : Fin l → R` (`M r = m r` for `r < l`, `tupleM`), in a set `𝒮` of admissible
coefficients (the structure of the rules: which states and samples each row may use);
`boundedRules 𝒮 w H` are those with `‖N‖ ≤ w H` and `‖m q‖ ≤ w H` for `q ≥ 1`. The coefficient
`m 0` of the instant `t_k` (own state and current samples) is free.

* **The least defect exists** (`exists_least_tupleDefect`): in a proper normed ring (finite
  dimension), for `𝒮` closed and `l ≥ 1`, `‖𝒯‖` attains its least value on `boundedRules 𝒮 w H`
  (if the class is not empty): the defect is coercive in `m 0`
  (`‖m 0‖ ≤ ‖𝒯‖ + ‖(1 - N) U‖ + Σ_{q≥1} ‖m q‖ ‖U^{-q}‖`) and the other coefficients are bounded.
* **(a) Order bounds the least defect** (`norm_runDefect_le_of_run_error`,
  `least_defect_le_of_run_error`): if all runs of a rule with `‖N‖ ≤ w H`, `‖M r‖ ≤ w H`
  (`1 ≤ r < l`) have relative errors at most `δ < 0.175` over `K` steps, `l ≤ K`,
  `K H ‖A‖ ≤ 1/2`, then `‖𝒯‖ ≤ δ B / (0.175 (K - l + 1))`,
  `B = 2.65 (1 + w H) + w H l (l - 1) (1 + ¼ e^{(l-1) H ‖A‖})` (Lemma A.1, `run_order_barrier`);
  with `δ = c H^q`, `0 < H ≤ 1` and `(K - l + 1) H ≥ τ > 0`:
  `‖𝒯‖ ≤ c orderB l w / (0.175 τ) H^{q+1}`, `orderB l w = 2.65 (1 + w) + (3/2) w l (l - 1)`,
  and so is the least defect over the class.
* **(b) The least defect bounds the order** (`run_convergence_pow`, `run_error_le_of_defect`,
  `least_defect_run_error_le`): a rule with `‖N‖ ≤ w H`, `‖M r‖ ≤ w H` (`1 ≤ r < l`) and
  `‖𝒯‖ ≤ D H^p`, `p ≥ 1`, `0 < H ≤ 1`, `l H ‖A‖ ≤ 1`, `b H ≤ 1/2` with
  `b = 3 (‖A‖ + l w) + D` has `‖M 0 - 1‖ ≤ b H` (`norm_M_zero_sub_one_le`), hence is
  zero-stable, and its run from exact starting values has, over `K H ≤ T₀`,
  `‖x^k - U^k x_0‖ ≤ 2 D T₀ e^{(‖A‖ + 2 (l + 1) b) T₀} H^{p-1} ‖x_0‖`: order `p - 1`.

Together, (a) and (b) say that the largest order of convergence of the rules with weights bounded
by `w` is one less than the order of their least local defect. The statements are
for the stacked recursion of the whole network; the per-subsystem form (`min_i p_i^w - 1`) is
not formalised here.
-/
import CoSimFoundations.OrderReached

open NormedSpace Finset

namespace CoSimFoundations

/-! ### The rules with bounded weights and the least defect -/

section Rules

variable {R : Type*} [NormedRing R]

/-- The coefficients of the samples of a rule given by a tuple: `M r = m r` for `r < l`, zero
beyond. -/
def tupleM {l : ℕ} (m : Fin l → R) (r : ℕ) : R :=
  if h : r < l then m ⟨r, h⟩ else 0

/-- A sum over the ages with the coefficients of a tuple is a sum over the tuple. -/
theorem sum_range_tupleM_mul {l : ℕ} (m : Fin l → R) (f : ℕ → R) :
    ∑ r ∈ range l, tupleM m r * f r = ∑ q : Fin l, m q * f q := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun q _ => ?_
  simp [tupleM, q.isLt]

/-- The local defect of the rule `ρ = (N, m)`: `𝒯 = (1 - N) U - Σ_{q<l} m q Ui^q`. -/
def tupleDefect {l : ℕ} (U Ui : R) (ρ : R × (Fin l → R)) : R :=
  runDefect ρ.1 (tupleM ρ.2) U Ui l

/-- The local defect of a rule as a sum over the tuple. -/
theorem tupleDefect_eq {l : ℕ} (U Ui : R) (ρ : R × (Fin l → R)) :
    tupleDefect U Ui ρ = (1 - ρ.1) * U - ∑ q : Fin l, ρ.2 q * Ui ^ (q : ℕ) := by
  rw [tupleDefect, runDefect]
  congr 1
  exact sum_range_tupleM_mul ρ.2 fun r => Ui ^ r

/-- **The rules with weights bounded by `w`** within a set `𝒮` of admissible coefficients: the
coefficients of the new samples and of the samples of the instants before `t_k` are at most
`w H`. -/
def boundedRules {l : ℕ} (𝒮 : Set (R × (Fin l → R))) (w H : ℝ) : Set (R × (Fin l → R)) :=
  {ρ | ρ ∈ 𝒮 ∧ ‖ρ.1‖ ≤ w * H ∧ ∀ q : Fin l, 1 ≤ (q : ℕ) → ‖ρ.2 q‖ ≤ w * H}

/-- The local defect is continuous in the coefficients. -/
theorem continuous_tupleDefect {l : ℕ} (U Ui : R) :
    Continuous (tupleDefect (l := l) U Ui) := by
  have e : tupleDefect (l := l) U Ui =
      fun ρ => (1 - ρ.1) * U - ∑ q : Fin l, ρ.2 q * Ui ^ (q : ℕ) :=
    funext fun ρ => tupleDefect_eq U Ui ρ
  rw [e]
  exact ((continuous_const.sub continuous_fst).mul continuous_const).sub
    (continuous_finsetSum _ fun q _ =>
      ((continuous_apply q).comp continuous_snd).mul continuous_const)

/-- The class of the rules with bounded weights is closed if `𝒮` is. -/
theorem isClosed_boundedRules {l : ℕ} {𝒮 : Set (R × (Fin l → R))} (h𝒮 : IsClosed 𝒮)
    (w H : ℝ) : IsClosed (boundedRules 𝒮 w H) := by
  have h2 : IsClosed {ρ : R × (Fin l → R) | ‖ρ.1‖ ≤ w * H} :=
    isClosed_le (continuous_norm.comp continuous_fst) continuous_const
  have h3 : IsClosed {ρ : R × (Fin l → R) | ∀ q : Fin l, 1 ≤ (q : ℕ) → ‖ρ.2 q‖ ≤ w * H} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun q => isClosed_iInter fun _ =>
      isClosed_le (continuous_norm.comp ((continuous_apply q).comp continuous_snd))
        continuous_const
  exact h𝒮.inter (h2.inter h3)

/-- **Coercivity in the coefficient of the instant `t_k`:**
`‖m 0‖ ≤ ‖𝒯‖ + ‖(1 - N) U‖ + Σ_{q≥1} ‖m q‖ ‖Ui^q‖`. -/
theorem norm_tuple_zero_le {l : ℕ} (U Ui : R) (ρ : R × (Fin (l + 1) → R)) :
    ‖ρ.2 0‖ ≤ ‖tupleDefect U Ui ρ‖ + ‖(1 - ρ.1) * U‖ +
      ∑ i : Fin l, ‖ρ.2 i.succ‖ * ‖Ui ^ ((i : ℕ) + 1)‖ := by
  have e : ρ.2 0 = (1 - ρ.1) * U - tupleDefect U Ui ρ -
      ∑ i : Fin l, ρ.2 i.succ * Ui ^ ((i : ℕ) + 1) := by
    rw [tupleDefect_eq, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sub_le ((1 - ρ.1) * U) (tupleDefect U Ui ρ)
  have h2 : ‖∑ i : Fin l, ρ.2 i.succ * Ui ^ ((i : ℕ) + 1)‖ ≤
      ∑ i : Fin l, ‖ρ.2 i.succ‖ * ‖Ui ^ ((i : ℕ) + 1)‖ :=
    (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_mul_le _ _)
  linarith

/-- **The least defect over the rules with bounded weights is attained** (the minimum
exists: the defect is coercive in `F_i`, and the other coefficients range over a compact set).
In a proper normed ring (e.g. operators on a finite-dimensional space), for a closed set `𝒮` of
admissible coefficients, `l ≥ 1` and a nonempty class, some rule of `boundedRules 𝒮 w H` has the
least `‖𝒯‖` over the class. -/
theorem exists_least_tupleDefect [ProperSpace R] {l : ℕ} (hl : 1 ≤ l) (U Ui : R)
    {𝒮 : Set (R × (Fin l → R))} (h𝒮 : IsClosed 𝒮) {w H : ℝ} {ρ₀ : R × (Fin l → R)}
    (hρ₀ : ρ₀ ∈ boundedRules 𝒮 w H) :
    ∃ ρ ∈ boundedRules 𝒮 w H, ∀ ρ' ∈ boundedRules 𝒮 w H,
      ‖tupleDefect U Ui ρ‖ ≤ ‖tupleDefect U Ui ρ'‖ := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hl
  set Kset := boundedRules 𝒮 w H ∩ {ρ | ‖tupleDefect U Ui ρ‖ ≤ ‖tupleDefect U Ui ρ₀‖} with hK
  have hwH : 0 ≤ w * H := (norm_nonneg _).trans hρ₀.2.1
  have hclosed : IsClosed Kset :=
    (isClosed_boundedRules h𝒮 w H).inter
      (isClosed_le (continuous_norm.comp (continuous_tupleDefect U Ui)) continuous_const)
  -- the bound of the coefficients on `Kset`
  set C := w * H + (‖tupleDefect U Ui ρ₀‖ + (‖(1 : R)‖ + w * H) * ‖U‖ +
    ∑ i : Fin l, w * H * ‖Ui ^ ((i : ℕ) + 1)‖) with hC
  have hC0 : w * H ≤ C := by
    have h1 : 0 ≤ ∑ i : Fin l, w * H * ‖Ui ^ ((i : ℕ) + 1)‖ :=
      sum_nonneg fun i _ => mul_nonneg hwH (norm_nonneg _)
    have h2 : 0 ≤ (‖(1 : R)‖ + w * H) * ‖U‖ := by positivity
    linarith [norm_nonneg (tupleDefect U Ui ρ₀)]
  have hbdd : Bornology.IsBounded Kset := by
    refine isBounded_iff_forall_norm_le.2 ⟨C, fun ρ hρ => ?_⟩
    obtain ⟨⟨-, hN, hm⟩, hT⟩ := hρ
    refine norm_prod_le_iff.2 ⟨hN.trans hC0, (pi_norm_le_iff_of_nonneg
      (hwH.trans hC0)).2 fun q => ?_⟩
    refine Fin.cases ?_ (fun i => (hm i.succ (by simp)).trans hC0) q
    have h1 := norm_tuple_zero_le U Ui ρ
    have h2 : ‖(1 - ρ.1) * U‖ ≤ (‖(1 : R)‖ + w * H) * ‖U‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _))
    have h3 : ∑ i : Fin l, ‖ρ.2 i.succ‖ * ‖Ui ^ ((i : ℕ) + 1)‖ ≤
        ∑ i : Fin l, w * H * ‖Ui ^ ((i : ℕ) + 1)‖ :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i.succ (by simp)) (norm_nonneg _)
    rw [Set.mem_ofPred_eq] at hT
    linarith
  have hcpt : IsCompact Kset := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨ρ, hρK, hmin⟩ := hcpt.exists_isMinOn
    ⟨ρ₀, hρ₀, show ‖tupleDefect U Ui ρ₀‖ ≤ ‖tupleDefect U Ui ρ₀‖ from le_rfl⟩
    (continuous_norm.comp (continuous_tupleDefect U Ui)).continuousOn
  refine ⟨ρ, hρK.1, fun ρ' hρ' => ?_⟩
  by_cases h : ‖tupleDefect U Ui ρ'‖ ≤ ‖tupleDefect U Ui ρ₀‖
  · exact isMinOn_iff.1 hmin ρ' ⟨hρ', h⟩
  · exact (hρK.2 : ‖tupleDefect U Ui ρ‖ ≤ ‖tupleDefect U Ui ρ₀‖).trans (not_le.1 h).le

end Rules

/-! ### (a) The order bounds the least defect -/

section Barrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

/-- The constant of Lemma A.1 with weights bounded by `w`, for `0 < H ≤ 1`:
`orderB l w = 2.65 (1 + w) + (3/2) w l (l - 1)`. -/
noncomputable def orderB (l : ℕ) (w : ℝ) : ℝ := 2.65 * (1 + w) + 3 / 2 * w * ((l : ℝ) * (l - 1))

/-- **The defect from the error over a run** (Lemma A.1 solved for the defect). If all runs of a
rule with `‖N‖ ≤ w H`, `‖M r‖ ≤ w H` (`1 ≤ r < l`) have relative errors at most `δ < 0.175` for
`k ≤ K`, `1 ≤ l ≤ K`, `K H ‖A‖ ≤ 1/2`, then
`‖𝒯‖ ≤ δ B / (0.175 (K - l + 1))`, `B = 2.65 (1 + w H) + w H l (l - 1) (1 + ¼ e^{(l-1) H ‖A‖})`. -/
theorem norm_runDefect_le_of_run_error (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H w : ℝ}
    (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    (hN : ‖N‖ ≤ w * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ w * H) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖)
    (hδ1 : δ < 0.175) :
    ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤
      δ * (2.65 * (1 + w * H) + w * H * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖)))) / (0.175 * ((K : ℝ) - l + 1)) := by
  have h := run_order_barrier A N M hH hl hK hKH hN hM x hx hδ
  have hwH : 0 ≤ w * H := (norm_nonneg _).trans hN
  have hl1 : (0 : ℝ) ≤ (l : ℝ) * (l - 1) := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  set B := 2.65 * (1 + w * H) + w * H * ((l : ℝ) * (l - 1)) *
    (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) with hB
  have hB0 : 0 < B := by
    have : 0 ≤ w * H * ((l : ℝ) * (l - 1)) * (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) :=
      mul_nonneg (mul_nonneg hwH hl1) (by positivity)
    rw [hB]
    linarith
  have hK' := run_length_pos hK
  have h2 : 0.175 * ((K : ℝ) - l + 1) *
      ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ / B ≤ δ := by
    rcases min_le_iff.1 h with h3 | h3
    · exact absurd h3 (not_le.2 hδ1)
    · exact h3
  rw [div_le_iff₀ hB0] at h2
  rw [le_div_iff₀ (mul_pos (by norm_num) hK'), runDefect]
  calc ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ *
        (0.175 * ((K : ℝ) - l + 1))
      = 0.175 * ((K : ℝ) - l + 1) *
          ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ := by ring
    _ ≤ δ * B := h2

/-- **(a) An order of convergence bounds the defect** (lower bound: "if `ε_K = O(H^q)` then
`f^w = O(H^{q+1})`"). Under the hypotheses of `norm_runDefect_le_of_run_error` with `δ = c H^q`,
`c H^q < 0.175`, `0 < H ≤ 1`, `w ≥ 0` and a run long enough, `τ ≤ (K - l + 1) H`, `0 < τ`:
`‖𝒯‖ ≤ c orderB l w / (0.175 τ) · H^{q+1}`. -/
theorem norm_runDefect_le_of_order (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H w c τ : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hw : 0 ≤ w) {l K q : ℕ} (hl : 1 ≤ l) (hK : l ≤ K)
    (hKH : K * H * ‖A‖ ≤ 1 / 2) (hτ : 0 < τ) (hτK : τ ≤ ((K : ℝ) - l + 1) * H)
    (hN : ‖N‖ ≤ w * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ w * H) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ c * H ^ q * ‖x0‖)
    (hc : c * H ^ q < 0.175) :
    ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤
      c * orderB l w / (0.175 * τ) * H ^ (q + 1) := by
  have h := norm_runDefect_le_of_run_error A N M hH.le hl hK hKH hN hM x hx hδ hc
  have hc0 : 0 ≤ c * H ^ q := by
    obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
    have h1 := (norm_nonneg _).trans (hδ x0 hx0 0 (Nat.zero_le _))
    exact nonneg_of_mul_nonneg_left h1 (norm_pos_iff.2 hx0)
  have hK' := run_length_pos hK
  have hl1 : (0 : ℝ) ≤ (l : ℝ) * (l - 1) := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  -- `B ≤ orderB l w`
  have hexp : Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) ≤ 2 := by
    have h1 : ((l : ℝ) - 1) * (H * ‖A‖) ≤ 1 / 2 := by
      have hlK : (l : ℝ) - 1 ≤ K := by
        have : (l : ℝ) ≤ K := by exact_mod_cast hK
        linarith
      calc ((l : ℝ) - 1) * (H * ‖A‖) ≤ K * (H * ‖A‖) :=
            mul_le_mul_of_nonneg_right hlK (mul_nonneg hH.le (norm_nonneg A))
        _ = K * H * ‖A‖ := by ring
        _ ≤ 1 / 2 := hKH
    have h2 : Real.exp (1 / 2) ≤ 2 :=
      (Real.exp_bound_div_one_sub_of_interval (x := 1 / 2) (by norm_num) (by norm_num)).trans_eq
        (by norm_num)
    exact (Real.exp_le_exp.2 h1).trans h2
  have hB : 2.65 * (1 + w * H) + w * H * ((l : ℝ) * (l - 1)) *
      (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) ≤ orderB l w := by
    rw [orderB]
    have h1 : w * H ≤ w := mul_le_of_le_one_right hw hH1
    have h2 : 1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) ≤ 3 / 2 := by linarith
    have h4 := mul_le_mul (mul_le_mul_of_nonneg_right h1 hl1) h2 (by positivity)
      (mul_nonneg hw hl1)
    linarith
  have hOB : 0 ≤ orderB l w := by
    rw [orderB]
    have := mul_nonneg hw hl1
    linarith
  -- the passage to `H^{q+1}`
  have hKpos : 0 < 0.175 * ((K : ℝ) - l + 1) := mul_pos (by norm_num) hK'
  have hτH : 0 < 0.175 * τ / H := div_pos (mul_pos (by norm_num) hτ) hH
  have hτK' : 0.175 * τ / H ≤ 0.175 * ((K : ℝ) - l + 1) := by
    rw [div_le_iff₀ hH]
    linarith
  calc ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖
      ≤ c * H ^ q * (2.65 * (1 + w * H) + w * H * ((l : ℝ) * (l - 1)) *
          (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖)))) /
          (0.175 * ((K : ℝ) - l + 1)) := h
    _ ≤ c * H ^ q * orderB l w / (0.175 * ((K : ℝ) - l + 1)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB hc0) hKpos.le
    _ ≤ c * H ^ q * orderB l w / (0.175 * τ / H) :=
        div_le_div_of_nonneg_left (mul_nonneg hc0 hOB) hτH hτK'
    _ = c * orderB l w / (0.175 * τ) * H ^ (q + 1) := by
        rw [div_div_eq_mul_div, pow_succ]
        ring

/-- **(a) for the least defect** (every such rule has `‖𝒯_i‖ ≥ f^w`; if `ε_K = O(H^q)` then
`f^w = O(H^{q+1})`). If a rule `ρ` of `boundedRules 𝒮 w H` has all runs with relative errors at
most `c H^q < 0.175` (hypotheses of `norm_runDefect_le_of_order`), then every rule `ρ'` with the
least defect over the class has `‖𝒯(ρ')‖ ≤ c orderB l w / (0.175 τ) · H^{q+1}`. -/
theorem least_defect_le_of_run_error (A : E →L[ℝ] E) {l : ℕ}
    {𝒮 : Set ((E →L[ℝ] E) × (Fin l → E →L[ℝ] E))} {H w c τ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1)
    (hw : 0 ≤ w) {K q : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) (hτ : 0 < τ)
    (hτK : τ ≤ ((K : ℝ) - l + 1) * H) {ρ : (E →L[ℝ] E) × (Fin l → E →L[ℝ] E)}
    (hρ : ρ ∈ boundedRules 𝒮 w H) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - ρ.1) (x x0 (k + 1)) = ∑ r ∈ range l, tupleM ρ.2 r (x x0 (k - r)))
    (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ c * H ^ q * ‖x0‖)
    (hc : c * H ^ q < 0.175) {ρ' : (E →L[ℝ] E) × (Fin l → E →L[ℝ] E)}
    (hρ' : ∀ ρ'' ∈ boundedRules 𝒮 w H,
      ‖tupleDefect (exp (H • A)) (exp (-(H • A))) ρ'‖ ≤
        ‖tupleDefect (exp (H • A)) (exp (-(H • A))) ρ''‖) :
    ‖tupleDefect (exp (H • A)) (exp (-(H • A))) ρ'‖ ≤
      c * orderB l w / (0.175 * τ) * H ^ (q + 1) := by
  refine (hρ' ρ hρ).trans ?_
  have hM : ∀ r, 1 ≤ r → r < l → ‖tupleM ρ.2 r‖ ≤ w * H := fun r hr1 hrl => by
    rw [tupleM, dite_eq_left hrl]
    exact hρ.2.2 ⟨r, hrl⟩ hr1
  exact norm_runDefect_le_of_order A ρ.1 (tupleM ρ.2) hH hH1 hw hl hK hKH hτ hτK hρ.2.1 hM x hx
    hδ hc

end Barrier

/-! ### (b) The least defect bounds the order -/

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Order `p - 1` over an interval of the length `T₀`** (`run_convergence` with a defect of the
order `H^p`): under the hypotheses of `run_error_le` with `‖𝒯‖ ≤ D H^p`, `p ≥ 1`, `K H ≤ T₀`,
`0 < H`: `‖x^k - U^k x_0‖ ≤ 2 D T₀ e^{(‖A‖ + 2 (l + 1) b) T₀} H^{p-1} ‖x_0‖` for every `k ≤ K`. -/
theorem run_convergence_pow (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H b D T₀ : ℝ} (hH : 0 < H)
    (hb : 0 ≤ b) (hbH : b * H ≤ 1 / 2) {l K p : ℕ} (hl : 1 ≤ l) (hp : 1 ≤ p) (hKT : K * H ≤ T₀)
    (hN : ‖N‖ ≤ b * H) (hM0 : ‖M 0 - 1‖ ≤ b * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (hT : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤ D * H ^ p) (x0 : E)
    (x : ℕ → E) (hstart : ∀ k < l, x k = (exp (H • A) ^ k) x0)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) (x (k + 1)) = ∑ r ∈ range l, M r (x (k - r))) :
    ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0‖ ≤
      2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) * H ^ (p - 1) * ‖x0‖ := by
  intro k hk
  have h := run_error_le A N M hH.le hb hbH hl hN hM0 hM hT x0 x hstart hx k hk
  have hD : 0 ≤ D * H ^ p := (norm_nonneg _).trans hT
  have hD' : 0 ≤ D := by
    have : 0 < H ^ p := by positivity
    exact nonneg_of_mul_nonneg_left hD this
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hkH : (k : ℝ) * H ≤ T₀ := (mul_le_mul_of_nonneg_right hkK hH.le).trans hKT
  have hc : (1 + 2 * (l + 1) * b * H) ^ k ≤ Real.exp (2 * (l + 1) * b * T₀) := by
    have h1 : 1 + 2 * (l + 1) * b * H ≤ Real.exp (2 * (l + 1) * b * H) := by
      have := Real.add_one_le_exp (2 * (l + 1) * b * H)
      linarith
    have h2 : 0 ≤ 1 + 2 * (l + 1) * b * H := by positivity
    calc (1 + 2 * (l + 1) * b * H) ^ k ≤ Real.exp (2 * (l + 1) * b * H) ^ k :=
          pow_le_pow_left₀ h2 h1 k
      _ = Real.exp (k * (2 * (l + 1) * b * H)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * (l + 1) * b * T₀) := by
          refine Real.exp_le_exp.2 ?_
          have : (k : ℝ) * (2 * (l + 1) * b * H) = 2 * (l + 1) * b * (k * H) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hkH (by positivity)
  have hexp : Real.exp (K * (H * ‖A‖)) * Real.exp (2 * (l + 1) * b * T₀) ≤
      Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [norm_nonneg A]
  refine h.trans ?_
  have hx0 := norm_nonneg x0
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hHp : H ^ p = H * H ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e1 : 2 * (D * H ^ p * Real.exp (K * (H * ‖A‖)) * ‖x0‖) * k *
      (1 + 2 * (l + 1) * b * H) ^ k =
      2 * D * ((k : ℝ) * H) * (Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k) *
        H ^ (p - 1) * ‖x0‖ := by
    rw [hHp]
    ring
  rw [e1]
  have hHl : 0 ≤ H ^ (p - 1) := by positivity
  have h3 : Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k ≤
      Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) :=
    (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le).trans hexp
  have h4 : 0 ≤ Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k := by positivity
  have hT0 : 0 ≤ T₀ := (by positivity : (0 : ℝ) ≤ k * H).trans hkH
  calc 2 * D * ((k : ℝ) * H) * (Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k) *
        H ^ (p - 1) * ‖x0‖
      ≤ 2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) * H ^ (p - 1) * ‖x0‖ := by
        gcongr

/-- `‖exp (H A)^r‖ ≤ e^{r H ‖A‖}` for operators. -/
theorem norm_exp_smul_pow_le (A : E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H) (r : ℕ) :
    ‖exp (H • A) ^ r‖ ≤ Real.exp (r * (H * ‖A‖)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    (norm_exp_smul_pow_apply_le A hH r)

/-- **Zero-stability from bounded weights and a small defect** (upper bound: "the rule that
attains `f^w` has the defect `O(H^p)` and bounded weights, so it is zero-stable"). If
`‖N‖ ≤ w H`, `‖M r‖ ≤ w H` (`1 ≤ r < l`), `‖𝒯‖ ≤ D H^p`, `p ≥ 1`, `0 < H ≤ 1` and
`l H ‖A‖ ≤ 1`, then `‖M 0 - 1‖ ≤ (3 (‖A‖ + l w) + D) H`. -/
theorem norm_M_zero_sub_one_le (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H w D : ℝ} (hH : 0 < H)
    (hH1 : H ≤ 1) {l p : ℕ} (hl : 1 ≤ l) (hp : 1 ≤ p) (hlA : (l : ℝ) * (H * ‖A‖) ≤ 1)
    (hN : ‖N‖ ≤ w * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ w * H)
    (hT : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤ D * H ^ p) :
    ‖M 0 - 1‖ ≤ (3 * (‖A‖ + l * w) + D) * H := by
  set U := exp (H • A) with hU
  set Ui := exp (-(H • A)) with hUi
  set T := runDefect N M U Ui l with hT'
  have hw : 0 ≤ w * H := (norm_nonneg _).trans hN
  have hA0 := norm_nonneg A
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hHA : H * ‖A‖ ≤ 1 := by nlinarith [mul_nonneg hH.le hA0]
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  -- `M 0 - 1 = (U - 1) - N U - Σ_{1≤r<l} M r Ui^r - 𝒯`
  have e : M 0 - 1 = (U - 1) - N * U - ∑ r ∈ Ico 1 l, M r * Ui ^ r - T := by
    rw [hT', runDefect, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < l), zero_add,
      pow_zero, mul_one, sub_mul, one_mul]
    abel
  have hU1 : ‖U - 1‖ ≤ 3 * ‖A‖ * H := by
    have h : ‖U - 1‖ ≤ Real.exp (H * ‖A‖) - 1 := by
      have h0 := norm_exp_smul_pow_sub_one_le A hH.le 1
      rwa [pow_one, Nat.cast_one, one_mul] at h0
    have h1 := exp_sub_one_le_mul_exp (H * ‖A‖)
    have h2 : Real.exp (H * ‖A‖) ≤ 3 := (Real.exp_le_exp.2 hHA).trans he
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hH.le hA0)
    linarith
  have hpow : ∀ r ≤ l, ‖Ui ^ r‖ ≤ 3 := fun r hr => by
    have h := norm_exp_smul_pow_le (-A) hH.le r
    rw [smul_neg, norm_neg] at h
    have h2 : (r : ℝ) * (H * ‖A‖) ≤ 1 := by
      have : (r : ℝ) ≤ l := by exact_mod_cast hr
      nlinarith [mul_nonneg hH.le hA0]
    exact h.trans ((Real.exp_le_exp.2 h2).trans he)
  have hNU : ‖N * U‖ ≤ 3 * (w * H) := by
    have h := norm_exp_smul_pow_le A hH.le 1
    rw [pow_one, Nat.cast_one, one_mul] at h
    have h2 : ‖U‖ ≤ 3 := h.trans ((Real.exp_le_exp.2 hHA).trans he)
    calc ‖N * U‖ ≤ ‖N‖ * ‖U‖ := norm_mul_le _ _
      _ ≤ (w * H) * 3 := mul_le_mul hN h2 (norm_nonneg _) hw
      _ = 3 * (w * H) := by ring
  have hsum : ‖∑ r ∈ Ico 1 l, M r * Ui ^ r‖ ≤ ((l : ℝ) - 1) * (3 * (w * H)) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ r ∈ Ico 1 l, ‖M r * Ui ^ r‖ ≤ 3 * (w * H) := fun r hr => by
      have hr' := mem_Ico.1 hr
      calc ‖M r * Ui ^ r‖ ≤ ‖M r‖ * ‖Ui ^ r‖ := norm_mul_le _ _
        _ ≤ (w * H) * 3 := mul_le_mul (hM r hr'.1 hr'.2) (hpow r hr'.2.le) (norm_nonneg _) hw
        _ = 3 * (w * H) := by ring
    refine (sum_le_sum h1).trans (le_of_eq ?_)
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hl]
    push_cast
    ring
  have hTH : ‖T‖ ≤ D * H := by
    have hD : 0 ≤ D * H ^ p := (norm_nonneg _).trans hT
    have hD' : 0 ≤ D := nonneg_of_mul_nonneg_left hD (pow_pos hH p)
    have hHp : H ^ p ≤ H := by
      calc H ^ p ≤ H ^ 1 := pow_le_pow_of_le_one hH.le hH1 hp
        _ = H := pow_one H
    exact hT.trans (mul_le_mul_of_nonneg_left hHp hD')
  rw [e]
  have h1 := norm_sub_le ((U - 1) - N * U - ∑ r ∈ Ico 1 l, M r * Ui ^ r) T
  have h2 := norm_sub_le ((U - 1) - N * U) (∑ r ∈ Ico 1 l, M r * Ui ^ r)
  have h3 := norm_sub_le (U - 1) (N * U)
  linarith

/-- **(b) The least defect bounds the order** (upper bound). A rule with `‖N‖ ≤ w H`,
`‖M r‖ ≤ w H` (`1 ≤ r < l`) and `‖𝒯‖ ≤ D H^p`, `p ≥ 1`, run from exact starting values over
`K H ≤ T₀`, with `0 < H ≤ 1`, `l H ‖A‖ ≤ 1` and `b H ≤ 1/2`, `b = 3 (‖A‖ + l w) + D`, has
`‖x^k - U^k x_0‖ ≤ 2 D T₀ e^{(‖A‖ + 2 (l + 1) b) T₀} H^{p-1} ‖x_0‖` for `k ≤ K`: order `p - 1`. -/
theorem run_error_le_of_defect (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H w D T₀ : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) {l K p : ℕ} (hl : 1 ≤ l) (hp : 1 ≤ p)
    (hlA : (l : ℝ) * (H * ‖A‖) ≤ 1) (hN : ‖N‖ ≤ w * H)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ w * H)
    (hT : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤ D * H ^ p)
    (hbH : (3 * (‖A‖ + l * w) + D) * H ≤ 1 / 2) (hKT : K * H ≤ T₀) (x0 : E) (x : ℕ → E)
    (hstart : ∀ k < l, x k = (exp (H • A) ^ k) x0)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) (x (k + 1)) = ∑ r ∈ range l, M r (x (k - r))) :
    ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0‖ ≤
      2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * (3 * (‖A‖ + l * w) + D)) * T₀) *
        H ^ (p - 1) * ‖x0‖ := by
  have hw : 0 ≤ w * H := (norm_nonneg _).trans hN
  have hw0 : 0 ≤ w := nonneg_of_mul_nonneg_left hw hH
  have hD : 0 ≤ D := by
    have h := (norm_nonneg _).trans hT
    exact nonneg_of_mul_nonneg_left h (pow_pos hH p)
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hA0 := norm_nonneg A
  have hlw := mul_le_mul_of_nonneg_right hl' hw0
  have hwb : w * H ≤ (3 * (‖A‖ + l * w) + D) * H := by
    refine mul_le_mul_of_nonneg_right ?_ hH.le
    linarith
  have hb : 0 ≤ 3 * (‖A‖ + l * w) + D := by linarith
  exact run_convergence_pow A N M hH hb hbH hl hp hKT (hN.trans hwb)
    (norm_M_zero_sub_one_le A N M hH hH1 hl hp hlA hN hM hT)
    (fun r hr1 hrl => (hM r hr1 hrl).trans hwb) hT x0 x hstart hx

/-- **(b) for the rule with the least defect** (for `p < p^w` the rule that attains `f^w`
has the defect `O(H^p)` and bounded weights, so it is zero-stable and converges with the order
`p - 1`). If some rule of `boundedRules 𝒮 w H` has `‖𝒯‖ ≤ D H^p`, then every rule `ρ'` of the
class with the least defect, run from exact starting values, has
`‖x^k - U^k x_0‖ ≤ 2 D T₀ e^{(‖A‖ + 2 (l + 1) b) T₀} H^{p-1} ‖x_0‖`, `b = 3 (‖A‖ + l w) + D`,
under the hypotheses of `run_error_le_of_defect`. -/
theorem least_defect_run_error_le (A : E →L[ℝ] E) {l : ℕ}
    {𝒮 : Set ((E →L[ℝ] E) × (Fin l → E →L[ℝ] E))} {H w D T₀ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1)
    {K p : ℕ} (hl : 1 ≤ l) (hp : 1 ≤ p) (hlA : (l : ℝ) * (H * ‖A‖) ≤ 1)
    (hbH : (3 * (‖A‖ + l * w) + D) * H ≤ 1 / 2) (hKT : K * H ≤ T₀)
    {ρ : (E →L[ℝ] E) × (Fin l → E →L[ℝ] E)} (hρ : ρ ∈ boundedRules 𝒮 w H)
    (hρD : ‖tupleDefect (exp (H • A)) (exp (-(H • A))) ρ‖ ≤ D * H ^ p)
    {ρ' : (E →L[ℝ] E) × (Fin l → E →L[ℝ] E)} (hρ' : ρ' ∈ boundedRules 𝒮 w H)
    (hmin : ∀ ρ'' ∈ boundedRules 𝒮 w H,
      ‖tupleDefect (exp (H • A)) (exp (-(H • A))) ρ'‖ ≤
        ‖tupleDefect (exp (H • A)) (exp (-(H • A))) ρ''‖)
    (x0 : E) (x : ℕ → E) (hstart : ∀ k < l, x k = (exp (H • A) ^ k) x0)
    (hx : ∀ k, l - 1 ≤ k → k < K →
      (1 - ρ'.1) (x (k + 1)) = ∑ r ∈ range l, tupleM ρ'.2 r (x (k - r))) :
    ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0‖ ≤
      2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * (3 * (‖A‖ + l * w) + D)) * T₀) *
        H ^ (p - 1) * ‖x0‖ := by
  have hM : ∀ r, 1 ≤ r → r < l → ‖tupleM ρ'.2 r‖ ≤ w * H := fun r hr1 hrl => by
    rw [tupleM, dite_eq_left hrl]
    exact hρ'.2.2 ⟨r, hrl⟩ hr1
  exact run_error_le_of_defect A ρ'.1 (tupleM ρ'.2) hH hH1 hl hp hlA hρ'.2.1 hM
    ((hmin ρ hρ).trans hρD) hbH hKT x0 x hstart hx

end Convergence

end CoSimFoundations
