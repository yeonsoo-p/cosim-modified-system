/-
The least error over a run with `l` held samples (the paper, the display `eq:leastrun` and Theorem
`thm:runorder`), for the schemes in which every subsystem runs before all of its partners (the
Jacobi schemes with `l` old samples) with bounded weights.

**Setting**, that of `OrderReached` (section `Order`): the state space splits into subsystems
(`Pr i : E → Es i`, `Em i : Es i → E`, `Σ_i Em i Pr i = 1`; for the lower bound also
`Pr i Em i = 1`, `Pr i Em j = 0`, `‖Pr i‖ ≤ 1`), each driven through its own state and the outputs
`C i` of its partners, `Pr i A = Ai i Pr i + L i C i`; the Jacobi scheme `jacobiM` with the rules
`(Fi i, g i)`; `U = e^{HA}`, `T = 1/(2‖A‖)` or any `T > 0` with `T ‖A‖ ≤ 1/2`, `K = ⌊T/H⌋`.

**The value.** `𝒵_l = hiddenRows`: the maps whose row `i` vanishes on `𝒱_i^0`; `D⁰ = forcedLead`
with row `i` equal to `γ_l a_i A^l = γ_l L_i C_i A^l`; `𝒮` a subspace of start errors (`⊥` for the
values of the monolithic system, `⊤` for any linear start of the form `U^q (1 + H^l S)`);

  `g = min_{Z ∈ 𝒵_l, S ∈ 𝒮} sup_{0≤t≤T} ‖e^{tA} S - Φ_t(D⁰ + Z)‖`        (`leadMax`).

The minimum exists (`exists_least_leadMax`, Step 3: `F` is Lipschitz, `F ≥ ‖S‖` and
`F ≥ T (2 - e^{T‖A‖}) ‖D⁰ + Z‖ - e^{T‖A‖} ‖S‖`; `exists_forall_le_of_lipschitz`).

**Attainment** (`least_memory_attained`, Step 5): the Jacobi scheme with the rules of
`exists_rule_nodeDefect_lead` (row `i` of the leading defect `γ_l L_i C_i A^l + Pr i Z₀`) has
bounded weights and, from the start `U^q (1 + H^l S₀) x_0`, the errors
`‖x^k - U^k x_0‖ ≤ (H^l g + C H^{l+1}) ‖x_0‖`, `k ≤ K` (accumulation, `run_accumulation`).

**Every rule** (`least_memory_le`, Steps 1, 2, 4): every Jacobi scheme with `‖g i r ∘ C i‖ ≤ w H`
(`1 ≤ r < l`) started from `U^q (1 + H^l S) x_0 + O(H^{l+1})`, `S ∈ 𝒮`, `‖S‖ ≤ s`, has relative
errors at least `H^l g - C H^{l+1}` up to `K`, with `C` independent of the rule and of `H`. Rules
with defect at most `M₀ H^{l+1}` (`lower_of_small_defect`): Step 1 (`exists_hiddenRows_defect`,
from `forced_defect_apply`) gives `Z ∈ 𝒵_l` with `T = H^{l+1} (D⁰ + Z) + O(H^{l+2})`, and Step 2
(`run_accumulation`) the error `H^l (e^{kHA} S - Φ_{kH}(D⁰ + Z)) + O(H^{l+1})`. Rules with a larger
defect (`lower_of_large_defect`): the run-order lemma `run_order_fraction` gives
`ε ≥ 0.35 T_K / (b + T_K) ≥ H^l g` for `M₀ = 35 (g⁺ + 1) / T` and small `H`.

`least_memory` puts the three together. Not covered: subsystems that run after some partner (new
samples), and independent maps without bounded weights. Linear starts whose
start errors differ from slot to slot at the order `H^l` are in `LeastRunMemoryStart`.
-/
import CoSimFoundations.LeastRunMemory
import CoSimFoundations.LeastRunMemoryRule
import CoSimFoundations.RunOrderFraction

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

/-! ### The run from any start -/

section StartRun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The run of a scheme without new samples, `x^{k+1} = Σ_{r<l} M r x^{k-r}`, from the starting
values `s 0, …, s (l-1)`. -/
noncomputable def startRun (M : ℕ → E →L[ℝ] E) (l : ℕ) (s : ℕ → E) : ℕ → E
  | k => if h : k < l then s k else
      ∑ r ∈ (range l).attach, M r (startRun M l s (k - 1 - r))
decreasing_by
  have := mem_range.1 r.2
  omega

theorem startRun_of_lt (M : ℕ → E →L[ℝ] E) {l : ℕ} (s : ℕ → E) {k : ℕ} (hk : k < l) :
    startRun M l s k = s k := by
  rw [startRun]
  simp [hk]

theorem startRun_succ (M : ℕ → E →L[ℝ] E) {l : ℕ} (s : ℕ → E) {k : ℕ} (hk : l - 1 ≤ k)
    (hl : 1 ≤ l) : startRun M l s (k + 1) = ∑ r ∈ range l, M r (startRun M l s (k - r)) := by
  rw [startRun]
  simp only [show ¬ k + 1 < l by omega, ↓reduceDIte, Nat.add_sub_cancel]
  exact sum_attach (range l) (fun r => M r (startRun M l s (k - r)))

end StartRun

/-! ### The least value exists (Step 3) -/

section Minimiser

/-- **A function that is Lipschitz and coercive on a subspace of a finite-dimensional space
attains its least value there**: `f v ≤ f v' + L ‖v - v'‖` and `f v ≥ c ‖v‖ - d` on `W`, `c > 0`.
(The form of `exists_forall_le_of_coercive` for any finite-dimensional space.) -/
theorem exists_forall_le_of_lipschitz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (W : Submodule ℝ V) {f : V → ℝ} {L c d : ℝ}
    (hf : ∀ v v', f v ≤ f v' + L * ‖v - v'‖) (hc : 0 < c)
    (hcoer : ∀ v ∈ W, c * ‖v‖ - d ≤ f v) : ∃ v₀ ∈ W, ∀ v ∈ W, f v₀ ≤ f v := by
  have hW : IsClosed (W : Set V) := W.closed_of_finiteDimensional
  have hg : Continuous f := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) fun v v' => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]
    have h1 := hf v v'
    have h2 := hf v' v
    rw [norm_sub_rev] at h2
    have h3 : L * ‖v - v'‖ ≤ Real.toNNReal L * ‖v - v'‖ :=
      mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _)
    rw [abs_le]
    constructor <;> linarith
  have hf0 : c * ‖(0 : V)‖ - d ≤ f 0 := hcoer 0 W.zero_mem
  rw [norm_zero, mul_zero, zero_sub] at hf0
  set R := (f 0 + d) / c with hR
  have hR0 : 0 ≤ R := div_nonneg (by linarith) hc.le
  have hK : IsCompact ((W : Set V) ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : V) R).inter_left hW
  have hne : ((W : Set V) ∩ Metric.closedBall 0 R).Nonempty :=
    ⟨0, W.zero_mem, Metric.mem_closedBall_self hR0⟩
  obtain ⟨v₀, ⟨hv₀W, -⟩, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
  refine ⟨v₀, hv₀W, fun v hv => ?_⟩
  by_cases hvR : ‖v‖ ≤ R
  · exact hmin ⟨hv, by rw [Metric.mem_closedBall, dist_zero_right]; exact hvR⟩
  · have h : f v₀ ≤ f 0 := hmin ⟨W.zero_mem, Metric.mem_closedBall_self hR0⟩
    have h2 := hcoer v hv
    have h3 : c * R < c * ‖v‖ := mul_lt_mul_of_pos_left (lt_of_not_ge hvR) hc
    have h4 : c * R = f 0 + d := by
      rw [hR]
      field_simp
    linarith

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

/-- **The least leading error over a run is attained**: for `0 < T` with
`T ‖a‖ ≤ 1/2`, subspaces `W` (the rows) and `𝒮` (the start errors) and any `D⁰`, the function
`(Z, S) ↦ F(S, D⁰ + Z) = sup_{0≤t≤T} ‖e^{ta} S - Φ_t(D⁰ + Z)‖` has a least value on `W × 𝒮`. It
is Lipschitz, `F ≥ ‖S‖` and `F ≥ T (2 - e^{T‖a‖}) ‖D⁰ + Z‖ - e^{T‖a‖} ‖S‖`. -/
theorem exists_least_leadMax (h1 : ‖(1 : 𝔸)‖ ≤ 1) (a D0 : 𝔸) (W 𝒮 : Submodule ℝ 𝔸) {T : ℝ}
    (hT : 0 < T) (hTa : T * ‖a‖ ≤ 1 / 2) :
    ∃ Z₀ ∈ W, ∃ S₀ ∈ 𝒮, ∀ Z ∈ W, ∀ S ∈ 𝒮,
      leadMax a S₀ (D0 + Z₀) T ≤ leadMax a S (D0 + Z) T := by
  set E := Real.exp (T * ‖a‖) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hE2 : E < 2 := lt_of_le_of_lt (Real.exp_le_exp.2 hTa) exp_half_lt_two
  set c₀ := T * (2 - E) with hc₀
  have hc₀0 : 0 < c₀ := mul_pos hT (by linarith)
  have hc : 0 < min (c₀ / (1 + E)) 1 := lt_min (div_pos hc₀0 (by linarith)) one_pos
  set f : 𝔸 × 𝔸 → ℝ := fun p => leadMax a p.2 (D0 + p.1) T with hf
  have hlip : ∀ p p' : 𝔸 × 𝔸, f p ≤ f p' + E * (1 + T) * ‖p - p'‖ := by
    intro p p'
    have h := leadMax_le_add h1 a p.2 p'.2 (D0 + p.1) (D0 + p'.1) hT.le
    rw [add_sub_add_left_eq_sub] at h
    have h2 : ‖p.2 - p'.2‖ ≤ ‖p - p'‖ := norm_snd_le (p - p')
    have h3 : ‖p.1 - p'.1‖ ≤ ‖p - p'‖ := norm_fst_le (p - p')
    have h4 : E * (‖p.2 - p'.2‖ + T * ‖p.1 - p'.1‖) ≤ E * (1 + T) * ‖p - p'‖ := by
      have h5 : T * ‖p.1 - p'.1‖ ≤ T * ‖p - p'‖ := mul_le_mul_of_nonneg_left h3 hT.le
      have h6 : E * (‖p.2 - p'.2‖ + T * ‖p.1 - p'.1‖) ≤ E * (‖p - p'‖ + T * ‖p - p'‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    simp only [hf]
    linarith
  have hcoer : ∀ p ∈ W.prod 𝒮,
      min (c₀ / (1 + E)) 1 * ‖p‖ - c₀ * ‖D0‖ / (1 + E) ≤ f p := by
    intro p _
    simp only [hf]
    have hs := norm_le_leadMax h1 a p.2 (D0 + p.1) hT.le
    have hm := leadMax_ge h1 a p.2 (D0 + p.1) hT.le
    rw [← hE] at hm
    have h3 : ‖p.1‖ ≤ ‖D0 + p.1‖ + ‖D0‖ := by
      have e : p.1 = (D0 + p.1) - D0 := by abel
      calc ‖p.1‖ = ‖(D0 + p.1) - D0‖ := by rw [← e]
        _ ≤ ‖D0 + p.1‖ + ‖D0‖ := norm_sub_le _ _
    -- `(1 + E) F ≥ c₀ ‖D0 + p.1‖`
    have h4 : c₀ * ‖p.1‖ - c₀ * ‖D0‖ ≤ (1 + E) * leadMax a p.2 (D0 + p.1) T := by
      have h5 : c₀ * ‖p.1‖ ≤ c₀ * (‖D0 + p.1‖ + ‖D0‖) := mul_le_mul_of_nonneg_left h3 hc₀0.le
      have h6 : E * ‖p.2‖ ≤ E * leadMax a p.2 (D0 + p.1) T :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      nlinarith
    have h7 : c₀ / (1 + E) * ‖p.1‖ - c₀ * ‖D0‖ / (1 + E) ≤ leadMax a p.2 (D0 + p.1) T := by
      have hpos : 0 < 1 + E := by linarith
      rw [div_mul_eq_mul_div, ← sub_div, div_le_iff₀ hpos]
      linarith
    have hd : 0 ≤ c₀ * ‖D0‖ / (1 + E) := by positivity
    rw [Prod.norm_def]
    rcases le_total ‖p.1‖ ‖p.2‖ with h | h
    · rw [max_eq_right h]
      have := mul_le_of_le_one_left (norm_nonneg p.2) (min_le_right (c₀ / (1 + E)) 1)
      linarith
    · rw [max_eq_left h]
      have := mul_le_mul_of_nonneg_right (min_le_left (c₀ / (1 + E)) 1) (norm_nonneg p.1)
      linarith
  obtain ⟨p₀, hp₀, hmin⟩ := exists_forall_le_of_lipschitz (W.prod 𝒮) hlip hc hcoer
  exact ⟨p₀.1, (Submodule.mem_prod.1 hp₀).1, p₀.2, (Submodule.mem_prod.1 hp₀).2,
    fun Z hZ S hS => hmin (Z, S) (Submodule.mem_prod.2 ⟨hZ, hS⟩)⟩

end Minimiser

/-! ### The stacked scheme: the rows that vanish on the hidden states -/

section Stacked

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, FiniteDimensional ℝ (Es i)]
  {Gs : ι → Type*} [∀ i, NormedAddCommGroup (Gs i)] [∀ i, NormedSpace ℝ (Gs i)]
  [∀ i, FiniteDimensional ℝ (Gs i)]

/-- **The rows that vanish on the hidden states**, `𝒵_l = {Z : row i of Z vanishes on
𝒱_i^0 for every i}`, `𝒱_i^0 = unseen (Pr i) (C i) A l`. -/
def hiddenRows (Pr : ∀ i, E →L[ℝ] Es i) (C : ∀ i, E →L[ℝ] Gs i) (A : E →L[ℝ] E) (l : ℕ) :
    Submodule ℝ (E →L[ℝ] E) where
  carrier := {Z | ∀ i, ∀ v ∈ unseen (Pr i) (C i) A l, Pr i (Z v) = 0}
  add_mem' := by
    intro Z Z' hZ hZ' i v hv
    simp [hZ i v hv, hZ' i v hv]
  zero_mem' := by
    intro i v _
    simp
  smul_mem' := by
    intro c Z hZ i v hv
    simp [hZ i v hv]

theorem mem_hiddenRows {Pr : ∀ i, E →L[ℝ] Es i} {C : ∀ i, E →L[ℝ] Gs i} {A : E →L[ℝ] E}
    {l : ℕ} {Z : E →L[ℝ] E} :
    Z ∈ hiddenRows Pr C A l ↔ ∀ i, ∀ v ∈ unseen (Pr i) (C i) A l, Pr i (Z v) = 0 :=
  Iff.rfl

/-- **The forced leading defect** `D⁰` (all samples old): row `i` is `γ_l a_i A^l`,
`a_i A^l = L_i C_i A^l` (eq. `eq:multistep`). -/
noncomputable def forcedLead (Em : ∀ i, Es i →L[ℝ] E) (C : ∀ i, E →L[ℝ] Gs i) (A : E →L[ℝ] E)
    (L : ∀ i, Gs i →L[ℝ] Es i) (l : ℕ) : E →L[ℝ] E :=
  ∑ i, Em i ∘L (adamsGamma l • ((L i ∘L C i) ∘L A ^ l))

variable {Pr : ∀ i, E →L[ℝ] Es i} {Em : ∀ i, Es i →L[ℝ] E} {C : ∀ i, E →L[ℝ] Gs i}
  {A : E →L[ℝ] E} {Ai : ∀ i, Es i →L[ℝ] Es i} {L : ∀ i, Gs i →L[ℝ] Es i}

/-- The rows of a stacked map: `Pr i ∘ Σ_j Em j ∘ X j = X i` for a block decomposition. -/
theorem proj_comp_sum_emb (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (X : ∀ j, V →L[ℝ] Es j) (i : ι) :
    Pr i ∘L ∑ j, Em j ∘L X j = X i := by
  rw [ContinuousLinearMap.comp_finsetSum, sum_eq_single i]
  · rw [← ContinuousLinearMap.comp_assoc, hPEi, ContinuousLinearMap.id_comp]
  · intro j _ hji
    rw [← ContinuousLinearMap.comp_assoc, hPE i j (Ne.symm hji), ContinuousLinearMap.zero_comp]
  · intro hi
    exact absurd (mem_univ i) hi

/-- **The defect of the Jacobi scheme against `D⁰ + Σ_i Em i Z_i`, row by row:** if every rule has
`‖𝒯_i - H^{l+1} (γ_l L_i C_i A^l + Z_i)‖ ≤ K_i H^{l+2}`, the stacked defect is within
`(Σ_i ‖Em i‖ K_i) H^{l+2}` of `H^{l+1} (D⁰ + Σ_i Em i Z_i)`. -/
theorem norm_runDefect_jacobiM_sub_le (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i) (H : ℝ) {l : ℕ} (hl : 1 ≤ l)
    (Z : ∀ i, E →L[ℝ] Es i) {K : ι → ℝ}
    (hK : ∀ i, ‖localDefect (Pr i) (Fi i) (g i) (C i) A H l -
      H ^ (l + 1) • (adamsGamma l • ((L i ∘L C i) ∘L A ^ l) + Z i)‖ ≤ K i * H ^ (l + 2)) :
    ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l -
        H ^ (l + 1) • (forcedLead Em C A L l + ∑ i, Em i ∘L Z i)‖ ≤
      (∑ i, ‖Em i‖ * K i) * H ^ (l + 2) := by
  have e : runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l -
      H ^ (l + 1) • (forcedLead Em C A L l + ∑ i, Em i ∘L Z i) =
      ∑ i, Em i ∘L (localDefect (Pr i) (Fi i) (g i) (C i) A H l -
        H ^ (l + 1) • (adamsGamma l • ((L i ∘L C i) ∘L A ^ l) + Z i)) := by
    rw [runDefect_jacobiM hdec Fi g A H hl, forcedLead, ← sum_add_distrib, smul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_add]
  rw [e, sum_mul]
  refine norm_sum_le_of_le _ fun i _ => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK i) (norm_nonneg _)

/-- `Σ_i Em i ∘ Pr i ∘ Z = Z` for a decomposition of the identity. -/
theorem sum_emb_comp_proj_comp (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (Z : E →L[ℝ] E) : ∑ i, Em i ∘L (Pr i ∘L Z) = Z := by
  have h : ∑ i, Em i ∘L (Pr i ∘L Z) = (∑ i, Em i ∘L Pr i) ∘L Z := by
    rw [ContinuousLinearMap.finsetSum_comp]
    exact sum_congr rfl fun i _ => (ContinuousLinearMap.comp_assoc _ _ _).symm
  rw [h, hdec, ContinuousLinearMap.id_comp]

/-- **The least error over a run with `l` held samples is attained** (upper bound). Let the state
space split into subsystems (`Σ_i Em i Pr i = 1`), each driven through its own state and the outputs
of its partners (`Pr i A = Ai i Pr i + L i C i`), `l ≥ 1`, `0 < T`, `T ‖A‖ ≤ 1/2`, and let `𝒮` be
the space of the allowed start errors (`⊥`: the values of the monolithic system; `⊤`: any linear
start). Then `F(Z, S) = sup_{0≤t≤T} ‖e^{tA} S - Φ_t(D⁰ + Z)‖` has a minimiser `(Z₀, S₀)` on
`𝒵_l × 𝒮`, and there are `w, C, H₀` such that for `0 < H ≤ H₀` the Jacobi scheme with `l` old
samples whose rules have bounded weights (`‖Fi i - 1‖, ‖g i r ∘ C i‖ ≤ w H`, all `r < l`) and the
leading defect `D⁰ + Z₀` (`exists_rule_nodeDefect_lead`), started from `x^q = U^q (1 + H^l S₀) x_0`,
has `‖x^k - U^k x_0‖ ≤ (H^l F(Z₀, S₀) + C H^{l+1}) ‖x_0‖` for every `k ≤ ⌊T/H⌋`. -/
theorem least_memory_attained (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) {l : ℕ} (hl : 1 ≤ l)
    (𝒮 : Submodule ℝ (E →L[ℝ] E)) {T : ℝ} (hT : 0 < T) (hTA : T * ‖A‖ ≤ 1 / 2) :
    ∃ Z₀ ∈ hiddenRows Pr C A l, ∃ S₀ ∈ 𝒮,
      (∀ Z ∈ hiddenRows Pr C A l, ∀ S ∈ 𝒮,
        leadMax A S₀ (forcedLead Em C A L l + Z₀) T ≤
          leadMax A S (forcedLead Em C A L l + Z) T) ∧
      ∃ w Cr H₀ : ℝ, 0 ≤ w ∧ 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
        ∃ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
          (∀ i, ‖Fi i - 1‖ ≤ w * H) ∧ (∀ i, ∀ r < l, ‖g i r ∘L C i‖ ≤ w * H) ∧
          ∀ (x0 : E), ∀ k ≤ ⌊T / H⌋₊,
            ‖startRun (jacobiM Pr Em C Fi g) l
                (fun q => (exp (H • A) ^ q * (1 + H ^ l • S₀)) x0) k -
              (exp (H • A) ^ k) x0‖ ≤
              (H ^ l * leadMax A S₀ (forcedLead Em C A L l + Z₀) T + Cr * H ^ (l + 1)) *
                ‖x0‖ := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  obtain ⟨Z₀, hZ₀, S₀, hS₀, hmin⟩ :=
    exists_least_leadMax h1 A (forcedLead Em C A L l) (hiddenRows Pr C A l) 𝒮 hT hTA
  refine ⟨Z₀, hZ₀, S₀, hS₀, hmin, ?_⟩
  have hcard : (leadNodes l).card = l := card_leadNodes l
  have hrule := fun i => exists_rule_nodeDefect_lead (hA i) (leadNodes l)
    (by rw [hcard]; exact hl) (Pr i ∘L Z₀) (fun v hv => hZ₀ i v (by rwa [hcard] at hv))
  choose w K hw0 hK0 hrule using hrule
  choose Fi g hFi hg hTi using hrule
  set W := ∑ i, w i with hW
  have hwW : ∀ i, w i ≤ W := fun i => single_le_sum (fun j _ => hw0 j) (mem_univ i)
  have hW0 : 0 ≤ W := sum_nonneg fun i _ => hw0 i
  set b := ∑ i, ‖Em i‖ * (W * ‖Pr i‖ + W) with hb
  have hb0 : 0 ≤ b := sum_nonneg fun i _ => by positivity
  set c₁ := ∑ i, ‖Em i‖ * K i with hc₁
  set D := forcedLead Em C A L l + Z₀ with hD
  set σ := (l : ℝ) * Real.exp (l * ‖A‖) * ‖D‖ with hσ
  refine ⟨W, leadConst ‖A‖ l b c₁ ‖D‖ ‖S₀‖ σ T, 1 / (1 + ‖A‖ + 2 * b), hW0, by positivity,
    fun H hH hH₀ => ?_⟩
  have hden : 0 < 1 + ‖A‖ + 2 * b := by positivity
  have hHd : H * (1 + ‖A‖ + 2 * b) ≤ 1 := by
    rw [le_div_iff₀ hden] at hH₀
    linarith
  have hA0 := norm_nonneg A
  have hH1 : H ≤ 1 := by nlinarith
  have hx1 : H * ‖A‖ ≤ 1 := by nlinarith
  have hbH : b * H ≤ 1 / 2 := by nlinarith
  set Fi' : ∀ i, Es i →L[ℝ] Es i := fun i => Fi i H hH.le hH1 hx1 with hFi'
  set g' : ∀ i, ℕ → Gs i →L[ℝ] Es i := fun i n => g i H hH.le hH1 hx1 n with hg'
  have hgw : ∀ i, ∀ r < l, ‖g' i r ∘L C i‖ ≤ W * H := fun i r hr =>
    (hg i H hH.le hH1 hx1 r (mem_map.2 ⟨r, mem_range.2 hr, rfl⟩)).trans
      (mul_le_mul_of_nonneg_right (hwW i) hH.le)
  refine ⟨Fi', g', fun i => (hFi i H hH.le hH1 hx1).trans
    (mul_le_mul_of_nonneg_right (hwW i) hH.le), hgw, fun x0 k hk => ?_⟩
  set M := jacobiM Pr Em C Fi' g' with hM
  -- the coefficients of the run class
  have hM0 : ‖M 0 - 1‖ ≤ b * H := by
    refine (norm_jacobiM_zero_sub_one_le hdec _ _).trans ?_
    rw [hb, sum_mul]
    refine sum_le_sum fun i _ => ?_
    have h2 := (hFi i H hH.le hH1 hx1).trans (mul_le_mul_of_nonneg_right (hwW i) hH.le)
    have h3 : ‖Fi' i - 1‖ * ‖Pr i‖ ≤ W * H * ‖Pr i‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 := hgw i 0 (by omega)
    calc ‖Em i‖ * (‖Fi' i - 1‖ * ‖Pr i‖ + ‖g' i 0 ∘L C i‖)
        ≤ ‖Em i‖ * (W * H * ‖Pr i‖ + W * H) := by gcongr
      _ = ‖Em i‖ * (W * ‖Pr i‖ + W) * H := by ring
  have hMr : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H := by
    intro r hr1 hrl
    refine (norm_jacobiM_le _ _ hr1).trans ?_
    rw [hb, sum_mul]
    refine sum_le_sum fun i _ => ?_
    have h2 := hgw i r hrl
    have hP := norm_nonneg (Pr i)
    calc ‖Em i‖ * ‖g' i r ∘L C i‖ ≤ ‖Em i‖ * (W * H) := by gcongr
      _ ≤ ‖Em i‖ * (W * ‖Pr i‖ + W) * H := by
          have : 0 ≤ ‖Em i‖ * (W * ‖Pr i‖) * H := by positivity
          nlinarith
  -- the defect
  have hrow : ∀ i, ‖localDefect (Pr i) (Fi' i) (g' i) (C i) A H l -
      H ^ (l + 1) • (adamsGamma l • ((L i ∘L C i) ∘L A ^ l) + Pr i ∘L Z₀)‖ ≤
      K i * H ^ (l + 2) := by
    intro i
    have e : localDefect (Pr i) (Fi' i) (g' i) (C i) A H l =
        nodeDefect (Pr i) (Fi i H hH.le hH1 hx1) (g i H hH.le hH1 hx1) (C i) A H
          (leadNodes l) := by
      rw [← nodeDefect_leadNodes]
      unfold nodeDefect
      rw [sum_leadNodes, sum_leadNodes]
      simp only [Int.toNat_natCast, hg', hFi']
    have h2 := hTi i H hH.le hH1 hx1
    rw [hcard, nodeGamma_leadNodes] at h2
    rw [e]
    exact h2
  have hTd := norm_runDefect_jacobiM_sub_le hdec Fi' g' H hl (fun i => Pr i ∘L Z₀) hrow
    (L := L)
  rw [sum_emb_comp_proj_comp hdec Z₀] at hTd
  -- the run
  set x : ℕ → E := startRun M l (fun q => (exp (H • A) ^ q * (1 + H ^ l • S₀)) x0) with hx
  have hKT : (⌊T / H⌋₊ : ℝ) * H ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hH.le)
    rwa [le_div_iff₀ hH] at this
  have hrec : ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
      (1 - (0 : E →L[ℝ] E)) (x (k + 1)) = ∑ q ∈ range l, M q (x (k - q)) := by
    intro k hk _
    rw [sub_zero, one_apply_eq_self, hx, startRun_succ _ _ hk hl]
  have hstart : ∀ q < l, ‖x q - (exp (H • A) ^ q) x0 - H ^ l • runLead A S₀ D (q * H) x0‖ ≤
      σ * H ^ (l + 1) * ‖x0‖ := by
    intro q hq
    have hxq : x q = (exp (H • A) ^ q * (1 + H ^ l • S₀)) x0 := startRun_of_lt _ _ hq
    have h2 := start_lead_le A S₀ D hH.le hH1 le_rfl hq x0 (x q) (σ := 0) (by
      rw [hxq, mul_add, mul_one, mul_smul_comm, _root_.add_apply, _root_.smul_apply]
      simp)
    rw [zero_add] at h2
    exact h2
  have hacc := run_accumulation A 0 M D S₀ hH hH1 hb0 hbH (by positivity) hl hKT
    (by rw [norm_zero]; positivity) hM0 hMr hTd le_rfl le_rfl x0 x hstart hrec
  exact run_le_leadMax A S₀ D hH.le hKT x0 x hacc k hk

end Stacked

/-! ### Every rule: the lower bound (Steps 1 and 4) -/

section LowerHelpers

/-- `‖M 0 - 1‖ ≤ ‖U - 1‖ + Σ_{1≤r<l} ‖M r‖ ‖Ui^r‖ + ‖T‖` for a scheme without new samples:
the current step is the identity up to `O(H)` when the defect is small. -/
theorem norm_sub_one_le_of_runDefect {R : Type*} [NormedRing R] (M : ℕ → R) (U Ui : R) {l : ℕ}
    (hl : 1 ≤ l) :
    ‖M 0 - 1‖ ≤ ‖U - 1‖ + ∑ r ∈ Ico 1 l, ‖M r‖ * ‖Ui ^ r‖ + ‖runDefect 0 M U Ui l‖ := by
  have e : M 0 - 1 = (U - 1) - ∑ r ∈ Ico 1 l, M r * Ui ^ r - runDefect 0 M U Ui l := by
    rw [runDefect, sub_zero, one_mul, range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (by omega : 0 < l), pow_zero, mul_one]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add_left ((norm_sub_le _ _).trans
    (add_le_add_right ((norm_sum_le _ _).trans (sum_le_sum fun r _ => norm_mul_le _ _)) _)) _)

theorem leadLip_le {α s s' m m' T : ℝ} (hα : 0 ≤ α) (hT : 0 ≤ T) (hs : s ≤ s') (hm : m ≤ m') :
    leadLip α s m T ≤ leadLip α s' m' T := by
  unfold leadLip
  have : 0 ≤ 1 + T * α := by positivity
  gcongr

end LowerHelpers

section Lower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, FiniteDimensional ℝ (Es i)]
  {Gs : ι → Type*} [∀ i, NormedAddCommGroup (Gs i)] [∀ i, NormedSpace ℝ (Gs i)]
  [∀ i, FiniteDimensional ℝ (Gs i)]
  {Pr : ∀ i, E →L[ℝ] Es i} {Em : ∀ i, Es i →L[ℝ] E} {C : ∀ i, E →L[ℝ] Gs i}
  {A : E →L[ℝ] E} {Ai : ∀ i, Es i →L[ℝ] Es i} {L : ∀ i, Gs i →L[ℝ] Es i}

/-- **The stacked defect** (case (ii), every subsystem runs before all of its
partners, bounded weights). If the defect of the Jacobi scheme is at most `M₀ H^{l+1}`, there is
a `Z` in `𝒵_l` with `‖Z‖ ≤ 2 Σ_i ‖Em i‖ (M₀ + ‖L_i C_i A^l‖)` and
`‖T - H^{l+1} (D⁰ + Z)‖ ≤ (Σ_i ‖Em i‖ κ) H^{l+2}`,
`κ = b_l ‖A‖ M₀ + C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}`: `T / H^{l+1}` lies within `O(H)` of
`D⁰ + 𝒵_l`. -/
theorem exists_hiddenRows_defect (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i) {H w M₀ : ℝ} (hH : 0 < H)
    (hw0 : 0 ≤ w) (hx1 : H * ‖A‖ ≤ 1) {l : ℕ} (hl : 1 ≤ l)
    (hw : ∀ i r, 1 ≤ r → r < l → ‖g i r ∘L C i‖ ≤ w * H)
    (hT : ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l‖ ≤
      M₀ * H ^ (l + 1)) :
    ∃ Z ∈ hiddenRows Pr C A l,
      ‖Z‖ ≤ ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖)) ∧
      ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l -
          H ^ (l + 1) • (forcedLead Em C A L l + Z)‖ ≤
        (∑ i, ‖Em i‖ * (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
          memC2 l * w * ‖A‖ ^ (l + 1))) * H ^ (l + 2) := by
  set Td := runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l with hTd
  have hHl : 0 < H ^ (l + 1) := by positivity
  have hM₀ : 0 ≤ M₀ := by
    have h := (norm_nonneg _).trans hT
    exact nonneg_of_mul_nonneg_left h hHl
  have hrowT : ∀ i, Pr i ∘L Td = localDefect (Pr i) (Fi i) (g i) (C i) A H l := fun i => by
    rw [hTd, runDefect_jacobiM hdec Fi g A H hl]
    exact proj_comp_sum_emb hPEi hPE (fun j => localDefect (Pr j) (Fi j) (g j) (C j) A H l) i
  have hTi : ∀ i, ‖localDefect (Pr i) (Fi i) (g i) (C i) A H l‖ ≤ M₀ * H ^ (l + 1) :=
    fun i => by
      rw [← hrowT i]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hP i)).trans hT)
  set Q : ι → E →L[ℝ] E := fun i => (unseen (Pr i) (C i) A l).starProjection with hQ
  set Zi : ∀ i, E →L[ℝ] Es i := fun i =>
    ((H ^ (l + 1))⁻¹ • localDefect (Pr i) (Fi i) (g i) (C i) A H l -
      adamsGamma l • ((L i ∘L C i) ∘L A ^ l)) ∘L (ContinuousLinearMap.id ℝ E - Q i) with hZi
  refine ⟨∑ i, Em i ∘L Zi i, ?_, ?_, ?_⟩
  · -- the rows vanish on the hidden states
    intro j v hv
    have h := DFunLike.congr_fun (proj_comp_sum_emb hPEi hPE Zi j) v
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    have hQv : Q j v = v := (Submodule.starProjection_eq_self_iff).2 hv
    simp [hZi, hQv]
  · -- the size of `Z`
    refine norm_sum_le_of_le _ fun i _ => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hQn : ‖ContinuousLinearMap.id ℝ E - Q i‖ ≤ 2 := by
      have h2 : ‖Q i‖ ≤ 1 := Submodule.starProjection_norm_le _
      have h3 : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      linarith [norm_sub_le (ContinuousLinearMap.id ℝ E) (Q i)]
    have hfirst : ‖(H ^ (l + 1))⁻¹ • localDefect (Pr i) (Fi i) (g i) (C i) A H l -
        adamsGamma l • ((L i ∘L C i) ∘L A ^ l)‖ ≤ M₀ + ‖(L i ∘L C i) ∘L A ^ l‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ hHl, mul_comm]
        exact hTi i
      · rw [norm_smul, Real.norm_of_nonneg (adamsGamma_nonneg l)]
        exact mul_le_of_le_one_left (norm_nonneg _) (adamsGamma_le_one l)
    calc ‖(H ^ (l + 1))⁻¹ • localDefect (Pr i) (Fi i) (g i) (C i) A H l -
          adamsGamma l • ((L i ∘L C i) ∘L A ^ l)‖ * ‖ContinuousLinearMap.id ℝ E - Q i‖
        ≤ (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖) * 2 :=
          mul_le_mul hfirst hQn (norm_nonneg _) (by positivity)
      _ = 2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖) := by ring
  · -- the defect row by row
    have hrow : ∀ i, ‖localDefect (Pr i) (Fi i) (g i) (C i) A H l -
        H ^ (l + 1) • (adamsGamma l • ((L i ∘L C i) ∘L A ^ l) + Zi i)‖ ≤
        (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) *
          H ^ (l + 2) := by
      intro i
      set 𝒯 := localDefect (Pr i) (Fi i) (g i) (C i) A H l with h𝒯
      set X := (L i ∘L C i) ∘L A ^ l with hX
      have hZi' : H ^ (l + 1) • Zi i =
          (𝒯 - (H ^ (l + 1) * adamsGamma l) • X) ∘L (ContinuousLinearMap.id ℝ E - Q i) := by
        simp only [hZi]
        rw [← ContinuousLinearMap.smul_comp, smul_sub, smul_smul, smul_smul,
          mul_inv_cancel₀ hHl.ne', one_smul]
      have hop : 𝒯 - H ^ (l + 1) • (adamsGamma l • X + Zi i) =
          (𝒯 - (H ^ (l + 1) * adamsGamma l) • X) ∘L Q i := by
        rw [smul_add, hZi', smul_smul, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.comp_id]
        abel
      rw [hop]
      have hκ0 : 0 ≤ (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
          memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) := by
        have := memB_nonneg l
        have := memC1_nonneg l
        have := memC2_nonneg l
        positivity
      refine ContinuousLinearMap.opNorm_le_bound _ hκ0 fun v => ?_
      have hu : Q i v ∈ unseen (Pr i) (C i) A l := Submodule.starProjection_apply_mem _ v
      have hc := coupling_pow_apply_of_mem (hA i) hu
      have hv : ((𝒯 - (H ^ (l + 1) * adamsGamma l) • X) ∘L Q i) v =
          𝒯 (Q i v) - (adamsGamma l * H ^ (l + 1)) • Pr i ((A ^ (l + 1)) (Q i v)) := by
        simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, _root_.smul_apply, hX]
        rw [hc, mul_comm]
      rw [hv]
      have hf := forced_defect_apply (hA i) (hP i) (Fi i) (g i) hH.le hw0 hx1 hl (hw i) hu
      rw [← h𝒯] at hf
      have hQv : ‖Q i v‖ ≤ ‖v‖ := by
        have h2 := (Q i).le_opNorm v
        have h3 : ‖Q i‖ ≤ 1 := Submodule.starProjection_norm_le _
        nlinarith [norm_nonneg v]
      have hB : memB l * (H * ‖A‖) * ‖𝒯‖ ≤ memB l * ‖A‖ * M₀ * H ^ (l + 2) := by
        have h2 := mul_le_mul_of_nonneg_left (hTi i) (by
          have := memB_nonneg l
          positivity : 0 ≤ memB l * (H * ‖A‖))
        calc memB l * (H * ‖A‖) * ‖𝒯‖ ≤ memB l * (H * ‖A‖) * (M₀ * H ^ (l + 1)) := h2
          _ = memB l * ‖A‖ * M₀ * H ^ (l + 2) := by ring
      have h4 : memB l * (H * ‖A‖) * ‖𝒯‖ +
          (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) ≤
          (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) *
            H ^ (l + 2) := by
        nlinarith
      refine hf.trans ((mul_le_mul h4 hQv (norm_nonneg _) hκ0))
    exact norm_runDefect_jacobiM_sub_le hdec Fi g H hl Zi hrow

/-- **Step 4, rules with a large defect** (the run-order lemma). Let `E ≠ 0` be a Banach space,
`0 < H ≤ 1`, `0 < T`, `T ‖A‖ ≤ 1/2`, `2 l H ≤ T`, `gp ≥ 0` with `(gp + 1) H ≤ 0.175`, and a scheme
without new samples with `‖M r‖ ≤ m̄` (`1 ≤ r < l`), `1.42 m̄ l² ≤ 0.35`, whose defect exceeds
`M₀ H^{l+1}`, `M₀ = 35 (gp + 1) / T`. If `δ` bounds the relative errors of all runs up to
`⌊T/H⌋`, then `δ ≥ H^l gp`. -/
theorem lower_of_large_defect {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] [Nontrivial E'] (A : E' →L[ℝ] E') (M : ℕ → E' →L[ℝ] E')
    {H T gp mbar δ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hT : 0 < T) (hTA : T * ‖A‖ ≤ 1 / 2)
    {l : ℕ} (hl : 1 ≤ l) (hlH : 2 * l * H ≤ T) (hgp : 0 ≤ gp) (hgH : (gp + 1) * H ≤ 0.175)
    (hm0 : 0 ≤ mbar) (hm : 1.42 * mbar * (l : ℝ) ^ 2 ≤ 0.35)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar)
    (hbig : 35 * (gp + 1) / T * H ^ (l + 1) <
      ‖runDefect 0 M (exp (H • A)) (exp (-(H • A))) l‖)
    (x : E' → ℕ → E')
    (hx : ∀ x0, ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
      x x0 (k + 1) = ∑ q ∈ range l, M q (x x0 (k - q)))
    (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊T / H⌋₊, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    H ^ l * gp ≤ δ := by
  have hα0 := norm_nonneg A
  have hlpos : (1 : ℝ) ≤ l := by exact_mod_cast hl
  set K := ⌊T / H⌋₊ with hK
  have hKT : (K : ℝ) * H ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hH.le)
    rwa [le_div_iff₀ hH] at this
  have hK1 : T < ((K : ℝ) + 1) * H := by
    have := Nat.lt_floor_add_one (T / H)
    rwa [div_lt_iff₀ hH] at this
  have hx' : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - (0 : E' →L[ℝ] E')) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)) :=
    fun x0 _ k hk hkK => by
      rw [sub_zero, one_apply_eq_self]
      exact hx x0 k hk hkK
  have hlT : (l : ℝ) * H ≤ T := by
    have : 0 ≤ (l : ℝ) * H := by positivity
    linarith
  have hKl : l ≤ K := Nat.le_floor ((le_div_iff₀ hH).2 hlT)
  have hKH : (K : ℝ) * H * ‖A‖ ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hKT hα0).trans hTA
  have hro := run_order_fraction A 0 M hH.le hl hKl hKH (nbar := 0) (by rw [norm_zero])
    (mbar := mbar) hM x hx' hδ
  set Td := runDefect 0 M (exp (H • A)) (exp (-(H • A))) l with hTd
  have e : (1 - (0 : E' →L[ℝ] E')) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r =
      Td := rfl
  rw [e] at hro
  set M₀ := 35 * (gp + 1) / T with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set t := ((K : ℝ) - l + 1) * ‖Td‖ with ht
  set b' := 2.65 * (1 + 0) + 1.42 * mbar * ((l : ℝ) * (l - 1)) with hb'
  set X₀ := T / 2 * M₀ * H ^ l with hX₀
  have hX₀0 : 0 ≤ X₀ := by positivity
  have hKl' : T / 2 ≤ ((K : ℝ) - l + 1) * H := by linarith
  have hX₀t : X₀ ≤ t := by
    have h3 : 0 ≤ ((K : ℝ) - l + 1) := by
      have h4 : 0 < T / 2 := by positivity
      by_contra h5
      have h6 : ((K : ℝ) - l + 1) * H < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h5) hH
      linarith
    calc X₀ = T / 2 * (M₀ * H ^ l) := by rw [hX₀]; ring
      _ ≤ ((K : ℝ) - l + 1) * H * (M₀ * H ^ l) :=
          mul_le_mul_of_nonneg_right hKl' (by positivity)
      _ = ((K : ℝ) - l + 1) * (M₀ * H ^ (l + 1)) := by ring
      _ ≤ ((K : ℝ) - l + 1) * ‖Td‖ := mul_le_mul_of_nonneg_left hbig.le h3
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by linarith
  have hb'pos : 0 < b' := by
    have : 0 ≤ 1.42 * mbar * ((l : ℝ) * (l - 1)) := by positivity
    rw [hb']
    linarith
  have hb'3 : b' ≤ 3 := by
    have h2 : (l : ℝ) * (l - 1) ≤ (l : ℝ) ^ 2 := by nlinarith
    have h3 : 1.42 * mbar * ((l : ℝ) * (l - 1)) ≤ 1.42 * mbar * (l : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hb']
    linarith
  have hmono : 0.35 * X₀ / (b' + X₀) ≤ 0.35 * t / (b' + t) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h2 := mul_le_mul_of_nonneg_left hX₀t hb'pos.le
    have e1 : 0.35 * X₀ * (b' + t) = 0.35 * (b' * X₀) + 0.35 * (X₀ * t) := by ring
    have e2 : 0.35 * t * (b' + X₀) = 0.35 * (b' * t) + 0.35 * (X₀ * t) := by ring
    rw [e1, e2]
    linarith
  have hHl : H ^ l ≤ H := pow_le_of_le_one hH.le hH1 (by omega)
  have hHl0 : 0 ≤ H ^ l := by positivity
  have hkey : H ^ l * gp ≤ 0.35 * X₀ / (b' + X₀) := by
    rw [le_div_iff₀ (by linarith)]
    have h3 : H ^ l * gp ≤ H * gp := mul_le_mul_of_nonneg_right hHl hgp
    have e0 : (gp + 1) * H = H * gp + H := by ring
    have h2 : H ^ l * gp ≤ 0.175 := by linarith
    have hX₀' : X₀ = 35 / 2 * (gp + 1) * H ^ l := by
      rw [hX₀, hM₀]
      field_simp
    have hgl := mul_nonneg hHl0 hgp
    have h4 : H ^ l * gp * b' ≤ H ^ l * gp * 3 := mul_le_mul_of_nonneg_left hb'3 hgl
    have h5 : H ^ l * gp * X₀ ≤ 0.175 * X₀ := mul_le_mul_of_nonneg_right h2 hX₀0
    have h6 : 3 * (H ^ l * gp) ≤ 0.175 * X₀ := by
      rw [hX₀']
      have e3 : 0.175 * (35 / 2 * (gp + 1) * H ^ l) = 3.0625 * (H ^ l * gp) + 3.0625 * H ^ l := by
        ring
      rw [e3]
      linarith
    have e4 : H ^ l * gp * (b' + X₀) = H ^ l * gp * b' + H ^ l * gp * X₀ := by ring
    rw [e4]
    linarith
  linarith


/-- **The run class of a Jacobi rule with a small defect** (Step 1 and the coefficients of Step 2,
all samples old, bounded weights). If the defect is at most `M₀ H^{l+1}`, there is `Z ∈ 𝒵_l` with
`‖D⁰ + Z‖ ≤ δ_b`, `‖T - H^{l+1} (D⁰ + Z)‖ ≤ c₁ H^{l+2}`, and the coefficients satisfy
`‖M 0 - 1‖, ‖M r‖ ≤ b H` (`1 ≤ r < l`) for every `b` above
`‖A‖ e^{‖A‖} + l W w e^{l ‖A‖} + M₀ + W w`, `W = Σ_i ‖Em i‖`. -/
theorem small_defect_class (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) {w M₀ b H : ℝ} (hw : 0 ≤ w) (hM₀ : 0 ≤ M₀) (hH : 0 < H) (hH1 : H ≤ 1)
    (hx1 : H * ‖A‖ ≤ 1)
    (hb : ‖A‖ * Real.exp ‖A‖ + l * ((∑ i, ‖Em i‖) * w) * Real.exp (l * ‖A‖) + M₀ +
      (∑ i, ‖Em i‖) * w ≤ b)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i)
    (hg : ∀ i r, 1 ≤ r → r < l → ‖g i r ∘L C i‖ ≤ w * H)
    (hsmall : ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l‖ ≤
      M₀ * H ^ (l + 1)) :
    ∃ Z ∈ hiddenRows Pr C A l,
      ‖forcedLead Em C A L l + Z‖ ≤
        ‖forcedLead Em C A L l‖ + ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖)) ∧
      ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l -
          H ^ (l + 1) • (forcedLead Em C A L l + Z)‖ ≤
        (∑ i, ‖Em i‖ * (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
          memC2 l * w * ‖A‖ ^ (l + 1))) * H ^ (l + 2) ∧
      ‖jacobiM Pr Em C Fi g 0 - 1‖ ≤ b * H ∧
      ∀ r, 1 ≤ r → r < l → ‖jacobiM Pr Em C Fi g r‖ ≤ b * H := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hα0 := norm_nonneg A
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ i, ‖Em i‖ := ⟨_, rfl⟩
  rw [← hW] at hb
  have hW0 : 0 ≤ W := by rw [hW]; exact sum_nonneg fun i _ => norm_nonneg _
  obtain ⟨Z, hZ, hZn, hTZ⟩ := exists_hiddenRows_defect hdec hPEi hPE hA hP Fi g hH hw hx1 hl
    hg hsmall (L := L)
  refine ⟨Z, hZ, (norm_add_le _ _).trans (add_le_add le_rfl hZn), hTZ, ?_⟩
  obtain ⟨M, hM⟩ : ∃ M, M = jacobiM Pr Em C Fi g := ⟨_, rfl⟩
  rw [← hM] at hsmall ⊢
  have hMr : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ W * w * H := by
    intro r hr1 hrl
    rw [hM]
    refine (norm_jacobiM_le _ _ hr1).trans ?_
    rw [hW, sum_mul, sum_mul]
    refine sum_le_sum fun i _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg i r hr1 hrl) (norm_nonneg _)
  refine ⟨?_, fun r h1r hrl => (hMr r h1r hrl).trans (mul_le_mul_of_nonneg_right (by
      have : 0 ≤ ‖A‖ * Real.exp ‖A‖ + l * (W * w) * Real.exp (l * ‖A‖) + M₀ := by positivity
      linarith) hH.le)⟩
  refine (norm_sub_one_le_of_runDefect M (exp (H • A)) (exp (-(H • A))) hl).trans ?_
  have hU : ‖exp (H • A) - 1‖ ≤ ‖A‖ * Real.exp ‖A‖ * H := by
    refine (norm_exp_sub_one_le_exp_norm (H • A)).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hH.le]
    have h2 := exp_sub_one_le_mul_exp (H * ‖A‖)
    have h3 : Real.exp (H * ‖A‖) ≤ Real.exp ‖A‖ :=
      Real.exp_le_exp.2 (mul_le_of_le_one_left hα0 hH1)
    calc Real.exp (H * ‖A‖) - 1 ≤ H * ‖A‖ * Real.exp (H * ‖A‖) := h2
      _ ≤ H * ‖A‖ * Real.exp ‖A‖ := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ‖A‖ * Real.exp ‖A‖ * H := by ring
  have hsum : ∑ r ∈ Ico 1 l, ‖M r‖ * ‖exp (-(H • A)) ^ r‖ ≤
      l * (W * w) * Real.exp (l * ‖A‖) * H := by
    have h2 : ∀ r ∈ Ico 1 l, ‖M r‖ * ‖exp (-(H • A)) ^ r‖ ≤
        W * w * H * Real.exp (l * ‖A‖) := by
      intro r hr
      have hr' := mem_Ico.1 hr
      have h3 := norm_exp_neg_pow_le h1 A hH.le r
      have h4 : Real.exp (r * H * ‖A‖) ≤ Real.exp (l * ‖A‖) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hα0)
        have h5 : (r : ℝ) ≤ l := by exact_mod_cast hr'.2.le
        calc (r : ℝ) * H ≤ r * 1 := mul_le_mul_of_nonneg_left hH1 (Nat.cast_nonneg r)
          _ ≤ l := by rw [mul_one]; exact h5
      exact mul_le_mul (hMr r hr'.1 hr'.2) (h3.trans h4) (norm_nonneg _) (by positivity)
    refine (sum_le_sum h2).trans ?_
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    have h5 : ((l - 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast Nat.sub_le l 1
    have h6 : 0 ≤ W * w * H * Real.exp (l * ‖A‖) := by positivity
    calc ((l - 1 : ℕ) : ℝ) * (W * w * H * Real.exp (l * ‖A‖))
        ≤ l * (W * w * H * Real.exp (l * ‖A‖)) := mul_le_mul_of_nonneg_right h5 h6
      _ = l * (W * w) * Real.exp (l * ‖A‖) * H := by ring
  have hTd1 : ‖runDefect 0 M (exp (H • A)) (exp (-(H • A))) l‖ ≤ M₀ * H := by
    refine hsmall.trans (mul_le_mul_of_nonneg_left ?_ hM₀)
    simpa using pow_le_pow_of_le_one hH.le hH1 (by omega : 1 ≤ l + 1)
  have h7 := mul_le_mul_of_nonneg_right hb hH.le
  have h8 : 0 ≤ W * w * H := by positivity
  have e : (‖A‖ * Real.exp ‖A‖ + l * (W * w) * Real.exp (l * ‖A‖) + M₀ + W * w) * H =
      ‖A‖ * Real.exp ‖A‖ * H + l * (W * w) * Real.exp (l * ‖A‖) * H + M₀ * H + W * w * H := by
    ring
  linarith

/-- **Steps 1 and 2 for a rule with a small defect** (all samples old, bounded weights): if the
defect of the Jacobi scheme is at most `M₀ H^{l+1}`, the relative errors are at least
`H^l g₀ - C H^{l+1}`, with `C` from the accumulation (`leadConst`) and the grid (`leadLip`). -/
theorem lower_of_small_defect [Nontrivial E]
    (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) (𝒮 : Submodule ℝ (E →L[ℝ] E)) {T : ℝ} (hT : 0 < T) {g₀ : ℝ}
    (hg₀ : ∀ Z ∈ hiddenRows Pr C A l, ∀ S ∈ 𝒮,
      g₀ ≤ leadMax A S (forcedLead Em C A L l + Z) T)
    {w s σ M₀ b H : ℝ} (hw : 0 ≤ w) (hs : 0 ≤ s) (hσ : 0 ≤ σ) (hM₀ : 0 ≤ M₀) (hH : 0 < H)
    (hH1 : H ≤ 1) (hx1 : H * ‖A‖ ≤ 1) (hbH : b * H ≤ 1 / 2)
    (hb : ‖A‖ * Real.exp ‖A‖ + l * ((∑ i, ‖Em i‖) * w) * Real.exp (l * ‖A‖) + M₀ +
      (∑ i, ‖Em i‖) * w ≤ b)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i)
    (hg : ∀ i r, 1 ≤ r → r < l → ‖g i r ∘L C i‖ ≤ w * H)
    (hsmall : ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l‖ ≤
      M₀ * H ^ (l + 1))
    (S : E →L[ℝ] E) (hS : S ∈ 𝒮) (hSs : ‖S‖ ≤ s) (x : E → ℕ → E)
    (hstart : ∀ x0, ∀ q < l,
      ‖x x0 q - (exp (H • A) ^ q) x0 - H ^ l • (exp (H • A) ^ q * S) x0‖ ≤
        σ * H ^ (l + 1) * ‖x0‖)
    (hx : ∀ x0, ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
      x x0 (k + 1) = ∑ q ∈ range l, jacobiM Pr Em C Fi g q (x x0 (k - q)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊T / H⌋₊, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    H ^ l * g₀ -
      (leadConst ‖A‖ l b
          (∑ i, ‖Em i‖ * (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
            memC2 l * w * ‖A‖ ^ (l + 1)))
          (‖forcedLead Em C A L l‖ + ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖))) s
          (σ + l * Real.exp (l * ‖A‖) *
            (‖forcedLead Em C A L l‖ + ∑ i, ‖Em i‖ * (2 * (M₀ + ‖(L i ∘L C i) ∘L A ^ l‖))))
          T +
        leadLip ‖A‖ s
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
  have hσ'0 : 0 ≤ σ + l * Real.exp (l * ‖A‖) * δb := by positivity
  have hb0 : 0 ≤ b := le_trans (by positivity) hb
  obtain ⟨D, hD⟩ : ∃ D, D = forcedLead Em C A L l + Z := ⟨_, rfl⟩
  rw [← hD] at hTZ hDn
  obtain ⟨M, hM⟩ : ∃ M, M = jacobiM Pr Em C Fi g := ⟨_, rfl⟩
  rw [← hM] at hTZ hx hM0 hMr
  have hKT : (⌊T / H⌋₊ : ℝ) * H ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hH.le)
    rwa [le_div_iff₀ hH] at this
  have hacc : ∀ x0, ∀ k ≤ ⌊T / H⌋₊,
      ‖x x0 k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0‖ ≤
        leadConst ‖A‖ l b (∑ i, ‖Em i‖ * κ) δb s (σ + l * Real.exp (l * ‖A‖) * δb) T *
          H ^ (l + 1) * ‖x0‖ := by
    intro x0
    have hstart' : ∀ q < l,
        ‖x x0 q - (exp (H • A) ^ q) x0 - H ^ l • runLead A S D (q * H) x0‖ ≤
          (σ + l * Real.exp (l * ‖A‖) * δb) * H ^ (l + 1) * ‖x0‖ := fun q hq =>
      start_lead_le A S D hH.le hH1 hDn hq x0 (x x0 q) (hstart x0 q hq)
    have hrec : ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
        (1 - (0 : E →L[ℝ] E)) (x x0 (k + 1)) = ∑ q ∈ range l, M q (x x0 (k - q)) :=
      fun k hk hkK => by
        rw [sub_zero, one_apply_eq_self]
        exact hx x0 k hk hkK
    exact run_accumulation A 0 M D S hH hH1 hb0 hbH hσ'0 hl hKT
      (by rw [norm_zero]; positivity) hM0 hMr hTZ hDn hSs x0 (x x0) hstart' hrec
  have hlow := leadMax_le_of_runs A S D hH
    (leadConst_nonneg l hα0 hb0 hc₁0 hδb0 hs hσ'0 hT.le) (l := l) (j := 0)
    (by simp [hT.le]) x (fun x0 k _ hk => hacc x0 k hk) hδ
  have hLip : leadLip ‖A‖ ‖S‖ ‖D‖ T ≤ leadLip ‖A‖ s δb T := leadLip_le hα0 hT.le hSs hDn
  have hgZ := hg₀ Z hZ S hS
  rw [← hD] at hgZ
  have h2 : H ^ l * g₀ ≤ H ^ l * leadMax A S D T :=
    mul_le_mul_of_nonneg_left hgZ (by positivity)
  have h3 : (leadConst ‖A‖ l b (∑ i, ‖Em i‖ * κ) δb s (σ + l * Real.exp (l * ‖A‖) * δb) T +
      ((0 : ℕ) + 1) * leadLip ‖A‖ ‖S‖ ‖D‖ T) * H ^ (l + 1) ≤
      (leadConst ‖A‖ l b (∑ i, ‖Em i‖ * κ) δb s (σ + l * Real.exp (l * ‖A‖) * δb) T +
        leadLip ‖A‖ s δb T) * H ^ (l + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    push_cast
    linarith
  linarith

/-- **The least error over a run with `l` held samples, every rule** (lower bound), for the class in
which every subsystem runs before all of its partners (the Jacobi schemes with `l` old samples) and
the weights of the past samples are bounded, `‖g i r ∘ C i‖ ≤ w H` (`1 ≤ r < l`); `Fi i` and `g i 0`
are arbitrary. Let the state space split into blocks (`Σ_i Em i Pr i = 1`, `Pr i Em i = 1`,
`Pr i Em j = 0` for `i ≠ j`, `‖Pr i‖ ≤ 1`), `0 < T`, `T ‖A‖ ≤ 1/2`, `𝒮` the space of the allowed
start errors, and `g₀` a lower bound of `F(Z, S) = sup_{0≤t≤T} ‖e^{tA} S - Φ_t(D⁰ + Z)‖` on
`𝒵_l × 𝒮`. For every `w, s, σ ≥ 0` there are `C, H₀` such that for `0 < H ≤ H₀`, every such rule,
every `S ∈ 𝒮` with `‖S‖ ≤ s` and every run from a start with
`‖x^q - U^q (1 + H^l S) x_0‖ ≤ σ H^{l+1} ‖x_0‖` (`q < l`): if `δ` bounds the relative errors
`‖x^k - U^k x_0‖ / ‖x_0‖` for `k ≤ ⌊T/H⌋`, then `δ ≥ H^l g₀ - C H^{l+1}`. The constants do not
depend on the rule or on `H`. Rules with a defect above `M₀ H^{l+1}` are bounded through the
run-order lemma (`lower_of_large_defect`). -/
theorem least_memory_le [Nontrivial E]
    (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) (𝒮 : Submodule ℝ (E →L[ℝ] E)) {T : ℝ} (hT : 0 < T) (hTA : T * ‖A‖ ≤ 1 / 2)
    {g₀ : ℝ}
    (hg₀ : ∀ Z ∈ hiddenRows Pr C A l, ∀ S ∈ 𝒮,
      g₀ ≤ leadMax A S (forcedLead Em C A L l + Z) T)
    {w s σ : ℝ} (hw : 0 ≤ w) (hs : 0 ≤ s) (hσ : 0 ≤ σ) :
    ∃ Cl H₀ : ℝ, 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
      ∀ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
      (∀ i r, 1 ≤ r → r < l → ‖g i r ∘L C i‖ ≤ w * H) →
      ∀ S ∈ 𝒮, ‖S‖ ≤ s → ∀ x : E → ℕ → E,
      (∀ x0, ∀ q < l, ‖x x0 q - (exp (H • A) ^ q) x0 - H ^ l • (exp (H • A) ^ q * S) x0‖ ≤
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
  obtain ⟨Cl, hCl⟩ : ∃ Cl, Cl = leadConst ‖A‖ l b
      (∑ i, ‖Em i‖ * (memB l * ‖A‖ * M₀ + memC1 l * ‖A‖ ^ (l + 2) +
        memC2 l * w * ‖A‖ ^ (l + 1))) δb s (σ + l * Real.exp (l * ‖A‖) * δb) T +
      leadLip ‖A‖ s δb T := ⟨_, rfl⟩
  have hCl0 : 0 ≤ Cl := by
    have := memB_nonneg l
    have := memC1_nonneg l
    have := memC2_nonneg l
    have hδb0 : 0 ≤ δb := by rw [hδb]; positivity
    rw [hCl]
    exact add_nonneg (leadConst_nonneg l hα0 hb0 (sum_nonneg fun i _ => by positivity) hδb0
      hs (by positivity) hT.le) (leadLip_nonneg hα0 hs hδb0 hT.le)
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  refine ⟨Cl, min (min (1 / (1 + ‖A‖ + 2 * b)) (T / (2 * l)))
      (min (0.35 / (1.42 * (W * w) * l ^ 2 + 1)) (0.175 / (gp + 1))),
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)),
    fun H hH hHH₀ Fi g hg S hS hSs x hstart hx δ hδ => ?_⟩
  -- the smallness of `H`
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
  · -- a large defect: the run-order lemma
    have hm : 1.42 * (W * w * H) * (l : ℝ) ^ 2 ≤ 0.35 := by
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
  · -- a small defect: Steps 1 and 2
    have h := lower_of_small_defect hdec hPEi hPE hA hP hl 𝒮 hT hg₀ hw hs hσ hM₀0 hH hH1 hx1
      hbH (by rw [← hW, hb]) Fi g hg hsmall S hS hSs x hstart hx hδ
    rw [← hδb, ← hCl] at h
    exact h

end Lower
/-! ### The least error over a run -/

section Least

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, FiniteDimensional ℝ (Es i)]
  {Gs : ι → Type*} [∀ i, NormedAddCommGroup (Gs i)] [∀ i, NormedSpace ℝ (Gs i)]
  [∀ i, FiniteDimensional ℝ (Gs i)]
  {Pr : ∀ i, E →L[ℝ] Es i} {Em : ∀ i, Es i →L[ℝ] E} {C : ∀ i, E →L[ℝ] Gs i}
  {A : E →L[ℝ] E} {Ai : ∀ i, Es i →L[ℝ] Es i} {L : ∀ i, Gs i →L[ℝ] Es i}

/-- **The least error over a run with `l` held samples** ((a) with `𝒮 = ⊥`, (b) with `𝒮 = ⊤`), for
the schemes in which every subsystem runs before all of its partners, with bounded weights. The
value `g = min_{Z ∈ 𝒵_l, S ∈ 𝒮} sup_{0≤t≤T} ‖e^{tA} S - Φ_t(D⁰ + Z)‖` is attained at some
`(Z₀, S₀)`; some Jacobi scheme with bounded weights, started from `U^q (1 + H^l S₀) x_0`, has
`‖x^k - U^k x_0‖ ≤ (H^l g + C H^{l+1}) ‖x_0‖` for `k ≤ ⌊T/H⌋`; and for every `w, s, σ ≥ 0` every
Jacobi scheme with `‖g i r ∘ C i‖ ≤ w H` (`1 ≤ r < l`), started from `U^q (1 + H^l S) x_0` up to
`σ H^{l+1} ‖x_0‖` with `S ∈ 𝒮`, `‖S‖ ≤ s`, has relative errors whose every upper bound `δ` satisfies
`δ ≥ H^l g - C H^{l+1}`, for `0 < H ≤ H₀`. -/
theorem least_memory [Nontrivial E]
    (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) (𝒮 : Submodule ℝ (E →L[ℝ] E)) {T : ℝ} (hT : 0 < T) (hTA : T * ‖A‖ ≤ 1 / 2) :
    ∃ Z₀ ∈ hiddenRows Pr C A l, ∃ S₀ ∈ 𝒮,
      (∀ Z ∈ hiddenRows Pr C A l, ∀ S ∈ 𝒮,
        leadMax A S₀ (forcedLead Em C A L l + Z₀) T ≤
          leadMax A S (forcedLead Em C A L l + Z) T) ∧
      (∃ w Cr H₀ : ℝ, 0 ≤ w ∧ 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
        ∃ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
          (∀ i, ‖Fi i - 1‖ ≤ w * H) ∧ (∀ i, ∀ r < l, ‖g i r ∘L C i‖ ≤ w * H) ∧
          ∀ (x0 : E), ∀ k ≤ ⌊T / H⌋₊,
            ‖startRun (jacobiM Pr Em C Fi g) l
                (fun q => (exp (H • A) ^ q * (1 + H ^ l • S₀)) x0) k -
              (exp (H • A) ^ k) x0‖ ≤
              (H ^ l * leadMax A S₀ (forcedLead Em C A L l + Z₀) T + Cr * H ^ (l + 1)) *
                ‖x0‖) ∧
      ∀ w s σ : ℝ, 0 ≤ w → 0 ≤ s → 0 ≤ σ →
        ∃ Cl H₀ : ℝ, 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
          ∀ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
          (∀ i r, 1 ≤ r → r < l → ‖g i r ∘L C i‖ ≤ w * H) →
          ∀ S ∈ 𝒮, ‖S‖ ≤ s → ∀ x : E → ℕ → E,
          (∀ x0, ∀ q < l,
            ‖x x0 q - (exp (H • A) ^ q) x0 - H ^ l • (exp (H • A) ^ q * S) x0‖ ≤
              σ * H ^ (l + 1) * ‖x0‖) →
          (∀ x0, ∀ k, l - 1 ≤ k → k < ⌊T / H⌋₊ →
            x x0 (k + 1) = ∑ q ∈ range l, jacobiM Pr Em C Fi g q (x x0 (k - q))) →
          ∀ δ : ℝ,
          (∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊T / H⌋₊, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) →
          H ^ l * leadMax A S₀ (forcedLead Em C A L l + Z₀) T - Cl * H ^ (l + 1) ≤ δ := by
  obtain ⟨Z₀, hZ₀, S₀, hS₀, hmin, hup⟩ := least_memory_attained hdec hA hl 𝒮 hT hTA (L := L)
  exact ⟨Z₀, hZ₀, S₀, hS₀, hmin, hup, fun w s σ hw hs hσ =>
    least_memory_le hdec hPEi hPE hA hP hl 𝒮 hT hTA hmin hw hs hσ⟩

end Least

end CoSimFoundations
