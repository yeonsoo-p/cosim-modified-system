/-
The error over a run with `l` held samples is the accumulated leading defect (the paper, the display
`eq:leastrun` and the class of `OrderReached`).

**Setting**, that of `OrderReached`: the recursion `(1 - N) x^{k+1} = Σ_{q<l} M q x^{k-q}` on a
Banach space `E`, `U = e^{HA}`, the local defect `T = (1 - N) U - Σ_{q<l} M q U^{-q}`
(`runDefect`), and coefficients `‖N‖, ‖M 0 - 1‖, ‖M q‖ ≤ b H` (`1 ≤ q < l`), `b H ≤ 1/2`.

**The leading error** (`runLead`, `leadMax`). With `Φ_t(D) = ∫₀ᵗ e^{(t-s)A} D e^{sA} ds`
(`runPhi`) and a start error `S`,

  `ψ(t) = e^{tA} S - Φ_t(D)`,   `F(S, D) = sup_{0 ≤ t ≤ T} ‖ψ(t)‖`.

`F` is Lipschitz in `(S, D)` (`leadMax_le_add`), `F ≥ ‖S‖` and
`F ≥ T (2 - e^{T‖A‖}) ‖D‖ - e^{T‖A‖} ‖S‖` (`norm_le_leadMax`, `leadMax_ge`), and the grid
`k H`, `k ≥ j`, sees `F` up to `(j + 1) H` times a Lipschitz constant in `t`
(`leadMax_le_of_grid`).

**Zero-stability** (`run_stab_le`): an error `e` with `(1 - N) e_{k+1} = Σ_q M q e_{k-q} + r_k`,
`‖e_k‖ ≤ σ` for `k < l` and `‖r_k‖ ≤ ρ_k` has `‖e_k‖ ≤ (σ + 2 Σ_{j<k} ρ_j) (1 + 2 (l+1) b H)^k`
(the proof of `run_error_le` with a forcing and a start error).

**The residual of the comparison run** (`recResid_leadRun`, `norm_recResid_leadRun_le`). The
comparison run `Y_j = U^j + H^l (U^j S - Φ_{jH}(D))` (`leadRun`) satisfies the recursion up to

  `R_k = T U^k + H^l (T (U^k S - Φ_{kH}) - (1 - N) Φ_H U^k - Σ_q M q U^{-q} Φ_{qH} U^{k-q})`,

an identity from the semigroup law `Φ_{t+h} = e^{hA} Φ_t + Φ_h e^{tA}` (`runPhi_add`); no Taylor
expansion of `ψ` is needed. If `‖T - H^{l+1} D‖ ≤ c₁ H^{l+2}` then `‖R_k‖ ≤ R₀ e^{T₀‖A‖} H^{l+2}`
for `k H ≤ T₀`, `R₀ = leadRes`.

**Accumulation** (`run_accumulation`). If moreover the start has
`‖x^q - U^q x_0 - H^l ψ(qH) x_0‖ ≤ σ H^{l+1} ‖x_0‖` for `q < l` (for instance
`x^q = U^q (1 + H^l S) x_0`, `start_lead_le`), then for `k ≤ K`, `K H ≤ T₀`,

  `‖x^k - U^k x_0 - H^l (e^{kHA} S - Φ_{kH}(D)) x_0‖ ≤ C H^{l+1} ‖x_0‖`,
  `C = (σ + 2 T₀ R₀ e^{T₀‖A‖}) e^{2 (l+1) b T₀}`   (`leadConst`).

**The error over a run** (`run_le_leadMax`, `leadMax_le_of_runs`): hence
`ε_K ≤ H^l F(S, D) + C H^{l+1}` (`K H ≤ T`), and if `δ` bounds the relative errors of all runs
up to `K = ⌊T/H⌋`, `δ ≥ H^l F(S, D) - (C + (j + 1) L) H^{l+1}` (`L = leadLip`), when the
accumulation holds from the step `j` on.
-/
import CoSimFoundations.OrderReached
import CoSimFoundations.LeastRunError

open NormedSpace Finset

namespace CoSimFoundations

section Lead

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The leading error of a run at the time `t`**, `ψ(t) = e^{ta} s - Φ_t(m)`: `s` the start
error, `m` the leading defect. -/
noncomputable def runLead (a s m : 𝔸) (t : ℝ) : 𝔸 := exp (t • a) * s - runPhi a m t

/-- **The largest leading error over `[0, T]`**, `F(s, m) = sup_{0 ≤ t ≤ T} ‖e^{ta} s - Φ_t(m)‖`
(the value `g_l` for `s = 0`). -/
noncomputable def leadMax (a s m : 𝔸) (T : ℝ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) T, ‖runLead a s m t‖

/-- The Lipschitz constant in `t` of the leading error over `[0, T]`:
`e^{T α} (α ‖s‖ + ‖m‖ (1 + T α))`. -/
noncomputable def leadLip (α s m T : ℝ) : ℝ :=
  Real.exp (T * α) * (α * s + m * (1 + T * α))

theorem runLead_zero (a s m : 𝔸) : runLead a s m 0 = s := by
  simp [runLead, runPhi_zero]

theorem runLead_sub (a s s' m m' : 𝔸) (t : ℝ) :
    runLead a (s - s') (m - m') t = runLead a s m t - runLead a s' m' t := by
  simp only [runLead, runPhi_sub, mul_sub]
  abel

theorem leadLip_nonneg {α s m T : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hm : 0 ≤ m) (hT : 0 ≤ T) :
    0 ≤ leadLip α s m T := by
  unfold leadLip
  positivity

variable (h1 : ‖(1 : 𝔸)‖ ≤ 1)
include h1

/-- `‖ψ(t)‖ ≤ e^{tα} (‖s‖ + t ‖m‖)` for `t ≥ 0`. -/
theorem norm_runLead_le (a s m : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖runLead a s m t‖ ≤ Real.exp (t * ‖a‖) * (‖s‖ + t * ‖m‖) := by
  unfold runLead
  have e1 := norm_exp_smul_le' h1 a ht
  have e2 := norm_runPhi_le h1 a m ht
  have e3 : ‖exp (t • a) * s‖ ≤ Real.exp (t * ‖a‖) * ‖s‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right e1 (norm_nonneg _))
  calc ‖exp (t • a) * s - runPhi a m t‖ ≤ ‖exp (t • a) * s‖ + ‖runPhi a m t‖ := norm_sub_le _ _
    _ ≤ Real.exp (t * ‖a‖) * ‖s‖ + t * Real.exp (t * ‖a‖) * ‖m‖ := add_le_add e3 e2
    _ = Real.exp (t * ‖a‖) * (‖s‖ + t * ‖m‖) := by ring

theorem bddAbove_runLead (a s m : 𝔸) (T : ℝ) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => ‖runLead a s m t‖) := by
  refine ⟨Real.exp (T * ‖a‖) * (‖s‖ + T * ‖m‖), ?_⟩
  rintro _ ⟨⟨t, ht0, htT⟩, rfl⟩
  refine (norm_runLead_le h1 a s m ht0).trans ?_
  have := norm_nonneg m
  have := norm_nonneg s
  have := norm_nonneg a
  gcongr

theorem le_leadMax (a s m : 𝔸) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖runLead a s m t‖ ≤ leadMax a s m T :=
  le_ciSup (f := fun t : Set.Icc (0 : ℝ) T => ‖runLead a s m t‖) (bddAbove_runLead h1 a s m T)
    ⟨t, ht0, htT⟩

omit h1 in
theorem leadMax_le (a s m : 𝔸) {T B : ℝ} (hT : 0 ≤ T)
    (h : ∀ t, 0 ≤ t → t ≤ T → ‖runLead a s m t‖ ≤ B) : leadMax a s m T ≤ B := by
  have : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_refl _, hT⟩⟩
  exact ciSup_le fun t => h t t.2.1 t.2.2

/-- **`F` is Lipschitz:** `F(s, m) ≤ F(s', m') + e^{Tα} (‖s - s'‖ + T ‖m - m'‖)`, `T ≥ 0`. -/
theorem leadMax_le_add (a s s' m m' : 𝔸) {T : ℝ} (hT : 0 ≤ T) :
    leadMax a s m T ≤
      leadMax a s' m' T + Real.exp (T * ‖a‖) * (‖s - s'‖ + T * ‖m - m'‖) := by
  refine leadMax_le a s m hT fun t ht0 htT => ?_
  have e : runLead a s m t = runLead a s' m' t + runLead a (s - s') (m - m') t := by
    rw [runLead_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (le_leadMax h1 a s' m' ht0 htT) ?_)
  refine (norm_runLead_le h1 a _ _ ht0).trans ?_
  have := norm_nonneg (s - s')
  have := norm_nonneg (m - m')
  have := norm_nonneg a
  gcongr

/-- **`F` sees the start error:** `‖s‖ ≤ F(s, m)` (at `t = 0`), `T ≥ 0`. -/
theorem norm_le_leadMax (a s m : 𝔸) {T : ℝ} (hT : 0 ≤ T) : ‖s‖ ≤ leadMax a s m T := by
  have h := le_leadMax h1 a s m le_rfl hT
  rwa [runLead_zero] at h

/-- **`F` is coercive in `m`:** `T (2 - e^{Tα}) ‖m‖ - e^{Tα} ‖s‖ ≤ F(s, m)`, `T ≥ 0`. -/
theorem leadMax_ge (a s m : 𝔸) {T : ℝ} (hT : 0 ≤ T) :
    T * (2 - Real.exp (T * ‖a‖)) * ‖m‖ - Real.exp (T * ‖a‖) * ‖s‖ ≤ leadMax a s m T := by
  have h := le_leadMax h1 a s m hT le_rfl
  have h2 := norm_runPhi_ge h1 a m hT
  have h3 : ‖exp (T • a) * s‖ ≤ Real.exp (T * ‖a‖) * ‖s‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_exp_smul_le' h1 a hT)
      (norm_nonneg _))
  have e : runPhi a m T = exp (T • a) * s - runLead a s m T := by
    unfold runLead
    abel
  have h4 := norm_sub_le (exp (T • a) * s) (runLead a s m T)
  rw [← e] at h4
  linarith

/-- **`ψ` is Lipschitz in `t`:** for `t, h ≥ 0`,
`‖ψ(t + h) - ψ(t)‖ ≤ h e^{(h+t)α} (α ‖s‖ + ‖m‖ (1 + t α))`. -/
theorem norm_runLead_add_sub_le (a s m : 𝔸) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    ‖runLead a s m (t + h) - runLead a s m t‖ ≤
      h * Real.exp ((h + t) * ‖a‖) * (‖a‖ * ‖s‖ + ‖m‖ * (1 + t * ‖a‖)) := by
  have ee : exp ((t + h) • a) = exp (h • a) * exp (t • a) := by
    rw [add_comm t h]
    exact exp_add_smul_const a h t
  have e : runLead a s m (t + h) - runLead a s m t =
      (exp (h • a) - 1) * (exp (t • a) * s) - (runPhi a m (t + h) - runPhi a m t) := by
    unfold runLead
    rw [ee]
    noncomm_ring
  rw [e]
  have k1 := norm_exp_smul_sub_one_le' h1 a hh
  have k2 := norm_exp_smul_le' h1 a ht
  have k3 := norm_runPhi_add_sub_le h1 a m ht hh
  have hexp : Real.exp (h * ‖a‖) - 1 ≤ h * ‖a‖ * Real.exp (h * ‖a‖) :=
    exp_sub_one_le_mul_exp _
  have e5 : Real.exp ((h + t) * ‖a‖) = Real.exp (h * ‖a‖) * Real.exp (t * ‖a‖) := by
    rw [← Real.exp_add]
    ring_nf
  have n1 : ‖(exp (h • a) - 1) * (exp (t • a) * s)‖ ≤
      h * ‖a‖ * Real.exp (h * ‖a‖) * (Real.exp (t * ‖a‖) * ‖s‖) :=
    (norm_mul_le _ _).trans (mul_le_mul (k1.trans hexp)
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right k2 (norm_nonneg _)))
      (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  rw [e5]
  rw [e5] at k3
  have e6 : h * (Real.exp (h * ‖a‖) * Real.exp (t * ‖a‖)) *
      (‖a‖ * ‖s‖ + ‖m‖ * (1 + t * ‖a‖)) =
      h * ‖a‖ * Real.exp (h * ‖a‖) * (Real.exp (t * ‖a‖) * ‖s‖) +
        h * (Real.exp (h * ‖a‖) * Real.exp (t * ‖a‖)) * ‖m‖ * (1 + t * ‖a‖) := by ring
  rw [e6]
  exact add_le_add n1 k3

/-- Two times of `[0, T]` see `ψ` within `|v - u|` times `leadLip`. -/
theorem norm_runLead_le_add (a s m : 𝔸) {u v T : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖runLead a s m v‖ ≤ ‖runLead a s m u‖ + (v - u) * leadLip ‖a‖ ‖s‖ ‖m‖ T ∧
      ‖runLead a s m u‖ ≤ ‖runLead a s m v‖ + (v - u) * leadLip ‖a‖ ‖s‖ ‖m‖ T := by
  have h := norm_runLead_add_sub_le h1 a s m hu (sub_nonneg.2 huv)
  have euv : u + (v - u) = v := by ring
  rw [euv] at h
  have huT : u ≤ T := huv.trans hvT
  have h2 : (v - u) * Real.exp ((v - u + u) * ‖a‖) * (‖a‖ * ‖s‖ + ‖m‖ * (1 + u * ‖a‖)) ≤
      (v - u) * leadLip ‖a‖ ‖s‖ ‖m‖ T := by
    rw [sub_add_cancel, leadLip, mul_assoc]
    have : 0 ≤ v - u := sub_nonneg.2 huv
    have := norm_nonneg a
    have := norm_nonneg s
    have := norm_nonneg m
    gcongr
  have h3 := norm_sub_norm_le (runLead a s m v) (runLead a s m u)
  have h4 := norm_sub_norm_le (runLead a s m u) (runLead a s m v)
  rw [norm_sub_rev] at h4
  constructor <;> linarith

/-- **The grid from the step `j` is fine.** For `0 < H`, `j H ≤ T` and a bound `B` of `‖ψ(k H)‖`
at every `k ≥ j` with `k H ≤ T`: `F(s, m) ≤ B + (j + 1) H L`, `L = leadLip`. -/
theorem leadMax_le_of_grid (a s m : 𝔸) {H T B : ℝ} (hH : 0 < H) {j : ℕ}
    (hjT : (j : ℝ) * H ≤ T)
    (hB : ∀ k : ℕ, j ≤ k → (k : ℝ) * H ≤ T → ‖runLead a s m (k * H)‖ ≤ B) :
    leadMax a s m T ≤ B + (j + 1) * H * leadLip ‖a‖ ‖s‖ ‖m‖ T := by
  have hT : 0 ≤ T := le_trans (by positivity) hjT
  have hL : 0 ≤ leadLip ‖a‖ ‖s‖ ‖m‖ T :=
    leadLip_nonneg (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hT
  refine leadMax_le a s m hT fun t ht0 htT => ?_
  rcases lt_or_ge t ((j : ℝ) * H) with htj | htj
  · -- before the grid: compare with `j H`
    have h := (norm_runLead_le_add h1 a s m ht0 htj.le hjT).2
    have hBj := hB j le_rfl hjT
    have h5 : ((j : ℝ) * H - t) * leadLip ‖a‖ ‖s‖ ‖m‖ T ≤
        (j + 1) * H * leadLip ‖a‖ ‖s‖ ‖m‖ T := by
      refine mul_le_mul_of_nonneg_right ?_ hL
      nlinarith
    linarith
  · -- on the grid: compare with `⌊t/H⌋ H`
    set k := ⌊t / H⌋₊ with hk
    have hk1 : (k : ℝ) * H ≤ t := by
      have := Nat.floor_le (div_nonneg ht0 hH.le)
      rwa [le_div_iff₀ hH] at this
    have hk2 : t < ((k : ℝ) + 1) * H := by
      have := Nat.lt_floor_add_one (t / H)
      rwa [div_lt_iff₀ hH] at this
    have hjk : j ≤ k := Nat.le_floor ((le_div_iff₀ hH).2 htj)
    have hk0 : 0 ≤ (k : ℝ) * H := by positivity
    have h := (norm_runLead_le_add h1 a s m hk0 hk1 htT).1
    have hBk := hB k hjk (hk1.trans htT)
    have h5 : (t - (k : ℝ) * H) * leadLip ‖a‖ ‖s‖ ‖m‖ T ≤
        (j + 1) * H * leadLip ‖a‖ ‖s‖ ‖m‖ T := by
      refine mul_le_mul_of_nonneg_right ?_ hL
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    linarith

end Lead

/-! ### Zero-stability with a forcing -/

section Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Zero-stability of the run class with a forcing and a start error.** Let `‖N‖ ≤ b H`,
`‖M 0 - 1‖ ≤ b H`, `‖M q‖ ≤ b H` for `1 ≤ q < l`, `b H ≤ 1/2`, and let `e` satisfy
`(1 - N) e_{k+1} = Σ_{q<l} M q e_{k-q} + r_k` for `l - 1 ≤ k < K` with `‖r_k‖ ≤ ρ_k` and
`‖e_k‖ ≤ σ` for `k < l`. Then `‖e_k‖ ≤ (σ + 2 Σ_{j<k} ρ_j) (1 + 2 (l + 1) b H)^k` for `k ≤ K`. -/
theorem run_stab_le (N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H b : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b)
    (hbH : b * H ≤ 1 / 2) {l K : ℕ} (hl : 1 ≤ l) (hN : ‖N‖ ≤ b * H)
    (hM0 : ‖M 0 - 1‖ ≤ b * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (e r : ℕ → E) (ρ : ℕ → ℝ) {σ : ℝ} (hσ : ∀ k < l, ‖e k‖ ≤ σ) (hρ0 : ∀ k, 0 ≤ ρ k)
    (hρ : ∀ k, l - 1 ≤ k → k < K → ‖r k‖ ≤ ρ k)
    (he : ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (e (k + 1)) = ∑ q ∈ range l, M q (e (k - q)) + r k) :
    ∀ k ≤ K, ‖e k‖ ≤ (σ + 2 * ∑ j ∈ range k, ρ j) * (1 + 2 * (l + 1) * b * H) ^ k := by
  set c : ℝ := 1 + 2 * (l + 1) * b * H with hc
  have hbH0 : 0 ≤ b * H := mul_nonneg hb hH
  have hc1 : 1 ≤ c := by
    have : 0 ≤ 2 * (l + 1) * b * H := by positivity
    linarith
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans (hσ 0 (by omega))
  have hS : ∀ k, 0 ≤ ∑ j ∈ range k, ρ j := fun k => sum_nonneg fun j _ => hρ0 j
  set φ : ℕ → ℝ := fun k => (σ + 2 * ∑ j ∈ range k, ρ j) * c ^ k with hφ
  have hφmono : ∀ i j : ℕ, i ≤ j → φ i ≤ φ j := by
    intro i j hij
    have h1 : ∑ x ∈ range i, ρ x ≤ ∑ x ∈ range j, ρ x :=
      sum_le_sum_of_subset_of_nonneg (range_mono hij) fun x _ _ => hρ0 x
    have h2 : c ^ i ≤ c ^ j := pow_le_pow_right₀ hc1 hij
    have h3 : 0 ≤ c ^ i := by positivity
    have h4 := hS j
    exact mul_le_mul (by linarith) h2 h3 (by positivity)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases lt_or_ge k l with hkl | hkl
    · refine (hσ k hkl).trans ?_
      have h2 : 1 ≤ c ^ k := one_le_pow₀ hc1
      have := hS k
      nlinarith
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : l - 1 ≤ j := by omega
      have hjK : j < K := by omega
      have hIH : ∀ i ≤ j, ‖e i‖ ≤ φ j := fun i hi =>
        (ih i (by omega) (by omega)).trans (hφmono i j hi)
      have hrec : e (j + 1) = N (e (j + 1)) + e j + (M 0 - 1) (e j) +
          ∑ q ∈ Ico 1 l, M q (e (j - q)) + r j := by
        have h := he j hj hjK
        rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < l), Nat.sub_zero] at h
        simp only [_root_.sub_apply, one_apply_eq_self] at h ⊢
        linear_combination (norm := module) h
      have hsum : ‖∑ q ∈ Ico 1 l, M q (e (j - q))‖ ≤ ((l : ℝ) - 1) * (b * H) * φ j := by
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∀ q ∈ Ico 1 l, ‖M q (e (j - q))‖ ≤ b * H * φ j := by
          intro q hq
          have hq' := mem_Ico.1 hq
          refine ((M q).le_opNorm _).trans ?_
          exact mul_le_mul (hM q hq'.1 hq'.2) (hIH (j - q) (by omega)) (norm_nonneg _) hbH0
        refine (sum_le_sum h1).trans (le_of_eq ?_)
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hl]
        push_cast
        ring
      have hNe : ‖N (e (j + 1))‖ ≤ b * H * ‖e (j + 1)‖ :=
        (N.le_opNorm _).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
      have hM0e : ‖(M 0 - 1) (e j)‖ ≤ b * H * φ j :=
        ((M 0 - 1).le_opNorm _).trans (mul_le_mul hM0 (hIH j le_rfl) (norm_nonneg _) hbH0)
      have hej := hIH j le_rfl
      have hrj := hρ j hj hjK
      have htri : ‖e (j + 1)‖ ≤ b * H * ‖e (j + 1)‖ + φ j + b * H * φ j +
          ((l : ℝ) - 1) * (b * H) * φ j + ρ j := by
        have h2 := norm_add₃_le (a := N (e (j + 1)) + e j) (b := (M 0 - 1) (e j))
          (c := ∑ q ∈ Ico 1 l, M q (e (j - q)))
        have h3 := norm_add_le (N (e (j + 1))) (e j)
        have h4 := norm_add_le (N (e (j + 1)) + e j + (M 0 - 1) (e j) +
          ∑ q ∈ Ico 1 l, M q (e (j - q))) (r j)
        rw [← hrec] at h4
        linarith
      have hl0 : (0 : ℝ) ≤ l := by positivity
      have hstep := one_add_mul_div_le (l : ℝ) hl0 hbH0 hbH
      have hφ0 : 0 ≤ φ j := (norm_nonneg _).trans hej
      have hρj := hρ0 j
      have hpos : 0 < 1 - b * H := by linarith
      have h1 : (1 - b * H) * ‖e (j + 1)‖ ≤ (1 + l * (b * H)) * φ j + ρ j := by linarith
      have h2 : (1 - b * H) * ‖e (j + 1)‖ ≤ (1 - b * H) * (c * φ j + 2 * ρ j) := by
        have h3 : (1 + l * (b * H)) * φ j ≤ (c * (1 - b * H)) * φ j := by
          refine mul_le_mul_of_nonneg_right ?_ hφ0
          rw [hc]
          linarith
        nlinarith
      have h4 : ‖e (j + 1)‖ ≤ c * φ j + 2 * ρ j := le_of_mul_le_mul_left h2 hpos
      have h5 : c * φ j + 2 * ρ j ≤ φ (j + 1) := by
        have hcj : 1 ≤ c ^ j * c := by
          rw [← pow_succ]
          exact one_le_pow₀ hc1
        have h6 := mul_le_mul_of_nonneg_left hcj hρj
        simp only [hφ, sum_range_succ, pow_succ]
        linarith
      exact h4.trans h5

end Stability

/-! ### The residual of the comparison run -/

section Residual

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The residual of a sequence `Y` in the recursion of a scheme with `l` held samples at the
step `k`: `(1 - N) Y_{k+1} - Σ_{q<l} M q Y_{k-q}`. -/
def recResid (N : 𝔸) (M : ℕ → 𝔸) (l k : ℕ) (Y : ℕ → 𝔸) : 𝔸 :=
  (1 - N) * Y (k + 1) - ∑ q ∈ range l, M q * Y (k - q)

theorem recResid_add (N : 𝔸) (M : ℕ → 𝔸) (l k : ℕ) (Y Y' : ℕ → 𝔸) :
    recResid N M l k (fun j => Y j + Y' j) = recResid N M l k Y + recResid N M l k Y' := by
  simp only [recResid, mul_add, sum_add_distrib]
  abel

theorem recResid_sub (N : 𝔸) (M : ℕ → 𝔸) (l k : ℕ) (Y Y' : ℕ → 𝔸) :
    recResid N M l k (fun j => Y j - Y' j) = recResid N M l k Y - recResid N M l k Y' := by
  simp only [recResid, mul_sub, sum_sub_distrib]
  abel

theorem recResid_smul (N : 𝔸) (M : ℕ → 𝔸) (l k : ℕ) (c : ℝ) (Y : ℕ → 𝔸) :
    recResid N M l k (fun j => c • Y j) = c • recResid N M l k Y := by
  simp only [recResid, mul_smul_comm, ← smul_sum, smul_sub]

/-- **The comparison run** `Y_j = U^j + H^l (U^j S - Φ_{jH}(D))`, `U = e^{Ha}`. -/
noncomputable def leadRun (a S D : 𝔸) (H : ℝ) (l j : ℕ) : 𝔸 :=
  exp (H • a) ^ j + H ^ l • (exp (H • a) ^ j * S - runPhi a D (j * H))

theorem leadRun_eq (a S D : 𝔸) (H : ℝ) (l j : ℕ) :
    leadRun a S D H l j = exp (H • a) ^ j + H ^ l • runLead a S D (j * H) := by
  rw [leadRun, runLead, exp_natCast_mul_smul]

/-- `Φ_{(k+1)H} = U Φ_{kH} + Φ_H U^k`. -/
theorem runPhi_grid_succ (a D : 𝔸) (H : ℝ) (k : ℕ) :
    runPhi a D (((k + 1 : ℕ) : ℝ) * H) =
      exp (H • a) * runPhi a D (k * H) + runPhi a D H * exp (H • a) ^ k := by
  rw [show ((k + 1 : ℕ) : ℝ) * H = k * H + H by push_cast; ring, runPhi_add,
    exp_natCast_mul_smul]

/-- `Φ_{kH} = U^q Φ_{(k-q)H} + Φ_{qH} U^{k-q}` for `q ≤ k`. -/
theorem runPhi_grid_sub (a D : 𝔸) (H : ℝ) {q k : ℕ} (hq : q ≤ k) :
    runPhi a D (k * H) =
      exp (H • a) ^ q * runPhi a D (((k - q : ℕ) : ℝ) * H) +
        runPhi a D (q * H) * exp (H • a) ^ (k - q) := by
  have e : (k : ℝ) * H = ((k - q : ℕ) : ℝ) * H + q * H := by
    rw [Nat.cast_sub hq]
    ring
  rw [e, runPhi_add, exp_natCast_mul_smul, exp_natCast_mul_smul]

/-- The residual of `U^j X`: `T U^k X`, for `k ≥ l - 1`. -/
theorem recResid_pow_mul {N : 𝔸} {M : ℕ → 𝔸} {U Ui : 𝔸} (hU : Ui * U = 1) {l k : ℕ}
    (hk : l - 1 ≤ k) (X : 𝔸) :
    recResid N M l k (fun j => U ^ j * X) = runDefect N M U Ui l * (U ^ k * X) := by
  have h : runDefect N M U Ui l * (U ^ k * X) =
      (1 - N) * (U ^ (k + 1) * X) - ∑ q ∈ range l, M q * (U ^ (k - q) * X) := by
    rw [runDefect, sub_mul ((1 - N) * U) (∑ q ∈ range l, M q * Ui ^ q) (U ^ k * X), sum_mul]
    congr 1
    · rw [pow_succ', mul_assoc, mul_assoc]
    · refine sum_congr rfl fun q hq => ?_
      rw [mul_assoc, ← mul_assoc (Ui ^ q), inv_pow_mul_pow hU (by have := mem_range.1 hq; omega)]
  rw [h]
  rfl

/-- **The residual of the accumulated defect**, from the semigroup law:
`(1 - N) Φ_{(k+1)H} - Σ_q M q Φ_{(k-q)H} = T Φ_{kH} + (1 - N) Φ_H U^k
  + Σ_q M q U^{-q} Φ_{qH} U^{k-q}`, `k ≥ l - 1`. -/
theorem recResid_runPhi (N : 𝔸) (M : ℕ → 𝔸) (a D : 𝔸) (H : ℝ) {l k : ℕ} (hk : l - 1 ≤ k) :
    recResid N M l k (fun j => runPhi a D (j * H)) =
      runDefect N M (exp (H • a)) (exp (-(H • a))) l * runPhi a D (k * H) +
        (1 - N) * runPhi a D H * exp (H • a) ^ k +
        ∑ q ∈ range l, M q * exp (-(H • a)) ^ q * runPhi a D (q * H) *
          exp (H • a) ^ (k - q) := by
  have hU : exp (-(H • a)) * exp (H • a) = 1 := exp_neg_mul_exp (H • a)
  have hq : ∀ q ∈ range l, M q * runPhi a D (((k - q : ℕ) : ℝ) * H) =
      M q * exp (-(H • a)) ^ q * runPhi a D (k * H) -
        M q * exp (-(H • a)) ^ q * runPhi a D (q * H) * exp (H • a) ^ (k - q) := by
    intro q hq
    have hqk : q ≤ k := by have := mem_range.1 hq; omega
    have h := runPhi_grid_sub a D H hqk
    have h2 : exp (-(H • a)) ^ q * exp (H • a) ^ q = 1 := pow_mul_pow_eq_one q hU
    have h3 : runPhi a D (((k - q : ℕ) : ℝ) * H) =
        exp (-(H • a)) ^ q * runPhi a D (k * H) -
          exp (-(H • a)) ^ q * runPhi a D (q * H) * exp (H • a) ^ (k - q) := by
      rw [h, mul_add, ← mul_assoc (exp (-(H • a)) ^ q) (exp (H • a) ^ q), h2, one_mul]
      noncomm_ring
    rw [h3]
    noncomm_ring
  unfold recResid runDefect
  dsimp only
  rw [runPhi_grid_succ, sum_congr rfl hq, sum_sub_distrib, ← sum_mul]
  noncomm_ring

/-- **The residual of the comparison run**:
`R_k = T U^k + H^l (T (U^k S - Φ_{kH}) - (1 - N) Φ_H U^k - Σ_q M q U^{-q} Φ_{qH} U^{k-q})`. -/
theorem recResid_leadRun (N : 𝔸) (M : ℕ → 𝔸) (a S D : 𝔸) (H : ℝ) {l k : ℕ} (hk : l - 1 ≤ k) :
    recResid N M l k (leadRun a S D H l) =
      runDefect N M (exp (H • a)) (exp (-(H • a))) l * exp (H • a) ^ k +
        H ^ l • (runDefect N M (exp (H • a)) (exp (-(H • a))) l *
            (exp (H • a) ^ k * S - runPhi a D (k * H)) -
          (1 - N) * runPhi a D H * exp (H • a) ^ k -
          ∑ q ∈ range l, M q * exp (-(H • a)) ^ q * runPhi a D (q * H) *
            exp (H • a) ^ (k - q)) := by
  have hU : exp (-(H • a)) * exp (H • a) = 1 := exp_neg_mul_exp (H • a)
  have e : leadRun a S D H l = fun j : ℕ => (exp (H • a) ^ j * 1) +
      H ^ l • ((exp (H • a) ^ j * S) - runPhi a D ((j : ℝ) * H)) := by
    funext j
    rw [leadRun, mul_one]
  rw [e, recResid_add, recResid_smul, recResid_sub, recResid_pow_mul hU hk,
    recResid_pow_mul hU hk, recResid_runPhi N M a D H hk, mul_one]
  congr 1
  rw [mul_sub]
  abel_nf

/-- The constant of the residual,
`R₀ = c₁ + (δ + c₁)(s + T₀ δ) + δ e^α (α + b) + b l² e^{2 l α} δ`. -/
noncomputable def leadRes (α : ℝ) (l : ℕ) (b c₁ δ s T₀ : ℝ) : ℝ :=
  c₁ + (δ + c₁) * (s + T₀ * δ) + δ * Real.exp α * (α + b) +
    b * (l : ℝ) ^ 2 * Real.exp (2 * l * α) * δ

theorem leadRes_nonneg {α : ℝ} (l : ℕ) {b c₁ δ s T₀ : ℝ} (hα : 0 ≤ α) (hb : 0 ≤ b)
    (hc₁ : 0 ≤ c₁) (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hT₀ : 0 ≤ T₀) : 0 ≤ leadRes α l b c₁ δ s T₀ := by
  unfold leadRes
  positivity

variable (h1 : ‖(1 : 𝔸)‖ ≤ 1)
include h1

/-- `‖U^{-q}‖ ≤ e^{q H ‖a‖}` for `H ≥ 0`. -/
theorem norm_exp_neg_pow_le (a : 𝔸) {H : ℝ} (hH : 0 ≤ H) (q : ℕ) :
    ‖exp (-(H • a)) ^ q‖ ≤ Real.exp (q * H * ‖a‖) := by
  have h := norm_exp_pow_le h1 (-a) hH q
  rwa [smul_neg, norm_neg] at h

omit h1 in
/-- The residual of the comparison run, rearranged around the leading defect `H^{l+1} D`. -/
theorem recResid_leadRun_eq (N : 𝔸) (M : ℕ → 𝔸) (a S D : 𝔸) (H : ℝ) {l k : ℕ}
    (hk : l - 1 ≤ k) :
    recResid N M l k (leadRun a S D H l) =
      (runDefect N M (exp (H • a)) (exp (-(H • a))) l - H ^ (l + 1) • D) * exp (H • a) ^ k +
        H ^ l • (runDefect N M (exp (H • a)) (exp (-(H • a))) l *
          (exp (H • a) ^ k * S - runPhi a D (k * H))) -
        H ^ l • ((runPhi a D H - H • D - N * runPhi a D H) * exp (H • a) ^ k) -
        H ^ l • ∑ q ∈ range l, M q * exp (-(H • a)) ^ q * runPhi a D (q * H) *
          exp (H • a) ^ (k - q) := by
  rw [recResid_leadRun N M a S D H hk, pow_succ, mul_smul]
  simp only [smul_sub, sub_mul, smul_mul_assoc, one_mul]
  abel

/-- The third part of the residual: `‖Φ_H - H D - N Φ_H‖ ≤ H² δ e^{‖a‖} (‖a‖ + b)` for
`0 ≤ H ≤ 1`, `‖N‖ ≤ b H`, `‖D‖ ≤ δ`. -/
theorem norm_runPhi_step_sub_le (a D N : 𝔸) {H b δ : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1)
    (hN : ‖N‖ ≤ b * H) (hD : ‖D‖ ≤ δ) :
    ‖runPhi a D H - H • D - N * runPhi a D H‖ ≤ H ^ 2 * (δ * Real.exp ‖a‖ * (‖a‖ + b)) := by
  have hα0 := norm_nonneg a
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hD
  have hb : 0 ≤ b * H := (norm_nonneg _).trans hN
  have hEH : Real.exp (H * ‖a‖) ≤ Real.exp ‖a‖ :=
    Real.exp_le_exp.2 (mul_le_of_le_one_left hα0 hH1)
  have h2 := norm_runPhi_sub_smul_le h1 a D hH0
  have h3 := norm_runPhi_le h1 a D hH0
  have h4 : Real.exp (H * ‖a‖) - 1 ≤ H * ‖a‖ * Real.exp (H * ‖a‖) :=
    exp_sub_one_le_mul_exp _
  have h0 : 0 ≤ Real.exp (H * ‖a‖) - 1 := by
    have := Real.add_one_le_exp (H * ‖a‖)
    have := mul_nonneg hH0 hα0
    linarith
  have h3' : ‖runPhi a D H‖ ≤ H * Real.exp ‖a‖ * δ := h3.trans (by gcongr)
  have h5 : ‖N * runPhi a D H‖ ≤ b * H * (H * Real.exp ‖a‖ * δ) :=
    (norm_mul_le _ _).trans (mul_le_mul hN h3' (norm_nonneg _) hb)
  have h6 : ‖runPhi a D H - H • D‖ ≤ H * δ * (H * ‖a‖ * Real.exp ‖a‖) := by
    refine h2.trans ?_
    have h7 : Real.exp (H * ‖a‖) - 1 ≤ H * ‖a‖ * Real.exp ‖a‖ :=
      h4.trans (mul_le_mul_of_nonneg_left hEH (by positivity))
    gcongr
  refine (norm_sub_le _ _).trans ?_
  have h7 : H * δ * (H * ‖a‖ * Real.exp ‖a‖) + b * H * (H * Real.exp ‖a‖ * δ) =
      H ^ 2 * (δ * Real.exp ‖a‖ * (‖a‖ + b)) := by ring
  linarith

/-- The fourth part of the residual: for `0 ≤ H ≤ 1`, `k H ≤ T₀`, `‖M q‖ ≤ b H` (`1 ≤ q < l`),
`‖D‖ ≤ δ`: `‖Σ_{q<l} M q U^{-q} Φ_{qH} U^{k-q}‖ ≤ b l² δ e^{2 l ‖a‖} e^{T₀ ‖a‖} H²`. -/
theorem norm_sum_resid_le (a D : 𝔸) (M : ℕ → 𝔸) {H b δ T₀ : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1)
    (hb : 0 ≤ b) {l k : ℕ} (hkT : (k : ℝ) * H ≤ T₀) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (hD : ‖D‖ ≤ δ) :
    ‖∑ q ∈ range l, M q * exp (-(H • a)) ^ q * runPhi a D (q * H) * exp (H • a) ^ (k - q)‖ ≤
      b * (l : ℝ) ^ 2 * Real.exp (2 * l * ‖a‖) * δ * Real.exp (T₀ * ‖a‖) * H ^ 2 := by
  have hα0 := norm_nonneg a
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hD
  have hEl : ∀ q : ℕ, q ≤ l → Real.exp (q * H * ‖a‖) ≤ Real.exp (l * ‖a‖) := by
    intro q hq
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hα0)
    have h2 : (q : ℝ) ≤ l := by exact_mod_cast hq
    calc (q : ℝ) * H ≤ q * 1 := mul_le_mul_of_nonneg_left hH1 (Nat.cast_nonneg q)
      _ ≤ l := by rw [mul_one]; exact h2
  have e2 : Real.exp (2 * l * ‖a‖) = Real.exp (l * ‖a‖) * Real.exp (l * ‖a‖) := by
    rw [← Real.exp_add]
    ring_nf
  have hterm : ∀ q ∈ range l, ‖M q * exp (-(H • a)) ^ q * runPhi a D (q * H) *
      exp (H • a) ^ (k - q)‖ ≤
      b * l * δ * Real.exp (2 * l * ‖a‖) * Real.exp (T₀ * ‖a‖) * H ^ 2 := by
    intro q hq
    have hql := mem_range.1 hq
    have hbound : 0 ≤ b * l * δ * Real.exp (2 * l * ‖a‖) * Real.exp (T₀ * ‖a‖) * H ^ 2 := by
      positivity
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp [runPhi_zero, hbound]
    have h2 : ‖exp (-(H • a)) ^ q‖ ≤ Real.exp (l * ‖a‖) :=
      (norm_exp_neg_pow_le h1 a hH0 q).trans (hEl q hql.le)
    have hq0 : 0 ≤ (q : ℝ) * H := by positivity
    have h5 : (q : ℝ) * H ≤ l * H :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hql.le) hH0
    have h3 : ‖runPhi a D (q * H)‖ ≤ l * H * Real.exp (l * ‖a‖) * δ := by
      refine (norm_runPhi_le h1 a D hq0).trans ?_
      have h4 : Real.exp (q * H * ‖a‖) ≤ Real.exp (l * ‖a‖) := hEl q hql.le
      gcongr
    have h4 : ‖exp (H • a) ^ (k - q)‖ ≤ Real.exp (T₀ * ‖a‖) := by
      refine (norm_exp_pow_le h1 a hH0 (k - q)).trans (Real.exp_le_exp.2 ?_)
      have h6 : ((k - q : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k q
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right h6 hH0).trans hkT) hα0
    have h6 := hM q hq1 hql
    have h7 : ‖M q * exp (-(H • a)) ^ q * runPhi a D (q * H) * exp (H • a) ^ (k - q)‖ ≤
        ‖M q‖ * ‖exp (-(H • a)) ^ q‖ * ‖runPhi a D (q * H)‖ * ‖exp (H • a) ^ (k - q)‖ := by
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact norm_mul_le _ _
    have h8 : ‖M q‖ * ‖exp (-(H • a)) ^ q‖ * ‖runPhi a D (q * H)‖ *
        ‖exp (H • a) ^ (k - q)‖ ≤
        (b * H) * Real.exp (l * ‖a‖) * (l * H * Real.exp (l * ‖a‖) * δ) *
          Real.exp (T₀ * ‖a‖) := by gcongr
    have e3 : (b * H) * Real.exp (l * ‖a‖) * (l * H * Real.exp (l * ‖a‖) * δ) *
        Real.exp (T₀ * ‖a‖) =
        b * l * δ * Real.exp (2 * l * ‖a‖) * Real.exp (T₀ * ‖a‖) * H ^ 2 := by
      rw [e2]
      ring
    rw [e3] at h8
    exact h7.trans h8
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans (le_of_eq ?_))
  rw [sum_const, card_range, nsmul_eq_mul]
  ring

/-- **The residual of the comparison run is of the order `H^{l+2}`**. Let
`0 < H ≤ 1`, `‖N‖ ≤ b H`, `‖M q‖ ≤ b H` for `1 ≤ q < l`, `‖T - H^{l+1} D‖ ≤ c₁ H^{l+2}`,
`‖D‖ ≤ δ`, `‖S‖ ≤ s`, `l - 1 ≤ k` and `k H ≤ T₀`. Then `‖R_k‖ ≤ R₀ e^{T₀ ‖a‖} H^{l+2}`. -/
theorem norm_recResid_leadRun_le (a S D N : 𝔸) (M : ℕ → 𝔸) {H b c₁ δ s T₀ : ℝ} (hH : 0 < H)
    (hH1 : H ≤ 1) (hb : 0 ≤ b) {l k : ℕ} (hl : 1 ≤ l) (hk : l - 1 ≤ k)
    (hkT : (k : ℝ) * H ≤ T₀) (hN : ‖N‖ ≤ b * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (hT : ‖runDefect N M (exp (H • a)) (exp (-(H • a))) l - H ^ (l + 1) • D‖ ≤
      c₁ * H ^ (l + 2))
    (hD : ‖D‖ ≤ δ) (hS : ‖S‖ ≤ s) :
    ‖recResid N M l k (leadRun a S D H l)‖ ≤
      leadRes ‖a‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖a‖) * H ^ (l + 2) := by
  rw [recResid_leadRun_eq N M a S D H hk]
  set T := runDefect N M (exp (H • a)) (exp (-(H • a))) l with hTdef
  set Wq := ∑ q ∈ range l, M q * exp (-(H • a)) ^ q * runPhi a D (q * H) *
    exp (H • a) ^ (k - q) with hWq
  set E₀ := Real.exp (T₀ * ‖a‖) with hE₀
  have hH0 := hH.le
  have hα0 : 0 ≤ ‖a‖ := norm_nonneg a
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hD
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hS
  have hc₁ : 0 ≤ c₁ := by
    have h := (norm_nonneg _).trans hT
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hk0 : 0 ≤ (k : ℝ) * H := by positivity
  have hT₀ : 0 ≤ T₀ := hk0.trans hkT
  have hHl : 0 ≤ H ^ l := by positivity
  have hE0 : 0 ≤ E₀ := (Real.exp_pos _).le
  have hUk : ‖exp (H • a) ^ k‖ ≤ E₀ :=
    (norm_exp_pow_le h1 a hH0 k).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hkT hα0))
  -- the first part
  have B1 : ‖(T - H ^ (l + 1) • D) * exp (H • a) ^ k‖ ≤ c₁ * E₀ * H ^ (l + 2) := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖T - H ^ (l + 1) • D‖ * ‖exp (H • a) ^ k‖ ≤ c₁ * H ^ (l + 2) * E₀ :=
          mul_le_mul hT hUk (norm_nonneg _) (by positivity)
      _ = c₁ * E₀ * H ^ (l + 2) := by ring
  -- the second part
  have hTn : ‖T‖ ≤ (δ + c₁) * H ^ (l + 1) := by
    have h2 : ‖H ^ (l + 1) • D‖ ≤ H ^ (l + 1) * δ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hD (by positivity)
    have h3 : c₁ * H ^ (l + 2) ≤ c₁ * H ^ (l + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hH0 hH1 (by omega)) hc₁
    have h4 := norm_add_le (T - H ^ (l + 1) • D) (H ^ (l + 1) • D)
    rw [sub_add_cancel] at h4
    have e : (δ + c₁) * H ^ (l + 1) = H ^ (l + 1) * δ + c₁ * H ^ (l + 1) := by ring
    rw [e]
    linarith
  have hW : ‖exp (H • a) ^ k * S - runPhi a D (k * H)‖ ≤ E₀ * (s + T₀ * δ) := by
    have h2 := norm_runPhi_le h1 a D hk0
    have h3 : Real.exp (k * H * ‖a‖) ≤ E₀ :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hkT hα0)
    have h4 : ‖runPhi a D (k * H)‖ ≤ T₀ * E₀ * δ := h2.trans (by gcongr)
    have h5 : ‖exp (H • a) ^ k * S‖ ≤ E₀ * s :=
      (norm_mul_le _ _).trans (mul_le_mul hUk hS (norm_nonneg _) hE0)
    have e : E₀ * (s + T₀ * δ) = E₀ * s + T₀ * E₀ * δ := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add h5 h4)
  have B2 : ‖H ^ l • (T * (exp (H • a) ^ k * S - runPhi a D (k * H)))‖ ≤
      (δ + c₁) * (s + T₀ * δ) * E₀ * H ^ (l + 2) := by
    rw [norm_smul, Real.norm_of_nonneg hHl]
    have h2 : ‖T * (exp (H • a) ^ k * S - runPhi a D (k * H))‖ ≤
        (δ + c₁) * H ^ (l + 1) * (E₀ * (s + T₀ * δ)) :=
      (norm_mul_le _ _).trans (mul_le_mul hTn hW (norm_nonneg _) (by positivity))
    have h3 : H ^ l * H ^ (l + 1) ≤ H ^ (l + 2) := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hH0 hH1 (by omega)
    have h4 : 0 ≤ (δ + c₁) * (s + T₀ * δ) * E₀ := by positivity
    calc H ^ l * ‖T * (exp (H • a) ^ k * S - runPhi a D (k * H))‖
        ≤ H ^ l * ((δ + c₁) * H ^ (l + 1) * (E₀ * (s + T₀ * δ))) :=
          mul_le_mul_of_nonneg_left h2 hHl
      _ = (δ + c₁) * (s + T₀ * δ) * E₀ * (H ^ l * H ^ (l + 1)) := by ring
      _ ≤ (δ + c₁) * (s + T₀ * δ) * E₀ * H ^ (l + 2) :=
          mul_le_mul_of_nonneg_left h3 h4
  -- the third part
  have B3 : ‖H ^ l • ((runPhi a D H - H • D - N * runPhi a D H) * exp (H • a) ^ k)‖ ≤
      δ * Real.exp ‖a‖ * (‖a‖ + b) * E₀ * H ^ (l + 2) := by
    rw [norm_smul, Real.norm_of_nonneg hHl]
    have hΦH := norm_runPhi_step_sub_le h1 a D N hH0 hH1 hN hD
    have h2 := (norm_mul_le (runPhi a D H - H • D - N * runPhi a D H) (exp (H • a) ^ k)).trans
      (mul_le_mul hΦH hUk (norm_nonneg _) (by positivity))
    calc H ^ l * ‖(runPhi a D H - H • D - N * runPhi a D H) * exp (H • a) ^ k‖
        ≤ H ^ l * (H ^ 2 * (δ * Real.exp ‖a‖ * (‖a‖ + b)) * E₀) :=
          mul_le_mul_of_nonneg_left h2 hHl
      _ = δ * Real.exp ‖a‖ * (‖a‖ + b) * E₀ * H ^ (l + 2) := by ring
  -- the fourth part
  have B4 : ‖H ^ l • Wq‖ ≤ b * (l : ℝ) ^ 2 * Real.exp (2 * l * ‖a‖) * δ * E₀ * H ^ (l + 2) := by
    rw [norm_smul, Real.norm_of_nonneg hHl]
    have h2 := norm_sum_resid_le h1 a D M hH0 hH1 hb hkT hM hD (l := l)
    calc H ^ l * ‖Wq‖
        ≤ H ^ l * (b * (l : ℝ) ^ 2 * Real.exp (2 * l * ‖a‖) * δ * E₀ * H ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hHl
      _ = b * (l : ℝ) ^ 2 * Real.exp (2 * l * ‖a‖) * δ * E₀ * H ^ (l + 2) := by ring
  have h2 := norm_sub_le ((T - H ^ (l + 1) • D) * exp (H • a) ^ k +
    H ^ l • (T * (exp (H • a) ^ k * S - runPhi a D (k * H))) -
    H ^ l • ((runPhi a D H - H • D - N * runPhi a D H) * exp (H • a) ^ k)) (H ^ l • Wq)
  have h3 := norm_sub_le ((T - H ^ (l + 1) • D) * exp (H • a) ^ k +
    H ^ l • (T * (exp (H • a) ^ k * S - runPhi a D (k * H))))
    (H ^ l • ((runPhi a D H - H • D - N * runPhi a D H) * exp (H • a) ^ k))
  have h4 := norm_add_le ((T - H ^ (l + 1) • D) * exp (H • a) ^ k)
    (H ^ l • (T * (exp (H • a) ^ k * S - runPhi a D (k * H))))
  have e3 : leadRes ‖a‖ l b c₁ δ s T₀ * E₀ * H ^ (l + 2) =
      c₁ * E₀ * H ^ (l + 2) + (δ + c₁) * (s + T₀ * δ) * E₀ * H ^ (l + 2) +
        δ * Real.exp ‖a‖ * (‖a‖ + b) * E₀ * H ^ (l + 2) +
        b * (l : ℝ) ^ 2 * Real.exp (2 * l * ‖a‖) * δ * E₀ * H ^ (l + 2) := by
    unfold leadRes
    ring
  rw [e3]
  linarith

end Residual

/-! ### Accumulation -/

section Accumulation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The constant of the accumulation, `C = (σ + 2 T₀ R₀ e^{T₀ α}) e^{2 (l+1) b T₀}`. -/
noncomputable def leadConst (α : ℝ) (l : ℕ) (b c₁ δ s σ T₀ : ℝ) : ℝ :=
  (σ + 2 * T₀ * leadRes α l b c₁ δ s T₀ * Real.exp (T₀ * α)) *
    Real.exp (2 * (l + 1) * b * T₀)

theorem leadConst_nonneg {α : ℝ} (l : ℕ) {b c₁ δ s σ T₀ : ℝ} (hα : 0 ≤ α) (hb : 0 ≤ b)
    (hc₁ : 0 ≤ c₁) (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hσ : 0 ≤ σ) (hT₀ : 0 ≤ T₀) :
    0 ≤ leadConst α l b c₁ δ s σ T₀ := by
  have := leadRes_nonneg l hα hb hc₁ hδ hs hT₀ (b := b)
  unfold leadConst
  positivity

/-- `(1 + 2 (l + 1) b H)^k ≤ e^{2 (l + 1) b T₀}` for `k H ≤ T₀`. -/
theorem one_add_pow_le_exp_run {b H T₀ : ℝ} (hb : 0 ≤ b) (hH : 0 ≤ H) (l : ℕ) {k : ℕ}
    (hk : (k : ℝ) * H ≤ T₀) :
    (1 + 2 * (l + 1) * b * H) ^ k ≤ Real.exp (2 * (l + 1) * b * T₀) := by
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
        exact mul_le_mul_of_nonneg_left hk (by positivity)

/-- **Accumulation of the leading defect**. In the run class of `OrderReached`
(`‖N‖, ‖M 0 - 1‖, ‖M q‖ ≤ b H` for `1 ≤ q < l`, `b H ≤ 1/2`), let the local defect be within
`c₁ H^{l+2}` of `H^{l+1} D`, `‖D‖ ≤ δ`, `‖S‖ ≤ s`, `0 < H ≤ 1`, `K H ≤ T₀`, and let the start
have `‖x^q - U^q x_0 - H^l ψ(qH) x_0‖ ≤ σ H^{l+1} ‖x_0‖` for `q < l`, `ψ(t) = e^{tA} S - Φ_t(D)`.
Then for every `k ≤ K`,
`‖x^k - U^k x_0 - H^l (e^{kHA} S - Φ_{kH}(D)) x_0‖ ≤ C H^{l+1} ‖x_0‖`, `C = leadConst`. -/
theorem run_accumulation (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) (D S : E →L[ℝ] E)
    {H b c₁ δ s σ T₀ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hb : 0 ≤ b) (hbH : b * H ≤ 1 / 2)
    (hσ : 0 ≤ σ) {l K : ℕ} (hl : 1 ≤ l) (hKT : (K : ℝ) * H ≤ T₀) (hN : ‖N‖ ≤ b * H)
    (hM0 : ‖M 0 - 1‖ ≤ b * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (hT : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l - H ^ (l + 1) • D‖ ≤
      c₁ * H ^ (l + 2))
    (hD : ‖D‖ ≤ δ) (hS : ‖S‖ ≤ s) (x0 : E) (x : ℕ → E)
    (hstart : ∀ q < l, ‖x q - (exp (H • A) ^ q) x0 - H ^ l • runLead A S D (q * H) x0‖ ≤
      σ * H ^ (l + 1) * ‖x0‖)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) (x (k + 1)) = ∑ q ∈ range l, M q (x (k - q))) :
    ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0‖ ≤
      leadConst ‖A‖ l b c₁ δ s σ T₀ * H ^ (l + 1) * ‖x0‖ := by
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
  have hstart' : ∀ q < l, ‖e q‖ ≤ σ * H ^ (l + 1) * ‖x0‖ := fun q hq => by
    rw [hek]
    exact hstart q hq
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
  have hres : ∀ k, l - 1 ≤ k → k < K →
      ‖-(recResid N M l k (leadRun A S D H l) x0)‖ ≤ ρ := by
    intro k hk hkK
    rw [norm_neg]
    have hkT : (k : ℝ) * H ≤ T₀ :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkK.le) hH.le) hKT
    have h := norm_recResid_leadRun_le h1 A S D N M hH hH1 hb hl hk hkT hN hM hT hD hS
    exact ((recResid N M l k (leadRun A S D H l)).le_opNorm x0).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg x0))
  have hstab := run_stab_le N M hH.le hb hbH hl hN hM0 hM e _ (fun _ => ρ) hstart'
    (fun _ => hρ0) hres hrec
  intro k hk
  rw [← hek]
  refine (hstab k hk).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have hkT : (k : ℝ) * H ≤ T₀ :=
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hH.le) hKT
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
  have hbase : 0 ≤ σ * H ^ (l + 1) * ‖x0‖ + 2 * ((k : ℝ) * ρ) := by positivity
  calc (σ * H ^ (l + 1) * ‖x0‖ + 2 * ((k : ℝ) * ρ)) * (1 + 2 * (l + 1) * b * H) ^ k
      ≤ (σ * H ^ (l + 1) * ‖x0‖ + 2 * ((k : ℝ) * ρ)) * Real.exp (2 * (l + 1) * b * T₀) :=
        mul_le_mul_of_nonneg_left hc hbase
    _ ≤ (σ * H ^ (l + 1) * ‖x0‖ +
          2 * (T₀ * leadRes ‖A‖ l b c₁ δ s T₀ * Real.exp (T₀ * ‖A‖) * H ^ (l + 1) * ‖x0‖)) *
          Real.exp (2 * (l + 1) * b * T₀) := by gcongr
    _ = leadConst ‖A‖ l b c₁ δ s σ T₀ * H ^ (l + 1) * ‖x0‖ := by
        unfold leadConst
        ring

/-- **The start `x^q = U^q (1 + H^l S) x_0` and its leading error.** If
`‖x^q - U^q x_0 - H^l U^q S x_0‖ ≤ σ H^{l+1} ‖x_0‖`, `q < l`, `0 ≤ H ≤ 1`, `‖D‖ ≤ δ`, then
`‖x^q - U^q x_0 - H^l ψ(qH) x_0‖ ≤ (σ + l e^{l ‖A‖} δ) H^{l+1} ‖x_0‖`. -/
theorem start_lead_le (A S D : E →L[ℝ] E) {H δ σ : ℝ} (hH : 0 ≤ H) (hH1 : H ≤ 1)
    (hD : ‖D‖ ≤ δ) {l q : ℕ} (hq : q < l) (x0 y : E)
    (hy : ‖y - (exp (H • A) ^ q) x0 - H ^ l • (exp (H • A) ^ q * S) x0‖ ≤
      σ * H ^ (l + 1) * ‖x0‖) :
    ‖y - (exp (H • A) ^ q) x0 - H ^ l • runLead A S D (q * H) x0‖ ≤
      (σ + l * Real.exp (l * ‖A‖) * δ) * H ^ (l + 1) * ‖x0‖ := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have e : y - (exp (H • A) ^ q) x0 - H ^ l • runLead A S D (q * H) x0 =
      (y - (exp (H • A) ^ q) x0 - H ^ l • (exp (H • A) ^ q * S) x0) +
        H ^ l • runPhi A D (q * H) x0 := by
    rw [runLead, exp_natCast_mul_smul, _root_.sub_apply, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hq0 : 0 ≤ (q : ℝ) * H := by positivity
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hD
  have hql : (q : ℝ) ≤ l := by exact_mod_cast hq.le
  have h2 : ‖runPhi A D (q * H)‖ ≤ l * H * Real.exp (l * ‖A‖) * δ := by
    refine (norm_runPhi_le h1 A D hq0).trans ?_
    have h3 : (q : ℝ) * H ≤ l * H := mul_le_mul_of_nonneg_right hql hH
    have h4 : Real.exp (q * H * ‖A‖) ≤ Real.exp (l * ‖A‖) := by
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (norm_nonneg A))
      nlinarith
    gcongr
  have h3 : ‖H ^ l • runPhi A D (q * H) x0‖ ≤
      l * Real.exp (l * ‖A‖) * δ * H ^ (l + 1) * ‖x0‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc H ^ l * ‖runPhi A D (q * H) x0‖ ≤ H ^ l * (l * H * Real.exp (l * ‖A‖) * δ * ‖x0‖) :=
          mul_le_mul_of_nonneg_left (((runPhi A D (q * H)).le_opNorm x0).trans
            (mul_le_mul_of_nonneg_right h2 (norm_nonneg x0))) (by positivity)
      _ = l * Real.exp (l * ‖A‖) * δ * H ^ (l + 1) * ‖x0‖ := by ring
  linarith

/-- **The error over a run is at most `H^l F + C H^{l+1}`.** If the accumulation holds with the
constant `C` for every `k ≤ K`, `K H ≤ T`, `H ≥ 0`, then
`‖x^k - U^k x_0‖ ≤ (H^l F(S, D) + C H^{l+1}) ‖x_0‖` for `k ≤ K`, `F = leadMax` over `[0, T]`. -/
theorem run_le_leadMax (A S D : E →L[ℝ] E) {H T C : ℝ} (hH : 0 ≤ H) {l K : ℕ}
    (hKT : (K : ℝ) * H ≤ T) (x0 : E) (x : ℕ → E)
    (hacc : ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0‖ ≤
      C * H ^ (l + 1) * ‖x0‖) :
    ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0‖ ≤
      (H ^ l * leadMax A S D T + C * H ^ (l + 1)) * ‖x0‖ := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  intro k hk
  have hk0 : 0 ≤ (k : ℝ) * H := by positivity
  have hkT : (k : ℝ) * H ≤ T :=
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hH) hKT
  have h2 := le_leadMax h1 A S D hk0 hkT
  have h3 : ‖H ^ l • runLead A S D (k * H) x0‖ ≤ H ^ l * leadMax A S D T * ‖x0‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left (((runLead A S D (k * H)).le_opNorm x0).trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg x0))) (by positivity)
  have h4 := norm_add_le (x k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0)
    (H ^ l • runLead A S D (k * H) x0)
  rw [sub_add_cancel] at h4
  have h5 := hacc k hk
  nlinarith

/-- **The error over a run is at least `H^l F - C' H^{l+1}`.** Let `E ≠ 0`, `0 < H`, `j H ≤ T`,
`K = ⌊T/H⌋`, and let the runs `x x_0` of all initial states satisfy the accumulation with the
constant `C ≥ 0` for `j ≤ k ≤ K`. If `δ` bounds their relative errors for `k ≤ K`, then
`δ ≥ H^l F(S, D) - (C + (j + 1) L) H^{l+1}`, `L = leadLip ‖A‖ ‖S‖ ‖D‖ T`. -/
theorem leadMax_le_of_runs [Nontrivial E] (A S D : E →L[ℝ] E) {H T C δ : ℝ} (hH : 0 < H)
    (hC : 0 ≤ C) {l j : ℕ} (hjT : (j : ℝ) * H ≤ T) (x : E → ℕ → E)
    (hacc : ∀ x0, ∀ k, j ≤ k → k ≤ ⌊T / H⌋₊ →
      ‖x x0 k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0‖ ≤
        C * H ^ (l + 1) * ‖x0‖)
    (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊T / H⌋₊, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    H ^ l * leadMax A S D T - (C + (j + 1) * leadLip ‖A‖ ‖S‖ ‖D‖ T) * H ^ (l + 1) ≤ δ := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hδ0 : 0 ≤ δ := relative_error_bound_nonneg hδ
  have hHl : 0 < H ^ l := by positivity
  set B := (δ + C * H ^ (l + 1)) / H ^ l with hB
  have hgrid : ∀ k : ℕ, j ≤ k → (k : ℝ) * H ≤ T → ‖runLead A S D (k * H)‖ ≤ B := by
    intro k hjk hkT
    have hkK : k ≤ ⌊T / H⌋₊ := Nat.le_floor ((le_div_iff₀ hH).2 hkT)
    rw [hB, le_div_iff₀ hHl, mul_comm]
    have h0 : 0 ≤ δ + C * H ^ (l + 1) := by positivity
    have h2 : ‖H ^ l • runLead A S D (k * H)‖ ≤ δ + C * H ^ (l + 1) := by
      refine ContinuousLinearMap.opNorm_le_bound _ h0 fun x0 => ?_
      rcases eq_or_ne x0 0 with rfl | hx0
      · simp
      have h3 := hδ x0 hx0 k hkK
      have h4 := hacc x0 k hjk hkK
      have h5 := norm_sub_le (x x0 k - (exp (H • A) ^ k) x0)
        (x x0 k - (exp (H • A) ^ k) x0 - H ^ l • runLead A S D (k * H) x0)
      rw [sub_sub_cancel] at h5
      rw [_root_.smul_apply]
      nlinarith
    rwa [norm_smul, Real.norm_of_nonneg hHl.le] at h2
  have h2 := leadMax_le_of_grid h1 A S D hH hjT hgrid
  have h3 := mul_le_mul_of_nonneg_left h2 hHl.le
  have e : H ^ l * (B + (j + 1) * H * leadLip ‖A‖ ‖S‖ ‖D‖ T) =
      δ + (C + (j + 1) * leadLip ‖A‖ ‖S‖ ‖D‖ T) * H ^ (l + 1) := by
    rw [hB, mul_add, mul_div_cancel₀ _ hHl.ne']
    ring
  rw [e] at h3
  linarith

end Accumulation

end CoSimFoundations
