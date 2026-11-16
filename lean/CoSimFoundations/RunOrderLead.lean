/-
The order over a run with `l` held samples, explicit form (the paper, Theorem `thm:runorder`,
second display, eq. `eq:orderl`).

**Paper.** "For a family of schemes in which a subsystem `i` with `c_i > 0` runs before all of
its partners and has bounded weights on its past samples,

  `ε_{⌊T/H⌋} ≥ γ_l c_i / ((30.3 (1 + n̄) + 14.3 m̄ l (l - 1)) ‖A‖) · H^l (1 - O(H))`,
  `T = 1/(2‖A‖)`."

**Setting.** That of `RunOrder` and `MemoryLead` together. `A`, `N`, `M r` are operators on the
state space `E`; the scheme is `(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` with `‖N‖ ≤ ν` (the paper's
`n̄`) and `‖M r‖ ≤ m̄` for `1 ≤ r < l`. `P : E → F` is the projection onto subsystem `i`
(`‖P‖ ≤ 1`), `C : E → G` the outputs of its partners, `P ∘ A = Ai ∘ P + L ∘ C`. The subsystem runs
before all of its partners: its block row of the scheme has no new sample and is the rule with
the local coefficient `Fi` and the coefficients `g r ∘ C` on the samples of the ages `r < l`,

  `P ∘ N = 0`,   `P ∘ M 0 = Fi ∘ P + g 0 ∘ C`,   `P ∘ M r = g r ∘ C`  (`1 ≤ r < l`),

with bounded weights `‖g r ∘ C‖ ≤ w H` for `1 ≤ r < l`. `c_i = unseenRate P C A l` is the norm of
`P A^{l+1}` on the states not shown up to the order `l` (eq. `eq:ci`).

**Statement** (`run_order_lead`). Let `l ≥ 1`, `2 l H ‖A‖ ≤ 1`, and let `K` be the number of steps
of the interval `T = 1/(2‖A‖)`: `K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`. If `δ` bounds the relative error
`‖x^k - U^k x_0‖ / ‖x_0‖` of the runs of all initial states `x_0 ≠ 0` for all `k ≤ K`, then

  `δ ≥ (γ_l c_i H^l - κ H^{l+1}) / ((212/7 (1 + ν) + 100/7 m̄ l (l - 1)) ‖A‖)`,
  `κ = C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1} + γ_l c_i (2 l + b_l + (l - 1)/3) ‖A‖`,

with the constants `b_l = memB l`, `C_1 = memC1 l`, `C_2 = memC2 l` of `MemoryLead`. For
`c_i > 0` the numerator is `γ_l c_i H^l (1 - (κ / (γ_l c_i)) H)`: the paper's `1 - O(H)` with an
explicit constant. `run_order_lead_floor` is the same for `K = ⌊T/H⌋` with the paper's constants
`30.3` and `14.3`.

**The constants.** `212/7 = 2.65/0.0875 = 30.2857…` and `100/7 = 1.25/0.0875 = 14.2857…`; the
paper's `30.3` and `14.3` are these numbers rounded up, so the paper's display follows from the
statement here (a larger denominator gives a weaker bound). They come from `eq:runorder`:
`0.175 (K - l + 1) H ≥ 0.0875 (1 - 2 l H ‖A‖) / ‖A‖`, and the denominator of `eq:runorder` is
`2.65 (1 + ν) + 1.25 m̄ l (l - 1)` at `H = 0`.

**Proof.** The block row of the local defect `T` of the scheme is the local defect `𝒯_i` of the
rule (`proj_comp_runDefect`), so `‖T‖ ≥ ‖𝒯_i‖`, and `memory_lead` bounds `‖𝒯_i‖` from below. In
`run_order_barrier` the first entry `0.175` of the minimum is never the smaller one here, because
`γ_l ≤ 1` (`adamsGamma_le_one`), `c_i ≤ ‖A‖^{l+1}` and `H ‖A‖ ≤ 1/2`. The remainder: with
`s = 2 l H ‖A‖`, `p = b_l H ‖A‖`, `q = (l - 1) H ‖A‖ / 3`, the factors `1 - s` (the length of the
run), `1 / (1 + p)` (`memory_lead`) and `1 / (1 + q)` (the exponential in the denominator of
`eq:runorder`, `e^{(l-1) H ‖A‖} ≤ 1 + 1.65 (l - 1) H ‖A‖`) multiply to at least `1 - s - p - q`
(`lead_arith`).

The statement is that of the paper for one scheme and one macro step; a family of schemes enters
through the constants `ν`, `m̄`, `w`, which the family keeps fixed as `H → 0`.
-/
import CoSimFoundations.RunOrder
import CoSimFoundations.MemoryLead

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Gamma

/-- The Adams–Bashforth error constant is not negative: `0 ≤ γ_l`. -/
theorem adamsGamma_nonneg (l : ℕ) : 0 ≤ adamsGamma l := by
  rw [adamsGamma_eq_integral]
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun s hs => ?_)
  exact prod_nonneg fun r _ => add_nonneg hs.1 (Nat.cast_nonneg r)

/-- The Adams–Bashforth error constant is at most one: `γ_l ≤ 1`, because
`∏_{r<l} (s + r) ≤ ∏_{r<l} (1 + r) = l!` on `[0, 1]`. -/
theorem adamsGamma_le_one (l : ℕ) : adamsGamma l ≤ 1 := by
  rw [adamsGamma_eq_integral]
  have hfac : ∏ r ∈ range l, ((r : ℝ) + 1) = (l ! : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  have h1 : ∫ s in (0 : ℝ)..1, ∏ r ∈ range l, (s + r) ≤ ∫ _s in (0 : ℝ)..1, (l ! : ℝ) := by
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun s hs => ?_
    · exact (continuous_finsetProd _ fun r _ =>
        continuous_id.add continuous_const).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
    · rw [← hfac]
      exact prod_le_prod₀ (fun r _ => add_nonneg hs.1 (Nat.cast_nonneg r))
        fun r _ => by linarith [hs.2]
  have h2 : ∫ _s in (0 : ℝ)..1, (l ! : ℝ) = (l ! : ℝ) := by simp
  have hl : (0 : ℝ) < (l ! : ℝ) := by positivity
  rw [h2] at h1
  calc ((l ! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1, ∏ r ∈ range l, (s + r)
      ≤ ((l ! : ℝ))⁻¹ * (l ! : ℝ) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hl.le)
    _ = 1 := inv_mul_cancel₀ hl.ne'

end Gamma

section Real

/-- The remainder of `eq:orderl`: for `0 ≤ s ≤ 1`, `p, q ≥ 0` and `Y ≤ G`, if
`Y - G (s + p + q) ≥ 0` then `(Y - G (s + p + q)) (1 + p) (1 + q) ≤ (1 - s) Y`. -/
theorem lead_arith {Y G s p q : ℝ} (hG : 0 ≤ G) (hY : Y ≤ G) (hs0 : 0 ≤ s) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hQ : 0 ≤ Y - G * (s + p + q)) :
    (Y - G * (s + p + q)) * ((1 + p) * (1 + q)) ≤ (1 - s) * Y := by
  have hu : 0 ≤ s + p + q := by linarith
  have hY0 : 0 ≤ Y := by
    have := mul_nonneg hG hu
    linarith
  have h1 : Y - G * (s + p + q) ≤ Y * (1 - (s + p + q)) := by
    have := mul_nonneg (sub_nonneg.2 hY) hu
    linarith
  have h2 : (1 - (s + p + q)) * ((1 + p) * (1 + q)) ≤ 1 - s := by
    nlinarith [mul_nonneg hs0 hp, mul_nonneg hs0 hq, mul_nonneg hp hq,
      mul_nonneg hs0 (mul_nonneg hp hq), mul_nonneg hp (mul_nonneg hp hq),
      mul_nonneg hq (mul_nonneg hp hq), sq_nonneg p, sq_nonneg q]
  have hpq : 0 ≤ (1 + p) * (1 + q) := by positivity
  calc (Y - G * (s + p + q)) * ((1 + p) * (1 + q))
      ≤ Y * (1 - (s + p + q)) * ((1 + p) * (1 + q)) := mul_le_mul_of_nonneg_right h1 hpq
    _ = Y * ((1 - (s + p + q)) * ((1 + p) * (1 + q))) := by ring
    _ ≤ Y * (1 - s) := mul_le_mul_of_nonneg_left h2 hY0
    _ = (1 - s) * Y := by ring

/-- The arithmetic of `eq:orderl`: from the bound over a run (`hbar`, `eq:runorder` with
`K' = K - l + 1`, `t = ‖T‖`, `e = e^{(l-1) H a}`), the lower bound on the local defect (`hmem`,
`eq:memorylead`) and the length of the run (`hKp`) to the explicit order-`l` bound. Here `a`
stands for `‖A‖`, `G` for `γ_l c_i`, `Hl` for `H^l`, `lr` for `l` and `mm` for `m̄ l (l - 1)`. -/
theorem lead_of_barrier {G R H Hl a t b ν mm Kp e lr δ : ℝ} (hlr : 1 ≤ lr) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hH : 0 < H) (hHl : 0 ≤ Hl) (ha : 0 < a) (ht : 0 ≤ t) (hb : 0 ≤ b) (hν : 0 ≤ ν)
    (hm : 0 ≤ mm) (he0 : 0 ≤ e) (he : e ≤ 1 + 1.65 * ((lr - 1) * (H * a)))
    (hlx : 2 * lr * (H * a) ≤ 1) (hG1 : G * Hl ≤ a / 2)
    (hKp : (1 - 2 * lr * (H * a)) / 2 ≤ Kp * (H * a))
    (hmem : G * (Hl * H) - R * (Hl * H * H) ≤ (1 + b * (H * a)) * t)
    (hbar : min 0.175 (0.175 * Kp * t / (2.65 * (1 + ν) + mm * (1 + 1 / 4 * e))) ≤ δ) :
    (G * Hl - (R + G * (2 * lr + b + (lr - 1) / 3) * a) * (Hl * H)) /
      ((212 / 7 * (1 + ν) + 100 / 7 * mm) * a) ≤ δ := by
  have hx : 0 < H * a := mul_pos hH ha
  have hs0 : 0 ≤ 2 * lr * (H * a) := mul_nonneg (by linarith) hx.le
  have hp0 : 0 ≤ b * (H * a) := mul_nonneg hb hx.le
  have hq0 : 0 ≤ (lr - 1) / 3 * (H * a) := mul_nonneg (by linarith) hx.le
  have hGl : 0 ≤ G * Hl := mul_nonneg hG hHl
  have hRH : 0 ≤ R * (Hl * H) := mul_nonneg hR (mul_nonneg hHl hH.le)
  have hYG : G * Hl - R * (Hl * H) ≤ G * Hl := by linarith
  have hQeq : G * Hl - (R + G * (2 * lr + b + (lr - 1) / 3) * a) * (Hl * H) =
      G * Hl - R * (Hl * H) -
        G * Hl * (2 * lr * (H * a) + b * (H * a) + (lr - 1) / 3 * (H * a)) := by
    ring
  have hD0 : 0 < 2.65 * (1 + ν) + 1.25 * mm := by linarith
  have hD0' : 0 < (212 / 7 * (1 + ν) + 100 / 7 * mm) * a := mul_pos (by linarith) ha
  have hD : 0 < 2.65 * (1 + ν) + mm * (1 + 1 / 4 * e) := by
    have := mul_nonneg hm (by linarith : (0 : ℝ) ≤ 1 + 1 / 4 * e)
    linarith
  have hDle : 2.65 * (1 + ν) + mm * (1 + 1 / 4 * e) ≤
      (2.65 * (1 + ν) + 1.25 * mm) * (1 + (lr - 1) / 3 * (H * a)) := by
    have h1 : mm * e ≤ mm * (1 + 1.65 * ((lr - 1) * (H * a))) := mul_le_mul_of_nonneg_left he hm
    have h2 : 0 ≤ mm * ((lr - 1) * (H * a)) :=
      mul_nonneg hm (mul_nonneg (by linarith) hx.le)
    have h3 : 0 ≤ (1 + ν) * ((lr - 1) * (H * a)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hx.le)
    nlinarith
  have hKp0 : 0 ≤ Kp := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.1 h) hx
    linarith
  have hδ0 : 0 ≤ δ :=
    le_trans (le_min (by norm_num)
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKp0) ht) hD.le)) hbar
  rw [hQeq]
  rcases le_or_gt (G * Hl - R * (Hl * H) -
      G * Hl * (2 * lr * (H * a) + b * (H * a) + (lr - 1) / 3 * (H * a))) 0 with hQ | hQ
  · exact (div_nonpos_of_nonpos_of_nonneg hQ hD0'.le).trans hδ0
  refine le_trans (le_min ?_ ?_) hbar
  · rw [div_le_iff₀ hD0']
    have h1 := mul_nonneg hGl (add_nonneg (add_nonneg hs0 hp0) hq0)
    have h2 : 212 / 7 * a ≤ (212 / 7 * (1 + ν) + 100 / 7 * mm) * a :=
      mul_le_mul_of_nonneg_right (by linarith) ha.le
    linarith
  · rw [div_le_div_iff₀ hD0' hD]
    have harith := lead_arith hGl hYG hs0 hp0 hq0 hQ.le
    have hHY : H * (G * Hl - R * (Hl * H)) ≤ (1 + b * (H * a)) * t := by linarith
    have hc : 0 < (1 + b * (H * a)) * H := mul_pos (by linarith) hH
    refine le_of_mul_le_mul_right ?_ hc
    calc (G * Hl - R * (Hl * H) -
            G * Hl * (2 * lr * (H * a) + b * (H * a) + (lr - 1) / 3 * (H * a))) *
          (2.65 * (1 + ν) + mm * (1 + 1 / 4 * e)) * ((1 + b * (H * a)) * H)
        ≤ (G * Hl - R * (Hl * H) -
            G * Hl * (2 * lr * (H * a) + b * (H * a) + (lr - 1) / 3 * (H * a))) *
          ((2.65 * (1 + ν) + 1.25 * mm) * (1 + (lr - 1) / 3 * (H * a))) *
            ((1 + b * (H * a)) * H) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDle hQ.le) hc.le
      _ = (2.65 * (1 + ν) + 1.25 * mm) * H * ((G * Hl - R * (Hl * H) -
            G * Hl * (2 * lr * (H * a) + b * (H * a) + (lr - 1) / 3 * (H * a))) *
          ((1 + b * (H * a)) * (1 + (lr - 1) / 3 * (H * a)))) := by ring
      _ ≤ (2.65 * (1 + ν) + 1.25 * mm) * H *
            ((1 - 2 * lr * (H * a)) * (G * Hl - R * (Hl * H))) :=
          mul_le_mul_of_nonneg_left harith (mul_nonneg hD0.le hH.le)
      _ = (2.65 * (1 + ν) + 1.25 * mm) * (1 - 2 * lr * (H * a)) *
            (H * (G * Hl - R * (Hl * H))) := by ring
      _ ≤ (2.65 * (1 + ν) + 1.25 * mm) * (1 - 2 * lr * (H * a)) *
            ((1 + b * (H * a)) * t) :=
          mul_le_mul_of_nonneg_left hHY (mul_nonneg hD0.le (by linarith))
      _ ≤ (2.65 * (1 + ν) + 1.25 * mm) * (2 * (Kp * (H * a))) * ((1 + b * (H * a)) * t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hD0.le)
            (mul_nonneg (by linarith) ht)
      _ = 0.175 * Kp * t * ((212 / 7 * (1 + ν) + 100 / 7 * mm) * a) *
            ((1 + b * (H * a)) * H) := by ring

end Real

section Operator

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- `c_i` of the paper (eq. `eq:ci`): the norm of `P A^{l+1}` on the states that subsystem `i` is
not shown up to the order `l` (`P v = 0`, `C A^q v = 0` for `q < l`). -/
noncomputable def unseenRate (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) : ℝ :=
  ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖

/-- `c_i ≥ 0`. -/
theorem unseenRate_nonneg (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) :
    0 ≤ unseenRate P C A l :=
  norm_nonneg ((P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL)

/-- `c_i ≤ ‖A‖^{l+1}` for a projection of norm at most one. -/
theorem unseenRate_le (hP : ‖P‖ ≤ 1) (l : ℕ) : unseenRate P C A l ≤ ‖A‖ ^ (l + 1) := by
  have h1 : ‖P ∘L (A ^ (l + 1))‖ ≤ ‖A‖ ^ (l + 1) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hP).trans (norm_pow_le' A (Nat.succ_pos l)))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (Submodule.norm_subtypeL_le _)).trans h1)

/-- **The block row of the local defect of the scheme is the local defect of the rule** (the paper,
after eq. `eq:multistep`), for a subsystem that runs before all of its partners: no new sample
(`P ∘ N = 0`), the local coefficient and the current samples in `M 0`, the samples of the age `r`
in `M r`. -/
theorem proj_comp_runDefect (N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) (H : ℝ) {l : ℕ} (hl : 1 ≤ l) (hrowN : P ∘L N = 0)
    (hrow0 : P ∘L M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → P ∘L M r = g r ∘L C) :
    P ∘L ((1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r) =
      localDefect P Fi g C A H l := by
  have hN : ∀ y, P (N y) = 0 := fun y => by
    simpa using congrArg (fun T : E →L[ℝ] F => T y) hrowN
  have h0 : ∀ y, P (M 0 y) = Fi (P y) + g 0 (C y) := fun y => by
    simpa using congrArg (fun T : E →L[ℝ] F => T y) hrow0
  have hr : ∀ r, 1 ≤ r → r < l → ∀ y, P (M r y) = g r (C y) := fun r h1 h2 y => by
    simpa using congrArg (fun T : E →L[ℝ] F => T y) (hrow r h1 h2)
  have hsum : ∀ v : E, ∑ r ∈ range l, P (M r ((exp (-(H • A)) ^ r) v)) =
      Fi (P v) + ∑ r ∈ range l, g r (C ((exp (-(H • A)) ^ r) v)) := by
    intro v
    have hterm : ∀ r ∈ range l, P (M r ((exp (-(H • A)) ^ r) v)) =
        (if r = 0 then Fi (P v) else 0) + g r (C ((exp (-(H • A)) ^ r) v)) := by
      intro r hr'
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · simp [h0]
      · rw [hr r hpos (mem_range.1 hr')]
        simp [hpos.ne']
    have h0mem : 0 ∈ range l := mem_range.2 (by omega)
    rw [sum_congr rfl hterm, sum_add_distrib]
    simp [h0mem]
  ext v
  simp only [localDefect, ContinuousLinearMap.comp_apply, _root_.sub_apply, _root_.sum_apply,
    mul_apply_eq_comp, one_apply_eq_self, map_sub, map_sum, hN, sub_zero, hsum]
  abel

variable [Nontrivial E]

/-- **Theorem `thm:runorder`, second display (`eq:orderl`), with an explicit remainder.**
Operators on a real Banach space `E ≠ 0`. Let subsystem `i` (projection `P`, `‖P‖ ≤ 1`, driven
through its own state and the outputs `C` of its partners, `P ∘ A = Ai ∘ P + L ∘ C`) run before
all of its partners in a scheme `(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` with `l ≥ 1` held
samples: `P ∘ N = 0`, `P ∘ M 0 = Fi ∘ P + g 0 ∘ C`, `P ∘ M r = g r ∘ C` for `1 ≤ r < l`, with
bounded weights `‖g r ∘ C‖ ≤ w H` on the past samples. Let `‖N‖ ≤ ν`, `‖M r‖ ≤ m̄` for
`1 ≤ r < l`, `2 l H ‖A‖ ≤ 1`, and let `K` be the number of steps of the interval `1/(2‖A‖)`:
`K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`. If `δ` bounds the relative error of the runs of all initial
states `x_0 ≠ 0` for all `k ≤ K`, then
`δ ≥ (γ_l c_i H^l - κ H^{l+1}) / ((212/7 (1 + ν) + 100/7 m̄ l (l - 1)) ‖A‖)` with
`κ = C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1} + γ_l c_i (2 l + b_l + (l - 1)/3) ‖A‖`, `c_i = unseenRate`,
`γ_l = adamsGamma l`, `b_l = memB l`, `C_1 = memC1 l`, `C_2 = memC2 l`. This is the paper's
display with the largest relative error replaced by any upper bound `δ` of the relative errors,
with `1 - O(H)` made explicit, and with `212/7 ≤ 30.3`, `100/7 ≤ 14.3`. -/
theorem run_order_lead (N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E)
    (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) {l K : ℕ} (hl : 1 ≤ l)
    (hrowN : P ∘L N = 0) (hrow0 : P ∘L M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → P ∘L M r = g r ∘L C)
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H)
    (hlx : 2 * l * (H * ‖A‖) ≤ 1) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    (hK1 : 1 / 2 < (K + 1) * H * ‖A‖) {ν mbar : ℝ} (hN : ‖N‖ ≤ ν)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    (adamsGamma l * unseenRate P C A l * H ^ l -
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) +
          adamsGamma l * unseenRate P C A l * (2 * l + memB l + ((l : ℝ) - 1) / 3) * ‖A‖) *
          H ^ (l + 1)) /
      ((212 / 7 * (1 + ν) + 100 / 7 * (mbar * ((l : ℝ) * (l - 1)))) * ‖A‖) ≤ δ := by
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH hA0
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hxpos : 0 < H * ‖A‖ := by
    by_contra h
    have h0 : H * ‖A‖ = 0 := le_antisymm (not_lt.1 h) hx0
    rw [mul_assoc, h0, mul_zero] at hK1
    norm_num at hK1
  have hHpos : 0 < H := lt_of_le_of_ne hH fun h => by
    rw [← h, zero_mul] at hxpos
    exact lt_irrefl _ hxpos
  have hApos : 0 < ‖A‖ := lt_of_le_of_ne hA0 fun h => by
    rw [← h, mul_zero] at hxpos
    exact lt_irrefl _ hxpos
  have hlx' : (l : ℝ) * (H * ‖A‖) ≤ 1 / 2 := by linarith
  have hxhalf : H * ‖A‖ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hl1 hx0
    linarith
  have hK : l ≤ K := by
    by_contra h
    have h1 : (K : ℝ) + 1 ≤ l := by exact_mod_cast not_le.1 h
    have h2 : ((K : ℝ) + 1) * (H * ‖A‖) ≤ l * (H * ‖A‖) := mul_le_mul_of_nonneg_right h1 hx0
    linarith
  -- the bound over a run and the bound on the local defect
  have hbar := run_order_barrier A N M hH hl hK hKH hN hM x hx hδ
  have hrowT := proj_comp_runDefect (P := P) (C := C) (A := A) N M Fi g H hl hrowN hrow0 hrow
  have htl : ‖localDefect P Fi g C A H l‖ ≤
      ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ := by
    rw [← hrowT]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hP)
  have hmem : adamsGamma l * unseenRate P C A l * H ^ (l + 1) -
      (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) ≤
      (1 + memB l * (H * ‖A‖)) * ‖localDefect P Fi g C A H l‖ :=
    memory_lead hA hP Fi g hH hw0 (by linarith) hl hw
  have hb0 := memB_nonneg l
  have hmem' : adamsGamma l * unseenRate P C A l * (H ^ l * H) -
      (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * (H ^ l * H * H) ≤
      (1 + memB l * (H * ‖A‖)) *
        ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ := by
    have h1 := mul_le_mul_of_nonneg_left htl
      (by nlinarith : (0 : ℝ) ≤ 1 + memB l * (H * ‖A‖))
    rw [pow_succ H (l + 1), pow_succ H l] at hmem
    exact hmem.trans h1
  -- the constants
  have hG0 : 0 ≤ adamsGamma l * unseenRate P C A l :=
    mul_nonneg (adamsGamma_nonneg l) (unseenRate_nonneg P C A l)
  have hR0 : 0 ≤ memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) := by
    have h1 := memC1_nonneg l
    have h2 := memC2_nonneg l
    positivity
  have hν0 : 0 ≤ ν := (norm_nonneg N).trans hN
  have hmm : 0 ≤ mbar * ((l : ℝ) * (l - 1)) := by
    rcases Nat.lt_or_ge 1 l with h2 | h2
    · exact mul_nonneg ((norm_nonneg _).trans (hM 1 le_rfl h2))
        (mul_nonneg (by linarith) (by linarith))
    · have h1 : l = 1 := by omega
      rw [h1]
      simp
  have hy0 : 0 ≤ ((l : ℝ) - 1) * (H * ‖A‖) := mul_nonneg (by linarith) hx0
  have he : Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) ≤ 1 + 1.65 * (((l : ℝ) - 1) * (H * ‖A‖)) := by
    have h1 := exp_sub_one_le_mul_exp (((l : ℝ) - 1) * (H * ‖A‖))
    have h2 : Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 := exp_half_lt
    have h4 : ((l : ℝ) - 1) * (H * ‖A‖) * Real.exp (((l : ℝ) - 1) * (H * ‖A‖)) ≤
        ((l : ℝ) - 1) * (H * ‖A‖) * 1.65 := mul_le_mul_of_nonneg_left (by linarith) hy0
    linarith
  have hG1 : adamsGamma l * unseenRate P C A l * H ^ l ≤ ‖A‖ / 2 := by
    have h1 : adamsGamma l * unseenRate P C A l ≤ 1 * ‖A‖ ^ (l + 1) :=
      mul_le_mul (adamsGamma_le_one l) (unseenRate_le hP l) (unseenRate_nonneg P C A l)
        zero_le_one
    have h2 : (H * ‖A‖) ^ l ≤ 1 / 2 :=
      (pow_le_of_le_one hx0 (by linarith) (by omega)).trans hxhalf
    calc adamsGamma l * unseenRate P C A l * H ^ l
        ≤ 1 * ‖A‖ ^ (l + 1) * H ^ l := mul_le_mul_of_nonneg_right h1 (pow_nonneg hH l)
      _ = ‖A‖ * (H * ‖A‖) ^ l := by rw [mul_pow, pow_succ]; ring
      _ ≤ ‖A‖ * (1 / 2) := mul_le_mul_of_nonneg_left h2 hA0
      _ = ‖A‖ / 2 := by ring
  have hKp : (1 - 2 * (l : ℝ) * (H * ‖A‖)) / 2 ≤ ((K : ℝ) - l + 1) * (H * ‖A‖) := by
    linarith
  rw [pow_succ H l]
  exact lead_of_barrier hl1 hG0 hR0 hHpos (pow_nonneg hH l) hApos (norm_nonneg _) hb0 hν0 hmm
    (Real.exp_pos _).le he hlx hG1 hKp hmem' hbar

/-- **Theorem `thm:runorder`, eq. `eq:orderl`, for `K = ⌊T/H⌋`, `T = 1/(2‖A‖)`, with the paper's
constants `30.3` and `14.3`** and the explicit remainder of `run_order_lead`: under the hypotheses
of `run_order_lead` on the scheme and on subsystem `i`, for `H > 0`, `A ≠ 0` and `2 l H ‖A‖ ≤ 1`,
every bound `δ` on the relative errors of the runs up to the step `⌊T/H⌋` satisfies
`δ ≥ (γ_l c_i H^l - κ H^{l+1}) / ((30.3 (1 + ν) + 14.3 m̄ l (l - 1)) ‖A‖)`. -/
theorem run_order_lead_floor (N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E)
    (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    {H w : ℝ} (hH : 0 < H) (hA0 : A ≠ 0) (hw0 : 0 ≤ w) {l : ℕ} (hl : 1 ≤ l)
    (hrowN : P ∘L N = 0) (hrow0 : P ∘L M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → P ∘L M r = g r ∘L C)
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H)
    (hlx : 2 * l * (H * ‖A‖) ≤ 1) {ν mbar : ℝ} (hN : ‖N‖ ≤ ν)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < ⌊1 / (2 * ‖A‖) / H⌋₊ →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊1 / (2 * ‖A‖) / H⌋₊,
      ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    (adamsGamma l * unseenRate P C A l * H ^ l -
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) +
          adamsGamma l * unseenRate P C A l * (2 * l + memB l + ((l : ℝ) - 1) / 3) * ‖A‖) *
          H ^ (l + 1)) /
      ((30.3 * (1 + ν) + 14.3 * (mbar * ((l : ℝ) * (l - 1)))) * ‖A‖) ≤ δ := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.2 hA0
  have hy : 0 < 2 * ‖A‖ * H := by positivity
  have he : 1 / (2 * ‖A‖) / H * (2 * ‖A‖ * H) = 1 := by
    field_simp
  have h1 : ((⌊1 / (2 * ‖A‖) / H⌋₊ : ℕ) : ℝ) * (2 * ‖A‖ * H) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hy.le).trans he.le
  have h2 : 1 < (((⌊1 / (2 * ‖A‖) / H⌋₊ : ℕ) : ℝ) + 1) * (2 * ‖A‖ * H) :=
    he.symm.le.trans_lt (mul_lt_mul_of_pos_right (Nat.lt_floor_add_one _) hy)
  have hmain := run_order_lead N M hA hP Fi g hH.le hw0 hl hrowN hrow0 hrow hw hlx
    (K := ⌊1 / (2 * ‖A‖) / H⌋₊) (by linarith) (by linarith) hN hM x hx hδ
  have hδ0 : 0 ≤ δ := by
    obtain ⟨y, hy'⟩ := exists_ne (0 : E)
    have h := (norm_nonneg _).trans (hδ y hy' 0 (Nat.zero_le _))
    exact nonneg_of_mul_nonneg_left h (norm_pos_iff.2 hy')
  have hν0 : 0 ≤ ν := (norm_nonneg N).trans hN
  have hmm : 0 ≤ mbar * ((l : ℝ) * (l - 1)) := by
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    rcases Nat.lt_or_ge 1 l with h2 | h2
    · exact mul_nonneg ((norm_nonneg _).trans (hM 1 le_rfl h2))
        (mul_nonneg (by linarith) (by linarith))
    · have h1 : l = 1 := by omega
      rw [h1]
      simp
  have hd1 : 0 < (212 / 7 * (1 + ν) + 100 / 7 * (mbar * ((l : ℝ) * (l - 1)))) * ‖A‖ :=
    mul_pos (by linarith) hApos
  have hd2 : (212 / 7 * (1 + ν) + 100 / 7 * (mbar * ((l : ℝ) * (l - 1)))) * ‖A‖ ≤
      (30.3 * (1 + ν) + 14.3 * (mbar * ((l : ℝ) * (l - 1)))) * ‖A‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hApos.le
  rcases le_or_gt (adamsGamma l * unseenRate P C A l * H ^ l -
      (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) +
        adamsGamma l * unseenRate P C A l * (2 * l + memB l + ((l : ℝ) - 1) / 3) * ‖A‖) *
        H ^ (l + 1)) 0 with hQ | hQ
  · exact (div_nonpos_of_nonpos_of_nonneg hQ (hd1.le.trans hd2)).trans hδ0
  · exact (div_le_div_of_nonneg_left hQ.le hd1 hd2).trans hmain

end Operator

end CoSimFoundations
