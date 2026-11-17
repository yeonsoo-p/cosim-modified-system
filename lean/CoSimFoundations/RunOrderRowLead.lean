/-
The two leading-order displays that follow from the bound over a run for one block row (the
paper, the displays `eq:orderlmain` and `eq:firstorder` after the theorem
"order over a run"), with the printed constants and
explicit remainders.

**(30).** A subsystem `i` (projection `P`, `‖P‖ ≤ 1`, `P ∘ A = Ai ∘ P + L ∘ C`) with `l` held
samples that are all old or all new, with coefficients bounded by `w H` on the samples of every
instant other than `t_k`. Its row of the recursion is `(P - N) x^{k+1} = Σ_{r<l} M r x^{k-r}`
with `‖N‖ ≤ n̄`, `‖M r‖ ≤ m̄` (`1 ≤ r < l`), `b_i = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`. Over the
interval of length `1/(2‖A‖)` (`K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`, or `K = ⌊1/(2‖A‖)/H⌋`), for
`2 l H ‖A‖ ≤ 1`, every bound `δ` of the relative errors satisfies

  `δ ≥ 0.35 (|γ| c_i H^l - κ H^{l+1}) / (2 b_i ‖A‖)`,
  `κ = C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1} + |γ| c_i (2 l + β + 1/5) ‖A‖`,

that is `0.35 |γ| c_i / (2 b_i ‖A‖) · H^l (1 - (κ / (|γ| c_i)) H)`: the paper's display with its
constant `0.35 / (2 b_i ‖A‖)`.
* old samples (`run_order_row_lead`, `run_order_row_lead_floor`): `N = 0`,
  `M 0 = Fi ∘ P + g 0 ∘ C`, `M r = g r ∘ C`; `γ = adamsGamma l`, `β = memB l`, `C_1 = memC1 l`,
  `C_2 = memC2 l` (`memory_lead`);
* new samples (`run_order_row_late`, `run_order_row_late_floor`): `N = gNew ∘ C`,
  `M 0 = Fi ∘ P + g 0 ∘ C`, `M r = g r ∘ C`, `g (l-1) = 0` (the new sample and those of the ages
  `0, …, l-2`); `γ = lateGamma l`, `β = lateB l`, `C_1 = lateC1 l`, `C_2 = lateC2 l`
  (`memory_late`).
`c_i = unseenRate P C A l` is the norm of `P A^{l+1}` on the states not shown up to the order
`l`. Both follow from `run_order_row_lead_of_defect`, which takes any lower bound
`Γ H^{l+1} - R H^{l+2} ≤ (1 + β H ‖A‖) ‖T_i‖` of the local defect of the row.

**(31).** One held sample, a consistent scheme (`HeldScheme.Consistent`), subsystems `s ≠ t`
that are not partners, `‖Π_s N‖ ≤ n̄`, `b_s = 2.65 (1 + n̄)`, `K = ⌊1/(2 H ‖A‖)⌋`. If
`‖X^k - U^k‖ ≤ δ` for `k ≤ K`, then (`Consistent.first_order_row_lead`)

  `δ ≥ 0.35 (‖[A_ς A]_st‖ H - κ' H²) / (4 b_s ‖A‖)`,
  `κ' = 2 (C₃ + a c) + (11/5) ‖[A_ς A]_st‖ ‖A‖`,

with `C₃ = reactionC a b c ‖A‖ H` and `a`, `c` the constants of consistency (`‖N‖ ≤ a H`,
`‖X - U‖ ≤ c H²`): the paper's display with its constant `0.35 / (4 b_s ‖A‖)`. The row `s` of the
recursion is `(Π_s - Π_s N) x^{k+1} = Π_s (F + M) x^k`, its local defect is
`T_s = Π_s (1 - N)(U - X)`, and its block `(s, t)` is that of `U - X` up to `‖N‖ ‖X - U‖`
(`Consistent.norm_row_defect_ge`: `a_st H² - (C₃ + a c) H³ ≤ ‖T_s‖`, `a_st = ½ ‖[A_ς A]_st‖`).

**The arithmetic** (`row_lead_arith`). From `δ ≥ 0.35 K' t / (b + K' t)` (`run_order_row`),
`G H^{l+1} - R H^{l+2} ≤ (1 + β x) t`, `K' x ≥ (1 - 2 l x)/2`, `x = H ‖A‖`, `G H^l ≤ ‖A‖ x` and
`b ≥ 2.65`: with `Y = G H^l - R H^{l+1}` and `Q = Y - G H^l (2 l + β + 1/5) x`,
`K' t ≥ (1 - 2 l x) Y / (2 ‖A‖ (1 + β x))`, `Q ≤ Y (1 - (2 l + β + 1/5) x)`, `Q ≤ ‖A‖ x`, and
`2 b (1 + β x)(1 - (2 l + β + 1/5) x) ≤ (1 - 2 l x)(2 b - x)` give `Q b ≤ K' t (2 b ‖A‖ - Q)`,
which is `0.35 Q / (2 b ‖A‖) ≤ 0.35 K' t / (b + K' t)`. The term `1/5` pays for the saturation
`T_K / (b + T_K)` in place of `T_K / b`.
-/
import CoSimFoundations.RunOrderRow
import CoSimFoundations.RunOrderLead
import CoSimFoundations.MemoryLate
import CoSimFoundations.FirstOrderLead

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Real

/-- The core of the arithmetic: for `0 < Q ≤ Y`, `Q ≤ Y (1 - u)`, `u = (2 l + β + 1/5) x`,
`Y ≤ a x`, `b ≥ 2.65` and `(1 - 2 l x) Y ≤ 2 a (1 + β x) W`: `Q b ≤ W (2 b a - Q)`. -/
theorem row_lead_core {Q Y u x a b β lr W : ℝ} (ha : 0 < a) (hx0 : 0 < x) (hβ : 0 ≤ β)
    (hb : 2.65 ≤ b) (hlr : 1 ≤ lr) (hlx : 2 * lr * x ≤ 1)
    (hu : u = (2 * lr + β + 1 / 5) * x) (hQ0 : 0 < Q) (hQY1 : Q ≤ Y) (hQY : Q ≤ Y * (1 - u))
    (hYa : Y ≤ a * x) (hW : (1 - 2 * lr * x) * Y ≤ 2 * a * (1 + β * x) * W) :
    Q * b ≤ W * (2 * b * a - Q) := by
  have hx2 : x ≤ 1 / 2 := by
    have := mul_nonneg (sub_nonneg.2 hlr) hx0.le
    linarith
  have hY0 : 0 < Y := hQ0.trans_le hQY1
  have hc : 0 < 2 * a * (1 + β * x) := by
    have := mul_nonneg hβ hx0.le
    positivity
  have hkey : 2 * b * (1 + β * x) * (1 - u) ≤ (1 - 2 * lr * x) * (2 * b - x) := by
    have h1 : 0 ≤ (b - 5 / 2) * x := mul_nonneg (by linarith) hx0.le
    have h2 : 0 ≤ lr * (x * x) := mul_nonneg (by linarith) (mul_nonneg hx0.le hx0.le)
    have h3 : 0 ≤ b * β * ((2 * lr + β + 1 / 5) * (x * x)) :=
      mul_nonneg (mul_nonneg (by linarith) hβ)
        (mul_nonneg (by linarith) (mul_nonneg hx0.le hx0.le))
    rw [hu]
    nlinarith [h1, h2, h3]
  have hQa : Q ≤ a * x := hQY1.trans hYa
  have h2ba : 0 ≤ 2 * b * a - Q := by nlinarith [mul_pos ha hx0]
  have hl0 : 0 ≤ (1 - 2 * lr * x) * Y := mul_nonneg (by linarith) hY0.le
  refine le_of_mul_le_mul_right ?_ hc
  calc Q * b * (2 * a * (1 + β * x))
      ≤ Y * (1 - u) * b * (2 * a * (1 + β * x)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQY (by linarith)) hc.le
    _ = a * Y * (2 * b * (1 + β * x) * (1 - u)) := by ring
    _ ≤ a * Y * ((1 - 2 * lr * x) * (2 * b - x)) :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg ha.le hY0.le)
    _ = (1 - 2 * lr * x) * Y * (2 * b * a - a * x) := by ring
    _ ≤ (1 - 2 * lr * x) * Y * (2 * b * a - Q) :=
        mul_le_mul_of_nonneg_left (by linarith) hl0
    _ ≤ 2 * a * (1 + β * x) * W * (2 * b * a - Q) := mul_le_mul_of_nonneg_right hW h2ba
    _ = W * (2 * b * a - Q) * (2 * a * (1 + β * x)) := by ring

/-- **The arithmetic of the two displays:** from the bound over a run for one row (`hbar`, with
`Kp = K - l + 1`, `t = ‖T_i‖`), a lower bound of the local defect (`hmem`) and the length of the
run (`hKp`) to the leading-order bound with the constant `0.35 / (2 b a)`. Here `a` stands for
`‖A‖`, `G` for `|γ| c_i` (or `a_st`), `Hl` for `H^l`, `lr` for `l`. -/
theorem row_lead_arith {G R H Hl a t β b Kp lr δ : ℝ} (hlr : 1 ≤ lr) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hH : 0 < H) (hHl : 0 ≤ Hl) (ha : 0 < a) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hb : 2.65 ≤ b)
    (hlx : 2 * lr * (H * a) ≤ 1) (hG1 : G * Hl ≤ a * (H * a))
    (hKp : (1 - 2 * lr * (H * a)) / 2 ≤ Kp * (H * a))
    (hmem : G * (Hl * H) - R * (Hl * H * H) ≤ (1 + β * (H * a)) * t)
    (hbar : 0.35 * (Kp * t) / (b + Kp * t) ≤ δ) :
    0.35 * (G * Hl - (R + G * (2 * lr + β + 1 / 5) * a) * (Hl * H)) / (2 * b * a) ≤ δ := by
  have hx : 0 < H * a := mul_pos hH ha
  have hKp0 := run_length_nonneg_of_le hx hlx hKp
  have hKt : 0 ≤ Kp * t := mul_nonneg hKp0 ht
  have hδ0 : 0 ≤ δ :=
    le_trans (div_nonneg (mul_nonneg (by norm_num) hKt) (by linarith)) hbar
  have hd : 0 < 2 * b * a := by
    have : 0 < b := by linarith
    positivity
  rcases le_or_gt (G * Hl - (R + G * (2 * lr + β + 1 / 5) * a) * (Hl * H)) 0 with hQ | hQ
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hQ) hd.le).trans hδ0
  have hGl : 0 ≤ G * Hl := mul_nonneg hG hHl
  have hRH : 0 ≤ R * (Hl * H) := mul_nonneg hR (mul_nonneg hHl hH.le)
  have hu0 : 0 ≤ (2 * lr + β + 1 / 5) * (H * a) := mul_nonneg (by linarith) hx.le
  have hQY1 : G * Hl - (R + G * (2 * lr + β + 1 / 5) * a) * (Hl * H) ≤ G * Hl - R * (Hl * H) := by
    have := mul_nonneg hGl hu0
    linarith
  have hQY : G * Hl - (R + G * (2 * lr + β + 1 / 5) * a) * (Hl * H) ≤
      (G * Hl - R * (Hl * H)) * (1 - (2 * lr + β + 1 / 5) * (H * a)) := by
    have := mul_nonneg hRH hu0
    linarith
  have hYa : G * Hl - R * (Hl * H) ≤ a * (H * a) := by linarith
  have hY0 : 0 ≤ G * Hl - R * (Hl * H) := hQ.le.trans hQY1
  have hW : (1 - 2 * lr * (H * a)) * (G * Hl - R * (Hl * H)) ≤
      2 * a * (1 + β * (H * a)) * (Kp * t) := by
    have h1 : (1 - 2 * lr * (H * a)) * (G * Hl - R * (Hl * H)) ≤
        2 * (Kp * (H * a)) * (G * Hl - R * (Hl * H)) :=
      mul_le_mul_of_nonneg_right (by linarith) hY0
    have h2 : H * (G * Hl - R * (Hl * H)) ≤ (1 + β * (H * a)) * t := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg hKp0 ha.le))
    linarith
  have hmain := row_lead_core ha hx hβ hb hlr hlx rfl hQ hQY1 hQY hYa hW
  refine le_trans ?_ hbar
  rw [div_le_div_iff₀ hd (by linarith)]
  linarith

/-- The constant of a subsystem that runs after its partners is at most one in modulus:
`|γ'_l| ≤ (l-1)!/l! ≤ 1`. -/
theorem abs_lateGamma_le_one {l : ℕ} (hl : 1 ≤ l) : |lateGamma l| ≤ 1 := by
  have hl0 : (0 : ℝ) < (l ! : ℝ) := by positivity
  rw [lateGamma_eq_integral hl, abs_mul, abs_of_nonneg (inv_nonneg.2 hl0.le)]
  have hfac : ∏ r ∈ range (l - 1), ((r : ℝ) + 1) = ((l - 1) ! : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  have h1 : ‖∫ s in (0 : ℝ)..1, (s - 1) * ∏ k ∈ range (l - 1), (s + k)‖ ≤
      ((l - 1) ! : ℝ) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hp : 0 ≤ ∏ k ∈ range (l - 1), (s + k) :=
      prod_nonneg fun r _ => add_nonneg hs.1.le (Nat.cast_nonneg r)
    have h2 : |s - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    have h3 : ∏ k ∈ range (l - 1), (s + k) ≤ ∏ r ∈ range (l - 1), ((r : ℝ) + 1) :=
      prod_le_prod₀ (fun r _ => add_nonneg hs.1.le (Nat.cast_nonneg r))
        fun r _ => by linarith [hs.2]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp, ← hfac]
    exact (mul_le_mul h2 h3 hp zero_le_one).trans_eq (one_mul _)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h1
  have h4 : ((l - 1) ! : ℝ) ≤ (l ! : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.sub_le l 1)
  calc ((l ! : ℝ))⁻¹ * |∫ s in (0 : ℝ)..1, (s - 1) * ∏ k ∈ range (l - 1), (s + k)|
      ≤ ((l ! : ℝ))⁻¹ * (l ! : ℝ) :=
        mul_le_mul_of_nonneg_left (h1.trans h4) (inv_nonneg.2 hl0.le)
    _ = 1 := inv_mul_cancel₀ hl0.ne'

end Real

section Operator

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- The sum of the samples in the row of a rule: with `M 0 = Fi ∘ P + g 0 ∘ C` and
`M r = g r ∘ C` for `1 ≤ r ≤ n`, `Σ_{r ≤ n} M r (W^r v) = Fi (P v) + Σ_{r ≤ n} g r (C (W^r v))`. -/
theorem sum_row_rule_apply (W : E →L[ℝ] E) (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F) {n : ℕ}
    {M : ℕ → E →L[ℝ] F} (hrow0 : M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < n + 1 → M r = g r ∘L C) (v : E) :
    ∑ r ∈ range (n + 1), M r ((W ^ r) v) =
      Fi (P v) + ∑ r ∈ range (n + 1), g r (C ((W ^ r) v)) := by
  have hs : ∀ r ∈ range n, M (r + 1) ((W ^ (r + 1)) v) = g (r + 1) (C ((W ^ (r + 1)) v)) := by
    intro r hr
    rw [hrow (r + 1) (by omega) (by have := mem_range.1 hr; omega)]
    rfl
  rw [sum_range_succ', sum_range_succ', hrow0, sum_congr rfl hs]
  simp only [pow_zero, one_apply_eq_self, _root_.add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- **The local defect of the row of a subsystem with old samples only** is `localDefect`:
`N = 0`, `M 0 = Fi ∘ P + g 0 ∘ C`, `M r = g r ∘ C` for `1 ≤ r < l`. -/
theorem rowDefect_eq_localDefect (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F) (H : ℝ) {l : ℕ}
    (hl : 1 ≤ l) {N : E →L[ℝ] F} {M : ℕ → E →L[ℝ] F} (hrowN : N = 0)
    (hrow0 : M 0 = Fi ∘L P + g 0 ∘L C) (hrow : ∀ r, 1 ≤ r → r < l → M r = g r ∘L C) :
    rowDefect P N M (exp (H • A)) (exp (-(H • A))) l = localDefect P Fi g C A H l := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  ext v
  rw [rowDefect_apply, sum_row_rule_apply (exp (-(H • A))) Fi g hrow0 hrow v, hrowN, sub_zero]
  unfold localDefect
  simp only [_root_.sub_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  abel

/-- **The local defect of the row of a subsystem with a new sample** is `lateDefect`:
`N = gNew ∘ C`, `M 0 = Fi ∘ P + g 0 ∘ C`, `M r = g r ∘ C` for `1 ≤ r < l`, and the oldest
sample is not used (`g (l-1) = 0`). -/
theorem rowDefect_eq_lateDefect (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    (H : ℝ) {l : ℕ} (hl : 1 ≤ l) {N : E →L[ℝ] F} {M : ℕ → E →L[ℝ] F} (hrowN : N = gNew ∘L C)
    (hrow0 : M 0 = Fi ∘L P + g 0 ∘L C) (hrow : ∀ r, 1 ≤ r → r < l → M r = g r ∘L C)
    (hlast : g (l - 1) = 0) :
    rowDefect P N M (exp (H • A)) (exp (-(H • A))) l = lateDefect P Fi gNew g C A H l := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hlast
  ext v
  rw [rowDefect_apply, sum_row_rule_apply (exp (-(H • A))) Fi g hrow0 hrow v,
    sum_range_succ_of_last_eq_zero g hlast, hrowN]
  unfold lateDefect
  simp only [_root_.sub_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    Nat.add_sub_cancel]
  abel

variable [Nontrivial E]

/-- **The leading-order bound over a run for one row, from a lower bound of its local defect.**
In the setting of `run_order_row` let `K` be the number of steps of the interval `1/(2‖A‖)`
(`K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`), `2 l H ‖A‖ ≤ 1`, and let the local defect `T_i` of the row
satisfy `Γ H^{l+1} - R H^{l+2} ≤ (1 + β H ‖A‖) ‖T_i‖` with `0 ≤ Γ ≤ ‖A‖^{l+1}`, `R, β ≥ 0`. Then
`δ ≥ 0.35 (Γ H^l - (R + Γ (2 l + β + 1/5) ‖A‖) H^{l+1}) / (2 b_i ‖A‖)`,
`b_i = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`. -/
theorem run_order_row_lead_of_defect (A : E →L[ℝ] E) (P N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F)
    {H : ℝ} (hH : 0 ≤ H) {l K : ℕ} (hl : 1 ≤ l) (hlx : 2 * l * (H * ‖A‖) ≤ 1)
    (hKH : K * H * ‖A‖ ≤ 1 / 2) (hK1 : 1 / 2 < (K + 1) * H * ‖A‖) {nbar mbar : ℝ}
    (hP : ‖P‖ ≤ 1) (hN : ‖N‖ ≤ nbar) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar)
    (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖)
    {Γ R β : ℝ} (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ ‖A‖ ^ (l + 1)) (hR : 0 ≤ R) (hβ : 0 ≤ β)
    (hmem : Γ * H ^ (l + 1) - R * H ^ (l + 2) ≤
      (1 + β * (H * ‖A‖)) * ‖rowDefect P N M (exp (H • A)) (exp (-(H • A))) l‖) :
    0.35 * (Γ * H ^ l - (R + Γ * (2 * l + β + 1 / 5) * ‖A‖) * H ^ (l + 1)) /
      (2 * (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1))) * ‖A‖) ≤ δ := by
  obtain ⟨hHpos, hApos⟩ := pos_of_half_lt_horizon hH (norm_nonneg A) hK1
  have hx0 : 0 ≤ H * ‖A‖ := (mul_pos hHpos hApos).le
  have hx1 : H * ‖A‖ ≤ 1 := (le_half_of_two_mul_le hl hx0 hlx).trans (by norm_num)
  have hK : l ≤ K := le_of_half_lt_horizon hx0 hlx hK1
  have hbar := run_order_row A P N M hH hl hK hKH hP hN hM x hx hδ
  have hn : 0 ≤ nbar := (norm_nonneg N).trans hN
  have hmm := bound_mul_pred_nonneg hl hM
  have hb : (2.65 : ℝ) ≤ 2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1)) := by linarith
  have hG1 : Γ * H ^ l ≤ ‖A‖ * (H * ‖A‖) := by
    have h2 : (H * ‖A‖) ^ l ≤ H * ‖A‖ := pow_le_of_le_one hx0 hx1 (by omega)
    calc Γ * H ^ l ≤ ‖A‖ ^ (l + 1) * H ^ l := mul_le_mul_of_nonneg_right hΓ (pow_nonneg hH l)
      _ = ‖A‖ * (H * ‖A‖) ^ l := by rw [mul_pow, pow_succ]; ring
      _ ≤ ‖A‖ * (H * ‖A‖) := mul_le_mul_of_nonneg_left h2 hApos.le
  have hKp : (1 - 2 * (l : ℝ) * (H * ‖A‖)) / 2 ≤ ((K : ℝ) - l + 1) * (H * ‖A‖) := by
    linarith
  rw [pow_succ H (l + 1), pow_succ H l] at hmem
  rw [pow_succ H l]
  exact row_lead_arith (by exact_mod_cast hl) hΓ0 hR hHpos (pow_nonneg hH l) hApos
    (norm_nonneg _) hβ hb hlx hG1 hKp hmem hbar

/-- **Display (30) for a subsystem with old samples, with an explicit remainder.** Subsystem `i`
(projection `P`, `‖P‖ ≤ 1`, `P ∘ A = Ai ∘ P + L ∘ C`) with `l ≥ 1` held samples, all old: its
row of the recursion is `(P - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` with `N = 0`,
`M 0 = Fi ∘ P + g 0 ∘ C`, `M r = g r ∘ C` for `1 ≤ r < l`, and `‖g r ∘ C‖ ≤ w H` on the past
samples. Let `‖N‖ ≤ n̄` (one may take `n̄ = 0`), `‖M r‖ ≤ m̄` for `1 ≤ r < l`, `2 l H ‖A‖ ≤ 1`
and `K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`. If `δ` bounds the relative error of the sequences of all
initial states `x_0 ≠ 0` for `k ≤ K`, then
`δ ≥ 0.35 (γ_l c_i H^l - κ H^{l+1}) / (2 b_i ‖A‖)`, `b_i = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`,
`κ = C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1} + γ_l c_i (2 l + b_l + 1/5) ‖A‖`, with `γ_l = adamsGamma l`,
`c_i = unseenRate P C A l`, `b_l = memB l`, `C_1 = memC1 l`, `C_2 = memC2 l`. -/
theorem run_order_row_lead (N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F)
    (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) {l K : ℕ} (hl : 1 ≤ l)
    (hrowN : N = 0) (hrow0 : M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → M r = g r ∘L C)
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H)
    (hlx : 2 * l * (H * ‖A‖) ≤ 1) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    (hK1 : 1 / 2 < (K + 1) * H * ‖A‖) {nbar mbar : ℝ} (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (adamsGamma l * unseenRate P C A l * H ^ l -
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) +
          adamsGamma l * unseenRate P C A l * (2 * l + memB l + 1 / 5) * ‖A‖) * H ^ (l + 1)) /
      (2 * (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1))) * ‖A‖) ≤ δ := by
  have hmem := memory_lead hA hP Fi g hH hw0
    ((le_half_of_two_mul_le hl (mul_nonneg hH (norm_nonneg A)) hlx).trans (by norm_num)) hl hw
  rw [← rowDefect_eq_localDefect Fi g H hl hrowN hrow0 hrow] at hmem
  have hΓ : adamsGamma l * unseenRate P C A l ≤ ‖A‖ ^ (l + 1) :=
    (mul_le_mul (adamsGamma_le_one l) (unseenRate_le hP l) (unseenRate_nonneg P C A l)
      zero_le_one).trans_eq (one_mul _)
  exact run_order_row_lead_of_defect A P N M hH hl hlx hKH hK1 hP hN hM x hx hδ
    (mul_nonneg (adamsGamma_nonneg l) (unseenRate_nonneg P C A l)) hΓ
    (memRem_nonneg l (norm_nonneg A) hw0) (memB_nonneg l) hmem

/-- **Display (30) for a subsystem with old samples, over the interval `1/(2‖A‖)`:**
`run_order_row_lead` for `K = ⌊1/(2‖A‖)/H⌋`, `H > 0`, `A ≠ 0`. -/
theorem run_order_row_lead_floor (N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F)
    (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    {H w : ℝ} (hH : 0 < H) (hA0 : A ≠ 0) (hw0 : 0 ≤ w) {l : ℕ} (hl : 1 ≤ l)
    (hrowN : N = 0) (hrow0 : M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → M r = g r ∘L C)
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H)
    (hlx : 2 * l * (H * ‖A‖) ≤ 1) {nbar mbar : ℝ} (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < ⌊1 / (2 * ‖A‖) / H⌋₊ →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊1 / (2 * ‖A‖) / H⌋₊,
      ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (adamsGamma l * unseenRate P C A l * H ^ l -
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) +
          adamsGamma l * unseenRate P C A l * (2 * l + memB l + 1 / 5) * ‖A‖) * H ^ (l + 1)) /
      (2 * (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1))) * ‖A‖) ≤ δ := by
  obtain ⟨h1, h2⟩ := horizon_floor (norm_pos_iff.2 hA0) hH
  exact run_order_row_lead N M hA hP Fi g hH.le hw0 hl hrowN hrow0 hrow hw hlx h1 h2 hN hM x
    hx hδ

/-- **Display (30) for a subsystem with a new sample, with an explicit remainder.** Subsystem
`i` (projection `P`, `‖P‖ ≤ 1`, `P ∘ A = Ai ∘ P + L ∘ C`) with `l ≥ 1` held samples, the new one
and those of the ages `0, …, l-2`: its row of the recursion is
`(P - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` with `N = gNew ∘ C`, `M 0 = Fi ∘ P + g 0 ∘ C`,
`M r = g r ∘ C` for `1 ≤ r < l`, `g (l-1) = 0`, with `‖gNew ∘ C‖ ≤ w H` and `‖g r ∘ C‖ ≤ w H` for
`1 ≤ r < l - 1`. Let `‖N‖ ≤ n̄`, `‖M r‖ ≤ m̄` for `1 ≤ r < l`, `2 l H ‖A‖ ≤ 1` and
`K H ‖A‖ ≤ 1/2 < (K + 1) H ‖A‖`. If `δ` bounds the relative error of the sequences of all
initial states `x_0 ≠ 0` for `k ≤ K`, then
`δ ≥ 0.35 (|γ'_l| c_i H^l - κ H^{l+1}) / (2 b_i ‖A‖)`, `b_i = 2.65 (1 + n̄) + 1.42 m̄ l (l - 1)`,
`κ = C'_1 ‖A‖^{l+2} + C'_2 w ‖A‖^{l+1} + |γ'_l| c_i (2 l + b'_l + 1/5) ‖A‖`, with
`γ'_l = lateGamma l`, `c_i = unseenRate P C A l`, `b'_l = lateB l`, `C'_1 = lateC1 l`,
`C'_2 = lateC2 l`. -/
theorem run_order_row_late (N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F)
    (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) {l K : ℕ} (hl : 1 ≤ l)
    (hrowN : N = gNew ∘L C) (hrow0 : M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → M r = g r ∘L C) (hlast : g (l - 1) = 0)
    (hwNew : ‖gNew ∘L C‖ ≤ w * H) (hw : ∀ r, 1 ≤ r → r < l - 1 → ‖g r ∘L C‖ ≤ w * H)
    (hlx : 2 * l * (H * ‖A‖) ≤ 1) (hKH : K * H * ‖A‖ ≤ 1 / 2)
    (hK1 : 1 / 2 < (K + 1) * H * ‖A‖) {nbar mbar : ℝ} (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (|lateGamma l| * unseenRate P C A l * H ^ l -
        (lateC1 l * ‖A‖ ^ (l + 2) + lateC2 l * w * ‖A‖ ^ (l + 1) +
          |lateGamma l| * unseenRate P C A l * (2 * l + lateB l + 1 / 5) * ‖A‖) * H ^ (l + 1)) /
      (2 * (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1))) * ‖A‖) ≤ δ := by
  have hmem := memory_late hA hP Fi gNew g hH hw0
    ((le_half_of_two_mul_le hl (mul_nonneg hH (norm_nonneg A)) hlx).trans (by norm_num)) hl
    hwNew hw
  rw [← rowDefect_eq_lateDefect Fi gNew g H hl hrowN hrow0 hrow hlast] at hmem
  have hΓ : |lateGamma l| * unseenRate P C A l ≤ ‖A‖ ^ (l + 1) :=
    (mul_le_mul (abs_lateGamma_le_one hl) (unseenRate_le hP l) (unseenRate_nonneg P C A l)
      zero_le_one).trans_eq (one_mul _)
  have hR0 : 0 ≤ lateC1 l * ‖A‖ ^ (l + 2) + lateC2 l * w * ‖A‖ ^ (l + 1) := by
    have h1 := lateC1_nonneg l
    have h2 := lateC2_nonneg l
    positivity
  exact run_order_row_lead_of_defect A P N M hH hl hlx hKH hK1 hP hN hM x hx hδ
    (mul_nonneg (abs_nonneg _) (unseenRate_nonneg P C A l)) hΓ hR0 (lateB_nonneg l) hmem

/-- **Display (30) for a subsystem with a new sample, over the interval `1/(2‖A‖)`:**
`run_order_row_late` for `K = ⌊1/(2‖A‖)/H⌋`, `H > 0`, `A ≠ 0`. -/
theorem run_order_row_late_floor (N : E →L[ℝ] F) (M : ℕ → E →L[ℝ] F)
    (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 < H) (hA0 : A ≠ 0) (hw0 : 0 ≤ w) {l : ℕ}
    (hl : 1 ≤ l) (hrowN : N = gNew ∘L C) (hrow0 : M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → M r = g r ∘L C) (hlast : g (l - 1) = 0)
    (hwNew : ‖gNew ∘L C‖ ≤ w * H) (hw : ∀ r, 1 ≤ r → r < l - 1 → ‖g r ∘L C‖ ≤ w * H)
    (hlx : 2 * l * (H * ‖A‖) ≤ 1) {nbar mbar : ℝ} (hN : ‖N‖ ≤ nbar)
    (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < ⌊1 / (2 * ‖A‖) / H⌋₊ →
      (P - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ ⌊1 / (2 * ‖A‖) / H⌋₊,
      ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖) :
    0.35 * (|lateGamma l| * unseenRate P C A l * H ^ l -
        (lateC1 l * ‖A‖ ^ (l + 2) + lateC2 l * w * ‖A‖ ^ (l + 1) +
          |lateGamma l| * unseenRate P C A l * (2 * l + lateB l + 1 / 5) * ‖A‖) * H ^ (l + 1)) /
      (2 * (2.65 * (1 + nbar) + 1.42 * mbar * ((l : ℝ) * (l - 1))) * ‖A‖) ≤ δ := by
  obtain ⟨h1, h2⟩ := horizon_floor (norm_pos_iff.2 hA0) hH
  exact run_order_row_late N M hA hP Fi gNew g hH.le hw0 hl hrowN hrow0 hrow hlast hwNew hw hlx
    h1 h2 hN hM x hx hδ

end Operator

open Matrix OneStep

variable {n : ℕ}

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

/-- **The local defect of the row of a subsystem with one held sample** is
`T_s = Π_s (1 - N)(U - X)` (the row `s` of the recursion is
`(Π_s - Π_s N) x^{k+1} = Π_s (F + M) x^k`), and between `s` and a subsystem `t ≠ s` that is not
a partner of `s` it is at least the unavoidable error:
`a_st H² - (C₃ + a c) H³ ≤ ‖Π_s (1 - N)(U - X)‖`, `a_st = ½ ‖[A_ς A]_st‖`,
`C₃ = reactionC a b c ‖A‖ H`. -/
theorem Consistent.norm_row_defect_ge {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    S.forcedCoeff A s t * H ^ 2 - (reactionC a b c ‖opE A‖ H + a * c) * H ^ 3 ≤
      ‖opE (S.mask s * ((1 - S.N) * (U - S.X)))‖ := by
  have h1 := (abs_le.1 (h.forced_block_norm hst hnp)).1
  have h2 : ‖opE (S.cblock s t (S.N * (S.X - U)))‖ ≤ a * c * H ^ 3 := by
    refine (S.norm_opE_cblock_le s t _).trans ?_
    rw [opE_mul]
    refine (norm_mul_le _ _).trans ?_
    have := mul_le_mul h.ha h.hc (norm_nonneg (opE (S.X - U)))
      ((norm_nonneg (opE S.N)).trans h.ha)
    linarith
  have e1 : (1 - S.N) * (S.X - U) = (S.X - U) - S.N * (S.X - U) := by
    rw [sub_mul, one_mul]
  have h3 : ‖opE (S.cblock s t (S.X - U))‖ - ‖opE (S.cblock s t (S.N * (S.X - U)))‖ ≤
      ‖opE (S.cblock s t ((1 - S.N) * (S.X - U)))‖ := by
    have e4 : opE (S.cblock s t ((1 - S.N) * (S.X - U))) =
        opE (S.cblock s t (S.X - U)) - opE (S.cblock s t (S.N * (S.X - U))) := by
      rw [e1, S.cblock_sub s t (S.X - U) (S.N * (S.X - U)), opE_sub]
    rw [e4]
    exact norm_sub_norm_le (opE (S.cblock s t (S.X - U)))
      (opE (S.cblock s t (S.N * (S.X - U))))
  have h4 : ‖opE (S.cblock s t ((1 - S.N) * (S.X - U)))‖ ≤
      ‖opE (S.mask s * ((1 - S.N) * (S.X - U)))‖ := by
    have e : S.cblock s t ((1 - S.N) * (S.X - U)) =
        S.mask s * ((1 - S.N) * (S.X - U)) * S.mask t := rfl
    rw [e, opE_mul]
    refine (norm_mul_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left (S.norm_opE_mask_le t)
      (norm_nonneg (opE (S.mask s * ((1 - S.N) * (S.X - U)))))
    linarith
  have e2 : S.mask s * ((1 - S.N) * (U - S.X)) = -(S.mask s * ((1 - S.N) * (S.X - U))) := by
    rw [← Matrix.mul_neg, ← Matrix.mul_neg, neg_sub]
  have e3 : opE (-(S.mask s * ((1 - S.N) * (S.X - U)))) =
      -opE (S.mask s * ((1 - S.N) * (S.X - U))) := map_neg _ _
  rw [e2, e3, norm_neg]
  linarith

/-- **Display (31), with an explicit remainder.** A consistent scheme with one held sample, in
any order of execution and with any coefficients (`‖N‖ ≤ a H`, `‖X - 1‖ ≤ b H`,
`‖X - U‖ ≤ c H²`), two subsystems `s ≠ t` that are not partners, `‖Π_s N‖ ≤ n̄` and
`K = ⌊1/(2 H ‖A‖)⌋` the number of macro steps of the interval `1/(2‖A‖)`. If `‖X^k - U^k‖ ≤ δ`
for all `k ≤ K`, then
`δ ≥ 0.35 (‖[A_ς A]_st‖ H - κ' H²) / (4 b_s ‖A‖)`, `b_s = 2.65 (1 + n̄)`,
`κ' = 2 (C₃ + a c) + (11/5) ‖[A_ς A]_st‖ ‖A‖`, `C₃ = reactionC a b c ‖A‖ H`, where
`‖[A_ς A]_st‖ = ‖opE (cblock s t (A_ς A))‖` is the spectral norm of the block `(s, t)` of
`A_ς A`. -/
theorem Consistent.first_order_row_lead {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) {nbar : ℝ}
    (hn : ‖opE (S.mask s * S.N)‖ ≤ nbar) {δ : ℝ}
    (hδ : ∀ k ≤ ⌊1 / (2 * H * ‖opE A‖)⌋₊, ‖opE (S.X ^ k - U ^ k)‖ ≤ δ) :
    0.35 * (‖opE (S.cblock s t (S.signedCoupling A * A))‖ * H -
        (2 * (reactionC a b c ‖opE A‖ H + a * c) +
          11 / 5 * ‖opE (S.cblock s t (S.signedCoupling A * A))‖ * ‖opE A‖) * H ^ 2) /
      (4 * (2.65 * (1 + nbar)) * ‖opE A‖) ≤ δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (Nat.zero_le _))
  have hn0 : 0 ≤ nbar := (norm_nonneg _).trans hn
  have hα0 : 0 ≤ ‖opE A‖ := norm_nonneg _
  have hg0 := S.forcedCoeff_nonneg A s t
  have hgle := h.forcedCoeff_le hst hnp
  have hgdef : ‖opE (S.cblock s t (S.signedCoupling A * A))‖ = 2 * S.forcedCoeff A s t := by
    rw [forcedCoeff]
    ring
  rw [hgdef]
  have hH := h.hH
  -- the remainder of the local defect is not negative
  have hRH : 0 ≤ (reactionC a b c ‖opE A‖ H + a * c) * H ^ 3 := by
    have h1 := h.reaction_bound_nonneg
    have h2 : 0 ≤ a * H * (c * H ^ 2) :=
      mul_nonneg ((norm_nonneg _).trans h.ha) ((norm_nonneg _).trans h.hc)
    nlinarith [h1, h2]
  have hd : 0 ≤ 4 * (2.65 * (1 + nbar)) * ‖opE A‖ := by positivity
  rcases le_or_gt (2 * S.forcedCoeff A s t * H -
      (2 * (reactionC a b c ‖opE A‖ H + a * c) +
        11 / 5 * (2 * S.forcedCoeff A s t) * ‖opE A‖) * H ^ 2) 0 with hQ | hQ
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hQ) hd).trans hδ0
  -- the macro step, the coefficient and the norm of `A` are positive
  have hHpos : 0 < H := by
    rcases hH.eq_or_lt with h0 | hpos
    · rw [← h0] at hQ
      simp at hQ
    · exact hpos
  have hR : 0 ≤ reactionC a b c ‖opE A‖ H + a * c :=
    (mul_nonneg_iff_of_pos_right (pow_pos hHpos 3)).1 hRH
  have hRH2 : 0 ≤ (reactionC a b c ‖opE A‖ H + a * c) * H ^ 2 := by positivity
  have hgαH : 0 ≤ S.forcedCoeff A s t * ‖opE A‖ * H ^ 2 := by positivity
  have hgH : 0 < S.forcedCoeff A s t * H := by nlinarith [hQ, hRH2, hgαH]
  have hgpos : 0 < S.forcedCoeff A s t := (mul_pos_iff_of_pos_right hHpos).1 hgH
  have hαpos : 0 < ‖opE A‖ := by
    rcases hα0.eq_or_lt with h0 | hpos
    · rw [← h0] at hgle
      norm_num at hgle
      linarith
    · exact hpos
  have hxpos : 0 < H * ‖opE A‖ := mul_pos hHpos hαpos
  have hlx : 2 * (1 : ℝ) * (H * ‖opE A‖) ≤ 1 := by
    have h1 : S.forcedCoeff A s t * H * (11 / 5 * (H * ‖opE A‖)) <
        S.forcedCoeff A s t * H * 1 := by nlinarith [hQ, hRH2]
    have h2 := lt_of_mul_lt_mul_left h1 hgH.le
    linarith
  -- the number of steps
  have hHα : 0 < 2 * H * ‖opE A‖ := by positivity
  have hKle : ((⌊1 / (2 * H * ‖opE A‖)⌋₊ : ℕ) : ℝ) ≤ 1 / (2 * H * ‖opE A‖) :=
    Nat.floor_le (by positivity)
  have hKlt : 1 / (2 * H * ‖opE A‖) < ((⌊1 / (2 * H * ‖opE A‖)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hK1 : 1 ≤ ⌊1 / (2 * H * ‖opE A‖)⌋₊ :=
    (Nat.one_le_floor_iff _).2 (by rw [le_div_iff₀ hHα]; linarith)
  have hKH : ((⌊1 / (2 * H * ‖opE A‖)⌋₊ : ℕ) : ℝ) * H * ‖opE A‖ ≤ 1 / 2 := by
    rw [le_div_iff₀ hHα] at hKle
    linarith
  have hKp : (1 - 2 * (1 : ℝ) * (H * ‖opE A‖)) / 2 ≤
      (((⌊1 / (2 * H * ‖opE A‖)⌋₊ : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 1) * (H * ‖opE A‖) := by
    rw [div_lt_iff₀ hHα] at hKlt
    push_cast
    linarith
  -- the row of the recursion as operators on Euclidean space
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) := nontrivial_of_norm_opE_pos hαpos
  have hU := h.hU
  have hXe : S.X - S.N * S.X = S.F + S.M := by
    rw [sub_eq_iff_eq_add]
    exact S.hX
  have hmat : S.mask s * ((1 - S.N) * (U - S.X)) =
      (S.mask s - S.mask s * S.N) * U - S.mask s * (S.F + S.M) := by
    rw [← hXe]
    noncomm_ring
  have hdef : rowDefect (opE (S.mask s)) (opE (S.mask s * S.N))
      (fun _ => opE (S.mask s * (S.F + S.M))) (exp (H • opE A)) (exp (-(H • opE A))) 1 =
      opE (S.mask s * ((1 - S.N) * (U - S.X))) := by
    have e : rowDefect (opE (S.mask s)) (opE (S.mask s * S.N))
        (fun _ => opE (S.mask s * (S.F + S.M))) (exp (H • opE A)) (exp (-(H • opE A))) 1 =
        (opE (S.mask s) - opE (S.mask s * S.N)) * exp (H • opE A) -
          opE (S.mask s * (S.F + S.M)) * 1 := by
      unfold rowDefect
      rw [sum_range_one, pow_zero]
      rfl
    rw [e, mul_one, hmat, hU, opE_sub, opE_mul (S.mask s - S.mask s * S.N), opE_sub, opE_exp,
      opE_smul]
  have hτ := h.norm_row_defect_ge hst hnp
  rw [← hdef] at hτ
  have hτ0 : 0 ≤ S.forcedCoeff A s t * H ^ 2 -
      (reactionC a b c ‖opE A‖ H + a * c) * H ^ 3 := by nlinarith [hQ, hgαH, hHpos]
  have hx : ∀ x0 : EuclideanSpace ℝ (Fin n), x0 ≠ 0 → ∀ k, 1 - 1 ≤ k →
      k < ⌊1 / (2 * H * ‖opE A‖)⌋₊ →
      (opE (S.mask s) - opE (S.mask s * S.N)) ((opE S.X ^ (k + 1)) x0) =
        ∑ r ∈ range 1, (fun _ => opE (S.mask s * (S.F + S.M))) r ((opE S.X ^ (k - r)) x0) := by
    intro x0 _ k _ _
    have e : (S.mask s - S.mask s * S.N) * S.X ^ (k + 1) =
        S.mask s * (S.F + S.M) * S.X ^ k := by
      rw [pow_succ', ← mul_assoc, sub_mul, mul_assoc (S.mask s) S.N S.X, ← mul_sub, hXe]
    rw [sum_range_one, Nat.sub_zero, ← opE_sub, ← opE_pow, ← opE_pow, ← opE_mul_apply,
      ← opE_mul_apply, e]
  have hδ' : ∀ x0 : EuclideanSpace ℝ (Fin n), x0 ≠ 0 → ∀ k ≤ ⌊1 / (2 * H * ‖opE A‖)⌋₊,
      ‖(opE S.X ^ k) x0 - (exp (H • opE A) ^ k) x0‖ ≤ δ * ‖x0‖ := by
    intro x0 _ k hk
    have e : (opE S.X ^ k) x0 - (exp (H • opE A) ^ k) x0 = opE (S.X ^ k - U ^ k) x0 := by
      rw [hU, opE_pow_sub_exp_pow, _root_.sub_apply]
    rw [e]
    exact ((opE (S.X ^ k - U ^ k)).le_opNorm x0).trans
      (mul_le_mul_of_nonneg_right (hδ k hk) (norm_nonneg _))
  have hbar := run_order_row_of_le (opE A) (opE (S.mask s)) (opE (S.mask s * S.N))
    (fun _ => opE (S.mask s * (S.F + S.M))) hH (le_refl 1) hK1 hKH (mbar := 0)
    (S.norm_opE_mask_le s) hn
    (fun r h1 h2 => absurd h1 (by omega)) (fun x0 k => (opE S.X ^ k) x0) hx hδ' hτ0 hτ
  have hb : (2.65 : ℝ) ≤
      2.65 * (1 + nbar) + 1.42 * 0 * ((((1 : ℕ) : ℝ)) * (((1 : ℕ) : ℝ) - 1)) := by
    norm_num
    linarith
  have hG1 : S.forcedCoeff A s t * H ≤ ‖opE A‖ * (H * ‖opE A‖) := by nlinarith [hgle, hHpos]
  have hmem : S.forcedCoeff A s t * (H * H) -
      (reactionC a b c ‖opE A‖ H + a * c) * (H * H * H) ≤
      (1 + 0 * (H * ‖opE A‖)) * (S.forcedCoeff A s t * H ^ 2 -
        (reactionC a b c ‖opE A‖ H + a * c) * H ^ 3) := by
    apply le_of_eq
    ring
  have hfin := row_lead_arith (le_refl (1 : ℝ)) hg0 hR hHpos hHpos.le hαpos hτ0 (le_refl 0) hb
    hlx hG1 hKp hmem hbar
  have hbe : 2.65 * (1 + nbar) + 1.42 * 0 * ((((1 : ℕ) : ℝ)) * (((1 : ℕ) : ℝ) - 1)) =
      2.65 * (1 + nbar) := by
    norm_num
  rw [hbe] at hfin
  have hnum : 0.35 * (2 * S.forcedCoeff A s t * H -
      (2 * (reactionC a b c ‖opE A‖ H + a * c) +
        11 / 5 * (2 * S.forcedCoeff A s t) * ‖opE A‖) * H ^ 2) /
      (4 * (2.65 * (1 + nbar)) * ‖opE A‖) =
      0.35 * (S.forcedCoeff A s t * H - (reactionC a b c ‖opE A‖ H + a * c +
        S.forcedCoeff A s t * (2 * 1 + 0 + 1 / 5) * ‖opE A‖) * (H * H)) /
      (2 * (2.65 * (1 + nbar)) * ‖opE A‖) := by
    have hne : (4 * (2.65 * (1 + nbar)) * ‖opE A‖) ≠ 0 := by positivity
    have hne' : (2 * (2.65 * (1 + nbar)) * ‖opE A‖) ≠ 0 := by positivity
    rw [div_eq_div_iff hne hne']
    ring
  rw [hnum]
  exact hfin

end HeldScheme

end CoSimFoundations
