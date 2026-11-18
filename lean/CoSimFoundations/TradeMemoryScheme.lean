/-
The trade between energy and damping with `l` held samples, the schemes (the paper, the lower
bound).

**Setting**, that of `RunOrder`: a scheme with `l` held samples, stacked over the subsystems, is the
recursion `(1 - N) x^{k+1} = Σ_{q<l} M q x^{k-q}`, `U` the reference step with inverse `Ui`, and
`𝒯 = (1 - N) U - Σ_{q<l} M q Ui^q` its local defect (`runDefect`).

**The underlying one-step map** (`exists_underlying_step`, `underlying_run`,
`norm_underlying_sub_le`). In a real Banach algebra with `‖1‖ ≤ 1`: if `‖Ui - 1‖ ≤ 1/4`,
`‖M 0 - 1‖ ≤ β`, `‖M q‖ ≤ β` (`1 ≤ q < l`), `β λ_l ≤ 1/2` with `λ_l = Σ_{q<l} (q + 1) 2^q`
(`backLip`) and `‖𝒯‖ ≤ 1/16`, there are `X`, `Y = X⁻¹` with

  `(1 - N) X = Σ_{q<l} M q Y^q`   (the paper's `(I - 𝒩) X̂ = Σ_q M_q X̂^{-q}`),

and `‖Y - Ui‖ ≤ 4 ‖𝒯‖`, `‖Y - 1‖ ≤ 1/2`. The proof is the paper's contraction, written for the
inverse `Y`: the map `Y ↦ Y + (1 - N) - Σ_q M q Y^{q+1}` (`backMap`) has the Lipschitz constant
`β λ_l ≤ 1/2` on the ball `‖Y - Ui‖ ≤ 4 ‖𝒯‖` and maps it into itself, since it moves `Ui` by
`𝒯 Ui`; no inverse enters the map. Its fixed point solves `1 - N = Σ_q M q Y^{q+1}`, and `Y` is a
unit since `‖1 - Y‖ < 1`. The run started from `x^q = X^q x_0` is `x^k = X^k x_0`
(`underlying_run`): `X` is the one-step map of the scheme on the invariant graph.
For every such solution with `‖Y‖ ≤ 2`, `‖Ui‖ ≤ 2`, `‖N‖ ≤ β` and `β (1 + 4 λ_l) ≤ 1/2`, a priori:

  `‖X - U‖ ≤ 2 ‖𝒯‖`,   `‖X - U + 𝒯‖ ≤ 2 β (1 + 4 λ_l) ‖𝒯‖`   (the paper's `X̂ - U = -𝒯 + O(H ‖𝒯‖)`),

from `X - U + 𝒯 = N (X - U) + Σ_q M q (Y^q - Ui^q)` and `Y - Ui = Y (U - X) Ui`.

**The numerical dissipation** (`numDissipation_underlying_sub_le`). For matrices with the spectral
norm, `U = exp (H A)`, `Ui = exp (-H A)`, `0 < H ≤ 1`, `H ‖A‖ ≤ 1/8`, `‖N‖ ≤ b H`, `‖M q‖ ≤ b H`
(`1 ≤ q < l`), `b H (1 + 4 λ_l) ≤ 1/2`, `‖𝒯‖ ≤ m H^{l+1} ≤ 1/48`, and a leading defect in `D + 𝒵`,
`‖𝒯 - H^{l+1} (D + Z)‖ ≤ c H^{l+2}`: every solution `X` with `‖X⁻¹‖ ≤ 2` has

  `‖Δ_R - H^l sym (D + Z)‖ ≤ K H^{l+1}`,  `K = c + 2 b (1 + 4 λ_l) m + 6 m (m + ‖A‖)` (`tradeK`),

`Δ_R = numDissipation A (modifiedSystem H X) = -sym ((1/H) log X - A)` (the paper's
`Δ_R = H^l sym (D_H) + O(H^{l+1})`).

**The lower bound** (`trade_memory_le`, `exists_underlying_trade_le`). With moreover
`1 ∈ 𝒵`, `Z ∈ 𝒵`, `n ≥ 1`, `d ≤ ‖sym (D + Z')‖` for all `Z' ∈ 𝒵`, and all `μ`, `ι` with
`-ι ‖v‖² ≤ ⟪v, Δ_R v⟫ ≤ μ ‖v‖²`:

  `μ + ι ≥ 2 H^l d - 2 K H^{l+1}`.

`exists_underlying_trade_le` combines this with the existence of the underlying map (it needs
moreover `‖M 0 - 1‖ ≤ b H`). With `𝒵 = rowReach sub V` (`TradeMemory`) and `d` its least value,
this is the lower bound for every scheme whose leading defect lies in `D_l + 𝒵_l`.
With the entries that no scheme changes (`trade_memory_fixed_entry_le`): for unit `e` on
subsystem `s` in `V t` and unit `e'` on `t` in `V s`,
`μ + ι ≥ 2 H^l |⟪e, sym D e'⟫| - 2 K H^{l+1}`.

Not formalised here: that every scheme of the class (bounded weights, order `l`, cases (i) and (ii)
of Theorem 4.6) has its leading defect in `D_l + 𝒵_l`, and the attainment of the
half-plane by schemes (a rule that realises a given leading defect); the
matrices that attain it are `exists_rowReach_extremes`.
-/
import CoSimFoundations.TradeMemory
import CoSimFoundations.RunOrder
import Mathlib.Topology.MetricSpace.Contracting

open NormedSpace Finset Matrix Metric
open scoped RealInnerProductSpace NNReal

namespace CoSimFoundations

open OneStep

/-! ### The underlying one-step map in a Banach algebra -/

section Underlying

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The Lipschitz constant of the backward map near `1`, `λ_l = Σ_{q<l} (q + 1) 2^q`. -/
noncomputable def backLip (l : ℕ) : ℝ := ∑ q ∈ range l, ((q : ℝ) + 1) * 2 ^ q

theorem backLip_nonneg (l : ℕ) : 0 ≤ backLip l :=
  sum_nonneg fun q _ => by positivity

/-- **Powers near each other:** `‖a^{q+1} - b^{q+1}‖ ≤ (q + 1) R^q ‖a - b‖` for `‖a‖, ‖b‖ ≤ R`. -/
theorem norm_pow_succ_sub_pow_succ_le_pow {a b : 𝔸} {R : ℝ} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (q : ℕ) : ‖a ^ (q + 1) - b ^ (q + 1)‖ ≤ ((q : ℝ) + 1) * R ^ q * ‖a - b‖ := by
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  induction q with
  | zero => simp
  | succ q ih =>
    have e : a ^ (q + 1 + 1) - b ^ (q + 1 + 1) =
        a ^ (q + 1) * (a - b) + (a ^ (q + 1) - b ^ (q + 1)) * b := by
      rw [pow_succ a (q + 1), pow_succ b (q + 1), mul_sub, sub_mul]
      abel
    have h1 : ‖a ^ (q + 1) * (a - b)‖ ≤ R ^ (q + 1) * ‖a - b‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_pow_le' a (Nat.succ_pos q)).trans (pow_le_pow_left₀ (norm_nonneg a) ha _))
        (norm_nonneg _))
    have h2 : ‖(a ^ (q + 1) - b ^ (q + 1)) * b‖ ≤ ((q : ℝ) + 1) * R ^ q * ‖a - b‖ * R :=
      (norm_mul_le _ _).trans (mul_le_mul ih hb (norm_nonneg _) ((norm_nonneg _).trans ih))
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    push_cast
    ring

/-- The map of the backward step, `Y ↦ Y + (1 - N) - Σ_{q<l} M q Y^{q+1}`: its fixed points are
the solutions of `1 - N = Σ_{q<l} M q Y^{q+1}`. -/
noncomputable def backMap (N : 𝔸) (M : ℕ → 𝔸) (l : ℕ) (Y : 𝔸) : 𝔸 :=
  Y + (1 - N) - ∑ q ∈ range l, M q * Y ^ (q + 1)

/-- The difference of the backward map at two points. -/
theorem backMap_sub (N : 𝔸) (M : ℕ → 𝔸) {l : ℕ} (hl : 1 ≤ l) (Y Y' : 𝔸) :
    backMap N M l Y - backMap N M l Y' =
      ∑ q ∈ range l, ((if q = 0 then (1 : 𝔸) else 0) - M q) * (Y ^ (q + 1) - Y' ^ (q + 1)) := by
  have h0 : (0 : ℕ) ∈ range l := mem_range.2 (by omega)
  have hs : ∑ q ∈ range l, ((if q = 0 then (1 : 𝔸) else 0) - M q) * (Y ^ (q + 1) - Y' ^ (q + 1)) =
      ∑ q ∈ range l, (if q = 0 then Y ^ (q + 1) - Y' ^ (q + 1) else 0) -
        ∑ q ∈ range l, M q * (Y ^ (q + 1) - Y' ^ (q + 1)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    split_ifs <;> simp [sub_mul]
  rw [hs, sum_ite_eq' (range l) 0, ite_eq_left h0, zero_add, pow_one, pow_one, backMap, backMap]
  simp only [mul_sub, sum_sub_distrib]
  abel

/-- The backward map moves the inverse of the reference step by `𝒯 Ui`:
`backMap Ui - Ui = 𝒯 Ui`. -/
theorem backMap_sub_self (N : 𝔸) (M : ℕ → 𝔸) (l : ℕ) {U Ui : 𝔸} (hUUi : U * Ui = 1) :
    backMap N M l Ui - Ui = runDefect N M U Ui l * Ui := by
  rw [backMap, runDefect, sub_mul, sum_mul, mul_assoc, hUUi, mul_one]
  simp only [mul_assoc, ← pow_succ]
  abel

/-- **The backward map is a contraction near `1`:** if `‖Y - 1‖ ≤ 1/2`, `‖Y' - 1‖ ≤ 1/2`,
`‖1‖ ≤ 1`, `‖M 0 - 1‖ ≤ β` and `‖M q‖ ≤ β` for `1 ≤ q < l`, then
`‖backMap Y - backMap Y'‖ ≤ β λ_l ‖Y - Y'‖`. -/
theorem norm_backMap_sub_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) (N : 𝔸) {M : ℕ → 𝔸} {l : ℕ} (hl : 1 ≤ l)
    {β : ℝ} (hM0 : ‖M 0 - 1‖ ≤ β) (hM : ∀ q, 1 ≤ q → q < l → ‖M q‖ ≤ β) {Y Y' : 𝔸}
    (hY : ‖Y - 1‖ ≤ 1 / 2) (hY' : ‖Y' - 1‖ ≤ 1 / 2) :
    ‖backMap N M l Y - backMap N M l Y'‖ ≤ β * backLip l * ‖Y - Y'‖ := by
  have hn : ∀ Z : 𝔸, ‖Z - 1‖ ≤ 1 / 2 → ‖Z‖ ≤ 2 := fun Z hZ => by
    have := norm_le_norm_add_norm_sub' Z 1
    linarith
  rw [backMap_sub N M hl, backLip, mul_sum, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
  have hc : ‖(if q = 0 then (1 : 𝔸) else 0) - M q‖ ≤ β := by
    split_ifs with h
    · rw [h, norm_sub_rev]
      exact hM0
    · rw [zero_sub, norm_neg]
      exact hM q (Nat.one_le_iff_ne_zero.2 h) (mem_range.1 hq)
  have hp := norm_pow_succ_sub_pow_succ_le_pow (hn Y hY) (hn Y' hY') q
  refine (norm_mul_le _ _).trans ((mul_le_mul hc hp (norm_nonneg _)
    ((norm_nonneg _).trans hc)).trans_eq ?_)
  ring

/-- **The underlying one-step map exists** (the map `X ↦ (I - 𝒩)^{-1} (M_0 + Σ_{q≥1} M_q
X^{-q})` is a contraction near `U` for small `H`; here the equivalent equation for the inverse
`Y`). In a real Banach algebra with `‖1‖ ≤ 1`, let `U Ui = Ui U = 1`, `‖Ui - 1‖ ≤ 1/4`,
`‖M 0 - 1‖ ≤ β`, `‖M q‖ ≤ β` for `1 ≤ q < l`, `β λ_l ≤ 1/2` and `‖𝒯‖ ≤ 1/16`. Then there are
`X`, `Y` with `X Y = Y X = 1`, `(1 - N) X = Σ_{q<l} M q Y^q`, `‖Y - 1‖ ≤ 1/2` and
`‖Y - Ui‖ ≤ 4 ‖𝒯‖`. -/
theorem exists_underlying_step (h1 : ‖(1 : 𝔸)‖ ≤ 1) {U Ui N : 𝔸} {M : ℕ → 𝔸} {l : ℕ}
    (hl : 1 ≤ l) (hUUi : U * Ui = 1) (hUi1 : ‖Ui - 1‖ ≤ 1 / 4) {β : ℝ}
    (hM0 : ‖M 0 - 1‖ ≤ β) (hM : ∀ q, 1 ≤ q → q < l → ‖M q‖ ≤ β) (hβ : β * backLip l ≤ 1 / 2)
    (hT : ‖runDefect N M U Ui l‖ ≤ 1 / 16) :
    ∃ X Y : 𝔸, X * Y = 1 ∧ Y * X = 1 ∧ (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q ∧
      ‖Y - 1‖ ≤ 1 / 2 ∧ ‖Y - Ui‖ ≤ 4 * ‖runDefect N M U Ui l‖ := by
  set T := runDefect N M U Ui l with hTdef
  set s := closedBall Ui (4 * ‖T‖) with hs
  have hball : ∀ Y ∈ s, ‖Y - 1‖ ≤ 1 / 2 := fun Y hY => by
    have h2 : ‖Y - Ui‖ ≤ 4 * ‖T‖ := by rwa [hs, mem_closedBall, dist_eq_norm] at hY
    have h3 := norm_add_le (Y - Ui) (Ui - 1)
    rw [sub_add_sub_cancel] at h3
    linarith
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hM0
  have hLip : ∀ Y ∈ s, ∀ Y' ∈ s,
      ‖backMap N M l Y - backMap N M l Y'‖ ≤ 1 / 2 * ‖Y - Y'‖ := fun Y hY Y' hY' =>
    (norm_backMap_sub_le h1 N hl hM0 hM (hball Y hY) (hball Y' hY')).trans
      (mul_le_mul_of_nonneg_right hβ (norm_nonneg _))
  have hUi : ‖Ui‖ ≤ 5 / 4 := by
    have := norm_le_norm_add_norm_sub' Ui 1
    linarith
  have hmove : ‖backMap N M l Ui - Ui‖ ≤ 5 / 4 * ‖T‖ := by
    rw [backMap_sub_self N M l hUUi]
    exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_left hUi (norm_nonneg T)).trans_eq (by ring))
  have hUis : Ui ∈ s := mem_closedBall_self (by positivity)
  have hmaps : Set.MapsTo (backMap N M l) s s := fun Y hY => by
    have h2 := hLip Y hY Ui hUis
    rw [hs, mem_closedBall, dist_eq_norm] at hY ⊢
    have h3 := norm_add_le (backMap N M l Y - backMap N M l Ui) (backMap N M l Ui - Ui)
    rw [sub_add_sub_cancel] at h3
    linarith [norm_nonneg T]
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict (backMap N M l) s s) := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun Y Y' => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simp only [Set.MapsTo.val_restrict_apply]
    exact (hLip Y Y.2 Y' Y'.2).trans_eq (by norm_num)
  obtain ⟨Y, hYs, hfix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    hUis (edist_ne_top _ _)
  have hY1 := hball Y hYs
  have hY1' : ‖1 - Y‖ < 1 := by rw [norm_sub_rev]; linarith
  set u := Units.oneSub (1 - Y) hY1' with hu
  have huY : (u : 𝔸) = Y := by rw [hu, Units.val_oneSub, sub_sub_cancel]
  have heq : 1 - N = ∑ q ∈ range l, M q * Y ^ (q + 1) := by
    have h := hfix.eq
    rw [backMap] at h
    have h' : Y + (1 - N) - ∑ q ∈ range l, M q * Y ^ (q + 1) - Y = 0 := by rw [h, sub_self]
    rw [add_sub_assoc, add_sub_cancel_left, sub_eq_zero] at h'
    exact h'
  refine ⟨(u⁻¹ : 𝔸ˣ), Y, by rw [← huY, Units.inv_mul], by rw [← huY, Units.mul_inv],
    ?_, hY1, by rwa [hs, mem_closedBall, dist_eq_norm] at hYs⟩
  have hYX : Y * (u⁻¹ : 𝔸ˣ) = 1 := by rw [← huY, Units.mul_inv]
  rw [heq, sum_mul]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_assoc, pow_succ, mul_assoc, hYX, mul_one]

/-- **The run of the underlying map:** if `Y X = 1` and `(1 - N) X = Σ_{q<l} M q Y^q`, then the
powers of `X` satisfy the recursion of the scheme, `(1 - N) X^{k+1} = Σ_{q<l} M q X^{k-q}` for
`k ≥ l - 1`: the run started from `x^q = X^q x_0` is `x^k = X^k x_0`. -/
theorem underlying_run {N X Y : 𝔸} {M : ℕ → 𝔸} {l : ℕ} (hYX : Y * X = 1)
    (hX : (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q) {k : ℕ} (hk : l - 1 ≤ k) :
    (1 - N) * X ^ (k + 1) = ∑ q ∈ range l, M q * X ^ (k - q) := by
  rw [pow_succ', ← mul_assoc, hX, sum_mul]
  refine sum_congr rfl fun q hq => ?_
  rw [mul_assoc, inv_pow_mul_pow hYX (by have := mem_range.1 hq; omega)]

/-- **A priori bounds for the underlying map** (`X̂ - U = -𝒯 + O(H ‖𝒯‖)`). Let
`U Ui = 1`, `Y X = 1`, `(1 - N) X = Σ_{q<l} M q Y^q`, `‖Y‖ ≤ 2`, `‖Ui‖ ≤ 2`, `‖N‖ ≤ β`,
`‖M q‖ ≤ β` for `1 ≤ q < l` and `β (1 + 4 λ_l) ≤ 1/2`. Then `‖X - U‖ ≤ 2 ‖𝒯‖` and
`‖X - U + 𝒯‖ ≤ 2 β (1 + 4 λ_l) ‖𝒯‖`. -/
theorem norm_underlying_sub_le {U Ui N X Y : 𝔸} {M : ℕ → 𝔸} {l : ℕ} (hUUi : U * Ui = 1)
    (hYX : Y * X = 1) (hX : (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q) (hY : ‖Y‖ ≤ 2)
    (hUi : ‖Ui‖ ≤ 2) {β : ℝ} (hN : ‖N‖ ≤ β) (hM : ∀ q, 1 ≤ q → q < l → ‖M q‖ ≤ β)
    (hβ : β * (1 + 4 * backLip l) ≤ 1 / 2) :
    ‖X - U‖ ≤ 2 * ‖runDefect N M U Ui l‖ ∧
      ‖X - U + runDefect N M U Ui l‖ ≤
        2 * β * (1 + 4 * backLip l) * ‖runDefect N M U Ui l‖ := by
  set T := runDefect N M U Ui l with hTdef
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hN
  -- `Y - Ui = Y (U - X) Ui`
  have hYU : ‖Y - Ui‖ ≤ 4 * ‖X - U‖ := by
    have e : Y - Ui = Y * (U - X) * Ui := by
      rw [mul_sub, sub_mul, mul_assoc Y U Ui, hUUi, mul_one, hYX, one_mul]
    rw [e, norm_sub_rev X U]
    calc ‖Y * (U - X) * Ui‖ ≤ ‖Y * (U - X)‖ * ‖Ui‖ := norm_mul_le _ _
      _ ≤ (‖Y‖ * ‖U - X‖) * 2 :=
          mul_le_mul (norm_mul_le _ _) hUi (norm_nonneg _) (by positivity)
      _ ≤ (2 * ‖U - X‖) * 2 := by gcongr
      _ = 4 * ‖U - X‖ := by ring
  -- `X - U + 𝒯 = N (X - U) + Σ_q M q (Y^q - Ui^q)`
  have e : X - U + T = N * (X - U) + ∑ q ∈ range l, M q * (Y ^ q - Ui ^ q) := by
    have hX' : X = N * X + ∑ q ∈ range l, M q * Y ^ q := by
      rw [← hX, sub_mul, one_mul]
      abel
    rw [hTdef, runDefect, mul_sub N X U]
    simp only [mul_sub, sum_sub_distrib]
    nth_rewrite 1 [hX']
    rw [sub_mul, one_mul]
    abel
  have hsum : ‖∑ q ∈ range l, M q * (Y ^ q - Ui ^ q)‖ ≤ β * backLip l * ‖Y - Ui‖ := by
    rw [backLip, mul_sum, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [pow_zero, pow_zero, sub_self, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg hβ0 (by positivity)) (norm_nonneg _)
    · obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le' hq0
      have hp := norm_pow_succ_sub_pow_succ_le_pow hY hUi q'
      have hMq := hM (q' + 1) (by omega) (mem_range.1 hq)
      have h2 : ((q' : ℝ) + 1) * 2 ^ q' ≤ (((q' + 1 : ℕ) : ℝ) + 1) * 2 ^ (q' + 1) := by
        push_cast
        rw [pow_succ]
        have : (0 : ℝ) ≤ 2 ^ q' := by positivity
        nlinarith
      refine (norm_mul_le _ _).trans ?_
      have h3 := mul_le_mul hMq hp (norm_nonneg _) hβ0
      have h4 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h2 (norm_nonneg (Y - Ui))) hβ0
      exact h3.trans (h4.trans_eq (by ring))
  have hmain : ‖X - U + T‖ ≤ β * (1 + 4 * backLip l) * ‖X - U‖ := by
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖N * (X - U)‖ ≤ β * ‖X - U‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
    have h2 := mul_le_mul_of_nonneg_left hYU (mul_nonneg hβ0 (backLip_nonneg l))
    linarith
  have hXU : ‖X - U‖ ≤ 2 * ‖T‖ := by
    have h3 := norm_sub_le (X - U + T) T
    rw [add_sub_cancel_right] at h3
    have h4 := mul_le_mul_of_nonneg_right hβ (norm_nonneg (X - U))
    linarith
  refine ⟨hXU, hmain.trans ?_⟩
  have h5 := mul_le_mul_of_nonneg_left hXU
    (mul_nonneg hβ0 (by linarith [backLip_nonneg l] : (0 : ℝ) ≤ 1 + 4 * backLip l))
  linarith

end Underlying

/-! ### The numerical dissipation of a scheme with `l` held samples -/

section Matrices

variable {n : ℕ}

/-- The constant of the numerical dissipation with `l` held samples,
`K = c + 2 b (1 + 4 λ_l) m + 6 m (m + α)`. -/
noncomputable def tradeK (l : ℕ) (b m c α : ℝ) : ℝ :=
  c + 2 * b * (1 + 4 * backLip l) * m + 6 * m * (m + α)

/-- `‖1‖ ≤ 1` for the spectral norm. -/
theorem norm_opE_one_le : ‖opE (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
  rw [opE_one]
  exact ContinuousLinearMap.norm_id_le

/-- `‖exp (H A) - 1‖ ≤ 2 H ‖A‖` for `0 ≤ H`, `H ‖A‖ ≤ 1/8`. -/
theorem norm_opE_exp_sub_one_le_two {A : Matrix (Fin n) (Fin n) ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hAH : H * ‖opE A‖ ≤ 1 / 8) : ‖opE (exp (H • A) - 1)‖ ≤ 2 * (H * ‖opE A‖) := by
  have h := norm_opE_exp_sub_one_le A hH
  have he : Real.exp (H * ‖opE A‖) ≤ 2 := by
    have h1 : Real.exp (H * ‖opE A‖) ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 (by linarith)
    have h2 := exp_quarter_le
    linarith
  have hA := norm_nonneg (opE A)
  nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg hA hH)]

/-- **The underlying one-step map of a scheme with `l` held samples, matrices**. For
`0 ≤ H`, `H ‖A‖ ≤ 1/8`, `‖M 0 - 1‖ ≤ β`, `‖M q‖ ≤ β` for `1 ≤ q < l`, `β λ_l ≤ 1/2` and
`‖𝒯‖ ≤ 1/16` (spectral norm, `U = exp (H A)`, `Ui = exp (-H A)`) there are `X`, `Y` with
`X Y = Y X = 1`, `(1 - N) X = Σ_{q<l} M q Y^q`, `‖Y - 1‖ ≤ 1/2` and `‖Y - Ui‖ ≤ 4 ‖𝒯‖`. -/
theorem exists_underlying_step_matrix {A N : Matrix (Fin n) (Fin n) ℝ}
    {M : ℕ → Matrix (Fin n) (Fin n) ℝ} {l : ℕ} (hl : 1 ≤ l) {H : ℝ} (hH : 0 ≤ H)
    (hAH : H * ‖opE A‖ ≤ 1 / 8) {β : ℝ} (hM0 : ‖opE (M 0 - 1)‖ ≤ β)
    (hM : ∀ q, 1 ≤ q → q < l → ‖opE (M q)‖ ≤ β) (hβ : β * backLip l ≤ 1 / 2)
    (hT : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l)‖ ≤ 1 / 16) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℝ, X * Y = 1 ∧ Y * X = 1 ∧
      (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q ∧ ‖opE (Y - 1)‖ ≤ 1 / 2 ∧
      ‖opE (Y - exp (-(H • A)))‖ ≤ 4 * ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l)‖ := by
  have hUi : ‖opE (exp (-(H • A)) - 1)‖ ≤ 1 / 4 := by
    have h := norm_opE_exp_sub_one_le_two (A := -A) hH (by rwa [norm_opE_neg])
    rw [smul_neg, norm_opE_neg] at h
    linarith
  open scoped Matrix.Norms.L2Operator in
  exact exists_underlying_step (𝔸 := Matrix (Fin n) (Fin n) ℝ) norm_opE_one_le hl
    (exp_mul_exp_neg (H • A)) hUi hM0 hM hβ hT

/-- **The numerical dissipation of a scheme with `l` held samples**
(`Δ_R = H^l sym (D_H) + O(H^{l+1})` for `𝒯 = H^{l+1} D_H`). Spectral norm, `U = exp (H A)`,
`Ui = exp (-H A)`, `𝒯 = runDefect N M U Ui l`. Let `1 ≤ l`, `0 < H ≤ 1`, `H ‖A‖ ≤ 1/8`, `‖N‖ ≤ b H`,
`‖M q‖ ≤ b H` for `1 ≤ q < l`, `b H (1 + 4 λ_l) ≤ 1/2`, `‖𝒯‖ ≤ m H^{l+1}`, `m H^{l+1} ≤ 1/48` and
`‖𝒯 - H^{l+1} (D + Z)‖ ≤ c H^{l+2}`. Every underlying one-step map `X` (`Y X = 1`,
`(1 - N) X = Σ_{q<l} M q Y^q`) with `‖Y‖ ≤ 2` has `‖Δ_R - H^l sym (D + Z)‖ ≤ K H^{l+1}`,
`Δ_R = numDissipation A (modifiedSystem H X)`, `K = tradeK l b m c ‖A‖`. -/
theorem numDissipation_underlying_sub_le {A N D Z X Y : Matrix (Fin n) (Fin n) ℝ}
    {M : ℕ → Matrix (Fin n) (Fin n) ℝ} {l : ℕ} (hl : 1 ≤ l) {H b m c : ℝ} (hH : 0 < H)
    (hH1 : H ≤ 1) (hAH : H * ‖opE A‖ ≤ 1 / 8) (hN : ‖opE N‖ ≤ b * H)
    (hM : ∀ q, 1 ≤ q → q < l → ‖opE (M q)‖ ≤ b * H)
    (hbH : b * H * (1 + 4 * backLip l) ≤ 1 / 2)
    (hT : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l)‖ ≤ m * H ^ (l + 1))
    (hmH : m * H ^ (l + 1) ≤ 1 / 48)
    (hTD : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l - H ^ (l + 1) • (D + Z))‖ ≤
      c * H ^ (l + 2))
    (hYX : Y * X = 1) (hX : (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q)
    (hY : ‖opE Y‖ ≤ 2) :
    ‖opE (numDissipation A (modifiedSystem H X) - H ^ l • sym (D + Z))‖ ≤
      tradeK l b m c ‖opE A‖ * H ^ (l + 1) := by
  obtain ⟨U, hU⟩ : ∃ U, U = exp (H • A) := ⟨_, rfl⟩
  obtain ⟨Ui, hUi⟩ : ∃ Ui, Ui = exp (-(H • A)) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = runDefect N M U Ui l := ⟨_, rfl⟩
  rw [← hU, ← hUi, ← hTdef] at hT hTD
  have hUUi : U * Ui = 1 := by
    rw [hU, hUi]
    open scoped Matrix.Norms.L2Operator in
    exact exp_mul_exp_neg (H • A)
  have hm0 : 0 ≤ m := by
    have h := (norm_nonneg _).trans hT
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hb0 : 0 ≤ b := by
    have h := (norm_nonneg _).trans hN
    exact nonneg_of_mul_nonneg_left h hH
  have hUi2 : ‖opE Ui‖ ≤ 2 := by
    have h := norm_opE_exp_sub_one_le_two (A := -A) hH.le (by rwa [norm_opE_neg])
    rw [smul_neg, norm_opE_neg, ← hUi] at h
    have h2 := norm_le_norm_add_norm_sub' (opE Ui) (opE 1)
    rw [← opE_sub] at h2
    linarith [norm_opE_one_le (n := n)]
  -- the a priori bounds
  obtain ⟨hXU, hXUT⟩ : ‖opE (X - U)‖ ≤ 2 * ‖opE T‖ ∧
      ‖opE (X - U + T)‖ ≤ 2 * (b * H) * (1 + 4 * backLip l) * ‖opE T‖ := by
    rw [hTdef]
    open scoped Matrix.Norms.L2Operator in
    exact norm_underlying_sub_le (𝔸 := Matrix (Fin n) (Fin n) ℝ) hUUi hYX hX hY hUi2 hN hM hbH
  have hHl : H ^ (l + 1) = H ^ (l - 1) * H ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hHl1 : H ^ l ≤ 1 := pow_le_one₀ hH.le hH1
  have hmH0 : 0 ≤ m * H ^ l := mul_nonneg hm0 (pow_nonneg hH.le l)
  -- the passage to the difference
  have hc : ‖opE (X - U)‖ ≤ (2 * m * H ^ (l - 1)) * H ^ 2 := by
    rw [mul_assoc, ← hHl]
    linarith
  have hU1 : ‖opE (U - 1)‖ ≤ 2 * (H * ‖opE A‖) := by
    rw [hU]
    exact norm_opE_exp_sub_one_le_two hH.le hAH
  have eb : (2 * m * H ^ l + 2 * ‖opE A‖) * H =
      2 * (m * H ^ (l + 1)) + 2 * (H * ‖opE A‖) := by
    rw [pow_succ]
    ring
  have hb : ‖opE (X - 1)‖ ≤ (2 * m * H ^ l + 2 * ‖opE A‖) * H := by
    have h2 := norm_add_le (opE (X - U)) (opE (U - 1))
    rw [← opE_add, sub_add_sub_cancel] at h2
    rw [eb]
    linarith
  have hbH' : (2 * m * H ^ l + 2 * ‖opE A‖) * H ≤ 1 / 3 := by
    rw [eb]
    linarith
  have hE₂ := norm_opE_difference_sub_le hH hU hb hc hbH' (by linarith)
  have hK₂ : diffLeadC (2 * m * H ^ l + 2 * ‖opE A‖) (2 * m * H ^ (l - 1)) ‖opE A‖ * H ^ 2 ≤
      6 * m * (m + ‖opE A‖) * H ^ (l + 1) := by
    have hmax : max (2 * m * H ^ l + 2 * ‖opE A‖) (4 / 3 * ‖opE A‖) =
        2 * m * H ^ l + 2 * ‖opE A‖ :=
      max_eq_left (by linarith [norm_nonneg (opE A)])
    rw [diffLeadC, hmax]
    have e : 3 / 2 * (2 * m * H ^ (l - 1)) * (2 * m * H ^ l + 2 * ‖opE A‖) * H ^ 2 =
        6 * m * (m * H ^ l + ‖opE A‖) * H ^ (l + 1) := by
      rw [hHl]
      ring
    rw [e]
    have h1 : m * H ^ l + ‖opE A‖ ≤ m + ‖opE A‖ := by
      linarith [mul_le_of_le_one_right hm0 hHl1]
    have h2 : 0 ≤ 6 * m * H ^ (l + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) hm0) (pow_nonneg hH.le _)
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
  -- the decomposition of `Δ + H^l (D + Z)`
  have hs : H⁻¹ • (H ^ (l + 1) • (D + Z)) = H ^ l • (D + Z) := by
    rw [smul_smul, pow_succ, mul_comm (H ^ l) H, ← mul_assoc, inv_mul_cancel₀ hH.ne', one_mul]
  have hdec : difference A H X + H ^ l • (D + Z) =
      (difference A H X - H⁻¹ • (X - U)) + H⁻¹ • (X - U + T) -
        H⁻¹ • (T - H ^ (l + 1) • (D + Z)) := by
    rw [smul_add H⁻¹ (X - U) T, smul_sub H⁻¹ T, hs]
    abel
  have hinv : ∀ (E : Matrix (Fin n) (Fin n) ℝ) (r : ℝ), ‖opE E‖ ≤ r * H →
      ‖opE (H⁻¹ • E)‖ ≤ r := fun E r h => by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le), inv_mul_le_iff₀ hH,
      mul_comm]
    exact h
  have h3 : ‖opE (H⁻¹ • (X - U + T))‖ ≤ 2 * b * (1 + 4 * backLip l) * m * H ^ (l + 1) := by
    refine hinv _ _ (hXUT.trans ?_)
    have h4 := mul_le_mul_of_nonneg_left hT
      (mul_nonneg (mul_nonneg zero_le_two (mul_nonneg hb0 hH.le))
        (by linarith [backLip_nonneg l] : (0 : ℝ) ≤ 1 + 4 * backLip l))
    exact h4.trans_eq (by ring)
  have h5 : ‖opE (H⁻¹ • (T - H ^ (l + 1) • (D + Z)))‖ ≤ c * H ^ (l + 1) :=
    hinv _ _ (hTD.trans_eq (by ring))
  have hΔ' : ‖opE (difference A H X + H ^ l • (D + Z))‖ ≤
      tradeK l b m c ‖opE A‖ * H ^ (l + 1) := by
    rw [hdec, opE_sub, opE_add]
    refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    rw [tradeK]
    linarith
  -- `Δ_R - H^l sym (D + Z) = -sym (Δ + H^l (D + Z))`
  have e : numDissipation A (modifiedSystem H X) - H ^ l • sym (D + Z) =
      -sym (difference A H X + H ^ l • (D + Z)) := by
    rw [HeldScheme.numDissipation_eq_neg_sym, sym_add (difference A H X) (H ^ l • (D + Z)),
      sym_smul (H ^ l) (D + Z), difference]
    abel
  rw [e, norm_opE_neg]
  exact (norm_opE_sym_le _).trans hΔ'

/-- **The trade between energy and damping with `l` held samples, every scheme**
(`μ + ι ≥ 2 H^l d_l - O(H^{l+1})`). Under the hypotheses of `numDissipation_underlying_sub_le`, with
`n ≥ 1`, a subspace `𝒵` with `1 ∈ 𝒵` and `Z ∈ 𝒵`, every `d ≤ ‖sym (D + Z')‖` for `Z' ∈ 𝒵`, and all
`μ`, `ι` with `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫ ≤ μ ‖v‖²`: `2 H^l d - 2 K H^{l+1} ≤ μ + ι`,
`K = tradeK l b m c ‖A‖`. -/
theorem trade_memory_le {A N D Z X Y : Matrix (Fin n) (Fin n) ℝ}
    {M : ℕ → Matrix (Fin n) (Fin n) ℝ} {l : ℕ} (hl : 1 ≤ l) {H b m c : ℝ} (hH : 0 < H)
    (hH1 : H ≤ 1) (hAH : H * ‖opE A‖ ≤ 1 / 8) (hN : ‖opE N‖ ≤ b * H)
    (hM : ∀ q, 1 ≤ q → q < l → ‖opE (M q)‖ ≤ b * H)
    (hbH : b * H * (1 + 4 * backLip l) ≤ 1 / 2)
    (hT : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l)‖ ≤ m * H ^ (l + 1))
    (hmH : m * H ^ (l + 1) ≤ 1 / 48)
    (hTD : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l - H ^ (l + 1) • (D + Z))‖ ≤
      c * H ^ (l + 2))
    (hYX : Y * X = 1) (hX : (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q)
    (hY : ‖opE Y‖ ≤ 2) (hn : 0 < n) {𝒵 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ 𝒵) (hZ : Z ∈ 𝒵) {d : ℝ}
    (hd : ∀ Z' ∈ 𝒵, d ≤ ‖opE (sym (D + Z'))‖) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H X)) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    2 * H ^ l * d - 2 * tradeK l b m c ‖opE A‖ * H ^ (l + 1) ≤ μ + ι := by
  have hE := numDissipation_underlying_sub_le hl hH hH1 hAH hN hM hbH hT hmH hTD hYX hX hY
  set K := tradeK l b m c ‖opE A‖
  set ΔR := numDissipation A (modifiedSystem H X) with hΔR
  -- `μ + ι ≥ 0`
  have hμι : 0 ≤ μ + ι := by
    obtain ⟨u⟩ := nonempty_sphere hn
    have h1 := hlo u
    have h2 := hhi u
    rw [mem_sphere_zero_iff_norm.1 u.2] at h1 h2
    linarith
  -- the centred numerical dissipation
  set T' := ΔR - ((μ - ι) / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) with hT'def
  have hT' : ‖opE T'‖ ≤ (μ + ι) / 2 := by
    have hsym : T'.IsSymm := (isSymm_numDissipation A _).sub (isSymm_one.smul _)
    refine norm_opE_le_of_abs_inner_self_le hsym (by linarith) fun v => ?_
    rw [hT'def, inner_opE_sub_smul_one, abs_le]
    have h1 := hlo v
    have h2 := hhi v
    constructor <;> linarith
  -- `H^l sym (D + Z') = T' - (ΔR - H^l sym (D + Z))` with `Z' = Z - ((μ - ι)/(2 H^l)) 1`
  have hHl : 0 < H ^ l := pow_pos hH l
  set Z' := Z - ((μ - ι) / 2 / H ^ l) • (1 : Matrix (Fin n) (Fin n) ℝ) with hZ'def
  have hZ' : Z' ∈ 𝒵 := 𝒵.sub_mem hZ (𝒵.smul_mem _ h1)
  have e : H ^ l • sym (D + Z') = T' - (ΔR - H ^ l • sym (D + Z)) := by
    rw [hZ'def, hT'def, show D + (Z - ((μ - ι) / 2 / H ^ l) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      (D + Z) - ((μ - ι) / 2 / H ^ l) • (1 : Matrix (Fin n) (Fin n) ℝ) by abel, sym_sub,
      sym_smul, sym_of_isSymm isSymm_one, smul_sub, smul_smul, mul_div_cancel₀ _ hHl.ne']
    abel
  have h3 : H ^ l * ‖opE (sym (D + Z'))‖ ≤ (μ + ι) / 2 + K * H ^ (l + 1) := by
    have h4 : ‖opE (H ^ l • sym (D + Z'))‖ ≤ ‖opE T'‖ + ‖opE (ΔR - H ^ l • sym (D + Z))‖ := by
      rw [e, opE_sub]
      exact norm_sub_le _ _
    rw [opE_smul, norm_smul, Real.norm_of_nonneg hHl.le] at h4
    linarith
  have h5 := mul_le_mul_of_nonneg_left (hd Z' hZ') hHl.le
  linarith

/-- **The fixed entries bound the trade, every scheme** (with the entries that no
scheme changes). Under the hypotheses of `trade_memory_le` with `𝒵 = rowReach sub V`, where every
vector of `V i` vanishes on the coordinates of `i` and `Z ∈ 𝒵`: for unit `e` supported on
subsystem `s` with `e ∈ V t` and unit `e'` supported on `t` with `e' ∈ V s`,
`2 H^l |⟪e, sym D e'⟫| - 2 K H^{l+1} ≤ μ + ι`, `K = tradeK l b m c ‖A‖`. -/
theorem trade_memory_fixed_entry_le {κ : Type*} {sub : Fin n → κ}
    {V : κ → Submodule ℝ (EuclideanSpace ℝ (Fin n))} {A N D Z X Y : Matrix (Fin n) (Fin n) ℝ}
    {M : ℕ → Matrix (Fin n) (Fin n) ℝ} {l : ℕ} (hl : 1 ≤ l) {H b m c : ℝ} (hH : 0 < H)
    (hH1 : H ≤ 1) (hAH : H * ‖opE A‖ ≤ 1 / 8) (hN : ‖opE N‖ ≤ b * H)
    (hM : ∀ q, 1 ≤ q → q < l → ‖opE (M q)‖ ≤ b * H)
    (hbH : b * H * (1 + 4 * backLip l) ≤ 1 / 2)
    (hT : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l)‖ ≤ m * H ^ (l + 1))
    (hmH : m * H ^ (l + 1) ≤ 1 / 48)
    (hTD : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l - H ^ (l + 1) • (D + Z))‖ ≤
      c * H ^ (l + 2))
    (hYX : Y * X = 1) (hX : (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q)
    (hY : ‖opE Y‖ ≤ 2) (hn : 0 < n) (hV : ∀ i, ∀ v ∈ V i, ∀ p, sub p = i → v p = 0)
    (hZ : Z ∈ rowReach sub V) {s t : κ} {e e' : EuclideanSpace ℝ (Fin n)}
    (he : ∀ p, sub p ≠ s → e p = 0) (heV : e ∈ V t) (he' : ∀ p, sub p ≠ t → e' p = 0)
    (he'V : e' ∈ V s) (hne : ‖e‖ = 1) (hne' : ‖e'‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H X)) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    2 * H ^ l * |⟪e, opE (sym D) e'⟫| - 2 * tradeK l b m c ‖opE A‖ * H ^ (l + 1) ≤ μ + ι :=
  trade_memory_le hl hH hH1 hAH hN hM hbH hT hmH hTD hYX hX hY hn (one_mem_rowReach hV) hZ
    (fun _ hZ' => abs_inner_sym_le_norm_of_mem_rowReach D hZ' he heV he' he'V hne hne') hlo hhi

/-- **The trade with `l` held samples, the scheme and its underlying map**. Under the hypotheses of
`trade_memory_le` on the coefficients, with moreover `‖M 0 - 1‖ ≤ b H`, the scheme has an underlying
one-step map `X` (`X Y = Y X = 1`, `(1 - N) X = Σ_{q<l} M q Y^q`, `‖Y - 1‖ ≤ 1/2`), its numerical
dissipation `Δ_R = numDissipation A (modifiedSystem H X)` has `‖Δ_R - H^l sym (D + Z)‖ ≤ K H^{l+1}`,
and every `μ`, `ι` bounding its form have `μ + ι ≥ 2 H^l d - 2 K H^{l+1}`, `K = tradeK l b m c ‖A‖`.
-/
theorem exists_underlying_trade_le {A N D Z : Matrix (Fin n) (Fin n) ℝ}
    {M : ℕ → Matrix (Fin n) (Fin n) ℝ} {l : ℕ} (hl : 1 ≤ l) {H b m c : ℝ} (hH : 0 < H)
    (hH1 : H ≤ 1) (hAH : H * ‖opE A‖ ≤ 1 / 8) (hN : ‖opE N‖ ≤ b * H)
    (hM0 : ‖opE (M 0 - 1)‖ ≤ b * H) (hM : ∀ q, 1 ≤ q → q < l → ‖opE (M q)‖ ≤ b * H)
    (hbH : b * H * (1 + 4 * backLip l) ≤ 1 / 2)
    (hT : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l)‖ ≤ m * H ^ (l + 1))
    (hmH : m * H ^ (l + 1) ≤ 1 / 48)
    (hTD : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l - H ^ (l + 1) • (D + Z))‖ ≤
      c * H ^ (l + 2))
    (hn : 0 < n) {𝒵 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ 𝒵) (hZ : Z ∈ 𝒵) {d : ℝ}
    (hd : ∀ Z' ∈ 𝒵, d ≤ ‖opE (sym (D + Z'))‖) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℝ, X * Y = 1 ∧ Y * X = 1 ∧
      (1 - N) * X = ∑ q ∈ range l, M q * Y ^ q ∧ ‖opE (Y - 1)‖ ≤ 1 / 2 ∧
      ‖opE (numDissipation A (modifiedSystem H X) - H ^ l • sym (D + Z))‖ ≤
        tradeK l b m c ‖opE A‖ * H ^ (l + 1) ∧
      ∀ μ ι : ℝ,
        (∀ v : EuclideanSpace ℝ (Fin n),
          -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H X)) v⟫) →
        (∀ v : EuclideanSpace ℝ (Fin n),
          ⟪v, opE (numDissipation A (modifiedSystem H X)) v⟫ ≤ μ * ‖v‖ ^ 2) →
        2 * H ^ l * d - 2 * tradeK l b m c ‖opE A‖ * H ^ (l + 1) ≤ μ + ι := by
  have hb0 : 0 ≤ b * H := (norm_nonneg _).trans hN
  have hβ : b * H * backLip l ≤ 1 / 2 := by
    have := backLip_nonneg l
    nlinarith
  have hT16 : ‖opE (runDefect N M (exp (H • A)) (exp (-(H • A))) l)‖ ≤ 1 / 16 := by linarith
  obtain ⟨X, Y, hXY, hYX, hX, hY1, -⟩ :=
    exists_underlying_step_matrix hl hH.le hAH hM0 hM hβ hT16
  have hY : ‖opE Y‖ ≤ 2 := by
    have h2 := norm_le_norm_add_norm_sub' (opE Y) (opE 1)
    rw [← opE_sub] at h2
    linarith [norm_opE_one_le (n := n)]
  refine ⟨X, Y, hXY, hYX, hX, hY1,
    numDissipation_underlying_sub_le hl hH hH1 hAH hN hM hbH hT hmH hTD hYX hX hY,
    fun μ ι hlo hhi => trade_memory_le hl hH hH1 hAH hN hM hbH hT hmH hTD hYX hX hY hn h1
      hZ hd hlo hhi⟩

end Matrices

end CoSimFoundations
