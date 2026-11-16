/-
The first-order barrier for consistent schemes, with its leading term (the paper, Theorem 5.6
`thm:barrier`, second display `eq:firstorder`): if two subsystems `i` and `j` that are not
partners have `a_ij = ½ ‖Σ_k ς_ik A_ik A_kj‖ > 0`, every consistent family of holds has

  `max_{kH ≤ T} ‖X^k - U^k‖ ≥ a_ij H / (20 ‖A‖) · (1 - O(H))`,   `T = 1 / (2 ‖A‖)`.

Setting of `ForcedNorm`: a `HeldScheme` with `S.Consistent A U H a b c`, spectral norms
`‖opE ·‖`, `g = forcedCoeff A s t` (the paper's `a_st`), `C = reactionC a b c ‖A‖ H`,
`α = ‖A‖`.

**The bridge.** `first_order_barrier` (`BarrierConstants.lean`) is stated in a complete normed
algebra with `‖1‖ = 1`. The algebra used here is that of the operators on Euclidean space, into
which `opE` maps the matrices as a homomorphism of algebras: `opE (X ^ k) = opE X ^ k`
(`opE_pow`) and `opE (exp (H • A)) = exp (H • opE A)` (`opE_exp`), so that
`opE (X ^ k - U ^ k) = opE X ^ k - exp (H • opE A) ^ k` (`opE_pow_sub_exp_pow`). `‖1‖ = 1` needs
a space that is not zero; this follows from the positive lower bound of `‖X - U‖`
(`nontrivial_of_norm_opE_pos`), and without such a bound the statement is empty.

**Results.** For a consistent scheme and `s ≠ t` that are not partners:
* `Consistent.first_order_barrier_forced`: for `K ≥ 1` with `K H ‖A‖ ≤ 1/2`, if
  `‖X^k - U^k‖ ≤ δ` for all `k ≤ K`, then with `c = g H² - C H³` (`ForcedNorm`)
    `min (K c / 10) (√(c / 6)) ≤ δ`.
* `Consistent.first_order_lead`: with `K = ⌊1 / (2 H ‖A‖)⌋₊`, the largest `k` with `k H ≤ T`,
    `g H / (20 α) - (g / 10 + C / (10 α)) H² ≤ δ`,
  that is `δ ≥ g H / (20 α) · (1 - (2 α + 2 C / g) H)`: the paper's `eq:firstorder` with the
  paper's constant `20` and the remainder `(g / 10 + C / (10 α)) H²` (`firstOrderRem`). No
  smallness of `H` and no positivity of `g` is assumed: where the hypotheses of the paper fail
  (`g = 0`, `H ‖A‖ > 1/2`, `H = 0`) the left side is not positive.
* `Consistent.first_order_lead_sup`, `Consistent.exists_first_order_lead`: the same for the
  maximum over `k ≤ K`, and as the existence of a step `k` with `k H ≤ 1 / (2 ‖A‖)`.

Proof of the lead (the paper's, with the constants). If the left side `L` is positive, then
`(2 α g + 2 C) H < g`, hence `g > 0`, `2 α H < 1` (so `K ≥ 1`) and `c ≥ g H² / 2 > 0`. From
`K > 1 / (2 H α) - 1`: `K c / 10 ≥ g H / (20 α) - (g / 10 + C / (20 α)) H² ≥ L`. From
`g ≤ α² / 2` (`Consistent.forcedCoeff_le`): `(g H / (20 α))² ≤ g H² / 12 ≤ c / 6`, so that
`L ≤ √(c / 6)`: the first term of the minimum decides.
-/
import CoSimFoundations.ForcedNorm
import CoSimFoundations.BarrierConstants

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

variable {n : ℕ}

/-- The operator of a power of a matrix is the power of its operator. -/
theorem opE_pow (X : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : opE (X ^ k) = opE X ^ k :=
  map_pow _ X k

/-- **The bridge to the normed algebra of the operators:** the error after `k` macro steps, as
operators on Euclidean space. -/
theorem opE_pow_sub_exp_pow (X A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) (k : ℕ) :
    opE (X ^ k - NormedSpace.exp (H • A) ^ k) =
      opE X ^ k - NormedSpace.exp (H • opE A) ^ k := by
  rw [opE_sub, opE_pow, opE_pow, opE_exp, opE_smul]

/-- A matrix whose operator has a positive norm acts on a space that is not zero. -/
theorem nontrivial_of_norm_opE_pos {T : Matrix (Fin n) (Fin n) ℝ} (hT : 0 < ‖opE T‖) :
    Nontrivial (EuclideanSpace ℝ (Fin n)) := by
  by_contra hne
  rw [not_nontrivial_iff_subsingleton] at hne
  have h0 : opE T = 0 := Subsingleton.elim _ _
  rw [h0, norm_zero] at hT
  exact lt_irrefl _ hT

end OneStep

open OneStep

variable {n : ℕ}

/-- The steps up to `K = ⌊1 / (2 H α)⌋₊` are the steps within the horizon `T = 1 / (2 α)`:
`k ≤ K` gives `k H ≤ 1 / (2 α)`. -/
theorem mul_le_horizon_of_le_floor {H α : ℝ} (hH : 0 ≤ H) (hα : 0 ≤ α) {k : ℕ}
    (hk : k ≤ ⌊1 / (2 * H * α)⌋₊) : k * H ≤ 1 / (2 * α) := by
  have hk' : (k : ℝ) ≤ 1 / (2 * H * α) :=
    (Nat.cast_le.2 hk).trans (Nat.floor_le (by positivity))
  rcases hH.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    positivity
  · have h1 := mul_le_mul_of_nonneg_right hk' hpos.le
    have e : 1 / (2 * H * α) * H = 1 / (2 * α) := by
      field_simp
    rwa [e] at h1

/-- The remainder of the first-order barrier: `g / 10 + C / (10 α)`, with `g = a_st`,
`C = reactionC a b c ‖A‖ H`, `α = ‖A‖`. -/
noncomputable def firstOrderRem (g C α : ℝ) : ℝ := g / 10 + C / (10 * α)

/-- **The arithmetic of the leading term.** Let `0 ≤ g ≤ α² / 2`, `K` the integer part of
`1 / (2 H α)`, and suppose that `min (K c / 10) (√(c / 6)) ≤ δ` with `c = g H² - C H³` whenever
`K ≥ 1` and `K H α ≤ 1/2`. Then `g H / (20 α) - (g / 10 + C / (10 α)) H² ≤ δ`. -/
theorem first_order_lead_arith {g C α H δ : ℝ} {K : ℕ} (hH : 0 ≤ H) (hα0 : 0 ≤ α) (hg0 : 0 ≤ g)
    (hgle : g ≤ α ^ 2 / 2) (hCH : 0 ≤ C * H ^ 3) (hδ0 : 0 ≤ δ)
    (hfl : 1 / (2 * H * α) < K + 1) (hfl' : 0 ≤ 1 / (2 * H * α) → (K : ℝ) ≤ 1 / (2 * H * α))
    (hfl1 : (1 : ℝ) ≤ 1 / (2 * H * α) → 1 ≤ K)
    (hforced : 1 ≤ K → K * H * α ≤ 1 / 2 →
      min (K * (g * H ^ 2 - C * H ^ 3) / 10) (Real.sqrt ((g * H ^ 2 - C * H ^ 3) / 6)) ≤ δ) :
    g * H / (20 * α) - firstOrderRem g C α * H ^ 2 ≤ δ := by
  unfold firstOrderRem
  by_contra hL
  rw [not_le] at hL
  have hLpos : 0 < g * H / (20 * α) - (g / 10 + C / (10 * α)) * H ^ 2 := hδ0.trans_lt hL
  -- the macro step and the norm of `A` are positive
  have hHpos : 0 < H := by
    rcases hH.eq_or_lt with h0 | hpos
    · rw [← h0] at hLpos
      simp at hLpos
    · exact hpos
  have hαpos : 0 < α := by
    rcases hα0.eq_or_lt with h0 | hpos
    · rw [← h0] at hLpos
      simp only [mul_zero, div_zero, add_zero, zero_sub] at hLpos
      have : 0 ≤ g / 10 * H ^ 2 := by positivity
      linarith
    · exact hpos
  have hHne : H ≠ 0 := hHpos.ne'
  have hαne : α ≠ 0 := hαpos.ne'
  have hC0 : 0 ≤ C := (mul_nonneg_iff_of_pos_right (pow_pos hHpos 3)).1 hCH
  -- the positive left side says `(2 α g + 2 C) H < g`
  have hfac : g * H / (20 * α) - (g / 10 + C / (10 * α)) * H ^ 2 =
      H / (20 * α) * (g - (2 * α * g + 2 * C) * H) := by
    field_simp
    ring
  rw [hfac] at hLpos hL
  have hpre : 0 < H / (20 * α) := by positivity
  have hkey : (2 * α * g + 2 * C) * H < g := by
    have := (mul_pos_iff_of_pos_left hpre).1 hLpos
    linarith
  have hrem : 0 ≤ (2 * α * g + 2 * C) * H := by positivity
  have hgpos : 0 < g := by linarith
  have hCg : 2 * (C * H) < g := by
    have : 0 ≤ 2 * α * g * H := by positivity
    linarith
  have hαH : 2 * H * α < 1 := by
    have h1 : 0 ≤ 2 * C * H := by positivity
    have h2 : (2 * H * α) * g < 1 * g := by linarith
    exact lt_of_mul_lt_mul_right h2 hg0
  have hHα : 0 < 2 * H * α := by positivity
  -- the number of steps
  have hK1 : 1 ≤ K := hfl1 (by rw [le_div_iff₀ hHα]; linarith)
  have hKle : (K : ℝ) ≤ 1 / (2 * H * α) := hfl' (by positivity)
  have hKH : (K : ℝ) * H * α ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hKle (mul_nonneg hH hα0)
    have e : 1 / (2 * H * α) * (H * α) = 1 / 2 := by
      field_simp
    rw [e] at h1
    linarith
  have hmin := hforced hK1 hKH
  -- the one-step bound is at least `g H² / 2`
  have hcge : g * H ^ 2 / 2 ≤ g * H ^ 2 - C * H ^ 3 := by
    have h1 : 0 ≤ H ^ 2 * (g - 2 * (C * H)) := mul_nonneg (sq_nonneg H) (by linarith)
    have e : H ^ 2 * (g - 2 * (C * H)) = g * H ^ 2 - 2 * (C * H ^ 3) := by ring
    linarith
  have hgH : 0 < g * H ^ 2 / 2 := by positivity
  have hcpos : 0 < g * H ^ 2 - C * H ^ 3 := lt_of_lt_of_le hgH hcge
  -- the first term of the minimum
  have hfirst : H / (20 * α) * (g - (2 * α * g + 2 * C) * H) ≤
      K * (g * H ^ 2 - C * H ^ 3) / 10 := by
    have h1 : (1 / (2 * H * α) - 1) * (g * H ^ 2 - C * H ^ 3) ≤ K * (g * H ^ 2 - C * H ^ 3) :=
      mul_le_mul_of_nonneg_right (by linarith) hcpos.le
    have e : (1 / (2 * H * α) - 1) * (g * H ^ 2 - C * H ^ 3) / 10 -
        H / (20 * α) * (g - (2 * α * g + 2 * C) * H) = C * H ^ 2 / (20 * α) + C * H ^ 3 / 10 := by
      field_simp
      ring
    have h2 : 0 ≤ C * H ^ 2 / (20 * α) + C * H ^ 3 / 10 := by positivity
    linarith
  -- the second term of the minimum
  have hsecond : H / (20 * α) * (g - (2 * α * g + 2 * C) * H) ≤
      Real.sqrt ((g * H ^ 2 - C * H ^ 3) / 6) := by
    refine (Real.le_sqrt' hLpos).2 ?_
    have h1 : H / (20 * α) * (g - (2 * α * g + 2 * C) * H) ≤ H / (20 * α) * g :=
      mul_le_mul_of_nonneg_left (by linarith) hpre.le
    have h2 : (H / (20 * α) * (g - (2 * α * g + 2 * C) * H)) ^ 2 ≤ (H / (20 * α) * g) ^ 2 :=
      pow_le_pow_left₀ hLpos.le h1 2
    have h3 : (H / (20 * α) * g) ^ 2 ≤ g * H ^ 2 / 12 := by
      have e : (H / (20 * α) * g) ^ 2 = g * H ^ 2 * (g / (400 * α ^ 2)) := by
        field_simp
        ring
      have h4 : g / (400 * α ^ 2) ≤ 1 / 12 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [sq_nonneg α]
      have h5 : (0 : ℝ) ≤ g * H ^ 2 := by positivity
      have h6 := mul_le_mul_of_nonneg_left h4 h5
      rw [e]
      linarith
    linarith
  exact absurd ((le_min hfirst hsecond).trans hmin) (not_le.2 hL)

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

/-- **The first-order barrier for a consistent scheme** (Theorem 5.6 with the one-step bound
`eq:aij`). For a consistent scheme with one held sample, two subsystems `s ≠ t` that are not
partners and `K ≥ 1` macro steps with `K H ‖A‖ ≤ 1/2`: if `‖X^k - U^k‖ ≤ δ` for all `k ≤ K`,
then `min (K c / 10) (√(c / 6)) ≤ δ` with `c = a_st H² - C H³`. -/
theorem Consistent.first_order_barrier_forced {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) {K : ℕ}
    (hK : 1 ≤ K) (hKH : K * H * ‖opE A‖ ≤ 1 / 2) {δ : ℝ}
    (hδ : ∀ k ≤ K, ‖opE (S.X ^ k - U ^ k)‖ ≤ δ) :
    min (K * (S.forcedCoeff A s t * H ^ 2 - reactionC a b c ‖opE A‖ H * H ^ 3) / 10)
      (Real.sqrt ((S.forcedCoeff A s t * H ^ 2 - reactionC a b c ‖opE A‖ H * H ^ 3) / 6)) ≤ δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (Nat.zero_le _))
  have hc := h.forced_norm hst hnp
  rcases le_or_gt (S.forcedCoeff A s t * H ^ 2 - reactionC a b c ‖opE A‖ H * H ^ 3) 0 with
    hc0 | hc0
  · have h1 : (K : ℝ) * (S.forcedCoeff A s t * H ^ 2 - reactionC a b c ‖opE A‖ H * H ^ 3) / 10
        ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg K) hc0)
        (by norm_num)
    exact (min_le_left _ _).trans (h1.trans hδ0)
  · have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      nontrivial_of_norm_opE_pos (hc0.trans_le hc)
    have hU := h.hU
    subst hU
    have hc' : S.forcedCoeff A s t * H ^ 2 - reactionC a b c ‖opE A‖ H * H ^ 3 ≤
        ‖opE S.X - NormedSpace.exp (H • opE A)‖ := by
      have e := opE_pow_sub_exp_pow S.X A H 1
      rw [pow_one, pow_one, pow_one, pow_one] at e
      rw [← e]
      exact hc
    refine first_order_barrier (opE A) (opE S.X) h.hH hK hKH hc' fun k hk => ?_
    rw [← opE_pow_sub_exp_pow]
    exact hδ k hk

/-- **The first-order barrier, leading term** (Theorem 5.6, `eq:firstorder`, with an explicit
remainder). For a consistent scheme with one held sample, in any order of execution, and two
subsystems `s ≠ t` that are not partners, let `K = ⌊1 / (2 H ‖A‖)⌋₊` be the number of macro steps
within the horizon `T = 1 / (2 ‖A‖)`. If `‖X^k - U^k‖ ≤ δ` for all `k ≤ K`, then
`a_st H / (20 ‖A‖) - (a_st / 10 + C / (10 ‖A‖)) H² ≤ δ`, `C = reactionC a b c ‖A‖ H`. -/
theorem Consistent.first_order_lead {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) {δ : ℝ}
    (hδ : ∀ k ≤ ⌊1 / (2 * H * ‖opE A‖)⌋₊, ‖opE (S.X ^ k - U ^ k)‖ ≤ δ) :
    S.forcedCoeff A s t * H / (20 * ‖opE A‖) -
      firstOrderRem (S.forcedCoeff A s t) (reactionC a b c ‖opE A‖ H) ‖opE A‖ * H ^ 2 ≤ δ :=
  first_order_lead_arith h.hH (norm_nonneg _) (S.forcedCoeff_nonneg A s t)
    (h.forcedCoeff_le hst hnp) h.reaction_bound_nonneg
    ((norm_nonneg _).trans (hδ 0 (Nat.zero_le _))) (Nat.lt_floor_add_one _)
    (fun h0 => Nat.floor_le h0) (fun h1 => (Nat.one_le_floor_iff _).2 h1)
    (fun hK hKH => h.first_order_barrier_forced hst hnp hK hKH hδ)

/-- **The first-order barrier, leading term, with the maximum** (`eq:firstorder`):
`max_{k ≤ K} ‖X^k - U^k‖ ≥ a_st H / (20 ‖A‖) - (a_st / 10 + C / (10 ‖A‖)) H²`,
`K = ⌊1 / (2 H ‖A‖)⌋₊`. -/
theorem Consistent.first_order_lead_sup {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    S.forcedCoeff A s t * H / (20 * ‖opE A‖) -
        firstOrderRem (S.forcedCoeff A s t) (reactionC a b c ‖opE A‖ H) ‖opE A‖ * H ^ 2 ≤
      (Finset.range (⌊1 / (2 * H * ‖opE A‖)⌋₊ + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖opE (S.X ^ k - U ^ k)‖) :=
  h.first_order_lead hst hnp fun _ hj =>
    Finset.le_sup' (fun k => ‖opE (S.X ^ k - U ^ k)‖)
      (Finset.mem_range.2 (Nat.lt_succ_iff.2 hj))

/-- **The first-order barrier, leading term, as the paper states it** (`eq:firstorder`): there is
a step `k` within the horizon, `k H ≤ T = 1 / (2 ‖A‖)`, at which
`‖X^k - U^k‖ ≥ a_st H / (20 ‖A‖) - (a_st / 10 + C / (10 ‖A‖)) H²`. -/
theorem Consistent.exists_first_order_lead {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t) :
    ∃ k : ℕ, k * H ≤ 1 / (2 * ‖opE A‖) ∧
      S.forcedCoeff A s t * H / (20 * ‖opE A‖) -
        firstOrderRem (S.forcedCoeff A s t) (reactionC a b c ‖opE A‖ H) ‖opE A‖ * H ^ 2 ≤
      ‖opE (S.X ^ k - U ^ k)‖ := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_add_one (n := ⌊1 / (2 * H * ‖opE A‖)⌋₊))
    (fun k => ‖opE (S.X ^ k - U ^ k)‖)
  refine ⟨k, mul_le_horizon_of_le_floor h.hH (norm_nonneg _)
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), ?_⟩
  rw [← hmax]
  exact h.first_order_lead_sup hst hnp

end HeldScheme

end CoSimFoundations
