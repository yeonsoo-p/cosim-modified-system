/-
Injection by the subsystem that runs first, damping of the subsystem that runs last (the
paper, Theorem 6.2 `thm:access`, equation `eq:gi`, and the two consequences stated after it), as
inequalities with explicit remainders.

Setting of `ForcedBlock`, `Reaction`, `ReactionDiag`: a `HeldScheme` that is `Consistent` with
constants `a`, `b`, `c` at the macro step `H ≥ 0`; `A_{kl} = -A_{lk}ᵀ` between different
subsystems (`hskew`); the subsystem `s` is not its own partner and has `F_s = e^{H A_s}` (partner
weights only, `hFs`); `e` a unit vector supported on `s`. `D` is a defect: `D * U = X`, with
`‖D - 1‖ ≤ c' H²` (`Consistent.defect`: `D = X exp (-H A)` has
`c' = c (1 + ‖A‖ e^{H‖A‖} H)`). Write
  `coupled s A e = Σ_{r ∉ s} ((A e)_r)² = Σ_{k ≠ s} |A_{ks} e|²`,
  `C_d = reactionC a b c ‖A‖ H + ‖A_s‖³/6 · e^{H‖A_s‖}`   (`reactionDiagC`).

* `Consistent.reaction_quadratic` (`eq:gi`):
    `|⟪e, (X - U) e⟫ + ½H² Σ_{k ≠ s} ς_{sk} |A_{ks} e|²| ≤ C_d H³`.
* `Consistent.injection_first`: if no partner of `s` runs before `s`,
    `½H² Σ_k |A_{ks} e|² - (C_d + c' ‖A‖ e^{H‖A‖}) H³ ≤ ‖D‖ - 1`      (`‖D‖ = s₊`).
* `Consistent.damping_last`: if every partner of `s` runs before `s` and `c' H² ≤ ½`,
    `½H² Σ_k |A_{ks} e|² - (C_d + 2 c' b) H³ ≤ ‖D⁻¹‖ - 1`            (`‖D⁻¹‖ = 1 / s₋`).
* `Consistent.smin_last`, `Consistent.smin_last_le`: for every `σ > 0` with `σ ‖v‖ ≤ ‖D v‖` for
  all `v` (in particular `σ = s₋`), with `y = ½H² Σ_k |A_{ks} e|² - (C_d + 2 c' b) H³`:
    `σ (1 + y) ≤ 1`,   and   `σ ≤ 1 - y + y²` if `y ≥ 0`.

Proofs: `Consistent.reaction_partner_weights` with `x = y = e`; the signs `ς_{sk}` are all `-1`
(first) or all `+1` (last) on the partners, and `A_{ks} e = 0` for the other subsystems; then
`diag_gain` (`PairLaws`) and `diag_gain_inverse`, `diag_gain_smin_complete` (`ReactionGain`) with
`‖U e - e‖ ≤ ‖A‖ e^{H‖A‖} H`, `‖X e - e‖ ≤ b H` and `α / (1 - α) ≤ 2 c' H²`.

* `inner_X_eq_inner_F_of_first`, `inner_step_error_of_first` (Theorem 6.2, last statement): a
  subsystem that receives no new sample has `Π_s X Π_sᵀ = F_s` exactly, hence
  `⟪e, (X - U) e⟫ = ⟪e, (e^{H A_s} - U) e⟫` with partner weights only.

The paper states the two consequences with `O(H³)` for "a hold with partner weights only". Here
the partner weights enter through `F_s = e^{H A_s}` for the one subsystem `s` only (`hFs`; see
`BlockExp.block_eq_of_sblock` for the form with the matrix `A_s` on the states of `s`). The
partner relation of a `HeldScheme` is not assumed symmetric: "no partner of `s` runs before `s`"
is `∀ k, partner k s → …` where the entries of `A` are used and `∀ k, partner s k → …` where the
new samples of `s` are used.
-/
import CoSimFoundations.ReactionDiag
import CoSimFoundations.ReactionGain

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-- If `0 ≤ α ≤ t ≤ ½`, then `α / (1 - α) ≤ 2 t`. -/
theorem div_one_sub_le_two_mul {α t : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ t) (h2 : t ≤ 1 / 2) :
    α / (1 - α) ≤ 2 * t := by
  rw [div_le_iff₀ (by linarith)]
  have h3 := mul_nonneg (le_trans h0 h1) (by linarith : (0 : ℝ) ≤ 1 - 2 * α)
  linarith

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- What a state `e` of the subsystem `s` drives in the other subsystems, squared:
`Σ_{r ∉ s} ((A e)_r)² = Σ_{k ≠ s} |A_{ks} e|²`. -/
noncomputable def coupled (s : κ) (A : Matrix (Fin n) (Fin n) ℝ)
    (e : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ r, if S.sub r = s then 0 else ((opE A e) r) ^ 2

/-- The constant of the diagonal block: `reactionC a b c α H + αs³/6 · e^{H αs}`, with
`α = ‖A‖`, `αs = ‖A_s‖`. -/
noncomputable def reactionDiagC (a b c α αs H : ℝ) : ℝ :=
  reactionC a b c α H + αs ^ 3 / 6 * Real.exp (H * αs)

omit [DecidableEq κ] in
/-- A state of `s` does not drive a subsystem that is not a partner of `s`. -/
theorem opE_apply_eq_zero_of_not_partner {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {s : κ}
    {e : EuclideanSpace ℝ (Fin n)} (hes : ∀ p, S.sub p ≠ s → e p = 0) {r : Fin n}
    (hr : S.sub r ≠ s) (hnp : ¬ S.partner (S.sub r) s) : (opE A e) r = 0 := by
  rw [opE_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : S.sub q = s
  · rw [hA r q (by rw [hq]; exact hr) (by rw [hq]; exact hnp), zero_mul]
  · rw [hes q hq, mul_zero]

/-- If no partner of `s` runs before `s`, all signs are `-1`:
`Σ_k ς_{sk} |A_{ks} e|² = -Σ_k |A_{ks} e|²`. -/
theorem inner_osgn_first {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {s : κ}
    (hfirst : ∀ k, S.partner k s → ¬ S.stage k < S.stage s)
    {e : EuclideanSpace ℝ (Fin n)} (hes : ∀ p, S.sub p ≠ s → e p = 0) :
    ⟪opE A e, opE (S.osgn s) (opE A e)⟫ = -S.coupled s A e := by
  unfold coupled
  rw [S.inner_osgn, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = s
  · simp [hr]
  · simp only [hr, ↓reduceIte]
    by_cases hp : S.partner (S.sub r) s
    · have e1 : S.sg s (S.sub r) = -1 := by simp [sg, hfirst _ hp]
      rw [e1]
      ring
    · rw [S.opE_apply_eq_zero_of_not_partner hA hes hr hp]
      ring

/-- If every partner of `s` runs before `s`, all signs are `+1`:
`Σ_k ς_{sk} |A_{ks} e|² = Σ_k |A_{ks} e|²`. -/
theorem inner_osgn_last {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {s : κ}
    (hlast : ∀ k, S.partner k s → S.stage k < S.stage s)
    {e : EuclideanSpace ℝ (Fin n)} (hes : ∀ p, S.sub p ≠ s → e p = 0) :
    ⟪opE A e, opE (S.osgn s) (opE A e)⟫ = S.coupled s A e := by
  unfold coupled
  rw [S.inner_osgn]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = s
  · simp [hr]
  · simp only [hr, ↓reduceIte]
    by_cases hp : S.partner (S.sub r) s
    · have e1 : S.sg s (S.sub r) = 1 := by simp [sg, hlast _ hp]
      rw [e1]
      ring
    · rw [S.opE_apply_eq_zero_of_not_partner hA hes hr hp]
      ring

variable {S}

omit [DecidableEq κ] in
/-- **The defect and its size.** For a consistent scheme `D = X exp (-H A)` satisfies
`D * U = X` and `‖D - 1‖ ≤ c (1 + ‖A‖ e^{H‖A‖} H) H²`. -/
theorem Consistent.defect {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) :
    S.X * NormedSpace.exp (-(H • A)) * U = S.X ∧
      ‖opE (S.X * NormedSpace.exp (-(H • A))) - 1‖ ≤
        c * (1 + ‖opE A‖ * Real.exp (H * ‖opE A‖) * H) * H ^ 2 := by
  have hVU : NormedSpace.exp (-(H • A)) * U = 1 := by
    rw [h.hU, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl (H • A))),
      neg_add_cancel, NormedSpace.exp_zero]
  have hUV : U * NormedSpace.exp (-(H • A)) = 1 := by
    rw [h.hU, ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl (H • A))),
      add_neg_cancel, NormedSpace.exp_zero]
  refine ⟨by rw [Matrix.mul_assoc, hVU, Matrix.mul_one], ?_⟩
  have e1 : S.X * NormedSpace.exp (-(H • A)) - 1 = (S.X - U) * NormedSpace.exp (-(H • A)) := by
    rw [Matrix.sub_mul, hUV]
  have hV1 : ‖opE (NormedSpace.exp (-(H • A)))‖ ≤ 1 + ‖opE A‖ * Real.exp (H * ‖opE A‖) * H := by
    have h1 := norm_exp_sub_one_le (-(H • opE A))
    rw [norm_neg, norm_smul, Real.norm_of_nonneg h.hH] at h1
    have h2 : opE (NormedSpace.exp (-(H • A))) = NormedSpace.exp (-(H • opE A)) := by
      have h0 : opE (-(H • A)) = -(H • opE A) := by
        rw [← opE_smul]
        exact map_neg _ _
      rw [opE_exp, h0]
    have h3 := norm_add_le (NormedSpace.exp (-(H • opE A)) - 1)
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    rw [sub_add_cancel] at h3
    have h4 : ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    rw [h2]
    linarith
  have hcH : 0 ≤ c * H ^ 2 := le_trans (norm_nonneg _) h.hc
  rw [← opE_one, ← opE_sub, e1, opE_mul]
  refine (norm_mul_le _ _).trans ?_
  have h5 := mul_le_mul h.hc hV1 (norm_nonneg _) hcH
  have e2 : c * (1 + ‖opE A‖ * Real.exp (H * ‖opE A‖) * H) * H ^ 2 =
      c * H ^ 2 * (1 + ‖opE A‖ * Real.exp (H * ‖opE A‖) * H) := by ring
  rw [e2]
  exact h5

/-- **The quadratic form of the diagonal block** (Theorem 6.2, `eq:gi`, with its remainder).
Partner weights only for the subsystem `s`, `e` a unit vector supported on `s`:
`|⟪e, (X - U) e⟫ + ½H² Σ_{k ≠ s} ς_{sk} |A_{ks} e|²| ≤ C_d H³`. -/
theorem Consistent.reaction_quadratic {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hes : ∀ p, S.sub p ≠ s → e p = 0) :
    |⟪e, opE (S.X - U) e⟫ + H ^ 2 / 2 * ⟪opE A e, opE (S.osgn s) (opE A e)⟫| ≤
      reactionDiagC a b c ‖opE A‖ ‖opE (S.blk s A)‖ H * H ^ 3 := by
  have h1 := h.reaction_partner_weights hskew hnp hFs hes hes
  rwa [he, mul_one, mul_one] at h1

/-- **Injection by a subsystem that runs before all of its partners** (after Theorem 6.2, with
its remainder). `D * U = X`, `‖D - 1‖ ≤ c' H²`, partner weights only for `s`, no partner of `s`
runs before `s`, `e` a unit vector supported on `s`:
`½H² Σ_k |A_{ks} e|² - (C_d + c' ‖A‖ e^{H‖A‖}) H³ ≤ ‖D‖ - 1`, and `‖D‖` is the largest singular
value `s₊` of the defect. -/
theorem Consistent.injection_first {A U D : Matrix (Fin n) (Fin n) ℝ} {H a b c c' : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    (hfirst : ∀ k, S.partner k s → ¬ S.stage k < S.stage s) (hD : D * U = S.X)
    (hα : ‖opE D - 1‖ ≤ c' * H ^ 2) {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hes : ∀ p, S.sub p ≠ s → e p = 0) :
    H ^ 2 / 2 * S.coupled s A e - (reactionDiagC a b c ‖opE A‖ ‖opE (S.blk s A)‖ H +
      c' * (‖opE A‖ * Real.exp (H * ‖opE A‖))) * H ^ 3 ≤ ‖opE D‖ - 1 := by
  have h1 := h.reaction_quadratic hskew hnp hFs he hes
  rw [S.inner_osgn_first h.hA hfirst hes] at h1
  have h2 := diag_gain (opE D) (opE U) he
  rw [← opE_mul_apply, hD] at h2
  have h3 := inner_opE_sub S.X U e e
  have h4 : ‖opE U e - e‖ ≤ ‖opE A‖ * Real.exp (H * ‖opE A‖) * H := by
    have e1 : opE U e - e = opE (U - 1) e := by
      rw [opE_sub, opE_one]
      simp
    have h5 := (opE (U - 1)).le_opNorm e
    rw [he, mul_one] at h5
    rw [e1]
    refine h5.trans ?_
    rw [h.hU]
    exact norm_opE_exp_sub_one_le A h.hH
  have h6 := mul_le_mul hα h4 (norm_nonneg _) (le_trans (norm_nonneg _) hα)
  have h7 := (abs_le.1 h1).1
  linarith

/-- The lower bound behind the damping of the last subsystem: with
`y = ½H² Σ_k |A_{ks} e|² - (C_d + 2 c' b) H³`, `y ≤ -g - α / (1 - α) ‖X e - e‖`. -/
theorem Consistent.damping_aux {A U D : Matrix (Fin n) (Fin n) ℝ} {H a b c c' : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    (hlast : ∀ k, S.partner k s → S.stage k < S.stage s) (hD : D * U = S.X)
    (hα : ‖opE D - 1‖ ≤ c' * H ^ 2) (hsmall : c' * H ^ 2 ≤ 1 / 2)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hes : ∀ p, S.sub p ≠ s → e p = 0) :
    H ^ 2 / 2 * S.coupled s A e -
        (reactionDiagC a b c ‖opE A‖ ‖opE (S.blk s A)‖ H + 2 * c' * b) * H ^ 3 ≤
      -(⟪e, opE D (opE U e)⟫ - ⟪e, opE U e⟫) -
        ‖opE D - 1‖ / (1 - ‖opE D - 1‖) * ‖opE D (opE U e) - e‖ := by
  have h1 := h.reaction_quadratic hskew hnp hFs he hes
  rw [S.inner_osgn_last h.hA hlast hes] at h1
  rw [← opE_mul_apply, hD]
  have h3 := inner_opE_sub S.X U e e
  have h4 : ‖opE S.X e - e‖ ≤ b * H := by
    have e1 : opE S.X e - e = opE (S.X - 1) e := by
      rw [opE_sub, opE_one]
      simp
    have h5 := (opE (S.X - 1)).le_opNorm e
    rw [he, mul_one] at h5
    rw [e1]
    exact h5.trans h.hb
  have h5 := div_one_sub_le_two_mul (norm_nonneg (opE D - 1)) hα hsmall
  have h6 := mul_le_mul h5 h4 (norm_nonneg _)
    (by linarith [norm_nonneg (opE D - 1)] : (0 : ℝ) ≤ 2 * (c' * H ^ 2))
  have h7 := (abs_le.1 h1).2
  linarith

/-- **Damping of a subsystem that runs after all of its partners** (after Theorem 6.2, with its
remainder). `D * U = X`, `‖D - 1‖ ≤ c' H² ≤ ½`, partner weights only for `s`, every partner of
`s` runs before `s`, `e` a unit vector supported on `s`:
`½H² Σ_k |A_{ks} e|² - (C_d + 2 c' b) H³ ≤ ‖D⁻¹‖ - 1`, and `‖D⁻¹‖ = 1 / s₋` for the smallest
singular value `s₋` of the defect. -/
theorem Consistent.damping_last {A U D : Matrix (Fin n) (Fin n) ℝ} {H a b c c' : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    (hlast : ∀ k, S.partner k s → S.stage k < S.stage s) (hD : D * U = S.X)
    (hα : ‖opE D - 1‖ ≤ c' * H ^ 2) (hsmall : c' * H ^ 2 ≤ 1 / 2)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hes : ∀ p, S.sub p ≠ s → e p = 0) :
    H ^ 2 / 2 * S.coupled s A e -
        (reactionDiagC a b c ‖opE A‖ ‖opE (S.blk s A)‖ H + 2 * c' * b) * H ^ 3 ≤
      ‖Ring.inverse (opE D)‖ - 1 :=
  (h.damping_aux hskew hnp hFs hlast hD hα hsmall he hes).trans
    (diag_gain_inverse (opE D) (opE U) (by linarith) he)

/-- **The smallest singular value under a subsystem that runs last.** In the setting of
`Consistent.damping_last`, every `σ > 0` with `σ ‖v‖ ≤ ‖D v‖` for all `v` (in particular the
smallest singular value of the defect) satisfies `σ (1 + y) ≤ 1`,
`y = ½H² Σ_k |A_{ks} e|² - (C_d + 2 c' b) H³`. -/
theorem Consistent.smin_last {A U D : Matrix (Fin n) (Fin n) ℝ} {H a b c c' : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    (hlast : ∀ k, S.partner k s → S.stage k < S.stage s) (hD : D * U = S.X)
    (hα : ‖opE D - 1‖ ≤ c' * H ^ 2) (hsmall : c' * H ^ 2 ≤ 1 / 2)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hes : ∀ p, S.sub p ≠ s → e p = 0) {σ : ℝ}
    (hσ : 0 < σ) (hσD : ∀ v, σ * ‖v‖ ≤ ‖opE D v‖) :
    σ * (1 + (H ^ 2 / 2 * S.coupled s A e -
      (reactionDiagC a b c ‖opE A‖ ‖opE (S.blk s A)‖ H + 2 * c' * b) * H ^ 3)) ≤ 1 := by
  have h1 := (h.damping_aux hskew hnp hFs hlast hD hα hsmall he hes).trans
    (diag_gain_smin_complete (opE D) (opE U) (by linarith) he hσ hσD)
  have h2 : σ * (1 / σ) = 1 := mul_one_div_cancel hσ.ne'
  have h3 := mul_le_mul_of_nonneg_left (by linarith : 1 + (H ^ 2 / 2 * S.coupled s A e -
    (reactionDiagC a b c ‖opE A‖ ‖opE (S.blk s A)‖ H + 2 * c' * b) * H ^ 3) ≤ 1 / σ) hσ.le
  rwa [h2] at h3

/-- **`s₋ ≤ 1 - ½H² Σ_k |A_{ks} e|² + O(H³)`, explicitly.** In the setting of
`Consistent.smin_last`, if `y = ½H² Σ_k |A_{ks} e|² - (C_d + 2 c' b) H³ ≥ 0`, then
`σ ≤ 1 - y + y²`. -/
theorem Consistent.smin_last_le {A U D : Matrix (Fin n) (Fin n) ℝ} {H a b c c' : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    (hlast : ∀ k, S.partner k s → S.stage k < S.stage s) (hD : D * U = S.X)
    (hα : ‖opE D - 1‖ ≤ c' * H ^ 2) (hsmall : c' * H ^ 2 ≤ 1 / 2)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hes : ∀ p, S.sub p ≠ s → e p = 0) {σ : ℝ}
    (hσ : 0 < σ) (hσD : ∀ v, σ * ‖v‖ ≤ ‖opE D v‖) {y : ℝ}
    (hy : y = H ^ 2 / 2 * S.coupled s A e -
      (reactionDiagC a b c ‖opE A‖ ‖opE (S.blk s A)‖ H + 2 * c' * b) * H ^ 3) (hy0 : 0 ≤ y) :
    σ ≤ 1 - y + y ^ 2 := by
  have h1 := h.smin_last hskew hnp hFs hlast hD hα hsmall he hes hσ hσD
  rw [← hy] at h1
  have h2 : σ * (1 + y) ≤ (1 - y + y ^ 2) * (1 + y) := by
    have h3 : (1 - y + y ^ 2) * (1 + y) = 1 + y ^ 3 := by ring
    rw [h3]
    linarith [pow_nonneg hy0 3]
  exact le_of_mul_le_mul_right h2 (by linarith)

omit [DecidableEq κ] in
/-- **A subsystem that receives no new sample** (Theorem 6.2, last statement): if no partner of
`s` runs before `s` (and `s` is not its own partner), the diagonal block of the one-step map is
the local map, `Π_s X Π_sᵀ = F_s`, exactly. -/
theorem inner_X_eq_inner_F_of_first {s : κ} (hnp : ¬ S.partner s s)
    (hfirst : ∀ k, S.partner s k → ¬ S.stage k < S.stage s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    ⟪x, opE S.X y⟫ = ⟪x, opE S.F y⟫ := by
  refine inner_opE_congr hx hy fun p q hp hq => ?_
  have h0 := congrFun (congrFun S.hX p) q
  rw [Matrix.add_apply, Matrix.add_apply] at h0
  have hM : S.M p q = 0 := S.hM p q fun h => by
    have h1 := h.1
    rw [hp, hq] at h1
    exact hnp h1
  have hN : (S.N * S.X) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    have hr : S.N p r = 0 := S.hN p r fun h => by
      have h1 := h.1
      have h2 := h.2
      rw [hp] at h1 h2
      exact hfirst _ h1 h2
    rw [hr, zero_mul]
  rw [h0, hM, hN, add_zero, add_zero]

/-- **The quadratic form for a subsystem that runs first, exactly** (Theorem 6.2, last
statement): with partner weights only, `g_s(e) = ⟪e, (e^{H A_s} - U) e⟫`. -/
theorem inner_step_error_of_first {A U : Matrix (Fin n) (Fin n) ℝ} {H : ℝ} {s : κ}
    (hnp : ¬ S.partner s s) (hfirst : ∀ k, S.partner s k → ¬ S.stage k < S.stage s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    {e : EuclideanSpace ℝ (Fin n)} (hes : ∀ p, S.sub p ≠ s → e p = 0) :
    ⟪e, opE (S.X - U) e⟫ = ⟪e, opE (NormedSpace.exp (H • S.blk s A) - U) e⟫ := by
  rw [inner_opE_sub, inner_opE_sub, inner_X_eq_inner_F_of_first hnp hfirst hes hes,
    inner_opE_congr hes hes hFs]

end HeldScheme

end CoSimFoundations
