/-
The leading value of the visibility bound (the paper, Theorem `thm:memory` (i), eq.
`eq:leading`, and eq. `eq:vbound`): the conditional form for `l` held samples, and one held
sample of the old instant in full.

**Paper.** With `l` held samples, if the maps `Π_i` and `C_j A^p` (`j` a partner of `i`,
`p < l`) are independent,

  `min ‖𝒯_i‖ = f_i = H^{l+1} ‖D|𝒱_i^0‖ + O(H^{l+2})`,   `D = Σ_j γ_l^{σ_ij} A_ij Π_j A^l`.

The first equality is `isLeast_visBound` of `VisibilityExact` (`f_i = visBound`); this file is
about the second.

**Conditional form** (`leading_value_of_kernel`), for every `l` and every order of execution.
`f = visBound Pr U S` for any family `S` of sample maps, `𝒱^0 = unseen Pr C A l`. Assumed:
* the states not shown are the kernel of a map `N`, `notShown Pr S = ker N`, and `𝒱^0 = ker N₀`;
* `N₀` has a bounded right inverse `R` (independence of the maps stacked in `N₀`);
* `‖N - N₀‖ ≤ c₁ H` and `c₁ H ‖R‖ ≤ 1/2`;
* on the states not shown the block row is `H^{l+1} D` up to `c₂ H^{l+2}`:
  `‖Pr (U v) - H^{l+1} D v‖ ≤ c₂ H^{l+2} ‖v‖`.
Conclusion: `|f - H^{l+1} ‖D|𝒱^0‖| ≤ (c₂ + 4 ‖R‖ c₁ ‖D‖) H^{l+2}`.
Proof: the last hypothesis gives `|f - H^{l+1} ‖D|ker N‖| ≤ c₂ H^{l+2}`, and
`abs_restrNorm_ker_sub_le` of `KernelPerturbation` gives
`|‖D|ker N‖ - ‖D|ker N₀‖| ≤ 2 ‖R‖ c₁ H ‖D‖ / (1 - c₁ H ‖R‖) ≤ 4 ‖R‖ c₁ H ‖D‖`.
The hypotheses are discharged for the samples of a scheme in `LeadingValueScheme`.

**One held sample of the old instant, in full** (`visBound_old_one`, paper eq. `eq:vbound`).
Setting of `MemoryLead`: `P ∘ A = Ai ∘ P + L ∘ C`, `‖P‖ ≤ 1`, `C` the stack of the outputs of the
partners, all of whose samples are those of `t_k`. Then the states not shown are
`𝒱 = {P v = 0, C v = 0} = unseen P C A 1` for every `H`, and

  `|f - (H²/2) ‖P A²|𝒱‖| ≤ Σ_{p≥3} (H ‖A‖)^p / p! ≤ (e - 5/2) ‖A‖³ H³`   (the last for `H ‖A‖ ≤ 1`).

No independence is needed here because the states not shown do not depend on `H`.
-/
import CoSimFoundations.KernelPerturbation
import CoSimFoundations.VisibilityExact
import CoSimFoundations.RunOrderLead

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Conditional

variable {E Ei G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Ei] [NormedSpace ℝ Ei] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ k, NormedAddCommGroup (Y k)]
  [∀ k, NormedSpace ℝ (Y k)]

/-- The visibility bound is the norm of the block row restricted to the states not shown. -/
theorem visBound_eq_restrNorm (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (S : ∀ k, E →L[ℝ] Y k) :
    visBound Pr U S = restrNorm (Pr ∘L U) (notShown Pr S) :=
  rfl

/-- **The leading value of the visibility bound, conditional form** (the paper, Theorem
`thm:memory` (i), eq. `eq:leading`; every `l`, every order of execution). If the states not shown
are the kernel of a map `N` within `c₁ H` of a map `N₀` with right inverse `R` and kernel
`𝒱^0 = unseen Pr C A l`, `c₁ H ‖R‖ ≤ 1/2`, and the block row is `H^{l+1} D` up to
`c₂ H^{l+2} ‖v‖` on the states not shown, then

  `|f - H^{l+1} ‖D|𝒱^0‖| ≤ (c₂ + 4 ‖R‖ c₁ ‖D‖) H^{l+2}`.

The four hypotheses `hker`, `hker₀`, `hN`, `hdef` are assumptions of this statement. -/
theorem leading_value_of_kernel (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (S : ∀ k, E →L[ℝ] Y k)
    (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) (D : E →L[ℝ] Ei) {N N₀ : E →L[ℝ] W}
    {R : W →L[ℝ] E} {H c₁ c₂ : ℝ} (hH : 0 ≤ H) (hc₂ : 0 ≤ c₂)
    (hker : notShown Pr S = LinearMap.ker (N : E →ₗ[ℝ] W))
    (hker₀ : unseen Pr C A l = LinearMap.ker (N₀ : E →ₗ[ℝ] W))
    (hR : N₀ ∘L R = ContinuousLinearMap.id ℝ W) (hN : ‖N - N₀‖ ≤ c₁ * H)
    (hsmall : c₁ * H * ‖R‖ ≤ 1 / 2)
    (hdef : ∀ v ∈ notShown Pr S, ‖Pr (U v) - H ^ (l + 1) • D v‖ ≤ c₂ * H ^ (l + 2) * ‖v‖) :
    |visBound Pr U S - H ^ (l + 1) * restrNorm D (unseen Pr C A l)| ≤
      (c₂ + 4 * ‖R‖ * c₁ * ‖D‖) * H ^ (l + 2) := by
  have hHl : 0 ≤ H ^ (l + 1) := pow_nonneg hH _
  have h1 : |restrNorm (Pr ∘L U) (notShown Pr S) -
      restrNorm (H ^ (l + 1) • D) (notShown Pr S)| ≤ c₂ * H ^ (l + 2) :=
    abs_restrNorm_sub_le _ _ _ (mul_nonneg hc₂ (pow_nonneg hH _)) fun v hv => by
      simpa using hdef v hv
  rw [restrNorm_smul D _ hHl, ← visBound_eq_restrNorm] at h1
  have hε : c₁ * H * ‖R‖ < 1 := by linarith
  have h2 := abs_restrNorm_ker_sub_le hR hN hε D
  rw [← hker, ← hker₀] at h2
  have hε0 : 0 ≤ c₁ * H := (norm_nonneg _).trans hN
  have hnum : 0 ≤ 2 * ‖R‖ * (c₁ * H) * ‖D‖ := by positivity
  have h3 : 2 * ‖R‖ * (c₁ * H) * ‖D‖ / (1 - c₁ * H * ‖R‖) ≤ 4 * ‖R‖ * c₁ * ‖D‖ * H := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h4 : |restrNorm D (notShown Pr S) - restrNorm D (unseen Pr C A l)| ≤
      4 * ‖R‖ * c₁ * ‖D‖ * H := h2.trans h3
  have h5 : |H ^ (l + 1) * restrNorm D (notShown Pr S) -
      H ^ (l + 1) * restrNorm D (unseen Pr C A l)| ≤ H ^ (l + 1) * (4 * ‖R‖ * c₁ * ‖D‖ * H) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hHl]
    exact mul_le_mul_of_nonneg_left h4 hHl
  have h6 := abs_sub_le (visBound Pr U S) (H ^ (l + 1) * restrNorm D (notShown Pr S))
    (H ^ (l + 1) * restrNorm D (unseen Pr C A l))
  have h7 : (c₂ + 4 * ‖R‖ * c₁ * ‖D‖) * H ^ (l + 2) =
      c₂ * H ^ (l + 2) + H ^ (l + 1) * (4 * ‖R‖ * c₁ * ‖D‖ * H) := by ring
  rw [h7]
  linarith

end Conditional

section OldOne

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- `c_i` is the norm of `P A^{l+1}` restricted to the states not shown up to the order `l`. -/
theorem unseenRate_eq_restrNorm (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) :
    unseenRate P C A l = restrNorm (P ∘L (A ^ (l + 1))) (unseen P C A l) :=
  rfl

/-- With one held sample of the old instant the states not shown are those not shown up to the
order one, for every macro step: `{P v = 0, C v = 0}`. -/
theorem notShown_old_one (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) :
    notShown P (fun _ : Unit => C) = unseen P C A 1 := by
  ext v
  rw [mem_notShown, mem_unseen]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun q hq => ?_⟩
    obtain rfl : q = 0 := by omega
    simpa using h2 ()
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ => by simpa using h2 0 one_pos⟩

/-- **The visibility bound for one held sample of the old instant** (the paper, eq. `eq:vbound`,
and Theorem `thm:memory` (i) for `l = 1`, `σ = 0`): for a subsystem with
`P ∘ A = Ai ∘ P + L ∘ C` that is shown the old samples `C v` of its partners,

  `|f - (H²/2) c_i| ≤ Σ_{p≥3} (H ‖A‖)^p / p!`,   `c_i = ‖P A²|{P v = 0, C v = 0}‖`.

No hypothesis of independence: the states not shown do not depend on `H`. -/
theorem visBound_old_one (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) {H : ℝ}
    (hH : 0 ≤ H) :
    |visBound P (exp (H • A)) (fun _ : Unit => C) - H ^ 2 / 2 * unseenRate P C A 1| ≤
      expTail 3 (H * ‖A‖) := by
  have h1 : |restrNorm (P ∘L exp (H • A)) (unseen P C A 1) -
      restrNorm ((H ^ 2 / 2) • (P ∘L (A ^ 2))) (unseen P C A 1)| ≤ expTail 3 (H * ‖A‖) := by
    refine abs_restrNorm_sub_le _ _ _ (expTail_nonneg _ (mul_nonneg hH (norm_nonneg A)))
      fun v hv => ?_
    obtain ⟨ρ, h2, h3⟩ := exists_proj_exp_apply_eq hA hP hH hv
    have h4 : (P ∘L exp (H • A)) v - ((H ^ 2 / 2) • (P ∘L (A ^ 2))) v = ρ := by
      simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply]
      rw [h2]
      norm_num [Nat.factorial]
    rw [h4]
    exact h3
  rw [restrNorm_smul _ _ (by positivity)] at h1
  rw [visBound_eq_restrNorm, notShown_old_one P C A, unseenRate_eq_restrNorm]
  exact h1

/-- **The same with the remainder in the paper's form:** for `H ‖A‖ ≤ 1`,
`|f - (H²/2) c_i| ≤ (e - 5/2) ‖A‖³ H³`. -/
theorem visBound_old_one_cubic (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) {H : ℝ}
    (hH : 0 ≤ H) (hHA : H * ‖A‖ ≤ 1) :
    |visBound P (exp (H • A)) (fun _ : Unit => C) - H ^ 2 / 2 * unseenRate P C A 1| ≤
      (Real.exp 1 - 5 / 2) * ‖A‖ ^ 3 * H ^ 3 := by
  refine (visBound_old_one hA hP hH).trans ?_
  have h := expTail_mul_le 3 (y := 1) zero_le_one (mul_nonneg hH (norm_nonneg A)) hHA
  rw [one_mul, expTail_three_one] at h
  refine h.trans (le_of_eq ?_)
  ring

end OldOne

end CoSimFoundations
