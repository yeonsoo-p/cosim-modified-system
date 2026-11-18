/-
The leading defect of a rule with `l` held samples, all old.

**Setting**, that of `MemoryLead.lean` and `MemoryReached.lean`: `P = Π_i : E → F`, `C : E → G`
the stack of the outputs of the partners of `i`, `P ∘ A = Ai ∘ P + L ∘ C`, `U = exp (H • A)`,
`𝒱^0 = unseen P C A l` the states not shown up to the order `l`, and the local defect
`𝒯 = P U - Fi P - Σ_r g r C U^{-r}` (`localDefect`, `nodeDefect`).

**Step 1, the forced part** (`forced_defect_apply`, all samples old). For a
rule with bounded weights `‖g r ∘ C‖ ≤ w H` (`1 ≤ r < l`) and `H ‖A‖ ≤ 1`, on `𝒱^0`

  `‖𝒯 v - γ_l H^{l+1} P A^{l+1} v‖ ≤ (b_l H ‖A‖ ‖𝒯‖ + (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2})`
  `· ‖v‖`,

the constants of `memory_lead`. So a rule with `‖𝒯‖ ≤ M H^{l+1}` has on `𝒱^0` the forced leading
defect `γ_l a_i A^l` up to `O(H^{l+2})`. This strengthens `memory_lead` (which bounds `‖𝒯‖` from
below) and is derived from the same relations: the key step as an identity up to its remainder
(`key_step_apply`), its shifts to the order `l` (`key_step_shift`) and the identity of the top
moment (`gamma_identity`).

**Step 5, every allowed leading defect is reached** (`exists_rule_nodeDefect_lead`). For any set
`S` of `l ≥ 1` sample ages and any row `Zr` that vanishes on `𝒱^0` there is a rule with bounded
weights (`‖Fi - 1‖, ‖g r ∘ C‖ ≤ w H`) and `‖𝒯 - H^{l+1} (γ_S L C A^l + Zr)‖ ≤ K H^{l+2}`: the rule
of `MemoryReached` (`norm_reach_defect_sub_le`: its defect is `γ_S H^{l+1} L C A^l Q₀ + O(H^{l+2})`)
lowered by `H^{l+1} Z ΛF` on the own state and by `H^{l+1} Z Λ_p` on the divided differences
(`addRule`, `addRule_apply`), with `Z = Zr + γ_S L C A^l (1 - Q₀)`.
-/
import CoSimFoundations.OrderReached

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations


/-! ### Step 1: the forced part of the defect on the hidden states (all samples old) -/

section Forced

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- **Step 1 of the proof of `memory_lead` as an identity up to the remainder.** On the states
not shown up to the order `m`, the local defect is the negative of the deviation of the `m`-th
moment from its Adams value, up to `e_m`:
`‖𝒯 v + (H^m ν_m A^m v - H^{m+1}/(m+1)! P A^{m+1} v)‖ ≤ e_m ‖v‖`, if the coefficients of the
past samples are at most `w H`. -/
theorem key_step_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) {l : ℕ}
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) {m : ℕ} {v : E}
    (hv : v ∈ unseen P C A m) :
    ‖localDefect P Fi g C A H l v + (H ^ m • moment g C l m ((A ^ m) v) -
        (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v))‖ ≤
      memE l m w H (H * ‖A‖) * ‖v‖ := by
  obtain ⟨ρ0, h0, hρ0⟩ := exists_proj_exp_apply_eq hA hP hH hv
  choose ρ h1 hρ using fun r : ℕ => exists_sample_apply_eq (g r) hH hv r
  obtain ⟨hPv, -⟩ := mem_unseen.1 hv
  have hT : localDefect P Fi g C A H l v =
      (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v) + ρ0 -
        H ^ m • moment g C l m ((A ^ m) v) - ∑ r ∈ range l, ρ r := by
    simp only [localDefect, _root_.sub_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]
    rw [h0, hPv, map_zero, sub_zero, sum_congr rfl fun r _ => h1 r, sum_add_distrib, moment,
      smul_sum]
    simp only [smul_smul]
    abel_nf
  have hkey : localDefect P Fi g C A H l v + (H ^ m • moment g C l m ((A ^ m) v) -
      (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v)) = ρ0 - ∑ r ∈ range l, ρ r := by
    rw [hT]
    abel
  rw [hkey]
  have hsum : ‖∑ r ∈ range l, ρ r‖ ≤
      ∑ r ∈ range l, w * H * (expTail (m + 1) (r * (H * ‖A‖)) * ‖v‖) := by
    refine norm_sum_le_of_le _ fun r hr => (hρ r).trans ?_
    rcases Nat.eq_zero_or_pos r with rfl | h0
    · simp [expTail_zero]
    · exact mul_le_mul_of_nonneg_right (hw r h0 (mem_range.1 hr))
        (mul_nonneg (expTail_nonneg _ (by positivity)) (norm_nonneg _))
  have h5 : ∑ r ∈ range l, w * H * (expTail (m + 1) (r * (H * ‖A‖)) * ‖v‖) =
      w * H * (∑ r ∈ range l, expTail (m + 1) (r * (H * ‖A‖))) * ‖v‖ := by
    rw [mul_sum, sum_mul]
    exact sum_congr rfl fun r _ => by ring
  rw [h5] at hsum
  have h3 := norm_sub_le ρ0 (∑ r ∈ range l, ρ r)
  unfold memE
  linarith

/-- **All samples old: the defect on the hidden states is forced.**
Let subsystem `i` run before all of its partners with `l ≥ 1` held samples and bounded weights
`‖g r ∘ C‖ ≤ w H` (`1 ≤ r < l`), `H ‖A‖ ≤ 1`. For every state `v` not shown up to the order `l`,
`‖𝒯 v - γ_l H^{l+1} P A^{l+1} v‖ ≤ (b_l H ‖A‖ ‖𝒯‖ + (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2}) ‖v‖`
with the constants of `memory_lead`. With `‖𝒯‖ ≤ M H^{l+1}` the right side is of the order
`H^{l+2}`: the restriction of the defect to `𝒱_i^0` is within `O(H^{l+2})` of the forced one
`γ_l H^{l+1} a_i A^l`. -/
theorem forced_defect_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) (hx1 : H * ‖A‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) {v : E}
    (hv : v ∈ unseen P C A l) :
    ‖localDefect P Fi g C A H l v - (adamsGamma l * H ^ (l + 1)) • P ((A ^ (l + 1)) v)‖ ≤
      (memB l * (H * ‖A‖) * ‖localDefect P Fi g C A H l‖ +
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2)) * ‖v‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  set t := ‖localDefect P Fi g C A H l‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hkl := key_step_apply hA hP Fi g hH hw hv
  have hkm : ∀ m ∈ Ico 1 l,
      ‖H ^ l • moment g C l m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v)‖ ≤
      (H * ‖A‖) ^ (l - m) * (t + memE l m w H (H * ‖A‖)) * ‖v‖ :=
    fun m hm => key_step_shift hA hH (mem_Ico.1 hm).2 (moment g C l m)
      (add_nonneg ht0 (memE_nonneg l m hw0 hH hx0))
      (fun _ hu => memory_key_step hA hP Fi g hH hw hu) hv
  have hid := gamma_identity g C hl H ((A ^ l) v) (P ((A ^ (l + 1)) v))
  set X : ℕ → F := fun m => H ^ l • moment g C l m ((A ^ l) v) -
    (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v) with hX
  have e : localDefect P Fi g C A H l v - (adamsGamma l * H ^ (l + 1)) • P ((A ^ (l + 1)) v) =
      (localDefect P Fi g C A H l v + X l) +
        ∑ m ∈ Ico 1 l, (adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)) • X m := by
    rw [hid]
    simp only [hX]
    abel
  rw [e]
  have hsum : ‖∑ m ∈ Ico 1 l, (adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)) • X m‖ ≤
      ∑ m ∈ Ico 1 l, memBeta l m * ((H * ‖A‖) ^ (l - m) *
        (t + memE l m w H (H * ‖A‖)) * ‖v‖) := by
    refine norm_sum_le_of_le _ fun m hm => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_adamsCoeff_mul_div]
    exact mul_le_mul_of_nonneg_left (hkm m hm) (memBeta_nonneg l m)
  have hsumeq : ∑ m ∈ Ico 1 l, memBeta l m * ((H * ‖A‖) ^ (l - m) *
        (t + memE l m w H (H * ‖A‖)) * ‖v‖) =
      ((∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m)) * t +
        ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) * memE l m w H (H * ‖A‖)) * ‖v‖ := by
    simp only [add_mul, sum_mul]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hsumeq] at hsum
  have harith := lead_of_bounded_arith (Ico 1 l) (fun m hm => (mem_Ico.1 hm).2) (memBeta l)
    (fun m => memE l m w H (H * ‖A‖)) (fun m => expTail (m + 2) 1)
    (fun m => ∑ r ∈ range l, expTail (m + 1) r) (memBeta_nonneg l) hx0 hx1 ht0
    fun m => memE_le l m hw0 hH hx0 hx1
  have h2 := norm_add_le (localDefect P Fi g C A H l v + X l)
    (∑ m ∈ Ico 1 l, (adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)) • X m)
  have hv0 := norm_nonneg v
  have h3 : (memE l l w H (H * ‖A‖) +
      ((∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m)) * t +
        ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) * memE l m w H (H * ‖A‖))) ≤
      memB l * (H * ‖A‖) * t +
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) := by
    unfold memB memC1 memC2
    linarith
  have h4 := mul_le_mul_of_nonneg_right h3 hv0
  have hX' : ‖localDefect P Fi g C A H l v + X l‖ ≤ memE l l w H (H * ‖A‖) * ‖v‖ := hkl
  nlinarith

end Forced

/-! ### A rule with any leading defect that the class allows -/

section Rule

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Lowering the coefficients by `ΔF` and `Δg r` raises the defect by `ΔF P + Σ_r Δg r C U^{-r}`. -/
theorem nodeDefect_sub (P : E →L[ℝ] F) (Fi ΔF : F →L[ℝ] F) (g Δg : ℤ → G →L[ℝ] F)
    (C : E →L[ℝ] G) (A : E →L[ℝ] E) (H : ℝ) (S : Finset ℤ) :
    nodeDefect P (Fi - ΔF) (fun r => g r - Δg r) C A H S =
      nodeDefect P Fi g C A H S + ΔF ∘L P +
        ∑ r ∈ S, (Δg r ∘L C) ∘L exp ((-((r : ℝ) * H)) • A) := by
  unfold nodeDefect
  simp only [ContinuousLinearMap.sub_comp, sum_sub_distrib]
  abel

end Rule

section RuleLead

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- The added coefficient of the samples, `Δg r = Σ_{p<l} δ p r p! H^{l+1-p} Z Λ_p`: `H^{l+1}`
times `Z Λ_p` applied to the divided difference of order `p`. -/
noncomputable def addRule (δ : ℕ → ℤ → ℝ) (Z : E →L[ℝ] F) (Λ : ℕ → G →L[ℝ] E) (H : ℝ) (l : ℕ)
    (r : ℤ) : G →L[ℝ] F :=
  ∑ p ∈ range l, δ p r • (((p ! : ℝ) * H ^ (l + 1 - p)) • (Z ∘L Λ p))

/-- The constant of the added coefficient: `Σ_{p<l} |δ p r| p! ‖Z Λ_p‖`. -/
noncomputable def addConst (δ : ℕ → ℤ → ℝ) (Z : E →L[ℝ] F) (Λ : ℕ → G →L[ℝ] E) (l : ℕ)
    (r : ℤ) : ℝ :=
  ∑ p ∈ range l, |δ p r| * ((p ! : ℝ) * ‖Z ∘L Λ p‖)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem addConst_nonneg (δ : ℕ → ℤ → ℝ) (Z : E →L[ℝ] F) (Λ : ℕ → G →L[ℝ] E) (l : ℕ) (r : ℤ) :
    0 ≤ addConst δ Z Λ l r :=
  sum_nonneg fun p _ => by positivity

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- `‖Δg r‖ ≤ H² Σ_p |δ p r| p! ‖Z Λ_p‖` for `0 ≤ H ≤ 1`. -/
theorem norm_addRule_le (δ : ℕ → ℤ → ℝ) (Z : E →L[ℝ] F) (Λ : ℕ → G →L[ℝ] E) {H : ℝ}
    (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (l : ℕ) (r : ℤ) :
    ‖addRule δ Z Λ H l r‖ ≤ H * (H * addConst δ Z Λ l r) := by
  have e : H * (H * addConst δ Z Λ l r) =
      ∑ p ∈ range l, |δ p r| * ((p ! : ℝ) * H ^ 2 * ‖Z ∘L Λ p‖) := by
    rw [addConst, mul_sum, mul_sum]
    exact sum_congr rfl fun p _ => by ring
  rw [e]
  refine norm_sum_le_of_le _ fun p hp => ?_
  rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h2 : H ^ (l + 1 - p) ≤ H ^ 2 :=
    pow_le_pow_of_le_one hH0 hH1 (by have := mem_range.1 hp; omega)
  gcongr

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- **The added part of the defect.** If `ΛF (P v) + Σ_{p<l} Λ p (C A^p v) = v - Q₀ v` and `Z`
vanishes on the states not shown, the added coefficients `H^{l+1} Z ΛF` and `Δg` raise the
defect by `H^{l+1} Z v` up to the remainders of the samples. -/
theorem addRule_apply [CompleteSpace E] {S : Finset ℤ} {δ : ℕ → ℤ → ℝ}
    (hδ : ∀ p < S.card, ∀ n < S.card,
      ∑ r ∈ S, δ p r * (-(r : ℝ)) ^ n = if p = n then 1 else 0)
    {ΛF : F →L[ℝ] E} {Λ : ℕ → G →L[ℝ] E}
    (hΛ : ∀ v : E, ΛF (P v) + ∑ p ∈ range S.card, Λ p (C ((A ^ p) v)) =
      v - (unseen P C A S.card).starProjection v)
    {Z : E →L[ℝ] F} (hZ : ∀ u ∈ unseen P C A S.card, Z u = 0) (H : ℝ) (v : E) :
    (H ^ (S.card + 1) • (Z ∘L ΛF)) (P v) +
        ∑ r ∈ S, addRule δ Z Λ H S.card r (C (exp ((-((r : ℝ) * H)) • A) v)) =
      H ^ (S.card + 1) • Z v +
        ∑ r ∈ S, addRule δ Z Λ H S.card r (C (expRem S.card ((-(r : ℝ) * H) • A) v)) := by
  set l := S.card with hl
  set X : ℕ → G →L[ℝ] F := fun p => ((p ! : ℝ) * H ^ (l + 1 - p)) • (Z ∘L Λ p) with hX
  have hmom : ∀ n ∈ range l, ∑ r ∈ S, (-(r : ℝ)) ^ n • addRule δ Z Λ H l r = X n :=
    fun n hn => sum_neg_pow_smul_weights hδ X (mem_range.1 hn)
  rw [sum_coef_sample_apply A C S (addRule δ Z Λ H l) H l v]
  have h2 : ∑ n ∈ range l, ((n ! : ℝ)⁻¹ * H ^ n) • (∑ r ∈ S, (-(r : ℝ)) ^ n • addRule δ Z Λ H l r)
      (C ((A ^ n) v)) = H ^ (l + 1) • ∑ n ∈ range l, Z (Λ n (C ((A ^ n) v))) := by
    rw [smul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [hmom n hn, hX]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_smul]
    congr 1
    have hn' := mem_range.1 hn
    have hf : (n ! : ℝ) ≠ 0 := by positivity
    have e : H ^ n * H ^ (l + 1 - n) = H ^ (l + 1) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    field_simp
    rw [← e]
  have h3 : Z (ΛF (P v)) + ∑ n ∈ range l, Z (Λ n (C ((A ^ n) v))) = Z v := by
    rw [← map_sum, ← map_add, hΛ v, map_sub, hZ _ (Submodule.starProjection_apply_mem _ v),
      sub_zero]
  rw [h2]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply]
  rw [← h3, smul_add]
  abel

/-- The constant of the remainders of the rule of `MemoryReached`. -/
noncomputable def reachRemConst (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (S : Finset ℤ)
    (δ : ℕ → ℤ → ℝ) (κ : ℕ → ℝ) : ℝ :=
  ‖P‖ * expTail (S.card + 2) 1 * ‖A‖ ^ (S.card + 2) +
    ∑ p ∈ range S.card, |nodeCoeff S p| * (κ p * (‖C‖ * ‖A‖ ^ S.card)) +
    ∑ r ∈ S, (∑ p ∈ range S.card, |δ p r| * κ p) * ‖C‖ *
      (‖A‖ ^ (S.card + 1) * expTail (S.card + 1) |(r : ℝ)|)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem reachRemConst_nonneg (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (S : Finset ℤ)
    (δ : ℕ → ℤ → ℝ) {κ : ℕ → ℝ} (hκ : ∀ p, 0 ≤ κ p) : 0 ≤ reachRemConst P C A S δ κ := by
  unfold reachRemConst
  have hε := expTail_nonneg (S.card + 2) (zero_le_one : (0 : ℝ) ≤ 1)
  have h1 : 0 ≤ ∑ p ∈ range S.card, |nodeCoeff S p| * (κ p * (‖C‖ * ‖A‖ ^ S.card)) :=
    sum_nonneg fun p _ => by
      have := hκ p
      positivity
  have h2 : 0 ≤ ∑ r ∈ S, (∑ p ∈ range S.card, |δ p r| * κ p) * ‖C‖ *
      (‖A‖ ^ (S.card + 1) * expTail (S.card + 1) |(r : ℝ)|) :=
    sum_nonneg fun r _ => by
      have : 0 ≤ ∑ p ∈ range S.card, |δ p r| * κ p :=
        sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (hκ p)
      have := expTail_nonneg (S.card + 1) (abs_nonneg (r : ℝ))
      positivity
  positivity

/-- **The rule of `MemoryReached` has the leading defect `γ_S L C A^l Q₀`** (with the
remainder made explicit): `‖𝒯 v - γ_S H^{l+1} L C A^l Q₀ v‖ ≤ K H^{l+2} ‖v‖`. -/
theorem norm_reach_defect_sub_le [CompleteSpace E] (hA : P ∘L A = Ai ∘L P + L ∘L C)
    {S : Finset ℤ} {δ : ℕ → ℤ → ℝ}
    (hδ : ∀ p < S.card, ∀ n < S.card,
      ∑ r ∈ S, δ p r * (-(r : ℝ)) ^ n = if p = n then 1 else 0)
    {ΛF : F →L[ℝ] E} {Λ : ℕ → G →L[ℝ] E}
    (hΛ : ∀ v : E, ΛF (P v) + ∑ p ∈ range S.card, Λ p (C ((A ^ p) v)) =
      v - (unseen P C A S.card).starProjection v)
    {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hx1 : H * ‖A‖ ≤ 1) (v : E) :
    ‖nodeDefect P (reachFi Ai ((L ∘L C) ∘L A ^ S.card) ΛF (nodeGamma S) H S.card)
        (reachRule δ Ai L ((L ∘L C) ∘L A ^ S.card) Λ (nodeGamma S) H S.card) C A H S v -
      (nodeGamma S * H ^ (S.card + 1)) •
        L (C ((A ^ S.card) ((unseen P C A S.card).starProjection v)))‖ ≤
      reachRemConst P C A S δ
        (reachConst Ai L ((L ∘L C) ∘L A ^ S.card) Λ (nodeGamma S) S.card) *
        H ^ (S.card + 2) * ‖v‖ := by
  set l := S.card with hl
  set γ := nodeGamma S with hγ
  set M : E →L[ℝ] F := (L ∘L C) ∘L A ^ l with hM
  set κ : ℕ → ℝ := reachConst Ai L M Λ γ l with hκ
  set gc : ℤ → ℝ := fun r => ∑ p ∈ range l, |δ p r| * κ p with hgc
  rw [reach_defect_apply hA rfl hδ hΛ H v]
  have hA' := norm_proj_expRem_apply_le P A hH0 hx1 (by omega : 0 < l + 2) v
  have hB := norm_sum_top_le C A l (nodeCoeff S)
    (fun p => reachMoment Ai L M Λ γ H l p - ((p ! : ℝ) / ((p + 1)! : ℝ) * H) • L) κ hH0
    (fun p hp => norm_reachMoment_sub_le Ai L M Λ γ hH0 hH1 (mem_range.1 hp)) v
  have hC := norm_sum_coef_expRem_le C A S (reachRule δ Ai L M Λ γ H l) gc hH0 hx1
    (fun r _ => norm_reachRule_le δ Ai L M Λ γ hH0 hH1 l r) (by omega : 0 < l + 1) v
  rw [show l + 1 + 1 = l + 2 by omega] at hC
  set R1 := P (expRem (l + 2) (H • A) v)
  set R2 := ∑ p ∈ range l, (nodeCoeff S p * ((l ! : ℝ)⁻¹ * H ^ l)) •
    (reachMoment Ai L M Λ γ H l p - ((p ! : ℝ) / ((p + 1)! : ℝ) * H) • L) (C ((A ^ l) v))
  set R3 := ∑ r ∈ S, reachRule δ Ai L M Λ γ H l r (C (expRem (l + 1) ((-(r : ℝ) * H) • A) v))
  have e : (γ * H ^ (l + 1)) • L (C ((A ^ l) ((unseen P C A l).starProjection v))) + R1 + R2 -
      R3 - (γ * H ^ (l + 1)) • L (C ((A ^ l) ((unseen P C A l).starProjection v))) =
      R1 + R2 - R3 := by abel
  rw [e]
  have h2 := norm_sub_le (R1 + R2) R3
  have h3 := norm_add_le R1 R2
  have e2 : reachRemConst P C A S δ κ * H ^ (l + 2) * ‖v‖ =
      ‖P‖ * expTail (l + 2) 1 * ‖A‖ ^ (l + 2) * H ^ (l + 2) * ‖v‖ +
        H ^ (l + 2) * (∑ p ∈ range l, |nodeCoeff S p| * (κ p * (‖C‖ * ‖A‖ ^ l))) * ‖v‖ +
        H ^ (l + 2) * (∑ r ∈ S, gc r * ‖C‖ * (‖A‖ ^ (l + 1) * expTail (l + 1) |(r : ℝ)|)) *
          ‖v‖ := by
    unfold reachRemConst
    ring
  rw [e2]
  linarith

/-- **Every leading defect that the class allows is reached by a rule with bounded weights**
(with an added row). For a set `S` of `l ≥ 1` sample ages and a row `Zr` that
vanishes on the states not shown up to the order `l`, there are `w, K ≥ 0` such that for every
`0 ≤ H ≤ 1` with `H ‖A‖ ≤ 1` a rule has `‖Fi - 1‖ ≤ w H`, `‖g r ∘ C‖ ≤ w H` for `r ∈ S`, and
`‖𝒯 - H^{l+1} (γ_S L C A^l + Zr)‖ ≤ K H^{l+2}`: its leading defect is the forced one
`γ_S a_i A^l` plus `Zr`. The rule is that of `MemoryReached` plus `H^{l+1}` times a linear
function of the own state and the divided differences of the samples. -/
theorem exists_rule_nodeDefect_lead [CompleteSpace E] (hA : P ∘L A = Ai ∘L P + L ∘L C)
    (S : Finset ℤ) (hS : 1 ≤ S.card) (Zr : E →L[ℝ] F)
    (hZr : ∀ v ∈ unseen P C A S.card, Zr v = 0) :
    ∃ w K : ℝ, 0 ≤ w ∧ 0 ≤ K ∧ ∀ H : ℝ, 0 ≤ H → H ≤ 1 → H * ‖A‖ ≤ 1 →
      ∃ (Fi : F →L[ℝ] F) (g : ℤ → G →L[ℝ] F), ‖Fi - 1‖ ≤ w * H ∧
        (∀ r ∈ S, ‖g r ∘L C‖ ≤ w * H) ∧
        ‖nodeDefect P Fi g C A H S -
            H ^ (S.card + 1) • (nodeGamma S • ((L ∘L C) ∘L A ^ S.card) + Zr)‖ ≤
          K * H ^ (S.card + 2) := by
  obtain ⟨δ, hδ⟩ := exists_nodeWeights S
  obtain ⟨ΛF, Λ, hΛ⟩ := exists_shown_inverse P C A S.card
  set l := S.card with hl
  set γ := nodeGamma S with hγ
  set M : E →L[ℝ] F := (L ∘L C) ∘L A ^ l with hM
  set Q₀ := (unseen P C A l).starProjection with hQ₀
  -- the added row: `Zr` and the shown part of the forced row
  set Z' : E →L[ℝ] F := Zr + γ • (M ∘L (ContinuousLinearMap.id ℝ E - Q₀)) with hZ'
  have hZ'0 : ∀ u ∈ unseen P C A l, Z' u = 0 := by
    intro u hu
    have hQ : Q₀ u = u := (Submodule.starProjection_eq_self_iff).2 hu
    simp [hZ', hZr u hu, hQ]
  set κ : ℕ → ℝ := reachConst Ai L M Λ γ l with hκ
  set gc : ℤ → ℝ := fun r => ∑ p ∈ range l, |δ p r| * κ p with hgc
  have hκ0 : ∀ p, 0 ≤ κ p := fun p => reachConst_nonneg Ai L M Λ γ l p
  have hgc0 : ∀ r, 0 ≤ gc r := fun r =>
    sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (hκ0 p)
  have hgd0 : ∀ r, 0 ≤ addConst δ Z' Λ l r := addConst_nonneg δ Z' Λ l
  set w := ((l : ℝ) + 1) * (1 + ‖Ai‖) ^ (l + 1) + |γ| * ‖M ∘L ΛF‖ + ‖Z' ∘L ΛF‖ +
    ((∑ r ∈ S, gc r) + ∑ r ∈ S, addConst δ Z' Λ l r) * ‖C‖ with hw
  set KD := ∑ r ∈ S, addConst δ Z' Λ l r * ‖C‖ * (‖A‖ ^ l * expTail l |(r : ℝ)|) with hKD
  have hKD0 : 0 ≤ KD := sum_nonneg fun r _ => by
    have := hgd0 r
    have := expTail_nonneg l (abs_nonneg (r : ℝ))
    positivity
  have hR0 := reachRemConst_nonneg P C A S δ hκ0
  have hgcS : 0 ≤ ∑ r ∈ S, gc r := sum_nonneg fun r _ => hgc0 r
  have hgdS : 0 ≤ ∑ r ∈ S, addConst δ Z' Λ l r := sum_nonneg fun r _ => hgd0 r
  have hAi := norm_nonneg Ai
  refine ⟨w, reachRemConst P C A S δ κ + KD, by positivity, by positivity,
    fun H hH0 hH1 hx1 => ⟨reachFi Ai M ΛF γ H l - H ^ (l + 1) • (Z' ∘L ΛF),
      fun r => reachRule δ Ai L M Λ γ H l r - addRule δ Z' Λ H l r, ?_, ?_, ?_⟩⟩
  · -- the coefficient of the own state
    have e : reachFi Ai M ΛF γ H l - H ^ (l + 1) • (Z' ∘L ΛF) - 1 =
        (taylorLocal Ai H l - 1) + ((γ * H ^ (l + 1)) • (M ∘L ΛF) -
          H ^ (l + 1) • (Z' ∘L ΛF)) := by
      rw [reachFi]
      abel
    rw [e]
    have h1 := norm_taylorLocal_sub_one_le Ai hH0 hH1 l
    have h2 : H ^ (l + 1) ≤ H := by
      simpa using pow_le_pow_of_le_one hH0 hH1 (by omega : 1 ≤ l + 1)
    have h3 : ‖(γ * H ^ (l + 1)) • (M ∘L ΛF)‖ ≤ H * (|γ| * ‖M ∘L ΛF‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hH0 _)]
      calc |γ| * H ^ (l + 1) * ‖M ∘L ΛF‖ ≤ |γ| * H * ‖M ∘L ΛF‖ := by gcongr
        _ = H * (|γ| * ‖M ∘L ΛF‖) := by ring
    have h4 : ‖H ^ (l + 1) • (Z' ∘L ΛF)‖ ≤ H * ‖Z' ∘L ΛF‖ := by
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hH0 _)]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h5 := norm_sub_le ((γ * H ^ (l + 1)) • (M ∘L ΛF)) (H ^ (l + 1) • (Z' ∘L ΛF))
    have h6 := norm_add_le (taylorLocal Ai H l - 1)
      ((γ * H ^ (l + 1)) • (M ∘L ΛF) - H ^ (l + 1) • (Z' ∘L ΛF))
    have h7 : 0 ≤ H * (((∑ r ∈ S, gc r) + ∑ r ∈ S, addConst δ Z' Λ l r) * ‖C‖) := by
      positivity
    have e2 : w * H = H * (((l : ℝ) + 1) * (1 + ‖Ai‖) ^ (l + 1)) + H * (|γ| * ‖M ∘L ΛF‖) +
        H * ‖Z' ∘L ΛF‖ + H * (((∑ r ∈ S, gc r) + ∑ r ∈ S, addConst δ Z' Λ l r) * ‖C‖) := by
      rw [hw]
      ring
    rw [e2]
    linarith
  · -- the weights
    intro r hr
    have hg1 := norm_addRule_le δ Z' Λ hH0 hH1 l r
    have h1 := norm_reachRule_le δ Ai L M Λ γ hH0 hH1 l r
    have h2 : gc r ≤ ∑ r ∈ S, gc r := single_le_sum (fun r _ => hgc0 r) hr
    have h3 : addConst δ Z' Λ l r ≤ ∑ r ∈ S, addConst δ Z' Λ l r :=
      single_le_sum (fun r _ => hgd0 r) hr
    have h4 : ‖(reachRule δ Ai L M Λ γ H l r - addRule δ Z' Λ H l r) ∘L C‖ ≤
        (‖reachRule δ Ai L M Λ γ H l r‖ + ‖addRule δ Z' Λ H l r‖) * ‖C‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _))
    have h5 : H * addConst δ Z' Λ l r ≤ ∑ r ∈ S, addConst δ Z' Λ l r :=
      (mul_le_of_le_one_left (hgd0 r) hH1).trans h3
    have h6 : ‖reachRule δ Ai L M Λ γ H l r‖ + ‖addRule δ Z' Λ H l r‖ ≤
        H * ((∑ r ∈ S, gc r) + ∑ r ∈ S, addConst δ Z' Λ l r) := by
      have h7 : H * gc r ≤ H * ∑ r ∈ S, gc r := mul_le_mul_of_nonneg_left h2 hH0
      have h8 : H * (H * addConst δ Z' Λ l r) ≤ H * ∑ r ∈ S, addConst δ Z' Λ l r :=
        mul_le_mul_of_nonneg_left h5 hH0
      have e : H * ((∑ r ∈ S, gc r) + ∑ r ∈ S, addConst δ Z' Λ l r) =
          H * ∑ r ∈ S, gc r + H * ∑ r ∈ S, addConst δ Z' Λ l r := by ring
      rw [e]
      linarith
    have h9 := mul_le_mul_of_nonneg_right h6 (norm_nonneg C)
    have h10 : 0 ≤ H * (((l : ℝ) + 1) * (1 + ‖Ai‖) ^ (l + 1) + |γ| * ‖M ∘L ΛF‖ +
        ‖Z' ∘L ΛF‖) := by positivity
    have e2 : w * H = H * (((l : ℝ) + 1) * (1 + ‖Ai‖) ^ (l + 1) + |γ| * ‖M ∘L ΛF‖ +
        ‖Z' ∘L ΛF‖) + H * ((∑ r ∈ S, gc r) + ∑ r ∈ S, addConst δ Z' Λ l r) * ‖C‖ := by
      rw [hw]
      ring
    rw [e2]
    linarith
  · -- the defect
    have hK : 0 ≤ (reachRemConst P C A S δ κ + KD) * H ^ (l + 2) := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun v => ?_
    rw [_root_.sub_apply, nodeDefect_sub, _root_.add_apply, _root_.add_apply,
      ContinuousLinearMap.comp_apply]
    have hbase := norm_reach_defect_sub_le hA hδ hΛ hH0 hH1 hx1 v
    have hadd := addRule_apply hδ hΛ hZ'0 H v
    simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply] at hadd ⊢
    have hD := norm_sum_coef_expRem_le C A S (addRule δ Z' Λ H l)
      (fun r => H * addConst δ Z' Λ l r) hH0 hx1
      (fun r _ => norm_addRule_le δ Z' Λ hH0 hH1 l r) (by omega : 0 < l) v
    have hD' : ‖∑ r ∈ S, addRule δ Z' Λ H l r (C (expRem l ((-(r : ℝ) * H) • A) v))‖ ≤
        KD * H ^ (l + 2) * ‖v‖ := by
      refine hD.trans (le_of_eq ?_)
      rw [hKD, sum_mul, sum_mul, mul_sum, sum_mul]
      refine sum_congr rfl fun r _ => ?_
      ring
    -- the leading part
    have hlead : (γ * H ^ (l + 1)) • L (C ((A ^ l) (Q₀ v))) + H ^ (l + 1) • Z' v =
        (H ^ (l + 1) • (γ • ((L ∘L C) ∘L A ^ l) + Zr)) v := by
      simp only [hZ', _root_.smul_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, _root_.sub_apply, hM, map_sub, smul_sub, smul_add,
        smul_smul]
      rw [mul_comm γ (H ^ (l + 1))]
      abel
    set B := nodeDefect P (reachFi Ai M ΛF γ H l) (reachRule δ Ai L M Λ γ H l) C A H S v
    set R4 := ∑ r ∈ S, addRule δ Z' Λ H l r (C (expRem l ((-(r : ℝ) * H) • A) v))
    have e : B + ((H ^ (l + 1) • (Z' ∘L ΛF)) (P v) +
        ∑ r ∈ S, addRule δ Z' Λ H l r (C (exp ((-((r : ℝ) * H)) • A) v))) -
        (H ^ (l + 1) • (γ • ((L ∘L C) ∘L A ^ l) + Zr)) v =
        (B - (γ * H ^ (l + 1)) • L (C ((A ^ l) (Q₀ v)))) + R4 := by
      rw [hadd, ← hlead]
      abel
    have e' : B + (H ^ (l + 1) • (Z' ∘L ΛF)) (P v) +
        ∑ r ∈ S, addRule δ Z' Λ H l r (C (exp ((-((r : ℝ) * H)) • A) v)) -
        (H ^ (l + 1) • (γ • ((L ∘L C) ∘L A ^ l) + Zr)) v =
        (B - (γ * H ^ (l + 1)) • L (C ((A ^ l) (Q₀ v)))) + R4 := by
      rw [← e]
      abel
    rw [e']
    have h1 := norm_add_le (B - (γ * H ^ (l + 1)) • L (C ((A ^ l) (Q₀ v)))) R4
    have e2 : (reachRemConst P C A S δ κ + KD) * H ^ (l + 2) * ‖v‖ =
        reachRemConst P C A S δ κ * H ^ (l + 2) * ‖v‖ + KD * H ^ (l + 2) * ‖v‖ := by ring
    rw [e2]
    linarith

end RuleLead

end CoSimFoundations
