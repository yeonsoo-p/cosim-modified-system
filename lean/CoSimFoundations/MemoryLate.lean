/-
One order per held sample for any set of sample ages, and for a subsystem that runs after all of
its partners (the paper, Section 4: Theorem 4.10 `thm:memory` and the sentence after Theorem
4.11, "For a subsystem that runs after all of its partners the same argument gives the bound with
the constants 1/12, 1/24, 19/720 of the Adams–Moulton methods for `l = 2, 3, 4`, the bounded
weights then including that of the new sample").

**Setting**, as in `MemoryLead.lean`: `P = Π_i` (`‖P‖ ≤ 1`), `C` the stack of the outputs of the
partners of `i`, `P ∘ A = Ai ∘ P + L ∘ C`, `U = exp (H • A)`,
`unseen P C A m = {v : P v = 0, C (A^q v) = 0 for q < m}`.

**General ages** (`memory_nodes`). Let `S ⊂ ℤ` be a set of `l` sample ages; the sample of the age
`r` is `C U^{-r}` (`r = 0` the current sample, `r ≥ 1` past samples, `r = -1` the new sample),
with the coefficient `g r ∘ C`. The local defect is

  `𝒯 = P ∘ U - Fi ∘ P - Σ_{r ∈ S} g r ∘ C ∘ U^{-r}`        (`nodeDefect`).

If `‖g r ∘ C‖ ≤ w H` for every age `r ∈ S`, `r ≠ 0` (`Fi` and `g 0` arbitrary), then for
`H ‖A‖ ≤ 1`, with `c_i` the norm of `P A^{l+1}` on `unseen P C A l`,

  `(1 + b H ‖A‖) ‖𝒯‖ ≥ |γ_S| c_i H^{l+1} - (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2}`,
  `γ_S = (1/l!) ∫₀¹ ∏_{r ∈ S} (s + r) ds`                    (`nodeGamma`),

with `b = nodeB S`, `C_1 = nodeC1 S`, `C_2 = nodeC2 S` (`MemoryLateConstants.lean`), which depend
on `S` only. No hypothesis on `S` is needed (it may be empty, and need not contain the age `0`).

**Proof**, that of Theorem 4.10 with two changes. Step 1 (`node_key_step`): on `unseen m` the
moment `ν_m = Σ_{r ∈ S} ((-r)^m/m!) g r ∘ C` (`nodeMoment`) satisfies
`‖H^m ν_m A^m v - H^{m+1}/(m+1)! P A^{m+1} v‖ ≤ (‖𝒯‖ + e_m) ‖v‖`; the sample of the age `r` is
expanded in the Taylor series of `exp (-r H • A)`, whose tail depends on `|r|` only, so that the
new sample is treated like a sample of the age `1` and no factor `‖U‖` appears. Step 2
(`nodeMoment_top`, `node_gamma_identity`): the ages are the roots of
`∏_{r ∈ S} (s + r) = s^l + Σ_{m<l} a_m s^m`. The first change: the sum runs over `0 ≤ m < l`,
because the polynomial has a constant term when `0 ∉ S`; Step 1 holds for `m = 0` as well (on
`unseen 0 = ker P`). The second change: `γ_S` may be negative, so the bound is for `|γ_S|`.

**Instances.**
* Ages `0, …, l-1` (`leadNodes l`): `nodeDefect = localDefect`, `γ_S = adamsGamma l`, and the
  constants `b`, `C_1`, `C_2` are those of `MemoryLead.lean` (`nodeB_leadNodes`,
  `nodeC1_leadNodes`, `nodeC2_leadNodes`).
* Ages `-1, 0, …, l-2` (`lateNodes l`), a subsystem that runs after all of its partners
  (`memory_late`): with `𝒯 = P U - Fi P - gNew C U - Σ_{r<l-1} g r C U^{-r}` (`lateDefect`),
  `‖gNew ∘ C‖ ≤ w H` and `‖g r ∘ C‖ ≤ w H` for `1 ≤ r < l-1`, for every `l ≥ 1`,

    `(1 + b'_l H ‖A‖) ‖𝒯‖ ≥ |γ'_l| c_i H^{l+1} - (C'_1 ‖A‖^{l+2} + C'_2 w ‖A‖^{l+1}) H^{l+2}`,

  `|γ'_l| = 1/2, 1/12, 1/24, 19/720` for `l = 1, …, 4` (`γ'_l < 0`). Explicit forms:
  `memory_late_one` (`b' = 1`, `C'_1 = 2e - 9/2`, `C'_2 = 2e - 3`), `memory_late_two`
  (`b' = 1/2`, `C'_1 = 3e/2 - 47/12`, `C'_2 = 3e/2 - 7/2`), `memory_late_three` (`b' = 1/6`,
  `C'_1 = 7e/6 - 25/8`, `C'_2 = 7e/3 - 6`), `memory_late_four` (`b' = 2/3`,
  `C'_1 = 5e/3 - 3241/720`, `C'_2 = 5e²/3 + 10e/3 - 59/3`).

**Order over a run** (`run_order_late`): if the block row of subsystem `i` in a scheme
`(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` is such a rule (`P ∘ N = gNew ∘ C`,
`P ∘ M 0 = Fi ∘ P + g 0 ∘ C`, `P ∘ M r = g r ∘ C`, `g (l-1) = 0`), then `‖𝒯_run‖ ≥ ‖𝒯‖` and
`run_order_barrier` (`RunOrder.lean`, whose `N` carries the new samples) gives the lower bound on
the error over a run with `‖𝒯_run‖` replaced by the lower bound of `memory_late`.

Differences from the sentence of the paper: the paper names `l = 2, 3, 4`; the statement here
holds for every `l ≥ 1`, with the weight of the new sample among the bounded ones (for `l = 1`
it is the only sample and `b'_1 = 1`). Not in this file: the converse (a rule with defect
`O(H^{l+2})` when `c_i = 0`), and a subsystem that runs between two of its partners.
-/
import CoSimFoundations.MemoryLead
import CoSimFoundations.MemoryLateConstants
import CoSimFoundations.RunOrder

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section NodeMoments

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The `p`-th moment of the coefficients of the samples of the ages `S`, applied to a state:
`ν_p y = Σ_{r ∈ S} ((-r)^p / p!) g r (C y)`. -/
noncomputable def nodeMoment (g : ℤ → G →L[ℝ] F) (C : E →L[ℝ] G) (S : Finset ℤ) (p : ℕ)
    (y : E) : F :=
  ∑ r ∈ S, ((-(r : ℝ)) ^ p / (p ! : ℝ)) • g r (C y)

/-- **Step 2, the moments:** with `l` samples the `l`-th moment is a fixed combination of the
lower ones, `ν_l = -Σ_{m<l} (nodeCoeff S m · m!/l!) ν_m`. -/
theorem nodeMoment_top (g : ℤ → G →L[ℝ] F) (C : E →L[ℝ] G) {S : Finset ℤ} {l : ℕ}
    (hS : S.card = l) (y : E) :
    nodeMoment g C S l y =
      -∑ m ∈ range l, (nodeCoeff S m * (m ! : ℝ) / (l ! : ℝ)) • nodeMoment g C S m y := by
  subst hS
  unfold nodeMoment
  simp only [smul_sum, smul_smul]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun r hr => ?_
  rw [← sum_smul, ← neg_smul, neg_pow_card_eq_neg_sum hr, neg_div, sum_div]
  congr 2
  refine sum_congr rfl fun m _ => ?_
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hl' : (S.card ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Step 2 for any set of `l` ages:** the identity for the top moment from the node
polynomial, in the form used in Step 3 (`y = A^l v`, `z = P A^{l+1} v`). -/
theorem node_gamma_identity (g : ℤ → G →L[ℝ] F) (C : E →L[ℝ] G) {S : Finset ℤ} {l : ℕ}
    (hS : S.card = l) (H : ℝ) (y : E) (z : F) :
    (nodeGamma S * H ^ (l + 1)) • z =
      -(H ^ l • nodeMoment g C S l y - (H ^ (l + 1) / ((l + 1)! : ℝ)) • z) -
        ∑ m ∈ range l, (nodeCoeff S m * (m ! : ℝ) / (l ! : ℝ)) •
          (H ^ l • nodeMoment g C S m y - (H ^ (l + 1) / ((m + 1)! : ℝ)) • z) := by
  rw [sum_smul_smul_sub (range l) (fun m => nodeCoeff S m * (m ! : ℝ) / (l ! : ℝ))
    (fun m => H ^ (l + 1) / ((m + 1)! : ℝ)) (H ^ l) (fun m => nodeMoment g C S m y) z,
    nodeMoment_top g C hS y, smul_neg]
  subst hS
  rw [nodeGamma_mul, add_smul]
  abel

end NodeMoments

section NodeTaylor

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- The sample of the age `r ∈ ℤ` of the reference, for a state not shown up to the order `m`:
`T C U^{-r} v = H^m ((-r)^m/m!) T C A^m v + ρ` with `‖ρ‖ ≤ ‖T ∘ C‖ Σ_{p≥m+1} (|r| x)^p/p! ‖v‖`.
The remainder depends on `|r|` only: a new sample (`r = -1`) is as a sample of the age `1`. -/
theorem exists_node_sample_apply_eq (T : G →L[ℝ] F) {H : ℝ} (hH : 0 ≤ H) {m : ℕ} {v : E}
    (hv : v ∈ unseen P C A m) (r : ℤ) :
    ∃ ρ : F, T (C (exp ((-((r : ℝ) * H)) • A) v)) =
        (H ^ m * ((-(r : ℝ)) ^ m / (m ! : ℝ))) • T (C ((A ^ m) v)) + ρ ∧
      ‖ρ‖ ≤ ‖T ∘L C‖ * (expTail (m + 1) (|(r : ℝ)| * (H * ‖A‖)) * ‖v‖) :=
  exists_age_sample_apply_eq T hH hv r

/-- The local defect of a rule that uses the samples of the ages `r ∈ S` (the sample of the age
`r` is `C U^{-r}`; `r = -1` is the new sample): `𝒯 = P U - Fi P - Σ_{r ∈ S} g r C U^{-r}`,
`U = exp (H • A)`. -/
noncomputable def nodeDefect (P : E →L[ℝ] F) (Fi : F →L[ℝ] F) (g : ℤ → G →L[ℝ] F)
    (C : E →L[ℝ] G) (A : E →L[ℝ] E) (H : ℝ) (S : Finset ℤ) : E →L[ℝ] F :=
  P ∘L exp (H • A) - Fi ∘L P - ∑ r ∈ S, (g r ∘L C) ∘L exp ((-((r : ℝ) * H)) • A)

/-- **Step 1 for any set of ages** (every `m ≥ 0`): on the states not shown up to the order `m`,
`‖H^m ν_m A^m v - H^{m+1}/(m+1)! P A^{m+1} v‖ ≤ (‖𝒯‖ + e_m) ‖v‖`, if the coefficients of all
samples except the current one (age `0`) are at most `w H`. -/
theorem node_key_step (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℤ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) {S : Finset ℤ}
    (hw : ∀ r ∈ S, r ≠ 0 → ‖g r ∘L C‖ ≤ w * H) {m : ℕ} {v : E}
    (hv : v ∈ unseen P C A m) :
    ‖H ^ m • nodeMoment g C S m ((A ^ m) v) -
        (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v)‖ ≤
      (‖nodeDefect P Fi g C A H S‖ + nodeE S m w H (H * ‖A‖)) * ‖v‖ :=
  age_key_step hA hP Fi S (fun r : ℤ => (r : ℝ)) g hH
    (fun r hr h0 => hw r hr (Int.cast_ne_zero.1 h0)) hv

end NodeTaylor

section NodeMain

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- **Inequality (bounded) of the report for any set `S` of `l` sample ages, on a state not
shown** (Steps 1 to 3). For `v` with `P v = 0` and `C A^q v = 0`, `q < l`:
`|γ_S| H^{l+1} ‖P A^{l+1} v‖ ≤ ((1 + Σ_m β_m x^{l-m}) ‖𝒯‖ + e_l + Σ_m β_m x^{l-m} e_m) ‖v‖`,
sums over `0 ≤ m < l`, `x = H ‖A‖`. -/
theorem node_bounded_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℤ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) {S : Finset ℤ} {l : ℕ}
    (hS : S.card = l) (hw : ∀ r ∈ S, r ≠ 0 → ‖g r ∘L C‖ ≤ w * H) {v : E}
    (hv : v ∈ unseen P C A l) :
    |nodeGamma S| * H ^ (l + 1) * ‖P ((A ^ (l + 1)) v)‖ ≤
      ((1 + ∑ m ∈ range l, nodeBeta S m * (H * ‖A‖) ^ (l - m)) * ‖nodeDefect P Fi g C A H S‖ +
        nodeE S l w H (H * ‖A‖) +
        ∑ m ∈ range l, nodeBeta S m * (H * ‖A‖) ^ (l - m) * nodeE S m w H (H * ‖A‖)) * ‖v‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have ht0 : 0 ≤ ‖nodeDefect P Fi g C A H S‖ := norm_nonneg _
  have hkl := node_key_step hA hP Fi g hH hw hv
  have hkm : ∀ m ∈ range l,
      ‖H ^ l • nodeMoment g C S m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v)‖ ≤
      (H * ‖A‖) ^ (l - m) * (‖nodeDefect P Fi g C A H S‖ + nodeE S m w H (H * ‖A‖)) * ‖v‖ :=
    fun m hm => key_step_shift hA hH (mem_range.1 hm) (nodeMoment g C S m)
      (add_nonneg ht0 (nodeE_nonneg S m hw0 hH hx0))
      (fun _ hu => node_key_step hA hP Fi g hH hw hu) hv
  have hid := node_gamma_identity g C hS H ((A ^ l) v) (P ((A ^ (l + 1)) v))
  have hβ : ∀ m, |nodeCoeff S m * (m ! : ℝ) / (l ! : ℝ)| = nodeBeta S m := by
    intro m
    rw [← hS]
    exact abs_nodeCoeff_mul_div S m
  have hsum : ‖∑ m ∈ range l, (nodeCoeff S m * (m ! : ℝ) / (l ! : ℝ)) •
      (H ^ l • nodeMoment g C S m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v))‖ ≤
      ∑ m ∈ range l, nodeBeta S m * ((H * ‖A‖) ^ (l - m) *
        (‖nodeDefect P Fi g C A H S‖ + nodeE S m w H (H * ‖A‖)) * ‖v‖) := by
    refine norm_sum_le_of_le _ fun m hm => ?_
    rw [norm_smul, Real.norm_eq_abs, hβ]
    exact mul_le_mul_of_nonneg_left (hkm m hm) (nodeBeta_nonneg S m)
  have hsumeq : ∑ m ∈ range l, nodeBeta S m * ((H * ‖A‖) ^ (l - m) *
        (‖nodeDefect P Fi g C A H S‖ + nodeE S m w H (H * ‖A‖)) * ‖v‖) =
      ((∑ m ∈ range l, nodeBeta S m * (H * ‖A‖) ^ (l - m)) * ‖nodeDefect P Fi g C A H S‖ +
        ∑ m ∈ range l, nodeBeta S m * (H * ‖A‖) ^ (l - m) * nodeE S m w H (H * ‖A‖)) *
          ‖v‖ := by
    simp only [add_mul, sum_mul]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have h1 : |nodeGamma S| * H ^ (l + 1) * ‖P ((A ^ (l + 1)) v)‖ =
      ‖(nodeGamma S * H ^ (l + 1)) • P ((A ^ (l + 1)) v)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hH _)]
  have h2 := norm_sub_le (-(H ^ l • nodeMoment g C S l ((A ^ l) v) -
      (H ^ (l + 1) / ((l + 1)! : ℝ)) • P ((A ^ (l + 1)) v)))
    (∑ m ∈ range l, (nodeCoeff S m * (m ! : ℝ) / (l ! : ℝ)) •
      (H ^ l • nodeMoment g C S m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v)))
  rw [← hid, norm_neg] at h2
  rw [hsumeq] at hsum
  linarith

/-- **Inequality (bounded) of the report for any set `S` of `l` sample ages**, with
`c_i = ‖P A^{l+1}` restricted to the states not shown`‖`:
`|γ_S| H^{l+1} c_i ≤ (1 + Σ_m β_m x^{l-m}) ‖𝒯‖ + e_l + Σ_m β_m x^{l-m} e_m`, every `H ≥ 0`. -/
theorem memory_nodes_bounded (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℤ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) {S : Finset ℤ} {l : ℕ}
    (hS : S.card = l) (hw : ∀ r ∈ S, r ≠ 0 → ‖g r ∘L C‖ ≤ w * H) :
    |nodeGamma S| * H ^ (l + 1) * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ ≤
      (1 + ∑ m ∈ range l, nodeBeta S m * (H * ‖A‖) ^ (l - m)) * ‖nodeDefect P Fi g C A H S‖ +
        nodeE S l w H (H * ‖A‖) +
        ∑ m ∈ range l, nodeBeta S m * (H * ‖A‖) ^ (l - m) * nodeE S m w H (H * ‖A‖) := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hβ : 0 ≤ ∑ m ∈ range l, nodeBeta S m * (H * ‖A‖) ^ (l - m) :=
    sum_nonneg fun m _ => mul_nonneg (nodeBeta_nonneg S m) (pow_nonneg hx0 _)
  refine mul_opNorm_le_of_forall _ ?_ fun u => node_bounded_apply hA hP Fi g hH hw0 hS hw u.2
  refine add_nonneg (add_nonneg (mul_nonneg (by linarith) (norm_nonneg _))
    (nodeE_nonneg S l hw0 hH hx0)) (sum_nonneg fun m _ => ?_)
  exact mul_nonneg (mul_nonneg (nodeBeta_nonneg S m) (pow_nonneg hx0 _))
    (nodeE_nonneg S m hw0 hH hx0)

/-- **One order per held sample for any set `S` of `l` sample ages, on a state not shown**, for
`H ‖A‖ ≤ 1`: `|γ_S| H^{l+1} ‖P A^{l+1} v‖ ≤
  ((1 + b H ‖A‖) ‖𝒯‖ + (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2}) ‖v‖`. -/
theorem memory_nodes_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℤ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) (hx1 : H * ‖A‖ ≤ 1)
    {S : Finset ℤ} {l : ℕ} (hS : S.card = l) (hw : ∀ r ∈ S, r ≠ 0 → ‖g r ∘L C‖ ≤ w * H) {v : E}
    (hv : v ∈ unseen P C A l) :
    |nodeGamma S| * H ^ (l + 1) * ‖P ((A ^ (l + 1)) v)‖ ≤
      ((1 + nodeB S * (H * ‖A‖)) * ‖nodeDefect P Fi g C A H S‖ +
        (nodeC1 S * ‖A‖ ^ (l + 2) + nodeC2 S * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2)) * ‖v‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  refine (node_bounded_apply hA hP Fi g hH hw0 hS hw hv).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
  subst hS
  exact lead_of_bounded_arith (range S.card) (fun m hm => mem_range.1 hm) (nodeBeta S)
    (fun m => nodeE S m w H (H * ‖A‖)) (fun m => expTail (m + 2) 1)
    (fun m => ∑ r ∈ S, expTail (m + 1) |(r : ℝ)|) (nodeBeta_nonneg S) hx0 hx1 (norm_nonneg _)
    fun m => nodeE_le S m hw0 hH hx0 hx1

/-- **One order per held sample for any set of sample ages.** Let subsystem `i` (projection `P`,
`‖P‖ ≤ 1`, `P ∘ A = Ai ∘ P + L ∘ C`) use the samples of the ages `r ∈ S`, a set of `l` integers
(the sample of the age `r` is `C U^{-r}`; `r = -1` is a new sample), with coefficients
`‖g r ∘ C‖ ≤ w H` on all samples except the current one (`r = 0`); `Fi` and `g 0` are arbitrary.
Then, for `H ‖A‖ ≤ 1`,
`|γ_S| c_i H^{l+1} - (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2} ≤ (1 + b H ‖A‖) ‖𝒯‖`,
with `c_i` the norm of `P A^{l+1}` on the states not shown (`P v = 0`, `C A^q v = 0`, `q < l`),
`γ_S = nodeGamma S = (1/l!) ∫₀¹ ∏_{r ∈ S} (s + r) ds` and the constants `b = nodeB S`,
`C_1 = nodeC1 S`, `C_2 = nodeC2 S`, which depend on `S` only. -/
theorem memory_nodes (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℤ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) (hx1 : H * ‖A‖ ≤ 1)
    {S : Finset ℤ} {l : ℕ} (hS : S.card = l) (hw : ∀ r ∈ S, r ≠ 0 → ‖g r ∘L C‖ ≤ w * H) :
    |nodeGamma S| * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) -
        (nodeC1 S * ‖A‖ ^ (l + 2) + nodeC2 S * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) ≤
      (1 + nodeB S * (H * ‖A‖)) * ‖nodeDefect P Fi g C A H S‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hD : 0 ≤ (1 + nodeB S * (H * ‖A‖)) * ‖nodeDefect P Fi g C A H S‖ +
      (nodeC1 S * ‖A‖ ^ (l + 2) + nodeC2 S * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) := by
    have h1 := nodeB_nonneg S
    have h2 := nodeC1_nonneg S
    have h3 := nodeC2_nonneg S
    positivity
  have h := mul_opNorm_le_of_forall ((P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL) hD
    fun u => memory_nodes_apply hA hP Fi g hH hw0 hx1 hS hw u.2
  linarith

end NodeMain

section Lead

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- For the ages `0, …, l-1` the local defect is that of `MemoryLead.lean`. -/
theorem nodeDefect_leadNodes (P : E →L[ℝ] F) (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    (C : E →L[ℝ] G) (A : E →L[ℝ] E) (H : ℝ) (l : ℕ) :
    nodeDefect P Fi (fun r => g r.toNat) C A H (leadNodes l) = localDefect P Fi g C A H l := by
  unfold nodeDefect localDefect
  rw [sum_leadNodes]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [exp_neg_smul_pow]
  simp only [Int.toNat_natCast, Int.cast_natCast]

/-- For the ages `0, …, l-1`, `l ≥ 1`: `b = b_l` of `MemoryLead.lean`. -/
theorem nodeB_leadNodes {l : ℕ} (hl : 1 ≤ l) : nodeB (leadNodes l) = memB l := by
  unfold nodeB memB nodeBeta memBeta
  rw [card_leadNodes, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < l)]
  simp [nodeCoeff_leadNodes, adamsCoeff_zero hl]

/-- For the ages `0, …, l-1`, `l ≥ 1`: `C_1` is that of `MemoryLead.lean`. -/
theorem nodeC1_leadNodes {l : ℕ} (hl : 1 ≤ l) : nodeC1 (leadNodes l) = memC1 l := by
  unfold nodeC1 memC1 nodeBeta memBeta
  rw [card_leadNodes, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < l)]
  simp [nodeCoeff_leadNodes, adamsCoeff_zero hl]

/-- For the ages `0, …, l-1`, `l ≥ 1`: `C_2` is that of `MemoryLead.lean`. -/
theorem nodeC2_leadNodes {l : ℕ} (hl : 1 ≤ l) : nodeC2 (leadNodes l) = memC2 l := by
  unfold nodeC2 memC2 nodeBeta memBeta
  rw [card_leadNodes, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < l)]
  simp [nodeCoeff_leadNodes, adamsCoeff_zero hl, sum_leadNodes]

end Lead

section Late

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- The local defect of the rule of a subsystem that runs after all of its partners with `l ≥ 1`
held samples, the new one (coefficient `gNew ∘ C`) and those of the ages `0, …, l-2`
(coefficients `g r ∘ C`): `𝒯 = P U - Fi P - gNew C U - Σ_{r<l-1} g r C U^{-r}`,
`U = exp (H • A)`. -/
noncomputable def lateDefect (P : E →L[ℝ] F) (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (H : ℝ) (l : ℕ) : E →L[ℝ] F :=
  P ∘L exp (H • A) - Fi ∘L P - (gNew ∘L C) ∘L exp (H • A) -
    ∑ r ∈ range (l - 1), (g r ∘L C) ∘L (exp (-(H • A)) ^ r)

/-- The coefficients of a rule with a new sample, indexed by the age: `gNew` at the age `-1`,
`g r` at the age `r ≥ 0`. -/
def lateCoef (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F) (r : ℤ) : G →L[ℝ] F :=
  if r = -1 then gNew else g r.toNat

/-- For the ages `-1, 0, …, l-2` the local defect is `lateDefect`. -/
theorem nodeDefect_lateNodes (P : E →L[ℝ] F) (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (H : ℝ) (l : ℕ) :
    nodeDefect P Fi (lateCoef gNew g) C A H (lateNodes l) = lateDefect P Fi gNew g C A H l := by
  have h0 : ((lateCoef gNew g (-1)) ∘L C) ∘L exp ((-(((-1 : ℤ) : ℝ) * H)) • A) =
      (gNew ∘L C) ∘L exp (H • A) := by
    simp [lateCoef]
  have h1 : ∀ k ∈ range (l - 1),
      ((lateCoef gNew g (k : ℤ)) ∘L C) ∘L exp ((-((((k : ℕ) : ℤ) : ℝ) * H)) • A) =
        (g k ∘L C) ∘L (exp (-(H • A)) ^ k) := by
    intro k _
    have hk : ((k : ℕ) : ℤ) ≠ -1 := by omega
    have hc : lateCoef gNew g (k : ℤ) = g k := by simp [lateCoef, hk]
    rw [exp_neg_smul_pow, hc, Int.cast_natCast]
  unfold nodeDefect lateDefect
  rw [sum_lateNodes, h0, sum_congr rfl h1, sub_sub (P ∘L exp (H • A) - Fi ∘L P)]

/-- **One order per held sample for a subsystem that runs after all of its partners.** Let
subsystem `i` (projection `P`, `‖P‖ ≤ 1`, `P ∘ A = Ai ∘ P + L ∘ C`) run after all of its partners
with `l ≥ 1` held samples: the new sample, with coefficient `‖gNew ∘ C‖ ≤ w H`, and the samples
of the ages `0, …, l-2`, with coefficients `‖g r ∘ C‖ ≤ w H` for `1 ≤ r < l-1`; `Fi` and the
coefficient `g 0` of the current sample are arbitrary. Then, for `H ‖A‖ ≤ 1`,
`|γ'_l| c_i H^{l+1} - (C'_1 ‖A‖^{l+2} + C'_2 w ‖A‖^{l+1}) H^{l+2} ≤ (1 + b'_l H ‖A‖) ‖𝒯‖`,
with the same `c_i` as in `memory_lead` (the norm of `P A^{l+1}` on the states with `P v = 0`,
`C A^q v = 0`, `q < l`), `γ'_l = lateGamma l = (1/l!) ∫₀¹ (s-1) ∏_{k<l-1} (s+k) ds` (the
Adams–Moulton constants; `|γ'_l| = 1/2, 1/12, 1/24, 19/720` for `l = 1, …, 4`) and constants
`b'_l = lateB l`, `C'_1 = lateC1 l`, `C'_2 = lateC2 l` that depend on `l` only. -/
theorem memory_late (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w)
    (hx1 : H * ‖A‖ ≤ 1) {l : ℕ} (hl : 1 ≤ l) (hwNew : ‖gNew ∘L C‖ ≤ w * H)
    (hw : ∀ r, 1 ≤ r → r < l - 1 → ‖g r ∘L C‖ ≤ w * H) :
    |lateGamma l| * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) -
        (lateC1 l * ‖A‖ ^ (l + 2) + lateC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) ≤
      (1 + lateB l * (H * ‖A‖)) * ‖lateDefect P Fi gNew g C A H l‖ := by
  have hw' : ∀ r ∈ lateNodes l, r ≠ 0 → ‖lateCoef gNew g r ∘L C‖ ≤ w * H := by
    intro r hr hr0
    rcases mem_insert.1 hr with rfl | hr'
    · simpa [lateCoef] using hwNew
    · obtain ⟨k, hk, rfl⟩ := mem_map.1 hr'
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hr0 rfl
      have hk1 : ((k : ℕ) : ℤ) ≠ -1 := by omega
      have h := hw k (by omega) (mem_range.1 hk)
      have he : lateCoef gNew g (Nat.castEmbedding k) = g k := by
        simp [lateCoef, hk1]
      rw [he]
      exact h
  have h := memory_nodes hA hP Fi (lateCoef gNew g) hH hw0 hx1 (card_lateNodes hl) hw'
  rw [nodeDefect_lateNodes] at h
  exact h

/-- **A subsystem that runs after all of its partners with one held sample, the new one**
(`γ'_1 = -1/2`, `b'_1 = 1`): if `‖gNew ∘ C‖ ≤ w H`, then for `H ‖A‖ ≤ 1`,
`½ c_i H² - ((2e - 9/2) ‖A‖³ + (2e - 3) w ‖A‖²) H³ ≤ (1 + H ‖A‖) ‖𝒯‖`,
with `c_i` the norm of `P A²` on the states with `P v = 0`, `C v = 0`. -/
theorem memory_late_one (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w)
    (hx1 : H * ‖A‖ ≤ 1) (hwNew : ‖gNew ∘L C‖ ≤ w * H) :
    1 / 2 * ‖(P ∘L (A ^ 2)) ∘L (unseen P C A 1).subtypeL‖ * H ^ 2 -
        ((2 * Real.exp 1 - 9 / 2) * ‖A‖ ^ 3 + (2 * Real.exp 1 - 3) * w * ‖A‖ ^ 2) * H ^ 3 ≤
      (1 + H * ‖A‖) * ‖lateDefect P Fi gNew g C A H 1‖ := by
  have h := memory_late hA hP Fi gNew g hH hw0 hx1 (le_refl 1) hwNew
    (fun r h1 h2 => absurd h2 (by omega))
  rw [lateGamma_one, lateB_one, lateC1_one, lateC2_one, one_mul] at h
  norm_num at h
  linarith

/-- **A subsystem that runs after all of its partners with two held samples**, the new and the
current one (`γ'_2 = -1/12`, `b'_2 = 1/2`): if `‖gNew ∘ C‖ ≤ w H`, then for `H ‖A‖ ≤ 1`,
`(1/12) c_i H³ - ((3e/2 - 47/12) ‖A‖⁴ + (3e/2 - 7/2) w ‖A‖³) H⁴ ≤ (1 + ½ H ‖A‖) ‖𝒯‖`,
with `c_i` the norm of `P A³` on the states with `P v = 0`, `C v = 0`, `C A v = 0`. The
coefficient `g 0` of the current sample is arbitrary. -/
theorem memory_late_two (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w)
    (hx1 : H * ‖A‖ ≤ 1) (hwNew : ‖gNew ∘L C‖ ≤ w * H) :
    1 / 12 * ‖(P ∘L (A ^ 3)) ∘L (unseen P C A 2).subtypeL‖ * H ^ 3 -
        ((3 / 2 * Real.exp 1 - 47 / 12) * ‖A‖ ^ 4 +
          (3 / 2 * Real.exp 1 - 7 / 2) * w * ‖A‖ ^ 3) * H ^ 4 ≤
      (1 + 1 / 2 * (H * ‖A‖)) * ‖lateDefect P Fi gNew g C A H 2‖ := by
  have h := memory_late hA hP Fi gNew g hH hw0 hx1 (by norm_num : 1 ≤ 2) hwNew
    (fun r h1 h2 => absurd h2 (by omega))
  rw [lateGamma_two, lateB_two, lateC1_two, lateC2_two] at h
  norm_num at h
  linarith

/-- **A subsystem that runs after all of its partners with three held samples** (`γ'_3 = -1/24`,
`b'_3 = 1/6`): if `‖gNew ∘ C‖ ≤ w H` and `‖g 1 ∘ C‖ ≤ w H`, then for `H ‖A‖ ≤ 1`,
`(1/24) c_i H⁴ - ((7e/6 - 25/8) ‖A‖⁵ + (7e/3 - 6) w ‖A‖⁴) H⁵ ≤ (1 + (1/6) H ‖A‖) ‖𝒯‖`,
with `c_i` the norm of `P A⁴` on the states with `P v = 0`, `C A^q v = 0`, `q < 3`. -/
theorem memory_late_three (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w)
    (hx1 : H * ‖A‖ ≤ 1) (hwNew : ‖gNew ∘L C‖ ≤ w * H) (hw : ‖g 1 ∘L C‖ ≤ w * H) :
    1 / 24 * ‖(P ∘L (A ^ 4)) ∘L (unseen P C A 3).subtypeL‖ * H ^ 4 -
        ((7 / 6 * Real.exp 1 - 25 / 8) * ‖A‖ ^ 5 + (7 / 3 * Real.exp 1 - 6) * w * ‖A‖ ^ 4) *
          H ^ 5 ≤
      (1 + 1 / 6 * (H * ‖A‖)) * ‖lateDefect P Fi gNew g C A H 3‖ := by
  have hw' : ∀ r, 1 ≤ r → r < 3 - 1 → ‖g r ∘L C‖ ≤ w * H := by
    intro r h1 h2
    have hr : r = 1 := by omega
    rw [hr]
    exact hw
  have h := memory_late hA hP Fi gNew g hH hw0 hx1 (by norm_num : 1 ≤ 3) hwNew hw'
  rw [lateGamma_three, lateB_three, lateC1_three, lateC2_three] at h
  norm_num at h
  linarith

/-- **A subsystem that runs after all of its partners with four held samples**
(`γ'_4 = -19/720`, `b'_4 = 2/3`): if `‖gNew ∘ C‖ ≤ w H`, `‖g 1 ∘ C‖ ≤ w H` and
`‖g 2 ∘ C‖ ≤ w H`, then for `H ‖A‖ ≤ 1`,
`(19/720) c_i H⁵ - ((5e/3 - 3241/720) ‖A‖⁶ + (5e²/3 + 10e/3 - 59/3) w ‖A‖⁵) H⁶
  ≤ (1 + (2/3) H ‖A‖) ‖𝒯‖`,
with `c_i` the norm of `P A⁵` on the states with `P v = 0`, `C A^q v = 0`, `q < 4`. -/
theorem memory_late_four (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w)
    (hx1 : H * ‖A‖ ≤ 1) (hwNew : ‖gNew ∘L C‖ ≤ w * H) (hw1 : ‖g 1 ∘L C‖ ≤ w * H)
    (hw2 : ‖g 2 ∘L C‖ ≤ w * H) :
    19 / 720 * ‖(P ∘L (A ^ 5)) ∘L (unseen P C A 4).subtypeL‖ * H ^ 5 -
        ((5 / 3 * Real.exp 1 - 3241 / 720) * ‖A‖ ^ 6 +
          (5 / 3 * Real.exp 2 + 10 / 3 * Real.exp 1 - 59 / 3) * w * ‖A‖ ^ 5) * H ^ 6 ≤
      (1 + 2 / 3 * (H * ‖A‖)) * ‖lateDefect P Fi gNew g C A H 4‖ := by
  have hw' : ∀ r, 1 ≤ r → r < 4 - 1 → ‖g r ∘L C‖ ≤ w * H := by
    intro r h1 h2
    rcases (by omega : r = 1 ∨ r = 2) with hr | hr
    · rw [hr]
      exact hw1
    · rw [hr]
      exact hw2
  have h := memory_late hA hP Fi gNew g hH hw0 hx1 (by norm_num : 1 ≤ 4) hwNew hw'
  rw [lateGamma_four, lateB_four, lateC1_four, lateC2_four] at h
  norm_num at h
  linarith

end Late

section RunOrderLate

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- The oldest sample is not used: if its coefficient `g n` is zero, the sum of the samples of
the ages `0, …, n` is the sum over the ages `0, …, n - 1`. -/
theorem sum_range_succ_of_last_eq_zero (g : ℕ → G →L[ℝ] F) {n : ℕ} (hlast : g n = 0)
    (y : ℕ → G) : ∑ r ∈ range (n + 1), g r (y r) = ∑ r ∈ range n, g r (y r) := by
  rw [sum_range_succ, hlast, _root_.zero_apply, add_zero]

/-- The block row of a subsystem that runs after all of its partners: if the row of subsystem
`i` in the scheme `(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` is `P ∘ N = gNew ∘ C` (new samples),
`P ∘ M 0 = Fi ∘ P + g 0 ∘ C`, `P ∘ M r = g r ∘ C` for `1 ≤ r < l`, and the oldest sample is not
used (`g (l-1) = 0`), then the row of the local defect of the scheme is `lateDefect`. -/
theorem proj_comp_runDefect_late (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) (H : ℝ) {l : ℕ}
    (hl : 1 ≤ l) (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    (hrowN : P ∘L N = gNew ∘L C) (hrow0 : P ∘L M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → P ∘L M r = g r ∘L C) (hlast : g (l - 1) = 0) :
    P ∘L ((1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r) =
      lateDefect P Fi gNew g C A H l := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hlast
  have hN' : ∀ y, P (N y) = gNew (C y) := fun y => DFunLike.congr_fun hrowN y
  have h0' : ∀ y, P (M 0 y) = Fi (P y) + g 0 (C y) := fun y => DFunLike.congr_fun hrow0 y
  have hr' : ∀ r, 1 ≤ r → r < n + 1 → ∀ y, P (M r y) = g r (C y) := fun r h1 h2 y =>
    DFunLike.congr_fun (hrow r h1 h2) y
  ext v
  have hsum : ∑ r ∈ range (n + 1), P (M r ((exp (-(H • A)) ^ r) v)) =
      Fi (P v) + ∑ r ∈ range (n + 1), g r (C ((exp (-(H • A)) ^ r) v)) := by
    rw [sum_range_succ', sum_range_succ', h0']
    have hs : ∀ r ∈ range n, P (M (r + 1) ((exp (-(H • A)) ^ (r + 1)) v)) =
        g (r + 1) (C ((exp (-(H • A)) ^ (r + 1)) v)) :=
      fun r hr => hr' (r + 1) (by omega) (by have := mem_range.1 hr; omega) _
    rw [sum_congr rfl hs]
    simp only [pow_zero, one_apply_eq_self]
    abel
  unfold lateDefect
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, _root_.sum_apply,
    mul_apply_eq_comp, one_apply_eq_self, map_sub, map_sum, hN', Nat.add_sub_cancel]
  rw [hsum, sum_range_succ_of_last_eq_zero g hlast]
  abel

variable [Nontrivial E]

/-- **`run_order_barrier` with a lower bound of the local defect:** in the setting of
`run_order_barrier`, if `t₀ ≤ ‖𝒯‖` for the local defect `𝒯 = (1 - N) U - Σ_{r<l} M r U^{-r}` of
the scheme, then
`δ ≥ min {0.175, 0.175 (K-l+1) t₀ / (2.65 (1+ν) + m̄ l (l-1) (1 + ¼ e^{(l-1) H ‖A‖}))}`. -/
theorem run_order_barrier_of_le (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {ν mbar : ℝ}
    (hN : ‖N‖ ≤ ν) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖)
    {t0 : ℝ} (ht0 : t0 ≤ ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖) :
    min 0.175 (0.175 * ((K : ℝ) - l + 1) * t0 /
      (2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))))) ≤ δ := by
  refine le_trans (min_le_min le_rfl ?_) (run_order_barrier A N M hH hl hK hKH hN hM x hx hδ)
  have hK' := run_length_pos hK
  have hν : 0 ≤ ν := (norm_nonneg N).trans hN
  have hm := bound_mul_pred_nonneg hl hM
  have hD : 0 ≤ 2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
      (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) := by
    have he := Real.exp_pos (((l : ℝ) - 1) * (H * ‖A‖))
    have h1 : 0 ≤ mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))) := mul_nonneg hm (by linarith)
    linarith
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ht0 (mul_nonneg (by norm_num) hK'.le)) hD

/-- **Order over a run for a scheme in which a subsystem runs after all of its partners.** In the
setting of `run_order_barrier` (scheme `(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` with `l` held
samples, `1 ≤ l ≤ K`, `K H ‖A‖ ≤ 1/2`, `‖N‖ ≤ ν`, `‖M r‖ ≤ m̄` for `1 ≤ r < l`, relative errors
of all runs at most `δ` for `k ≤ K`), let the block row of subsystem `i` (projection `P`,
`‖P‖ ≤ 1`, `P ∘ A = Ai ∘ P + L ∘ C`) be the rule of a subsystem that runs after all of its
partners: `P ∘ N = gNew ∘ C`, `P ∘ M 0 = Fi ∘ P + g 0 ∘ C`, `P ∘ M r = g r ∘ C` for `1 ≤ r < l`,
`g (l-1) = 0`, with bounded weights `‖gNew ∘ C‖ ≤ w H` and `‖g r ∘ C‖ ≤ w H` for `1 ≤ r < l-1`.
Then
`δ ≥ min {0.175, 0.175 (K-l+1) t₀ / (2.65 (1+ν) + m̄ l (l-1) (1 + ¼ e^{(l-1) H ‖A‖}))}`,
`t₀ = (|γ'_l| c_i H^{l+1} - (C'_1 ‖A‖^{l+2} + C'_2 w ‖A‖^{l+1}) H^{l+2}) / (1 + b'_l H ‖A‖)`,
the lower bound of `memory_late` on the local defect: the error over a run is of the order
`H^l` at least when `c_i > 0`. -/
theorem run_order_late (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    {l K : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hKH : K * H * ‖A‖ ≤ 1 / 2) {ν mbar : ℝ}
    (hN : ‖N‖ ≤ ν) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ mbar) (x : E → ℕ → E)
    (hx : ∀ x0, x0 ≠ 0 → ∀ k, l - 1 ≤ k → k < K →
      (1 - N) (x x0 (k + 1)) = ∑ r ∈ range l, M r (x x0 (k - r)))
    {δ : ℝ} (hδ : ∀ x0, x0 ≠ 0 → ∀ k ≤ K, ‖x x0 k - (exp (H • A) ^ k) x0‖ ≤ δ * ‖x0‖)
    (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) (hrowN : P ∘L N = gNew ∘L C) (hrow0 : P ∘L M 0 = Fi ∘L P + g 0 ∘L C)
    (hrow : ∀ r, 1 ≤ r → r < l → P ∘L M r = g r ∘L C) (hlast : g (l - 1) = 0) {w : ℝ}
    (hw0 : 0 ≤ w) (hwNew : ‖gNew ∘L C‖ ≤ w * H)
    (hw : ∀ r, 1 ≤ r → r < l - 1 → ‖g r ∘L C‖ ≤ w * H) :
    min 0.175 (0.175 * ((K : ℝ) - l + 1) *
        ((|lateGamma l| * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) -
          (lateC1 l * ‖A‖ ^ (l + 2) + lateC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2)) /
            (1 + lateB l * (H * ‖A‖))) /
      (2.65 * (1 + ν) + mbar * ((l : ℝ) * (l - 1)) *
        (1 + 1 / 4 * Real.exp (((l : ℝ) - 1) * (H * ‖A‖))))) ≤ δ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hx1 : H * ‖A‖ ≤ 1 := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hl.trans hK
    have h := mul_le_mul_of_nonneg_right hK1 hx0
    rw [one_mul, ← mul_assoc] at h
    linarith
  have hpos : 0 < 1 + lateB l * (H * ‖A‖) := by
    have := mul_nonneg (lateB_nonneg l) hx0
    linarith
  have hmem := memory_late hA hP Fi gNew g hH hw0 hx1 hl hwNew hw
  have hrowT := proj_comp_runDefect_late A N M H hl Fi gNew g hrowN hrow0 hrow hlast
  have hnorm : ‖lateDefect P Fi gNew g C A H l‖ ≤
      ‖(1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r‖ := by
    rw [← hrowT]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h := mul_le_mul_of_nonneg_right hP
      (norm_nonneg ((1 - N) * exp (H • A) - ∑ r ∈ range l, M r * exp (-(H • A)) ^ r))
    rwa [one_mul] at h
  refine run_order_barrier_of_le A N M hH hl hK hKH hN hM x hx hδ (le_trans ?_ hnorm)
  rw [div_le_iff₀ hpos]
  linarith

end RunOrderLate

end CoSimFoundations
