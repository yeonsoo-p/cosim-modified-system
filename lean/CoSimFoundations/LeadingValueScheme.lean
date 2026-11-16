/-
The leading value of the visibility bound for `l` held samples in every order of execution
(the paper, Theorem `thm:memory` (i), eq. `eq:leading`): the hypotheses of the conditional form
`leading_value_of_kernel` (`LeadingValue`) discharged for the samples of a scheme.

**Paper.** If the maps `Π_i` and `C_j A^p`, `j ∈ 𝒫(i)`, `p < l`, are independent, then in every
order of execution

  `f_i = H^{l+1} ‖Σ_j γ_l^{σ_ij} A_ij Π_j A^l | 𝒱_i^0‖ + O(H^{l+2})`,

which is `|γ_l^σ| c_i H^{l+1}` if the samples are all old or all new.

**Setting.** As in `LeadingDefect`: `P ∘ A = Ai ∘ P + Σ_j L j ∘ C j`, `‖P‖ ≤ 1`, the partners
`j ∈ J`; partner `j` is sampled at the nodes `x j q`, `q < l`, and `W j` is the inverse of the
Vandermonde matrix of its nodes. The samples are `nodeSample`, `C j ∘ exp (x j q H A)`;
`f = visBound P (exp (H A)) (nodeSample C A H x)`. The maps of the paper are stacked in
`N₀ = stackedDeriv P C A l : v ↦ (P v, (C j A^p v)_{j, p<l})` (range with the maximum norm), and
independence is a bounded right inverse `R` of `N₀` (it exists in finite dimension iff `N₀` is
surjective, `exists_rightInverse_of_surjective`). `D = leadingMap L C A γ l = Σ_j γ_j L j C j A^l`
and `𝒱^0 = unseen P (pi C) A l`.

**Statements.**
* `ker_stackedDiff`, `ker_stackedDeriv`: the states not shown are the kernel of the stack
  `stackedDiff` of `P` and of the divided differences of the samples, and `𝒱^0` is the kernel
  of `N₀`.
* `norm_stackedDiff_sub_le`: `‖stackedDiff - N₀‖ ≤ c₁ H`, `c₁ = Σ_j Σ_p p! ‖C j‖ ω_p^j ‖A‖^{p+1}`
  (`kernelConst`), for `0 < H`, `H ‖A‖ ≤ 1`.
* `leading_value_nodes` (**general nodes**): for `0 < H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`,
  `c₁ H ‖R‖ ≤ 1/2`,

    `|f - H^{l+1} ‖D|𝒱^0‖| ≤ (c₂ + 4 ‖R‖ c₁ ‖D‖) H^{l+2}`,   `γ_j = ddGamma (x j) (W j)`,

  with `c₂ = defectConst` of `LeadingDefect`.
* `visBound_le_leading_nodes` (**upper bound without independence**): for any generalised
  inverse `R` of `N₀` (`N₀ R N₀ = N₀`), `f ≤ H^{l+1} ‖D|𝒱^0‖ + (c₂ + 2 ‖R‖ c₁ ‖D‖) H^{l+2}`.
  Independence is needed for the lower bound only.
* `leading_value_uniform` (**all samples old or all new**): if every partner has the nodes
  `σ - q`, then `|f - |γ_l^σ| c_i H^{l+1}| ≤ (c₂ + 4 ‖R‖ c₁ |γ_l^σ| ‖Σ_j L j C j A^l‖) H^{l+2}`
  with `c_i = unseenRate` and `γ_l^σ = schemeGamma σ l`, which is `adamsGamma l` for `σ = 0` and
  `lateGamma l` for `σ = 1` (`LeadingConstant`).
* `leading_value_scheme` (**the scheme of `VisibilityConverse`**, every order of execution): the
  same for `f_i = visBound (Pr i) U (shownSample Pr c U Ui stage partner l i)`, `U = exp (H A)`,
  `Ui = exp (-H A)`, with `J` the partners of `i` and the nodes `σ_ij - q`,
  `σ_ij = newSample stage i j`; `γ_j = schemeGamma σ_ij l`.

All hypotheses of the conditional form are discharged; what remains assumed is what the paper
assumes (the coupling row, independence in the form of `R`) and the explicit smallness of `H`.
With `isLeast_visBound` (`VisibilityExact`; finite-dimensional inner product space) `f_i` is the
least norm of the local defect over all rules, which is the first equality of `eq:leading`.
-/
import CoSimFoundations.LeadingValue
import CoSimFoundations.LeadingDefect
import CoSimFoundations.LeadingConstant
import CoSimFoundations.VisibilityConverse
import CoSimFoundations.MemoryLate

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Nodes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {J : Type*} [Fintype J] {Y : J → Type*} [∀ j, NormedAddCommGroup (Y j)]
  [∀ j, NormedSpace ℝ (Y j)] [∀ j, CompleteSpace (Y j)] {l : ℕ}

/-- The monolithic sample of partner `j` at its node `x j q`: `C j ∘ exp (x j q H A)`. -/
noncomputable def nodeSample (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E) (H : ℝ)
    (x : J → Fin l → ℝ) (k : J × Fin l) : E →L[ℝ] Y k.1 :=
  C k.1 ∘L exp ((x k.1 k.2 * H) • A)

/-- The maps `Π_i` and `C_j A^p`, `p < l`, of the paper as one map `N₀`. -/
noncomputable def stackedDeriv (P : E →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E)
    (l : ℕ) : E →L[ℝ] F × (∀ k : J × Fin l, Y k.1) :=
  P.prod (ContinuousLinearMap.pi fun k : J × Fin l => C k.1 ∘L A ^ (k.2 : ℕ))

/-- `Π_i` and the divided differences of the samples as one map. -/
noncomputable def stackedDiff (P : E →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E) (H : ℝ)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) :
    E →L[ℝ] F × (∀ k : J × Fin l, Y k.1) :=
  P.prod (ContinuousLinearMap.pi fun k : J × Fin l => ddiff (C k.1) A H (x k.1) (W k.1) k.2)

/-- `c₁ = Σ_j Σ_{p<l} p! ‖C j‖ ω_p^j ‖A‖^{p+1}`: the divided differences are within `c₁ H` of the
derivatives. -/
noncomputable def kernelConst (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) (x : J → Fin l → ℝ)
    (W : J → Matrix (Fin l) (Fin l) ℝ) : ℝ :=
  ∑ j, ∑ p : Fin l, (p ! : ℝ) * ‖C j‖ * ddOmega (x j) (W j) l p * ‖A‖ ^ ((p : ℕ) + 1)

/-- The map `D = Σ_j γ_j L j C j A^l` of the leading term (the paper, eq. `eq:defectl`). -/
noncomputable def leadingMap (L : ∀ j, Y j →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E)
    (γ : J → ℝ) (l : ℕ) : E →L[ℝ] F :=
  ∑ j, γ j • (L j ∘L (C j ∘L A ^ l))

/-- The map of the leading term applied to a state. -/
theorem leadingMap_apply (L : ∀ j, Y j →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E)
    (γ : J → ℝ) (l : ℕ) (v : E) :
    leadingMap L C A γ l v = ∑ j, γ j • L j (C j ((A ^ l) v)) := by
  simp [leadingMap]

/-- A term of `c₁` is not negative. -/
theorem kernelTerm_nonneg (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) (x : J → Fin l → ℝ)
    (W : J → Matrix (Fin l) (Fin l) ℝ) (j : J) (p : Fin l) :
    0 ≤ (p ! : ℝ) * ‖C j‖ * ddOmega (x j) (W j) l p * ‖A‖ ^ ((p : ℕ) + 1) := by
  have := ddOmega_nonneg (x j) (W j) l p
  positivity

/-- `c₁ ≥ 0`. -/
theorem kernelConst_nonneg (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) (x : J → Fin l → ℝ)
    (W : J → Matrix (Fin l) (Fin l) ℝ) : 0 ≤ kernelConst A C x W :=
  sum_nonneg fun j _ => sum_nonneg fun p _ => kernelTerm_nonneg A C x W j p

/-- The states not shown: the own state and every sample at a node vanish. -/
theorem mem_notShown_nodeSample {P : E →L[ℝ] F} {C : ∀ j, E →L[ℝ] Y j} {A : E →L[ℝ] E}
    {H : ℝ} {x : J → Fin l → ℝ} {v : E} :
    v ∈ notShown P (nodeSample C A H x) ↔
      P v = 0 ∧ ∀ j q, C j (exp ((x j q * H) • A) v) = 0 := by
  rw [mem_notShown]
  exact and_congr Iff.rfl ⟨fun h j q => h (j, q), fun h k => h k.1 k.2⟩

/-- The stack of the derivatives vanishes iff the own state and the derivatives do. -/
theorem stackedDeriv_apply_eq_zero_iff {P : E →L[ℝ] F} {C : ∀ j, E →L[ℝ] Y j}
    {A : E →L[ℝ] E} {v : E} :
    stackedDeriv P C A l v = 0 ↔ P v = 0 ∧ ∀ j (p : Fin l), C j ((A ^ (p : ℕ)) v) = 0 := by
  unfold stackedDeriv
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero]
  refine and_congr Iff.rfl ⟨fun h j p => congrFun h (j, p), fun h => funext fun k => h k.1 k.2⟩

/-- **`𝒱^0` is the kernel of the stacked derivatives.** -/
theorem ker_stackedDeriv (P : E →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E) (l : ℕ) :
    unseen P (ContinuousLinearMap.pi C) A l =
      LinearMap.ker (stackedDeriv P C A l : E →ₗ[ℝ] F × (∀ k : J × Fin l, Y k.1)) := by
  ext v
  rw [mem_unseen, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, stackedDeriv_apply_eq_zero_iff]
  refine and_congr Iff.rfl ⟨fun h j p => congrFun (h p p.2) j, fun h q hq => funext fun j => ?_⟩
  exact h j ⟨q, hq⟩

/-- **The states not shown are the kernel of the stacked divided differences**, for a positive
macro step. -/
theorem ker_stackedDiff (P : E →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E)
    {x : J → Fin l → ℝ} {W : J → Matrix (Fin l) (Fin l) ℝ}
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1) {H : ℝ} (hH : 0 < H) :
    notShown P (nodeSample C A H x) =
      LinearMap.ker (stackedDiff P C A H x W : E →ₗ[ℝ] F × (∀ k : J × Fin l, Y k.1)) := by
  ext v
  rw [mem_notShown_nodeSample, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  unfold stackedDiff
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero]
  refine and_congr Iff.rfl ⟨fun h => funext fun k => ?_, fun h j => ?_⟩
  · exact (ddiff_apply_eq_zero_iff (C k.1) A hH (x k.1) (W k.1) k.2 v).2
      ((forall_ddComb_eq_zero_iff (hW k.1) (C k.1) A H v).2 (h k.1) k.2)
  · exact (forall_ddComb_eq_zero_iff (hW j) (C j) A H v).1 fun p =>
      (ddiff_apply_eq_zero_iff (C j) A hH (x j) (W j) p v).1 (congrFun h (j, p))

/-- `‖A‖^l H^{l-p} ≤ ‖A‖^{p+1} H` for `p < l` and `H ‖A‖ ≤ 1`. -/
theorem pow_mul_pow_sub_le {a H : ℝ} (ha : 0 ≤ a) (hH : 0 ≤ H) (hHa : H * a ≤ 1) {p l : ℕ}
    (hp : p < l) : a ^ l * H ^ (l - p) ≤ a ^ (p + 1) * H := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hp
  have h1 : p + d + 1 - p = d + 1 := by omega
  have h2 : a ^ (p + d + 1) * H ^ (d + 1) = a ^ (p + 1) * H * (H * a) ^ d := by ring
  rw [h1, h2]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (mul_nonneg hH ha) hHa)

/-- **The stacked divided differences are within `c₁ H` of the stacked derivatives** (the paper,
proof of Theorem `thm:memory` (i)), for `0 < H`, `H ‖A‖ ≤ 1`. -/
theorem norm_stackedDiff_sub_le (P : E →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E)
    {x : J → Fin l → ℝ} {W : J → Matrix (Fin l) (Fin l) ℝ}
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1) {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) :
    ‖stackedDiff P C A H x W - stackedDeriv P C A l‖ ≤ kernelConst A C x W * H := by
  have hk : 0 ≤ kernelConst A C x W := kernelConst_nonneg A C x W
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hk hH.le) fun v => ?_
  have hv : (stackedDiff P C A H x W - stackedDeriv P C A l) v =
      ((0 : F), fun k : J × Fin l =>
        (ddiff (C k.1) A H (x k.1) (W k.1) k.2 - C k.1 ∘L A ^ (k.2 : ℕ)) v) := by
    unfold stackedDiff stackedDeriv
    rw [_root_.sub_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply,
      Prod.mk_sub_mk, sub_self]
    rfl
  rw [hv, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _),
    pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hk hH.le) (norm_nonneg v))]
  intro k
  have h1 := norm_ddiff_sub_le (hW k.1) (C k.1) A hH hHA k.2
  have h2 := pow_mul_pow_sub_le (norm_nonneg A) hH.le hHA k.2.2
  have hω := ddOmega_nonneg (x k.1) (W k.1) l k.2
  have h3 : (k.2 ! : ℝ) * ‖C k.1‖ * ddOmega (x k.1) (W k.1) l k.2 * ‖A‖ ^ ((k.2 : ℕ) + 1) ≤
      kernelConst A C x W :=
    (single_le_sum (f := fun p : Fin l =>
        (p ! : ℝ) * ‖C k.1‖ * ddOmega (x k.1) (W k.1) l p * ‖A‖ ^ ((p : ℕ) + 1))
      (fun p _ => kernelTerm_nonneg A C x W k.1 p) (mem_univ k.2)).trans
    (single_le_sum (f := fun j : J => ∑ p : Fin l,
        (p ! : ℝ) * ‖C j‖ * ddOmega (x j) (W j) l p * ‖A‖ ^ ((p : ℕ) + 1))
      (fun j _ => sum_nonneg fun p _ => kernelTerm_nonneg A C x W j p) (mem_univ k.1))
  calc ‖(ddiff (C k.1) A H (x k.1) (W k.1) k.2 - C k.1 ∘L A ^ (k.2 : ℕ)) v‖
      ≤ ‖ddiff (C k.1) A H (x k.1) (W k.1) k.2 - C k.1 ∘L A ^ (k.2 : ℕ)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (k.2 ! : ℝ) * ‖C k.1‖ * ddOmega (x k.1) (W k.1) l k.2 * ‖A‖ ^ l *
          H ^ (l - (k.2 : ℕ)) * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
    _ = (k.2 ! : ℝ) * ‖C k.1‖ * ddOmega (x k.1) (W k.1) l k.2 *
          (‖A‖ ^ l * H ^ (l - (k.2 : ℕ))) * ‖v‖ := by ring
    _ ≤ (k.2 ! : ℝ) * ‖C k.1‖ * ddOmega (x k.1) (W k.1) l k.2 *
          (‖A‖ ^ ((k.2 : ℕ) + 1) * H) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity))
          (norm_nonneg v)
    _ = (k.2 ! : ℝ) * ‖C k.1‖ * ddOmega (x k.1) (W k.1) l k.2 * ‖A‖ ^ ((k.2 : ℕ) + 1) *
          H * ‖v‖ := by ring
    _ ≤ kernelConst A C x W * H * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hH.le) (norm_nonneg v)

variable {P : E →L[ℝ] F} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {C : ∀ j, E →L[ℝ] Y j}
  {L : ∀ j, Y j →L[ℝ] F} {x : J → Fin l → ℝ} {W : J → Matrix (Fin l) (Fin l) ℝ}

/-- **The leading value of the visibility bound for `l` samples at general nodes** (the paper,
Theorem `thm:memory` (i), eq. `eq:leading`). Let `P ∘ A = Ai ∘ P + Σ_j L j ∘ C j`, `‖P‖ ≤ 1`,
let partner `j` be sampled at the nodes `x j q`, `q < l`, with `W j` the inverse of their
Vandermonde matrix, and let the stack `N₀` of `P` and of the maps `C j A^p`, `p < l`, have the
right inverse `R` (independence). Then for `0 < H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`, `c₁ H ‖R‖ ≤ 1/2`

  `|f - H^{l+1} ‖D|𝒱^0‖| ≤ (c₂ + 4 ‖R‖ c₁ ‖D‖) H^{l+2}`,   `D = Σ_j γ_j L j C j A^l`,

`f` the visibility bound for the samples at the nodes, `γ_j = ddGamma (x j) (W j)`,
`𝒱^0 = unseen P (pi C) A l`, `c₁ = kernelConst`, `c₂ = defectConst`. -/
theorem leading_value_nodes (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1)
    {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C x W * H * ‖R‖ ≤ 1 / 2) :
    |visBound P (exp (H • A)) (nodeSample C A H x) -
        H ^ (l + 1) * restrNorm (leadingMap L C A (fun j => ddGamma (x j) (W j)) l)
          (unseen P (ContinuousLinearMap.pi C) A l)| ≤
      (defectConst A Ai C L x W + 4 * ‖R‖ * kernelConst A C x W *
        ‖leadingMap L C A (fun j => ddGamma (x j) (W j)) l‖) * H ^ (l + 2) := by
  refine leading_value_of_kernel P (exp (H • A)) (nodeSample C A H x) (ContinuousLinearMap.pi C)
    A l _ hH.le (defectConst_nonneg A Ai C L x W) (ker_stackedDiff P C A hW hH)
    (ker_stackedDeriv P C A l) hR (norm_stackedDiff_sub_le P C A hW hH hHA) hsmall
    fun v hv => ?_
  obtain ⟨hPv, hsv⟩ := mem_notShown_nodeSample.1 hv
  rw [leadingMap_apply]
  exact norm_proj_exp_sub_leading_le hA hP hW hH.le hHA hHAi hPv hsv

/-- **The upper bound needs no independence.** Under the hypotheses of `leading_value_nodes`
without the right inverse, for any generalised inverse `R` of the stack `N₀` of `P` and of the
maps `C j A^p`, `p < l` (`N₀ R N₀ = N₀`; one exists in finite dimension,
`exists_generalizedInverse`), and without a condition on `c₁ H ‖R‖`:

  `f ≤ H^{l+1} ‖D|𝒱^0‖ + (c₂ + 2 ‖R‖ c₁ ‖D‖) H^{l+2}`.

Where the maps are dependent the samples can show more than the derivatives, and the bound can
be smaller than the leading value, not larger. -/
theorem visBound_le_leading_nodes (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1)
    {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : ∀ v, stackedDeriv P C A l (R (stackedDeriv P C A l v)) = stackedDeriv P C A l v)
    {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1) :
    visBound P (exp (H • A)) (nodeSample C A H x) ≤
      H ^ (l + 1) * restrNorm (leadingMap L C A (fun j => ddGamma (x j) (W j)) l)
          (unseen P (ContinuousLinearMap.pi C) A l) +
        (defectConst A Ai C L x W + 2 * ‖R‖ * kernelConst A C x W *
          ‖leadingMap L C A (fun j => ddGamma (x j) (W j)) l‖) * H ^ (l + 2) := by
  set D := leadingMap L C A (fun j => ddGamma (x j) (W j)) l with hD
  have hHl : 0 ≤ H ^ (l + 1) := pow_nonneg hH.le _
  have h1 : |restrNorm (P ∘L exp (H • A)) (notShown P (nodeSample C A H x)) -
      restrNorm (H ^ (l + 1) • D) (notShown P (nodeSample C A H x))| ≤
      defectConst A Ai C L x W * H ^ (l + 2) :=
    abs_restrNorm_sub_le _ _ _ (mul_nonneg (defectConst_nonneg A Ai C L x W)
      (pow_nonneg hH.le _)) fun v hv => by
      obtain ⟨hPv, hsv⟩ := mem_notShown_nodeSample.1 hv
      rw [ContinuousLinearMap.comp_apply, _root_.smul_apply, hD, leadingMap_apply]
      exact norm_proj_exp_sub_leading_le hA hP hW hH.le hHA hHAi hPv hsv
  rw [restrNorm_smul D _ hHl, ← visBound_eq_restrNorm] at h1
  have h2 := restrNorm_ker_le_of_generalized hR (norm_stackedDiff_sub_le P C A hW hH hHA) D
  rw [← ker_stackedDiff P C A hW hH, ← ker_stackedDeriv] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hHl
  have h4 := (abs_le.1 h1).2
  have h5 : H ^ (l + 1) * (restrNorm D (unseen P (ContinuousLinearMap.pi C) A l) +
      2 * ‖R‖ * (kernelConst A C x W * H) * ‖D‖) + defectConst A Ai C L x W * H ^ (l + 2) =
      H ^ (l + 1) * restrNorm D (unseen P (ContinuousLinearMap.pi C) A l) +
        (defectConst A Ai C L x W + 2 * ‖R‖ * kernelConst A C x W * ‖D‖) * H ^ (l + 2) := by
    ring
  linarith

/-- On the states not shown up to the order `l` the map of the leading term with one constant
for all partners is `γ P A^{l+1}`: its restricted norm is `|γ| c_i`. -/
theorem restrNorm_leadingMap_const (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (γ₀ : ℝ) (l : ℕ) :
    restrNorm (leadingMap L C A (fun _ => γ₀) l) (unseen P (ContinuousLinearMap.pi C) A l) =
      |γ₀| * unseenRate P (ContinuousLinearMap.pi C) A l := by
  have hA' : P ∘L A = Ai ∘L P +
      (∑ j, L j ∘L ContinuousLinearMap.proj j) ∘L ContinuousLinearMap.pi C := by
    rw [hA]
    congr 1
    ext v
    simp
  have h : ∀ v ∈ unseen P (ContinuousLinearMap.pi C) A l,
      leadingMap L C A (fun _ => γ₀) l v = (γ₀ • (P ∘L (A ^ (l + 1)))) v := fun v hv => by
    have h0 : P ((A ^ l) v) = 0 := proj_pow_eq_zero hA' le_rfl hv
    rw [leadingMap_apply, ← smul_sum, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      proj_pow_succ_apply hA, h0, map_zero, zero_add]
  rw [restrNorm_congr _ _ _ h, restrNorm_smul_abs]
  rfl

/-- **The leading value if all samples are old or all are new** (the paper, Theorem `thm:memory`
(i), last line). If every partner is sampled at the nodes `σ - q`, `q < l`, then under the
hypotheses of `leading_value_nodes`

  `|f - |γ_l^σ| c_i H^{l+1}| ≤ (c₂ + 4 ‖R‖ c₁ ‖D‖) H^{l+2}`,   `D = γ_l^σ Σ_j L j C j A^l`,

with `c_i = unseenRate P (pi C) A l` and `γ_l^σ = schemeGamma σ l` (`adamsGamma l` for `σ = 0`,
`lateGamma l` for `σ = 1`). -/
theorem leading_value_uniform (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (σ : ℕ) {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C (fun _ : J => schemeNodes σ l) (fun _ => schemeWeights σ l) * H *
      ‖R‖ ≤ 1 / 2) :
    |visBound P (exp (H • A)) (nodeSample C A H fun _ : J => schemeNodes σ l) -
        |schemeGamma σ l| * unseenRate P (ContinuousLinearMap.pi C) A l * H ^ (l + 1)| ≤
      (defectConst A Ai C L (fun _ : J => schemeNodes σ l) (fun _ => schemeWeights σ l) +
        4 * ‖R‖ * kernelConst A C (fun _ : J => schemeNodes σ l) (fun _ => schemeWeights σ l) *
          ‖leadingMap L C A (fun _ => schemeGamma σ l) l‖) * H ^ (l + 2) := by
  have h := leading_value_nodes hA hP (x := fun _ : J => schemeNodes σ l)
    (W := fun _ => schemeWeights σ l) (fun _ => schemeWeights_mul σ l) hR hH hHA hHAi hsmall
  have h1 : (fun _ : J => ddGamma (schemeNodes σ l) (schemeWeights σ l)) =
      fun _ => schemeGamma σ l := rfl
  rw [h1, restrNorm_leadingMap_const hA] at h
  have h2 : |schemeGamma σ l| * unseenRate P (ContinuousLinearMap.pi C) A l * H ^ (l + 1) =
      H ^ (l + 1) * (|schemeGamma σ l| * unseenRate P (ContinuousLinearMap.pi C) A l) := by ring
  rw [h2]
  exact h

end Nodes

section Scheme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, CompleteSpace (Es i)]
  {Yo : ι → Type*} [∀ j, NormedAddCommGroup (Yo j)] [∀ j, NormedSpace ℝ (Yo j)]
  [∀ j, CompleteSpace (Yo j)]

/-- The flow between two communication points: `U^s U^{-q} = exp ((s - q) H A)`. -/
theorem exp_pow_mul_exp_neg_pow (A : E →L[ℝ] E) (H : ℝ) (s q : ℕ) :
    exp (H • A) ^ s * exp (-(H • A)) ^ q = exp ((((s : ℝ) - (q : ℝ)) * H) • A) := by
  let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  have h1 : exp (H • A) ^ s = exp (((s : ℝ) * H) • A) := by
    have h := exp_neg_smul_pow A (-H) s
    rw [neg_smul, neg_neg] at h
    rw [h]
    congr 2
    ring
  rw [h1, exp_neg_smul_pow,
    ← exp_add_of_commute ((Commute.refl A).smul_left _ |>.smul_right _), ← add_smul]
  congr 2
  ring

/-- **The states not shown to subsystem `i` of a scheme with `l` held samples** (Definition
`def:visibility`, `shownSample` with `U = exp (H A)`) are those of the samples of its partners at
the nodes `σ_ij - q`, `q < l`. -/
theorem notShown_shownSample_eq (Pr : ∀ i, E →L[ℝ] Es i) (c : ∀ j, Es j →L[ℝ] Yo j)
    (A : E →L[ℝ] E) (H : ℝ) (stage : ι → ℕ) (partner : ι → ι → Prop) [DecidableRel partner]
    (l : ℕ) (i : ι) :
    notShown (Pr i) (shownSample Pr c (exp (H • A)) (exp (-(H • A))) stage partner l i) =
      notShown (Pr i) (nodeSample (fun j : {j // partner i j} => c j ∘L Pr j) A H
        fun j => schemeNodes (newSample stage i j) l) := by
  have key : ∀ (j : ι) (q : Fin l) (v : E),
      exp ((schemeNodes (newSample stage i j) l q * H) • A) v =
        (exp (H • A) ^ newSample stage i j) ((exp (-(H • A)) ^ (q : ℕ)) v) := fun j q v => by
    unfold schemeNodes
    rw [← exp_pow_mul_exp_neg_pow]
    rfl
  ext v
  rw [mem_notShown_shownSample, mem_notShown_nodeSample]
  refine and_congr Iff.rfl ⟨fun h j q => ?_, fun h j hp r => ?_⟩
  · rw [ContinuousLinearMap.comp_apply, key]
    exact h j.1 j.2 q
  · have h1 := h ⟨j, hp⟩ r
    rw [ContinuousLinearMap.comp_apply, key] at h1
    exact h1

/-- **The leading value of the visibility bound of subsystem `i` in a scheme with `l` held
samples, in every order of execution** (the paper, Theorem `thm:memory` (i), eq. `eq:leading`).
Setting of `VisibilityConverse`: projections `Pr`, outputs `c j ∘ Pr j`, stages `stage`,
`σ_ij = newSample stage i j`, the monolithic step `U = exp (H A)`. Let
`Pr i ∘ A = Ai ∘ Pr i + Σ_{j ∈ 𝒫(i)} L j ∘ c j ∘ Pr j`, `‖Pr i‖ ≤ 1`, and let the stack `N₀` of
`Pr i` and of the maps `c j ∘ Pr j ∘ A^p`, `j ∈ 𝒫(i)`, `p < l`, have the right inverse `R`. Then
for `0 < H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`, `c₁ H ‖R‖ ≤ 1/2`

  `|f_i - H^{l+1} ‖D|𝒱_i^0‖| ≤ (c₂ + 4 ‖R‖ c₁ ‖D‖) H^{l+2}`,
  `D = Σ_{j ∈ 𝒫(i)} γ_l^{σ_ij} L j ∘ c j ∘ Pr j ∘ A^l`,

with `f_i` the visibility bound of Definition `def:visibility`, `γ_l^σ = schemeGamma σ l` and
`𝒱_i^0 = unseen` for the stacked outputs of the partners. -/
theorem leading_value_scheme (Pr : ∀ i, E →L[ℝ] Es i) (c : ∀ j, Es j →L[ℝ] Yo j)
    (A : E →L[ℝ] E) (stage : ι → ℕ) (partner : ι → ι → Prop) [DecidableRel partner] (l : ℕ)
    (i : ι) (Ai : Es i →L[ℝ] Es i) (L : ∀ j : {j // partner i j}, Yo j →L[ℝ] Es i)
    (hA : Pr i ∘L A = Ai ∘L Pr i + ∑ j : {j // partner i j}, L j ∘L (c j ∘L Pr j))
    (hP : ‖Pr i‖ ≤ 1)
    {R : Es i × (∀ k : {j // partner i j} × Fin l, Yo k.1) →L[ℝ] E}
    (hR : stackedDeriv (Pr i) (fun j : {j // partner i j} => c j ∘L Pr j) A l ∘L R =
      ContinuousLinearMap.id ℝ (Es i × (∀ k : {j // partner i j} × Fin l, Yo k.1)))
    {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A (fun j : {j // partner i j} => c j ∘L Pr j)
      (fun j => schemeNodes (newSample stage i j) l)
      (fun j => schemeWeights (newSample stage i j) l) * H * ‖R‖ ≤ 1 / 2) :
    |visBound (Pr i) (exp (H • A))
          (shownSample Pr c (exp (H • A)) (exp (-(H • A))) stage partner l i) -
        H ^ (l + 1) * restrNorm
          (leadingMap L (fun j : {j // partner i j} => c j ∘L Pr j) A
            (fun j => schemeGamma (newSample stage i j) l) l)
          (unseen (Pr i)
            (ContinuousLinearMap.pi fun j : {j // partner i j} => c j ∘L Pr j) A l)| ≤
      (defectConst A Ai (fun j : {j // partner i j} => c j ∘L Pr j) L
          (fun j => schemeNodes (newSample stage i j) l)
          (fun j => schemeWeights (newSample stage i j) l) +
        4 * ‖R‖ * kernelConst A (fun j : {j // partner i j} => c j ∘L Pr j)
          (fun j => schemeNodes (newSample stage i j) l)
          (fun j => schemeWeights (newSample stage i j) l) *
          ‖leadingMap L (fun j : {j // partner i j} => c j ∘L Pr j) A
            (fun j => schemeGamma (newSample stage i j) l) l‖) * H ^ (l + 2) := by
  have h := leading_value_nodes hA hP
    (x := fun j : {j // partner i j} => schemeNodes (newSample stage i j) l)
    (W := fun j => schemeWeights (newSample stage i j) l)
    (fun j => schemeWeights_mul (newSample stage i j) l) hR hH hHA hHAi hsmall
  rw [visBound_eq_restrNorm, notShown_shownSample_eq, ← visBound_eq_restrNorm]
  exact h

end Scheme

end CoSimFoundations
