/-
One held sample in every order of execution: the leading value of the visibility bound (the
paper; Theorem `thm:memory` (i) for `l = 1` with the independence
discharged).

**Statement.** For one held sample, in every order of execution,

  `f_i = (1/2) H² ‖Π_i A_σ A | 𝒱_i^0‖ + O(H³)`,   `𝒱_i^0 = {v : Π_i v = 0, C_j v = 0, j ∈ 𝒫(i)}`,

where `A_σ` is the coupling with the block `(i, k)` multiplied by `σ_ik = +1` if `k` runs at an
earlier stage than `i` and `-1` otherwise.

**Lean form.** Setting of `LeadingValueScheme`: `P ∘ A = Ai ∘ P + Σ_j L j ∘ C j`, `‖P‖ ≤ 1`, the
partners `j ∈ J`; `σ j ∈ {0, 1}` says whether the sample of `j` is the old one (`0`) or the new
one (`1`). The block row `i` of `A_σ` is `signedRow L C σ = Σ_j (2 σ_j - 1) L j ∘ C j`
(`stageSign`). With `γ_1^σ = 1/2 - σ` (`ddGamma_fin_one`) the map of the leading term of
`leading_value_nodes` is `-(1/2) signedRow ∘ A` (`leadingMap_one`).

* `leading_value_one_nodes`: if the stack of `P` and of the `C j` has a right inverse `R`,
  `‖R‖ ≤ ρ`, then for `0 < H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`, `(e - 1) ‖A‖ κ H ρ ≤ 1/2`,

    `|f - (H²/2) ‖signedRow ∘ A | 𝒱^0‖| ≤ c H³`,
    `c = (e - 2) Λ ‖A‖² + (e - 1)² ‖Ai‖ Λ ‖A‖ + (e - 5/2) ‖A‖³ + 2 (e - 1) ρ κ Λ ‖A‖²`,

  `Λ = Σ_j ‖L j‖ ‖C j‖`, `κ = Σ_j ‖C j‖` (`oneConst`). The constants of `leading_value_nodes`
  are evaluated for `l = 1` (`kernelConst_one_le`, `defectConst_one_le`).
* `exists_rightInverse_stackedDeriv_one`: **independence from surjective outputs.** If there are
  maps `I₀ : F → E` and `Ij j : Y j → E` with `P I₀ = 1`, `P Ij j = 0`, `C j I₀ = 0`,
  `C j Ij j = 1`, `C k Ij j = 0` (`j ≠ k`), then `R = I₀ ∘ fst + Σ_j Ij j ∘ (·)_j` is a right
  inverse of the stack with `‖R‖ ≤ ‖I₀‖ + Σ_j ‖Ij j‖`.
* `leading_value_one` (**the scheme of `VisibilityConverse`**, `f_i = visBound (Pr i) U
  (shownSample Pr c U Ui stage partner 1 i)`, `U = exp (H A)`): the outputs are
  `C_j = c j ∘ Pr j`; the state is the collection of the states of the subsystems, in the form of
  injections `In j : Es j → E` with `Pr j ∘ In j = 1` and `Pr k ∘ In j = 0` for `j ≠ k`; every
  output map `c j` of a partner has a bounded right inverse `r j`; and `i` is not its own partner.
  Then the conclusion of `leading_value_one_nodes` holds with `ρ = ‖In i‖ + Σ_j ‖In j ∘ r j‖` and
  `σ_j = newSample stage i j`.

**What remains a hypothesis:** the coupling row `hA`, `‖Pr i‖ ≤ 1`, the injections `In`, the
right inverses `r j` of the output maps of the partners (surjectivity of each `c j`), `i` not a
partner of itself, and the explicit smallness of `H`. Independence of the stacked maps is proved.
-/
import CoSimFoundations.LeadingValueScheme

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section FinOne

/-- The Vandermonde matrix of one node is the unit. -/
theorem vandermonde_fin_one (x : Fin 1 → ℝ) : Matrix.vandermonde x = 1 := by
  ext p q
  rw [Matrix.vandermonde_apply, Subsingleton.elim p q, Subsingleton.elim q 0]
  simp

/-- The unit is the inverse of the Vandermonde matrix of one node. -/
theorem one_mul_vandermonde_fin_one (x : Fin 1 → ℝ) :
    (1 : Matrix (Fin 1) (Fin 1) ℝ) * Matrix.vandermonde x = 1 := by
  rw [vandermonde_fin_one, one_mul]

/-- One node: `ω^b = Σ_{n≥b} |x|^n / n!`. -/
theorem ddOmega_fin_one (x : Fin 1 → ℝ) (b : ℕ) (p : Fin 1) :
    ddOmega x 1 b p = expTail b |x 0| := by
  obtain rfl : p = 0 := Subsingleton.elim _ _
  simp [ddOmega]

/-- One node: `β_0 = x`. -/
theorem ddBeta_fin_one (x : Fin 1 → ℝ) (p : Fin 1) : ddBeta x 1 p = x 0 := by
  obtain rfl : p = 0 := Subsingleton.elim _ _
  simp [ddBeta]

/-- One node: `γ = 1/2 - x`, which is `1/2` for the old sample and `-1/2` for the new one. -/
theorem ddGamma_fin_one (x : Fin 1 → ℝ) : ddGamma x 1 = 1 / 2 - x 0 := by
  unfold ddGamma
  rw [Fin.sum_univ_one, ddBeta_fin_one]
  norm_num

/-- The node of one held sample is `σ`. -/
theorem schemeNodes_one (σ : ℕ) : schemeNodes σ 1 0 = (σ : ℝ) := by
  simp [schemeNodes]

/-- The tail at the node `σ ∈ {0, 1}` is at most the tail at `1`. -/
theorem expTail_cast_le {b : ℕ} (hb : 0 < b) {σ : ℕ} (hσ : σ ≤ 1) :
    expTail b |(σ : ℝ)| ≤ expTail b 1 := by
  interval_cases σ
  · rw [Nat.cast_zero, abs_zero, expTail_zero hb]
    exact expTail_nonneg b zero_le_one
  · rw [Nat.cast_one, abs_one]

end FinOne

section Nodes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {J : Type*} [Fintype J] {Y : J → Type*} [∀ j, NormedAddCommGroup (Y j)]
  [∀ j, NormedSpace ℝ (Y j)] [∀ j, CompleteSpace (Y j)]

/-- `σ_ik` of the paper as a number: `+1` for the new sample (`σ = 1`), `-1` for the old one
(`σ = 0`). -/
def stageSign (σ : ℕ) : ℝ := 2 * (σ : ℝ) - 1

/-- The block row `i` of the signed coupling `A_σ`: `Σ_j σ_ij L j ∘ C j`. -/
noncomputable def signedRow (L : ∀ j, Y j →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (σ : J → ℕ) :
    E →L[ℝ] F :=
  ∑ j, stageSign (σ j) • (L j ∘L C j)

/-- The constant of the remainder for one held sample, in terms of `a = ‖A‖`, `ai = ‖Ai‖`,
`Λ = Σ_j ‖L j‖ ‖C j‖`, `κ = Σ_j ‖C j‖` and the bound `ρ` of the right inverse. -/
noncomputable def oneConst (a ai Λ κ ρ : ℝ) : ℝ :=
  (Real.exp 1 - 2) * Λ * a ^ 2 + (Real.exp 1 - 1) ^ 2 * ai * Λ * a +
    (Real.exp 1 - 5 / 2) * a ^ 3 + 2 * (Real.exp 1 - 1) * ρ * κ * Λ * a ^ 2

variable {P : E →L[ℝ] F} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {C : ∀ j, E →L[ℝ] Y j}
  {L : ∀ j, Y j →L[ℝ] F}

/-- **The map of the leading term for one held sample** is `-(1/2) Π_i A_σ A`. -/
theorem leadingMap_one (L : ∀ j, Y j →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E)
    (σ : J → ℕ) :
    leadingMap L C A (fun j => ddGamma (schemeNodes (σ j) 1) 1) 1 =
      (-(1 / 2) : ℝ) • (signedRow L C σ ∘L A) := by
  ext v
  rw [leadingMap_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply]
  unfold signedRow
  rw [_root_.sum_apply, smul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [ddGamma_fin_one, schemeNodes_one, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    smul_smul, pow_one]
  congr 1
  unfold stageSign
  ring

/-- `c₁ ≤ (e - 1) ‖A‖ Σ_j ‖C j‖` for one held sample. -/
theorem kernelConst_one_le (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) {σ : J → ℕ}
    (hσ : ∀ j, σ j ≤ 1) :
    kernelConst A C (fun j => schemeNodes (σ j) 1) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) ≤
      (Real.exp 1 - 1) * ‖A‖ * ∑ j, ‖C j‖ := by
  unfold kernelConst
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [Fin.sum_univ_one, ddOmega_fin_one]
  simp only [schemeNodes_one]
  have h := expTail_cast_le one_pos (hσ j)
  rw [expTail_one_one] at h
  have h0 : 0 ≤ ‖C j‖ * ‖A‖ := by positivity
  have h1 := mul_le_mul_of_nonneg_right h h0
  simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_one]
  nlinarith

/-- `c₂ ≤ (e - 2) Λ ‖A‖² + (e - 1)² ‖Ai‖ Λ ‖A‖ + (e - 5/2) ‖A‖³` for one held sample. -/
theorem defectConst_one_le (A : E →L[ℝ] E) (Ai : F →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) {σ : J → ℕ} (hσ : ∀ j, σ j ≤ 1) :
    defectConst A Ai C L (fun j => schemeNodes (σ j) 1)
        (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) ≤
      (Real.exp 1 - 2) * (∑ j, ‖L j‖ * ‖C j‖) * ‖A‖ ^ 2 +
        (Real.exp 1 - 1) ^ 2 * ‖Ai‖ * (∑ j, ‖L j‖ * ‖C j‖) * ‖A‖ +
          (Real.exp 1 - 5 / 2) * ‖A‖ ^ 3 := by
  have he : (1 : ℝ) ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hΘ : defectTheta C L (fun j => schemeNodes (σ j) 1)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) ≤
      (Real.exp 1 - 1) * ∑ j, ‖L j‖ * ‖C j‖ := by
    unfold defectTheta
    rw [Fin.sum_univ_one, mul_sum]
    refine sum_le_sum fun j _ => ?_
    rw [ddOmega_fin_one, ddBeta_fin_one]
    simp only [schemeNodes_one]
    have h := expTail_cast_le (b := 1 + 1) (by norm_num) (hσ j)
    rw [show (1 : ℕ) + 1 = 2 from rfl, expTail_two_one] at h
    have h1 : |(σ j : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hσ j
    have h0 : 0 ≤ ‖L j‖ * ‖C j‖ := by positivity
    simp only [Fin.val_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, one_mul,
      div_one]
    rw [show (1 : ℕ) + 1 = 2 from rfl]
    nlinarith
  have hΩ : defectOmega C L (fun j => schemeNodes (σ j) 1)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) ≤
      (Real.exp 1 - 2) * ∑ j, ‖L j‖ * ‖C j‖ := by
    unfold defectOmega
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    rw [Fin.sum_univ_one, ddOmega_fin_one]
    simp only [schemeNodes_one]
    have h := expTail_cast_le (b := 1 + 1) (by norm_num) (hσ j)
    rw [show (1 : ℕ) + 1 = 2 from rfl, expTail_two_one] at h
    have h0 : 0 ≤ ‖L j‖ * ‖C j‖ := by positivity
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, div_one]
    rw [show (1 : ℕ) + 1 = 2 from rfl]
    nlinarith
  have hΘ0 := defectTheta_nonneg C L (fun j => schemeNodes (σ j) 1)
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
  unfold defectConst
  rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl, expTail_three_one, pow_one]
  have h1 : defectOmega C L (fun j => schemeNodes (σ j) 1)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) * ‖A‖ ^ 2 ≤
      (Real.exp 1 - 2) * (∑ j, ‖L j‖ * ‖C j‖) * ‖A‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hΩ (by positivity)
  have h2 : (Real.exp 1 - 1) * ‖Ai‖ * defectTheta C L (fun j => schemeNodes (σ j) 1)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) * ‖A‖ ≤
      (Real.exp 1 - 1) * ‖Ai‖ * ((Real.exp 1 - 1) * ∑ j, ‖L j‖ * ‖C j‖) * ‖A‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΘ (by positivity)) (norm_nonneg A)
  nlinarith

/-- `‖Π_i A_σ‖ ≤ Σ_j ‖L j‖ ‖C j‖` for one held sample. -/
theorem norm_signedRow_le (L : ∀ j, Y j →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) {σ : J → ℕ}
    (hσ : ∀ j, σ j ≤ 1) : ‖signedRow L C σ‖ ≤ ∑ j, ‖L j‖ * ‖C j‖ := by
  unfold signedRow
  refine norm_sum_le_of_le _ fun j _ => ?_
  have h1 : |stageSign (σ j)| = 1 := by
    unfold stageSign
    have := hσ j
    interval_cases (σ j) <;> norm_num
  rw [norm_smul, Real.norm_eq_abs, h1, one_mul]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- **The leading value of the visibility bound for one held sample, in every order of
execution**. Let `P ∘ A = Ai ∘ P + Σ_j L j ∘ C j`, `‖P‖ ≤ 1`, let the sample of
partner `j` be the old one (`σ j = 0`) or the new one (`σ j = 1`), and let the stack of `P` and
of the outputs `C j` have a right inverse `R` with `‖R‖ ≤ ρ`. Then for `0 < H`, `H ‖A‖ ≤ 1`,
`H ‖Ai‖ ≤ 1`, `(e - 1) ‖A‖ (Σ_j ‖C j‖) H ρ ≤ 1/2`

  `|f - (H²/2) ‖Π_i A_σ A | 𝒱^0‖| ≤ c H³`,

`Π_i A_σ = signedRow L C σ`, `𝒱^0 = {P v = 0, C j v = 0}`, `c = oneConst`. -/
theorem leading_value_one_nodes (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (σ : J → ℕ) (hσ : ∀ j, σ j ≤ 1) {R : F × (∀ k : J × Fin 1, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A 1 ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin 1, Y k.1)))
    {ρ : ℝ} (hρ : ‖R‖ ≤ ρ) {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : (Real.exp 1 - 1) * ‖A‖ * (∑ j, ‖C j‖) * H * ρ ≤ 1 / 2) :
    |visBound P (exp (H • A)) (nodeSample C A H fun j => schemeNodes (σ j) 1) -
        H ^ 2 / 2 * restrNorm (signedRow L C σ ∘L A)
          (unseen P (ContinuousLinearMap.pi C) A 1)| ≤
      oneConst ‖A‖ ‖Ai‖ (∑ j, ‖L j‖ * ‖C j‖) (∑ j, ‖C j‖) ρ * H ^ 3 := by
  have he : (0 : ℝ) ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hκ : 0 ≤ ∑ j, ‖C j‖ := sum_nonneg fun j _ => norm_nonneg _
  have hΛ : 0 ≤ ∑ j, ‖L j‖ * ‖C j‖ := sum_nonneg fun j _ => by positivity
  have hk := kernelConst_one_le A C hσ
  have hk0 := kernelConst_nonneg A C (fun j => schemeNodes (σ j) 1)
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg R
  have hρ0 : 0 ≤ ρ := hR0.trans hρ
  have hsmall' : kernelConst A C (fun j => schemeNodes (σ j) 1)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) * H * ‖R‖ ≤ 1 / 2 := by
    refine le_trans ?_ hsmall
    exact mul_le_mul (mul_le_mul_of_nonneg_right hk hH.le) hρ hR0
      (by positivity)
  have h := leading_value_nodes hA hP (x := fun j => schemeNodes (σ j) 1)
    (W := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (fun j => one_mul_vandermonde_fin_one _) hR hH hHA hHAi hsmall'
  rw [leadingMap_one, restrNorm_smul_abs, norm_smul, Real.norm_eq_abs] at h
  have habs : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
  rw [habs] at h
  have h1 : H ^ 2 / 2 * restrNorm (signedRow L C σ ∘L A)
      (unseen P (ContinuousLinearMap.pi C) A 1) =
      H ^ (1 + 1) * (1 / 2 * restrNorm (signedRow L C σ ∘L A)
        (unseen P (ContinuousLinearMap.pi C) A 1)) := by
    ring
  rw [h1]
  refine h.trans ?_
  rw [show (1 : ℕ) + 2 = 3 from rfl]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hd := defectConst_one_le A Ai C L hσ
  have hS : ‖signedRow L C σ ∘L A‖ ≤ (∑ j, ‖L j‖ * ‖C j‖) * ‖A‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_signedRow_le L C hσ) (norm_nonneg A))
  have h2 : 4 * ‖R‖ * kernelConst A C (fun j => schemeNodes (σ j) 1)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (1 / 2 * ‖signedRow L C σ ∘L A‖) ≤
      4 * ρ * ((Real.exp 1 - 1) * ‖A‖ * ∑ j, ‖C j‖) *
        (1 / 2 * ((∑ j, ‖L j‖ * ‖C j‖) * ‖A‖)) := by
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hρ (by norm_num)) hk hk0
      (by positivity)) (mul_le_mul_of_nonneg_left hS (by norm_num)) (by positivity)
      (by positivity)
  unfold oneConst
  nlinarith

end Nodes

section RightInverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {J : Type*} [Fintype J] {Y : J → Type*} [∀ j, NormedAddCommGroup (Y j)]
  [∀ j, NormedSpace ℝ (Y j)]

/-- **Independence from surjective outputs.** If `I₀ : F → E` and `Ij j : Y j → E` are dual to
`P` and the outputs `C j` (`P I₀ = 1`, `P Ij j = 0`, `C j I₀ = 0`, `C j Ij j = 1`, `C k Ij j = 0`
for `j ≠ k`), the stack of `P` and of the `C j` has the right inverse
`R (a, y) = I₀ a + Σ_j Ij j y_j`, of norm at most `‖I₀‖ + Σ_j ‖Ij j‖`. -/
theorem exists_rightInverse_stackedDeriv_one (P : E →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (A : E →L[ℝ] E) (I₀ : F →L[ℝ] E) (Ij : ∀ j, Y j →L[ℝ] E)
    (h1 : ∀ a, P (I₀ a) = a) (h2 : ∀ j y, P (Ij j y) = 0) (h3 : ∀ j a, C j (I₀ a) = 0)
    (h4 : ∀ j y, C j (Ij j y) = y) (h5 : ∀ j k, j ≠ k → ∀ y, C k (Ij j y) = 0) :
    ∃ R : F × (∀ k : J × Fin 1, Y k.1) →L[ℝ] E,
      stackedDeriv P C A 1 ∘L R =
          ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin 1, Y k.1)) ∧
        ‖R‖ ≤ ‖I₀‖ + ∑ j, ‖Ij j‖ := by
  classical
  set R : F × (∀ k : J × Fin 1, Y k.1) →L[ℝ] E :=
    I₀ ∘L ContinuousLinearMap.fst ℝ F (∀ k : J × Fin 1, Y k.1) +
      ∑ j, Ij j ∘L ((ContinuousLinearMap.proj (j, 0) : (∀ k : J × Fin 1, Y k.1) →L[ℝ] Y j) ∘L
        ContinuousLinearMap.snd ℝ F (∀ k : J × Fin 1, Y k.1)) with hRdef
  have hRw : ∀ w : F × (∀ k : J × Fin 1, Y k.1), R w = I₀ w.1 + ∑ j, Ij j (w.2 (j, 0)) :=
    fun w => by
      rw [hRdef]
      simp
  refine ⟨R, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    unfold stackedDeriv
    rw [ContinuousLinearMap.prod_apply, hRw]
    refine Prod.ext ?_ (funext fun k => ?_)
    · change P (I₀ w.1 + ∑ j, Ij j (w.2 (j, 0))) = w.1
      rw [map_add, map_sum, h1, sum_eq_zero fun j _ => h2 j _, add_zero]
    · obtain ⟨j, q⟩ := k
      obtain rfl : q = 0 := Subsingleton.elim _ _
      change C j ((A ^ ((0 : Fin 1) : ℕ)) (I₀ w.1 + ∑ j', Ij j' (w.2 (j', 0)))) = w.2 (j, 0)
      have hA0 : ∀ v : E, (A ^ ((0 : Fin 1) : ℕ)) v = v := fun v => by simp
      rw [hA0, map_add, map_sum, h3, zero_add, sum_eq_single j, h4]
      · intro j' _ hj'
        exact h5 j' j hj' _
      · intro hj
        exact absurd (mem_univ j) hj
  · refine ContinuousLinearMap.opNorm_le_bound _
      (add_nonneg (norm_nonneg _) (sum_nonneg fun j _ => norm_nonneg _)) fun w => ?_
    rw [hRw, add_mul, sum_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (I₀.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le w) (norm_nonneg _))
    · refine norm_sum_le_of_le _ fun j _ => ?_
      exact ((Ij j).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm w.2 (j, 0)).trans (norm_snd_le w)) (norm_nonneg _))

end RightInverse

section Scheme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, CompleteSpace (Es i)]
  {Yo : ι → Type*} [∀ j, NormedAddCommGroup (Yo j)] [∀ j, NormedSpace ℝ (Yo j)]
  [∀ j, CompleteSpace (Yo j)]

/-- **One held sample, every order of execution**, for the scheme of
`VisibilityConverse`. Let `Pr i ∘ A = Ai ∘ Pr i + Σ_{j ∈ 𝒫(i)} L j ∘ c j ∘ Pr j`, `‖Pr i‖ ≤ 1`,
let the state be the collection of the states of the subsystems (injections `In j` with
`Pr j ∘ In j = 1`, `Pr k ∘ In j = 0` for `j ≠ k`), let every output map `c j` of a partner have a
right inverse `r j`, and let `i` not be its own partner. With
`ρ = ‖In i‖ + Σ_{j ∈ 𝒫(i)} ‖In j ∘ r j‖`, `κ = Σ_j ‖c j ∘ Pr j‖`, `Λ = Σ_j ‖L j‖ ‖c j ∘ Pr j‖`,
for `0 < H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`, `(e - 1) ‖A‖ κ H ρ ≤ 1/2`:

  `|f_i - (H²/2) ‖Π_i A_σ A | 𝒱_i^0‖| ≤ oneConst ‖A‖ ‖Ai‖ Λ κ ρ · H³`,

`f_i` the visibility bound of Definition `def:visibility` for one held sample,
`Π_i A_σ = Σ_j σ_ij L j ∘ c j ∘ Pr j` with `σ_ij = +1` if `j` runs at an earlier stage than `i`
and `-1` otherwise, `𝒱_i^0 = {Pr i v = 0, c j (Pr j v) = 0 for the partners j}`. -/
theorem leading_value_one (Pr : ∀ i, E →L[ℝ] Es i) (c : ∀ j, Es j →L[ℝ] Yo j)
    (A : E →L[ℝ] E) (stage : ι → ℕ) (partner : ι → ι → Prop) [DecidableRel partner]
    (i : ι) (Ai : Es i →L[ℝ] Es i) (L : ∀ j : {j // partner i j}, Yo j →L[ℝ] Es i)
    (hA : Pr i ∘L A = Ai ∘L Pr i + ∑ j : {j // partner i j}, L j ∘L (c j ∘L Pr j))
    (hP : ‖Pr i‖ ≤ 1) (In : ∀ j, Es j →L[ℝ] E) (hIn : ∀ j a, Pr j (In j a) = a)
    (hIn0 : ∀ j k, j ≠ k → ∀ a, Pr k (In j a) = 0)
    (r : ∀ j : {j // partner i j}, Yo j →L[ℝ] Es j)
    (hr : ∀ (j : {j // partner i j}) y, c j (r j y) = y)
    (hii : ¬ partner i i) {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : (Real.exp 1 - 1) * ‖A‖ * (∑ j : {j // partner i j}, ‖c j ∘L Pr j‖) * H *
      (‖In i‖ + ∑ j : {j // partner i j}, ‖In j ∘L r j‖) ≤ 1 / 2) :
    |visBound (Pr i) (exp (H • A))
          (shownSample Pr c (exp (H • A)) (exp (-(H • A))) stage partner 1 i) -
        H ^ 2 / 2 * restrNorm
          (signedRow L (fun j : {j // partner i j} => c j ∘L Pr j)
            (fun j => newSample stage i j) ∘L A)
          (unseen (Pr i)
            (ContinuousLinearMap.pi fun j : {j // partner i j} => c j ∘L Pr j) A 1)| ≤
      oneConst ‖A‖ ‖Ai‖ (∑ j : {j // partner i j}, ‖L j‖ * ‖c j ∘L Pr j‖)
        (∑ j : {j // partner i j}, ‖c j ∘L Pr j‖)
        (‖In i‖ + ∑ j : {j // partner i j}, ‖In j ∘L r j‖) * H ^ 3 := by
  have hne : ∀ j : {j // partner i j}, (j : ι) ≠ i := fun j hj => hii (by
    have h := j.2
    rwa [hj] at h)
  obtain ⟨R, hR, hRn⟩ := exists_rightInverse_stackedDeriv_one (Pr i)
    (fun j : {j // partner i j} => c j ∘L Pr j) A (In i)
    (fun j : {j // partner i j} => In j ∘L r j) (hIn i)
    (fun j y => hIn0 j i (hne j) _)
    (fun j a => by
      change c j (Pr j (In i a)) = 0
      rw [hIn0 i j (hne j).symm, map_zero])
    (fun j y => by
      change c j (Pr j (In j (r j y))) = y
      rw [hIn, hr])
    (fun j k hjk y => by
      change c k (Pr k (In j (r j y))) = 0
      rw [hIn0 j k (fun h => hjk (Subtype.ext h)), map_zero])
  have hσ : ∀ j : {j // partner i j}, newSample stage i j ≤ 1 := fun j => by
    unfold newSample
    split_ifs <;> norm_num
  have h := leading_value_one_nodes hA hP (fun j : {j // partner i j} => newSample stage i j)
    hσ hR hRn hH hHA hHAi hsmall
  rw [visBound_eq_restrNorm, notShown_shownSample_eq, ← visBound_eq_restrNorm]
  exact h

/-- The states not shown to first order for one held sample:
`𝒱_i^0 = {v : Pr i v = 0, c j (Pr j v) = 0 for every partner j}`. -/
theorem mem_unseen_one (Pr : ∀ i, E →L[ℝ] Es i) (c : ∀ j, Es j →L[ℝ] Yo j) (A : E →L[ℝ] E)
    (partner : ι → ι → Prop) [DecidableRel partner] (i : ι) (v : E) :
    v ∈ unseen (Pr i) (ContinuousLinearMap.pi fun j : {j // partner i j} => c j ∘L Pr j) A 1 ↔
      Pr i v = 0 ∧ ∀ j, partner i j → c j (Pr j v) = 0 := by
  rw [mem_unseen]
  refine and_congr Iff.rfl ⟨fun h j hj => ?_, fun h q hq => ?_⟩
  · have h1 := congrFun (h 0 one_pos) ⟨j, hj⟩
    simpa using h1
  · obtain rfl : q = 0 := by omega
    funext j
    simpa using h j.1 j.2

end Scheme

end CoSimFoundations
