/-
The block row of the monolithic step on the states not shown, to leading order (the paper,
Theorem `thm:memory` (i), proof: "`f_i` is the norm on `𝒱_i` of the defect of polynomial
extrapolation, which is `H^{l+1} D + O(H^{l+2})`", `D = Σ_j γ_l^{σ_ij} A_ij Π_j A^l`, eq.
`eq:defectl`).

**Setting.** `P : E → F` the projection onto subsystem `i`, `‖P‖ ≤ 1`; the partners `j ∈ J` with
outputs `C j : E → Y j` and input maps `L j : Y j → F`,

  `P ∘ A = Ai ∘ P + Σ_j L j ∘ C j`        (`Π_i A = A_i Π_i + Σ_j A_ij Π_j`, `A_ij Π_j = L j C j`).

The samples of partner `j` are those at the nodes `x j q`, `q < l` (the paper's `σ_ij - q`):
`C j ∘ exp (x j q H A)`; `W j` is the inverse of the Vandermonde matrix of the nodes of `j`.

**Statement** (`norm_proj_exp_sub_leading_le`). For a state `v` with `P v = 0` all of whose
samples vanish, `0 ≤ H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`,

  `‖P U v - H^{l+1} Σ_j γ_j L j C j A^l v‖ ≤ c₂ H^{l+2} ‖v‖`,   `U = exp (H A)`,
  `c₂ = Ω ‖A‖^{l+1} + (e - 1) ‖Ai‖ Θ ‖A‖^l + ε_{l+2} ‖A‖^{l+2}`   (`defectConst`),

with `γ_j = ddGamma (x j) (W j) = (1/l!) ∫₀¹ ∏_q (s - x j q) ds` (the paper's `γ_l^{σ_ij}`),
`Ω = Σ_j ‖L j‖ ‖C j‖ Σ_p ω_p^j/(p+1)` (`defectOmega`),
`Θ = Σ_p p! Σ_j ‖L j‖ ‖C j‖ (|β_p^j|/l! + ω_p^j)` (`defectTheta`), `ε_b = Σ_{n≥b} 1/n!`.
This is the statement about the defect of polynomial extrapolation restricted to the states not
shown, where the defect of every rule is `P U v`; no rule is constructed.

**Proof.** `P A^{m+1} v = Ai P A^m v + Σ_j L j C j A^m v` (`proj_pow_succ_apply`). By
`DividedDifference`, the vanishing samples give `‖H^m C j A^m v‖ = O((H ‖A‖)^l)` for `m < l`,
hence by induction `‖H^m P A^m v‖ ≤ Θ H (H ‖A‖)^l ‖v‖` for `m ≤ l`
(`norm_pow_smul_proj_le`). In the Taylor polynomial of `P U v` of degree `l + 1`,

  `Σ_{m≤l} H^{m+1}/(m+1)! (Ai P A^m v + Σ_j L j C j A^m v)`,

the first part is therefore `O(H^{l+2})`, and the second is the mean of the signals of the
partners over the macro step, `γ_j H^{l+1} C j A^l v + O(H^{l+2})` (`dd_mean`).
-/
import CoSimFoundations.DividedDifference
import CoSimFoundations.MemoryLead

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Constants

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {J : Type*} [Fintype J] {Y : J → Type*} [∀ j, NormedAddCommGroup (Y j)]
  [∀ j, NormedSpace ℝ (Y j)] {l : ℕ}

/-- `Θ = Σ_{p<l} p! Σ_j ‖L j‖ ‖C j‖ (|β_p^j|/l! + ω_p^j)`: the constant in the bound of
`H^m P A^m v` on the states not shown. -/
noncomputable def defectTheta (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : ℝ :=
  ∑ p : Fin l, ∑ j, ‖L j‖ * ((p ! : ℝ) * ‖C j‖ *
    (|ddBeta (x j) (W j) p| / (l ! : ℝ) + ddOmega (x j) (W j) (l + 1) p))

/-- `Ω = Σ_j ‖L j‖ ‖C j‖ Σ_{p<l} ω_p^j/(p+1)`: the constant of the remainder of the means. -/
noncomputable def defectOmega (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : ℝ :=
  ∑ j, ‖L j‖ * ((∑ p : Fin l, ddOmega (x j) (W j) (l + 1) p / ((p : ℝ) + 1)) * ‖C j‖)

/-- `c₂ = Ω ‖A‖^{l+1} + (e - 1) ‖Ai‖ Θ ‖A‖^l + ε_{l+2} ‖A‖^{l+2}`: the constant of the remainder
of the block row on the states not shown. -/
noncomputable def defectConst (A : E →L[ℝ] E) (Ai : F →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : ℝ :=
  defectOmega C L x W * ‖A‖ ^ (l + 1) +
    (Real.exp 1 - 1) * ‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l + expTail (l + 2) 1 * ‖A‖ ^ (l + 2)

/-- `Θ ≥ 0`. -/
theorem defectTheta_nonneg (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : 0 ≤ defectTheta C L x W :=
  sum_nonneg fun p _ => sum_nonneg fun j _ => by
    have := ddOmega_nonneg (x j) (W j) (l + 1) p
    positivity

/-- `Ω ≥ 0`. -/
theorem defectOmega_nonneg (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : 0 ≤ defectOmega C L x W :=
  sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (mul_nonneg
    (sum_nonneg fun p _ => div_nonneg (ddOmega_nonneg (x j) (W j) (l + 1) p) (by positivity))
    (norm_nonneg _))

/-- `c₂ ≥ 0`. -/
theorem defectConst_nonneg (A : E →L[ℝ] E) (Ai : F →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j)
    (L : ∀ j, Y j →L[ℝ] F) (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) :
    0 ≤ defectConst A Ai C L x W := by
  have h1 := defectTheta_nonneg C L x W
  have h2 := defectOmega_nonneg C L x W
  have h3 : (0 : ℝ) ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h4 := expTail_nonneg (l + 2) (zero_le_one : (0 : ℝ) ≤ 1)
  unfold defectConst
  positivity

/-- `Σ_{m≤l} 1/(m+1)! ≤ e - 1`. -/
theorem sum_inv_factorial_succ_le (l : ℕ) :
    ∑ m ∈ range (l + 1), (((m + 1) ! : ℝ))⁻¹ ≤ Real.exp 1 - 1 := by
  have h := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) (l + 2)
  rw [sum_range_succ'] at h
  simp only [one_pow, one_div, Nat.factorial_zero, Nat.cast_one, inv_one] at h
  linarith

end Constants

section Defect

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {J : Type*} [Fintype J] {Y : J → Type*} [∀ j, NormedAddCommGroup (Y j)]
  [∀ j, NormedSpace ℝ (Y j)] {l : ℕ}
  {P : E →L[ℝ] F} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {C : ∀ j, E →L[ℝ] Y j}
  {L : ∀ j, Y j →L[ℝ] F} {x : J → Fin l → ℝ} {W : J → Matrix (Fin l) (Fin l) ℝ}

/-- The coupling row along the derivatives:
`P A^{m+1} v = Ai P A^m v + Σ_j L j C j A^m v`. -/
theorem proj_pow_succ_apply (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (m : ℕ) (v : E) :
    P ((A ^ (m + 1)) v) = Ai (P ((A ^ m) v)) + ∑ j, L j (C j ((A ^ m) v)) := by
  have h : (A ^ (m + 1)) v = A ((A ^ m) v) := by
    rw [pow_succ']
    rfl
  have h' := congrArg (fun T : E →L[ℝ] F => T ((A ^ m) v)) hA
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.sum_apply] at h'
  rw [h]
  exact h'

/-- **The own state along the derivatives, from bounds of the coupling row.** If `P v = 0`,
`0 ≤ H`, `H ‖Ai‖ ≤ 1` and `‖Σ_j L j (H^k C j A^k v)‖ ≤ b k` for `k < l`, then
`‖H^m P A^m v‖ ≤ H Σ_{k<l} b k` for `m ≤ l`: by the coupling row,
`H^{k+1} P A^{k+1} v = H Ai (H^k P A^k v) + H Σ_j L j (H^k C j A^k v)`. -/
theorem norm_pow_smul_proj_le_sum (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) {H : ℝ}
    (hH : 0 ≤ H) (hHAi : H * ‖Ai‖ ≤ 1) {v : E} (hPv : P v = 0) (b : Fin l → ℝ)
    (hb0 : ∀ k, 0 ≤ b k)
    (hb : ∀ k : Fin l, ‖∑ j, L j (H ^ (k : ℕ) • C j ((A ^ (k : ℕ)) v))‖ ≤ b k) {m : ℕ}
    (hm : m ≤ l) : ‖H ^ m • P ((A ^ m) v)‖ ≤ H * ∑ k : Fin l, b k := by
  set θ : ℕ → ℝ := fun k => if h : k < l then b ⟨k, h⟩ else 0 with hθ
  have hθ0 : ∀ k, 0 ≤ θ k := fun k => by
    rw [hθ]
    dsimp only
    split_ifs with h
    · exact hb0 _
    · exact le_rfl
  have hθsum : ∑ k ∈ range l, θ k = ∑ k : Fin l, b k := by
    rw [← Fin.sum_univ_eq_sum_range θ l]
    refine sum_congr rfl fun p _ => ?_
    rw [hθ]
    dsimp only
    rw [dite_eq_left p.2]
  have key : ∀ m, m ≤ l → ‖H ^ m • P ((A ^ m) v)‖ ≤ H * ∑ k ∈ range m, θ k := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [hPv]
    | succ m ih =>
      intro hm1
      have hml : m < l := hm1
      have h1 : H ^ m • (Ai (P ((A ^ m) v)) + ∑ j, L j (C j ((A ^ m) v))) =
          Ai (H ^ m • P ((A ^ m) v)) + ∑ j, L j (H ^ m • C j ((A ^ m) v)) := by
        simp only [smul_add, map_smul, smul_sum]
      have hrec : H ^ (m + 1) • P ((A ^ (m + 1)) v) =
          H • Ai (H ^ m • P ((A ^ m) v)) + H • ∑ j, L j (H ^ m • C j ((A ^ m) v)) := by
        rw [proj_pow_succ_apply hA, pow_succ', mul_smul, h1, smul_add]
      have h2 : ‖H • Ai (H ^ m • P ((A ^ m) v))‖ ≤ H * ∑ k ∈ range m, θ k := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hH]
        have h3 := Ai.le_opNorm (H ^ m • P ((A ^ m) v))
        have h4 := ih hml.le
        have h5 : H * ‖Ai (H ^ m • P ((A ^ m) v))‖ ≤
            H * ‖Ai‖ * ‖H ^ m • P ((A ^ m) v)‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left h3 hH
        have h6 : H * ‖Ai‖ * ‖H ^ m • P ((A ^ m) v)‖ ≤ 1 * ‖H ^ m • P ((A ^ m) v)‖ :=
          mul_le_mul_of_nonneg_right hHAi (norm_nonneg _)
        linarith
      have h7 : ‖H • ∑ j, L j (H ^ m • C j ((A ^ m) v))‖ ≤ H * θ m := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hH]
        refine mul_le_mul_of_nonneg_left ?_ hH
        rw [hθ]
        dsimp only
        rw [dite_eq_left hml]
        exact hb ⟨m, hml⟩
      rw [hrec, sum_range_succ, mul_add]
      exact (norm_add_le _ _).trans (add_le_add h2 h7)
  refine (key m hm).trans (mul_le_mul_of_nonneg_left ?_ hH)
  rw [← hθsum]
  exact sum_le_sum_of_subset_of_nonneg (range_mono hm) fun k _ _ => hθ0 k

/-- **The own state along the derivatives, on the states not shown:**
`‖H^m P A^m v‖ ≤ Θ H (H ‖A‖)^l ‖v‖` for `m ≤ l`, if `P v = 0` and all samples of `v` vanish. -/
theorem norm_pow_smul_proj_le (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j)
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1) {H : ℝ} (hH : 0 ≤ H) (hHA : H * ‖A‖ ≤ 1)
    (hHAi : H * ‖Ai‖ ≤ 1) {v : E} (hPv : P v = 0)
    (hv : ∀ j q, C j (exp ((x j q * H) • A) v) = 0) {m : ℕ} (hm : m ≤ l) :
    ‖H ^ m • P ((A ^ m) v)‖ ≤ defectTheta C L x W * (H * (H * ‖A‖) ^ l * ‖v‖) := by
  have h := norm_pow_smul_proj_le_sum hA hH hHAi hPv
    (fun k : Fin l => ∑ j, ‖L j‖ * ((k ! : ℝ) * ‖C j‖ *
      (|ddBeta (x j) (W j) k| / (l ! : ℝ) + ddOmega (x j) (W j) (l + 1) k) *
        (H * ‖A‖) ^ l * ‖v‖))
    (fun k => sum_nonneg fun j _ => by
      have := ddOmega_nonneg (x j) (W j) (l + 1) k
      positivity)
    (fun k => norm_sum_le_of_le _ fun j _ => ((L j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_pow_smul_le (hW j) (C j) A hH hHA (hv j) k)
        (norm_nonneg _))) hm
  refine h.trans_eq ?_
  unfold defectTheta
  rw [mul_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, sum_mul]
  exact sum_congr rfl fun j _ => by ring

/-- **The block row of the monolithic step on the states not shown, to leading order** (the paper,
proof of Theorem `thm:memory` (i), with eq. `eq:defectl` on the states not shown). For a state
`v` with `P v = 0` whose samples `C j (exp (x j q H A) v)`, `q < l`, all vanish, and
`0 ≤ H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`:

  `‖P (exp (H A) v) - H^{l+1} Σ_j γ_j L j C j A^l v‖ ≤ c₂ H^{l+2} ‖v‖`,

`γ_j = ddGamma (x j) (W j)`, `c₂ = defectConst A Ai C L x W`. -/
theorem norm_proj_exp_sub_leading_le (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1) {H : ℝ} (hH : 0 ≤ H) (hHA : H * ‖A‖ ≤ 1)
    (hHAi : H * ‖Ai‖ ≤ 1) {v : E} (hPv : P v = 0)
    (hv : ∀ j q, C j (exp ((x j q * H) • A) v) = 0) :
    ‖P (exp (H • A) v) - H ^ (l + 1) • ∑ j, ddGamma (x j) (W j) • L j (C j ((A ^ l) v))‖ ≤
      defectConst A Ai C L x W * H ^ (l + 2) * ‖v‖ := by
  obtain ⟨ρ, h1, h2⟩ := exists_exp_smul_apply_eq A H (b := l + 2) (by omega) v
  rw [abs_of_nonneg hH] at h2
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  -- the Taylor polynomial, split along the coupling row
  have hterm : ∀ m : ℕ, P (((((m + 1) ! : ℝ))⁻¹ * H ^ (m + 1)) • (A ^ (m + 1)) v) =
      (((m + 1) ! : ℝ))⁻¹ • (H • Ai (H ^ m • P ((A ^ m) v))) +
        ∑ j, L j (((((m + 1) ! : ℝ))⁻¹ * H ^ (m + 1)) • C j ((A ^ m) v)) := fun m => by
    rw [map_smul, proj_pow_succ_apply hA, smul_add, smul_sum]
    congr 1
    · rw [map_smul, smul_smul, smul_smul]
      congr 1
      ring
    · exact sum_congr rfl fun j _ => (map_smul _ _ _).symm
  have h0 : P ((((0 ! : ℝ))⁻¹ * H ^ 0) • (A ^ 0) v) = 0 := by
    simp [hPv]
  have hsplit : P (exp (H • A) v) =
      ∑ m ∈ range (l + 1), (((m + 1) ! : ℝ))⁻¹ • (H • Ai (H ^ m • P ((A ^ m) v))) +
        ∑ j, L j (∑ m ∈ range (l + 1), ((((m + 1) ! : ℝ))⁻¹ * H ^ (m + 1)) • C j ((A ^ m) v)) +
          P ρ := by
    rw [h1, map_add, map_sum, sum_range_succ', h0, add_zero, sum_congr rfl fun m _ => hterm m,
      sum_add_distrib, sum_comm]
    congr 2
    exact sum_congr rfl fun j _ => (map_sum _ _ _).symm
  have hmean : ∀ j, ∑ m ∈ range (l + 1), ((((m + 1) ! : ℝ))⁻¹ * H ^ (m + 1)) • C j ((A ^ m) v) =
      (ddGamma (x j) (W j) * H ^ (l + 1)) • C j ((A ^ l) v) -
        ∑ p : Fin l, (H / ((p : ℝ) + 1)) • C j (ddRem A H (x j) (W j) (l + 1) p v) :=
    fun j => dd_mean (hW j) (C j) A H (hv j)
  have hsum : ∑ j, L j ((ddGamma (x j) (W j) * H ^ (l + 1)) • C j ((A ^ l) v) -
        ∑ p : Fin l, (H / ((p : ℝ) + 1)) • C j (ddRem A H (x j) (W j) (l + 1) p v)) =
      H ^ (l + 1) • ∑ j, ddGamma (x j) (W j) • L j (C j ((A ^ l) v)) -
        ∑ j, L j (∑ p : Fin l, (H / ((p : ℝ) + 1)) •
          C j (ddRem A H (x j) (W j) (l + 1) p v)) := by
    rw [smul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [map_sub, map_smul, smul_smul, mul_comm]
  have hmain : P (exp (H • A) v) -
      H ^ (l + 1) • ∑ j, ddGamma (x j) (W j) • L j (C j ((A ^ l) v)) =
      ∑ m ∈ range (l + 1), (((m + 1) ! : ℝ))⁻¹ • (H • Ai (H ^ m • P ((A ^ m) v))) -
        ∑ j, L j (∑ p : Fin l, (H / ((p : ℝ) + 1)) •
          C j (ddRem A H (x j) (W j) (l + 1) p v)) + P ρ := by
    rw [hsplit, sum_congr rfl fun j _ => congrArg (L j) (hmean j), hsum]
    abel
  -- the three remainders
  have hΘ := defectTheta_nonneg C L x W
  have hb1 : ‖∑ m ∈ range (l + 1), (((m + 1) ! : ℝ))⁻¹ • (H • Ai (H ^ m • P ((A ^ m) v)))‖ ≤
      (Real.exp 1 - 1) * ‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖ := by
    have h3 : ∀ m ∈ range (l + 1),
        ‖(((m + 1) ! : ℝ))⁻¹ • (H • Ai (H ^ m • P ((A ^ m) v)))‖ ≤
          (((m + 1) ! : ℝ))⁻¹ * (‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖) := by
      intro m hm
      have hml : m ≤ l := Nat.lt_succ_iff.1 (mem_range.1 hm)
      have h4 := norm_pow_smul_proj_le hA hW hH hHA hHAi hPv hv hml
      have h5 : ‖Ai (H ^ m • P ((A ^ m) v))‖ ≤
          ‖Ai‖ * (defectTheta C L x W * (H * (H * ‖A‖) ^ l * ‖v‖)) :=
        (Ai.le_opNorm _).trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hH,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((m + 1) ! : ℝ))⁻¹)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc H * ‖Ai (H ^ m • P ((A ^ m) v))‖
          ≤ H * (‖Ai‖ * (defectTheta C L x W * (H * (H * ‖A‖) ^ l * ‖v‖))) :=
            mul_le_mul_of_nonneg_left h5 hH
        _ = ‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖ := by
            rw [mul_pow]
            ring
    refine (norm_sum_le_of_le _ h3).trans ?_
    rw [← sum_mul]
    have h6 : 0 ≤ ‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖ := by positivity
    calc (∑ m ∈ range (l + 1), (((m + 1) ! : ℝ))⁻¹) *
          (‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖)
        ≤ (Real.exp 1 - 1) * (‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖) :=
          mul_le_mul_of_nonneg_right (sum_inv_factorial_succ_le l) h6
      _ = (Real.exp 1 - 1) * ‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖ := by
          ring
  have hb2 : ‖∑ j, L j (∑ p : Fin l, (H / ((p : ℝ) + 1)) •
      C j (ddRem A H (x j) (W j) (l + 1) p v))‖ ≤
      defectOmega C L x W * ‖A‖ ^ (l + 1) * H ^ (l + 2) * ‖v‖ := by
    have h3 : ∀ j ∈ (univ : Finset J), ‖L j (∑ p : Fin l, (H / ((p : ℝ) + 1)) •
        C j (ddRem A H (x j) (W j) (l + 1) p v))‖ ≤
        ‖L j‖ * ((∑ p : Fin l, ddOmega (x j) (W j) (l + 1) p / ((p : ℝ) + 1)) * ‖C j‖) *
          (‖A‖ ^ (l + 1) * H ^ (l + 2) * ‖v‖) := by
      intro j _
      have h4 := norm_dd_mean_le (C j) A hH hHA (x j) (W j) v
      refine ((L j).le_opNorm _).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (h4.trans (le_of_eq ?_)) (norm_nonneg _)
      rw [mul_pow]
      ring
    refine (norm_sum_le_of_le _ h3).trans (le_of_eq ?_)
    rw [← sum_mul]
    unfold defectOmega
    ring
  have hb3 : ‖P ρ‖ ≤ expTail (l + 2) 1 * ‖A‖ ^ (l + 2) * H ^ (l + 2) * ‖v‖ := by
    have h3 := expTail_mul_le (l + 2) (y := 1) zero_le_one hx0 hHA
    rw [one_mul] at h3
    calc ‖P ρ‖ ≤ ‖P‖ * ‖ρ‖ := P.le_opNorm ρ
      _ ≤ 1 * ‖ρ‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ 1 * (expTail (l + 2) (H * ‖A‖) * ‖v‖) := mul_le_mul_of_nonneg_left h2 zero_le_one
      _ ≤ 1 * ((H * ‖A‖) ^ (l + 2) * expTail (l + 2) 1 * ‖v‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (norm_nonneg v)) zero_le_one
      _ = expTail (l + 2) 1 * ‖A‖ ^ (l + 2) * H ^ (l + 2) * ‖v‖ := by
          rw [mul_pow]
          ring
  rw [hmain]
  have h7 := norm_add_le
    (∑ m ∈ range (l + 1), (((m + 1) ! : ℝ))⁻¹ • (H • Ai (H ^ m • P ((A ^ m) v))) -
      ∑ j, L j (∑ p : Fin l, (H / ((p : ℝ) + 1)) •
        C j (ddRem A H (x j) (W j) (l + 1) p v))) (P ρ)
  have h8 := norm_sub_le
    (∑ m ∈ range (l + 1), (((m + 1) ! : ℝ))⁻¹ • (H • Ai (H ^ m • P ((A ^ m) v))))
    (∑ j, L j (∑ p : Fin l, (H / ((p : ℝ) + 1)) •
      C j (ddRem A H (x j) (W j) (l + 1) p v)))
  have h9 : defectConst A Ai C L x W * H ^ (l + 2) * ‖v‖ =
      (Real.exp 1 - 1) * ‖Ai‖ * defectTheta C L x W * ‖A‖ ^ l * H ^ (l + 2) * ‖v‖ +
        defectOmega C L x W * ‖A‖ ^ (l + 1) * H ^ (l + 2) * ‖v‖ +
          expTail (l + 2) 1 * ‖A‖ ^ (l + 2) * H ^ (l + 2) * ‖v‖ := by
    unfold defectConst
    ring
  rw [h9]
  linarith

end Defect

end CoSimFoundations
