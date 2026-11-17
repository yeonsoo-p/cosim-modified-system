/-
Where the shown maps are independent, a small local defect forces bounded coefficients (the
paper).

**Setting.** That of `LeadingValueScheme`: `P ∘ A = Ai ∘ P + Σ_j L j ∘ C j`, `‖P‖ ≤ 1`, partner
`j ∈ J` sampled at the nodes `x j q`, `q < l`, `W j` the inverse of the Vandermonde matrix of its
nodes, and a bounded right inverse `R` of the stack `N₀` of `P` and of the maps `C j A^p`,
`p < l` (independence). A rule of the subsystem has a coefficient `Fi` on its own state and
coefficients `G (j, q)` on the samples `C j ∘ exp (x j q H A)`; its local defect is

  `𝒯 = P ∘ U - Fi ∘ P - Σ_{j,q} G (j, q) ∘ C j ∘ exp (x j q H A)`,   `U = exp (H A)`
  (`ruleDefect`).

**Statements**, for `0 < H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`, `c₁ H ‖R‖ ≤ 1/2` (`c₁ = kernelConst`), every
`Fi` and every `G`:
* `norm_coeff_le` (the precise form, every `l`):

    `‖G (j, q)‖ ≤ Σ_{p<l} |W j p q| (p!/H^p) (e ‖L j‖ H^{p+1} + 2 ‖R‖ (c_B H^{l+1} + ‖𝒯‖))`,

  `c_B = e Θ' ‖A‖^l + ε_{l+1} ‖A‖^{l+1}` (`coefBase`),
  `Θ' = Σ_{p<l} Σ_j ‖L j‖ p! ‖C j‖ ω_p^j` (`coefTheta`), `ε_b = Σ_{n≥b} 1/n!`.
* `norm_coeff_comp_le` (the form of the paper, every `l`): if moreover `H ≤ 1`,

    `‖G (j, q) ∘ C j‖ ≤ K (H + ‖𝒯‖ / H^{l-1})`,
    `K = ‖C j‖ Σ_{p<l} |W j p q| p! (e ‖L j‖ + 2 ‖R‖ (c_B + 1))`   (`coefConst`).
* `norm_coeff_comp_le_scheme`: the same for the nodes `σ_j - q`, `q < l`, of a scheme with `l`
  held samples in any order of execution (`schemeNodes`, `schemeWeights`), where the sample
  `(j, q)` is `C j ∘ U^{σ_j} ∘ U^{-q}` (`nodeSample_scheme`).

The bound is on the coefficient `G (j, q)` itself, not only on its product with the output.

**Proof.** The stack of `P` and of the divided differences of the samples (`stackedDiff`) is
within `c₁ H` of `N₀` and therefore has a right inverse `R'` with `‖R'‖ ≤ 2 ‖R‖`
(`exists_rightInverse_near`). For `p < l` and `y ∈ Y j` let `v = R' (0, y at (j, p))`: `P v = 0`,
the divided difference of order `p` of the samples of `j` is `y`, and all others vanish. The
samples are combinations of the divided differences (`sample_eq_sum_ddiff`), so that the rule
gives `(P U - 𝒯) v = (H^p/p!) Σ_q x_q^p G (j, q) y`, the `p`-th moment of the coefficients. On
the other hand `H^k C j' A^k v` is `H^p y` for `(j', k) = (j, p)` and `O((H ‖A‖)^l) ‖v‖`
otherwise, so that `‖H^m P A^m v‖ ≤ H (‖L j‖ H^p ‖y‖ + Θ' (H ‖A‖)^l ‖v‖)` by the recursion along
the coupling row, and `‖P U v‖ ≤ e` times this plus the Taylor remainder (`norm_moment_le`). The
coefficients are recovered from their moments with the rows of `W` (`sum_weights_moments`), which
costs the factor `p!/H^p`. No rule of polynomial extrapolation is constructed: the bound of
`P U v` is taken directly.
-/
import CoSimFoundations.LeadingValueScheme

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Samples

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
  {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {l : ℕ}
  {x : Fin l → ℝ} {W : Matrix (Fin l) (Fin l) ℝ}

/-- **Coefficients from their moments:** `Σ_p W p q' Σ_q x_q^p g_q = g_{q'}`. -/
theorem sum_weights_moments (hW : W * Matrix.vandermonde x = 1) (g : Fin l → M) (q' : Fin l) :
    ∑ p : Fin l, W p q' • ∑ q : Fin l, x q ^ (p : ℕ) • g q = g q' := by
  calc ∑ p : Fin l, W p q' • ∑ q : Fin l, x q ^ (p : ℕ) • g q
      = ∑ p : Fin l, ∑ q : Fin l, (x q ^ (p : ℕ) * W p q') • g q := by
        refine sum_congr rfl fun p _ => ?_
        rw [smul_sum]
        exact sum_congr rfl fun q _ => by rw [smul_smul, mul_comm]
    _ = ∑ q : Fin l, (∑ p : Fin l, x q ^ (p : ℕ) * W p q') • g q := by
        rw [sum_comm]
        exact sum_congr rfl fun q _ => by rw [sum_smul]
    _ = ∑ q : Fin l, (if q = q' then (1 : ℝ) else 0) • g q :=
        sum_congr rfl fun q _ => by rw [sum_pow_mul_eq hW]
    _ = g q' := by simp

/-- **The samples from the divided differences:** for a positive macro step,
`C exp (x_q H A) v = Σ_p x_q^p (H^p/p!) ddiff p v`. -/
theorem sample_eq_sum_ddiff (hW : W * Matrix.vandermonde x = 1) (C : E →L[ℝ] Y)
    (A : E →L[ℝ] E) {H : ℝ} (hH : 0 < H) (q : Fin l) (v : E) :
    C (exp ((x q * H) • A) v) =
      ∑ p : Fin l, (x q ^ (p : ℕ) * (H ^ (p : ℕ) / (p ! : ℝ))) • ddiff C A H x W p v := by
  rw [exp_node_apply_eq_sum hW, map_sum]
  refine sum_congr rfl fun p _ => ?_
  unfold ddiff
  rw [map_smul, _root_.smul_apply, ContinuousLinearMap.comp_apply, smul_smul, mul_assoc]
  have hfac : (p ! : ℝ) ≠ 0 := by positivity
  have hHp : H ^ (p : ℕ) ≠ 0 := by positivity
  have h1 : H ^ (p : ℕ) / (p ! : ℝ) * ((p ! : ℝ) / H ^ (p : ℕ)) = 1 := by
    field_simp
  rw [h1, mul_one]

/-- **The derivative of order `k < l` of the output from the divided difference:**
`‖H^k C A^k v‖ ≤ H^k ‖ddiff k v‖ + k! ‖C‖ ω_k (H ‖A‖)^l ‖v‖` for `0 < H`, `H ‖A‖ ≤ 1`. -/
theorem norm_pow_smul_apply_le (hW : W * Matrix.vandermonde x = 1) (C : E →L[ℝ] Y)
    (A : E →L[ℝ] E) {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (k : Fin l) (v : E) :
    ‖H ^ (k : ℕ) • C ((A ^ (k : ℕ)) v)‖ ≤
      H ^ (k : ℕ) * ‖ddiff C A H x W k v‖ +
        (k ! : ℝ) * ‖C‖ * ddOmega x W l k * (H * ‖A‖) ^ l * ‖v‖ := by
  have hk : (k : ℕ) ≤ l := k.2.le
  have hHk : 0 ≤ H ^ (k : ℕ) := pow_nonneg hH.le _
  have h1 : C ((A ^ (k : ℕ)) v) =
      ddiff C A H x W k v - (ddiff C A H x W k - C ∘L (A ^ (k : ℕ))) v := by
    rw [_root_.sub_apply, ContinuousLinearMap.comp_apply, sub_sub_cancel]
  have h2 : ‖(ddiff C A H x W k - C ∘L (A ^ (k : ℕ))) v‖ ≤
      (k ! : ℝ) * ‖C‖ * ddOmega x W l k * ‖A‖ ^ l * H ^ (l - (k : ℕ)) * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_ddiff_sub_le hW C A hH hHA k) (norm_nonneg v))
  have h3 : H ^ (k : ℕ) * H ^ (l - (k : ℕ)) = H ^ l := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hHk, h1]
  calc H ^ (k : ℕ) * ‖ddiff C A H x W k v - (ddiff C A H x W k - C ∘L (A ^ (k : ℕ))) v‖
      ≤ H ^ (k : ℕ) * (‖ddiff C A H x W k v‖ +
          (k ! : ℝ) * ‖C‖ * ddOmega x W l k * ‖A‖ ^ l * H ^ (l - (k : ℕ)) * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl h2)) hHk
    _ = H ^ (k : ℕ) * ‖ddiff C A H x W k v‖ +
          (k ! : ℝ) * ‖C‖ * ddOmega x W l k * ‖A‖ ^ l *
            (H ^ (k : ℕ) * H ^ (l - (k : ℕ))) * ‖v‖ := by ring
    _ = H ^ (k : ℕ) * ‖ddiff C A H x W k v‖ +
          (k ! : ℝ) * ‖C‖ * ddOmega x W l k * (H * ‖A‖) ^ l * ‖v‖ := by
        rw [h3, mul_pow]
        ring

end Samples

section Rule

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {J : Type*} [Fintype J] {Y : J → Type*} [∀ j, NormedAddCommGroup (Y j)]
  [∀ j, NormedSpace ℝ (Y j)] [∀ j, CompleteSpace (Y j)] {l : ℕ}

/-- **The local defect of a rule** on the monolithic samples at the nodes (the paper, eq.
`eq:localdefect`): `𝒯 = P ∘ U - Fi ∘ P - Σ_{j,q} G (j, q) ∘ C j ∘ exp (x j q H A)`. -/
noncomputable def ruleDefect (P : E →L[ℝ] F) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E) (H : ℝ)
    (x : J → Fin l → ℝ) : E →L[ℝ] F :=
  P ∘L exp (H • A) - Fi ∘L P - ∑ k : J × Fin l, G k ∘L nodeSample C A H x k

/-- `Θ' = Σ_{p<l} Σ_j ‖L j‖ p! ‖C j‖ ω_p^j` (remainders of order `l`). -/
noncomputable def coefTheta (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : ℝ :=
  ∑ k : Fin l, ∑ j, ‖L j‖ * ((k ! : ℝ) * ‖C j‖ * ddOmega (x j) (W j) l k)

/-- `c_B = e Θ' ‖A‖^l + ε_{l+1} ‖A‖^{l+1}`. -/
noncomputable def coefBase (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : ℝ :=
  Real.exp 1 * coefTheta C L x W * ‖A‖ ^ l + expTail (l + 1) 1 * ‖A‖ ^ (l + 1)

/-- `K = ‖C j‖ Σ_{p<l} |W j p q| p! (e ‖L j‖ + 2 ρ (c_B + 1))`, `ρ` the norm of the right
inverse: the constant of the bound of the coefficient of the sample `(j, q)`. -/
noncomputable def coefConst (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) (ρ : ℝ) (j : J) (q : Fin l) : ℝ :=
  ‖C j‖ * ∑ p : Fin l, |W j p q| * (p ! : ℝ) *
    (Real.exp 1 * ‖L j‖ + 2 * ρ * (coefBase A C L x W + 1))

/-- `Θ' ≥ 0`. -/
theorem coefTheta_nonneg (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : 0 ≤ coefTheta C L x W :=
  sum_nonneg fun k _ => sum_nonneg fun j _ => by
    have := ddOmega_nonneg (x j) (W j) l k
    positivity

/-- `c_B ≥ 0`. -/
theorem coefBase_nonneg (A : E →L[ℝ] E) (C : ∀ j, E →L[ℝ] Y j) (L : ∀ j, Y j →L[ℝ] F)
    (x : J → Fin l → ℝ) (W : J → Matrix (Fin l) (Fin l) ℝ) : 0 ≤ coefBase A C L x W := by
  have h1 := coefTheta_nonneg C L x W
  have h2 := expTail_nonneg (l + 1) (zero_le_one : (0 : ℝ) ≤ 1)
  unfold coefBase
  positivity

variable {P : E →L[ℝ] F} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {C : ∀ j, E →L[ℝ] Y j}
  {L : ∀ j, Y j →L[ℝ] F} {x : J → Fin l → ℝ} {W : J → Matrix (Fin l) (Fin l) ℝ}

/-- **The own state along the derivatives, from bounds of the derivatives of the outputs:** if
`P v = 0` and `‖H^k C j A^k v‖ ≤ a j k` for `k < l`, then
`‖H^m P A^m v‖ ≤ H Σ_{k<l} Σ_j ‖L j‖ a j k` for `m ≤ l`, for `0 ≤ H`, `H ‖Ai‖ ≤ 1`. -/
theorem norm_pow_smul_proj_le_of_bound (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) {H : ℝ}
    (hH : 0 ≤ H) (hHAi : H * ‖Ai‖ ≤ 1) {v : E} (hPv : P v = 0) (a : J → Fin l → ℝ)
    (ha : ∀ j (k : Fin l), ‖H ^ (k : ℕ) • C j ((A ^ (k : ℕ)) v)‖ ≤ a j k) {m : ℕ}
    (hm : m ≤ l) :
    ‖H ^ m • P ((A ^ m) v)‖ ≤ H * ∑ k : Fin l, ∑ j, ‖L j‖ * a j k := by
  exact norm_pow_smul_proj_le_sum hA hH hHAi hPv (fun k : Fin l => ∑ j, ‖L j‖ * a j k)
    (fun k => sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (ha j k)))
    (fun k => norm_sum_le_of_le _ fun j _ => ((L j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (ha j k) (norm_nonneg _))) hm

/-- **The block row of the monolithic step from bounds of the derivatives of the outputs:**
under the hypotheses of `norm_pow_smul_proj_le_of_bound` and `‖P‖ ≤ 1`,
`‖P U v‖ ≤ e H Σ_{k<l} Σ_j ‖L j‖ a j k + Σ_{n>l} (H ‖A‖)^n/n! ‖v‖`. -/
theorem norm_proj_exp_le_of_bound (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    {H : ℝ} (hH : 0 ≤ H) (hHAi : H * ‖Ai‖ ≤ 1) {v : E} (hPv : P v = 0) (a : J → Fin l → ℝ)
    (ha : ∀ j (k : Fin l), ‖H ^ (k : ℕ) • C j ((A ^ (k : ℕ)) v)‖ ≤ a j k) :
    ‖P (exp (H • A) v)‖ ≤
      Real.exp 1 * (H * ∑ k : Fin l, ∑ j, ‖L j‖ * a j k) +
        expTail (l + 1) (H * ‖A‖) * ‖v‖ := by
  obtain ⟨ρ, h1, h2⟩ := exists_exp_smul_apply_eq A H (b := l + 1) (Nat.succ_pos l) v
  rw [abs_of_nonneg hH] at h2
  set S := H * ∑ k : Fin l, ∑ j, ‖L j‖ * a j k with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact mul_nonneg hH (sum_nonneg fun k _ => sum_nonneg fun j _ =>
      mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (ha j k)))
  have h3 : ∀ n ∈ range (l + 1), ‖P ((((n ! : ℝ))⁻¹ * H ^ n) • (A ^ n) v)‖ ≤
      1 ^ n / (n ! : ℝ) * S := by
    intro n hn
    have hnl : n ≤ l := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have h4 := norm_pow_smul_proj_le_of_bound hA hH hHAi hPv a ha hnl
    have h5 : P ((((n ! : ℝ))⁻¹ * H ^ n) • (A ^ n) v) =
        ((n ! : ℝ))⁻¹ • (H ^ n • P ((A ^ n) v)) := by
      rw [map_smul, mul_smul]
    rw [h5, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n ! : ℝ))⁻¹), one_pow, one_div]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : ‖∑ n ∈ range (l + 1), P ((((n ! : ℝ))⁻¹ * H ^ n) • (A ^ n) v)‖ ≤
      Real.exp 1 * S := by
    refine (norm_sum_le_of_le _ h3).trans ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right
      (Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) (l + 1)) hS0
  have h7 : ‖P ρ‖ ≤ expTail (l + 1) (H * ‖A‖) * ‖v‖ :=
    calc ‖P ρ‖ ≤ ‖P‖ * ‖ρ‖ := P.le_opNorm ρ
      _ ≤ 1 * ‖ρ‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ expTail (l + 1) (H * ‖A‖) * ‖v‖ := by rw [one_mul]; exact h2
  rw [h1, map_add, map_sum]
  exact (norm_add_le _ _).trans (add_le_add h6 h7)

/-- The norm of a vector with one component. -/
theorem norm_pi_single_le [DecidableEq J] (k : J × Fin l) (y : Y k.1) :
    ‖(Pi.single k y : ∀ k' : J × Fin l, Y k'.1)‖ ≤ ‖y‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg y)]
  intro k'
  rcases eq_or_ne k' k with rfl | hk
  · rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hk, norm_zero]
    exact norm_nonneg y

/-- **The moments of the coefficients of a rule are bounded by its local defect** (the step of
N1 (c)). For `p < l` and `y ∈ Y j`:

  `‖(H^p/p!) Σ_q x_q^p G (j, q) y‖ ≤ (e ‖L j‖ H^{p+1} + 2 ‖R‖ (c_B H^{l+1} + ‖𝒯‖)) ‖y‖`. -/
theorem norm_moment_le (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1)
    {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C x W * H * ‖R‖ ≤ 1 / 2) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (j : J) (p : Fin l) (y : Y j) :
    ‖(H ^ (p : ℕ) / (p ! : ℝ)) • ∑ q : Fin l, x j q ^ (p : ℕ) • G (j, q) y‖ ≤
      (Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) +
        2 * ‖R‖ * (coefBase A C L x W * H ^ (l + 1) + ‖ruleDefect P Fi G C A H x‖)) * ‖y‖ := by
  classical
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH.le (norm_nonneg A)
  -- a right inverse of the stacked divided differences
  have hN := norm_stackedDiff_sub_le P C A hW hH hHA
  have hε : kernelConst A C x W * H * ‖R‖ < 1 := by linarith
  obtain ⟨R', hR', hR'n⟩ := exists_rightInverse_near hR hN hε
  have hR'2 : ‖R'‖ ≤ 2 * ‖R‖ := by
    refine hR'n.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg R]
  -- the state with one divided difference
  set w : F × (∀ k : J × Fin l, Y k.1) := ((0 : F), Pi.single (j, p) y) with hw
  set v : E := R' w with hv
  have hwn : ‖w‖ ≤ ‖y‖ := by
    rw [hw, Prod.norm_mk, norm_zero]
    exact max_le (norm_nonneg y) (norm_pi_single_le (j, p) y)
  have hvn : ‖v‖ ≤ 2 * ‖R‖ * ‖y‖ :=
    calc ‖v‖ ≤ ‖R'‖ * ‖w‖ := R'.le_opNorm w
      _ ≤ 2 * ‖R‖ * ‖y‖ := mul_le_mul hR'2 hwn (norm_nonneg w) (by positivity)
  have hNv : stackedDiff P C A H x W v = w := by
    have h := congrArg (fun T : F × (∀ k : J × Fin l, Y k.1) →L[ℝ]
      F × (∀ k : J × Fin l, Y k.1) => T w) hR'
    simpa using h
  unfold stackedDiff at hNv
  rw [ContinuousLinearMap.prod_apply, hw, Prod.mk.injEq] at hNv
  obtain ⟨hPv, hd⟩ := hNv
  have hdv : ∀ (j' : J) (k : Fin l),
      ddiff (C j') A H (x j') (W j') k v =
        (Pi.single (j, p) y : ∀ k' : J × Fin l, Y k'.1) (j', k) :=
    fun j' k => congrFun hd (j', k)
  -- the samples of this state
  have hs : ∀ (j' : J) (q : Fin l), C j' (exp ((x j' q * H) • A) v) =
      (x j' q ^ (p : ℕ) * (H ^ (p : ℕ) / (p ! : ℝ))) •
        (Pi.single (j, p) y : ∀ k' : J × Fin l, Y k'.1) (j', p) := by
    intro j' q
    rw [sample_eq_sum_ddiff (hW j') (C j') A hH q v, sum_eq_single p]
    · rw [hdv j' p]
    · intro k _ hk
      have hne : ((j', k) : J × Fin l) ≠ (j, p) := fun h => hk (congrArg Prod.snd h)
      rw [hdv j' k, Pi.single_eq_of_ne hne, smul_zero]
    · intro h
      exact absurd (mem_univ p) h
  -- the rule on this state
  have hT : ruleDefect P Fi G C A H x v =
      P (exp (H • A) v) - Fi (P v) - ∑ k : J × Fin l, G k (nodeSample C A H x k v) := by
    simp [ruleDefect]
  have hsum : ∑ k : J × Fin l, G k (nodeSample C A H x k v) =
      (H ^ (p : ℕ) / (p ! : ℝ)) • ∑ q : Fin l, x j q ^ (p : ℕ) • G (j, q) y := by
    rw [Fintype.sum_prod_type, sum_eq_single j]
    · rw [smul_sum]
      refine sum_congr rfl fun q _ => ?_
      change G (j, q) (C j (exp ((x j q * H) • A) v)) = _
      rw [hs j q, Pi.single_eq_same, map_smul, smul_smul, mul_comm]
    · intro j' _ hj'
      refine sum_eq_zero fun q _ => ?_
      have hne : ((j', p) : J × Fin l) ≠ (j, p) := fun h => hj' (congrArg Prod.fst h)
      change G (j', q) (C j' (exp ((x j' q * H) • A) v)) = 0
      rw [hs j' q, Pi.single_eq_of_ne hne, smul_zero, map_zero]
    · intro h
      exact absurd (mem_univ j) h
  have hkey : (H ^ (p : ℕ) / (p ! : ℝ)) • ∑ q : Fin l, x j q ^ (p : ℕ) • G (j, q) y =
      P (exp (H • A) v) - ruleDefect P Fi G C A H x v := by
    rw [hT, hPv, map_zero, sub_zero, sub_sub_cancel, hsum]
  -- the block row on this state
  set a : J → Fin l → ℝ := fun j' k =>
    H ^ (k : ℕ) * ‖(Pi.single (j, p) y : ∀ k' : J × Fin l, Y k'.1) (j', k)‖ +
      (k ! : ℝ) * ‖C j'‖ * ddOmega (x j') (W j') l k * (H * ‖A‖) ^ l * ‖v‖ with ha
  have hab : ∀ j' (k : Fin l), ‖H ^ (k : ℕ) • C j' ((A ^ (k : ℕ)) v)‖ ≤ a j' k := by
    intro j' k
    have h := norm_pow_smul_apply_le (hW j') (C j') A hH hHA k v
    rw [hdv j' k] at h
    exact h
  have hPU := norm_proj_exp_le_of_bound hA hP hH.le hHAi hPv a hab
  have hsa : ∑ k : Fin l, ∑ j', ‖L j'‖ * a j' k =
      ‖L j‖ * (H ^ (p : ℕ) * ‖y‖) + coefTheta C L x W * ((H * ‖A‖) ^ l * ‖v‖) := by
    have h1 : ∀ (k : Fin l) (j' : J), ‖L j'‖ * a j' k =
        ‖L j'‖ * (H ^ (k : ℕ) *
          ‖(Pi.single (j, p) y : ∀ k' : J × Fin l, Y k'.1) (j', k)‖) +
        ‖L j'‖ * ((k ! : ℝ) * ‖C j'‖ * ddOmega (x j') (W j') l k) *
          ((H * ‖A‖) ^ l * ‖v‖) := fun k j' => by
      rw [ha]
      ring
    have h2 : ∑ k : Fin l, ∑ j', ‖L j'‖ * (H ^ (k : ℕ) *
        ‖(Pi.single (j, p) y : ∀ k' : J × Fin l, Y k'.1) (j', k)‖) =
        ‖L j‖ * (H ^ (p : ℕ) * ‖y‖) := by
      rw [sum_eq_single p]
      · rw [sum_eq_single j]
        · rw [Pi.single_eq_same]
        · intro j' _ hj'
          have hne : ((j', p) : J × Fin l) ≠ (j, p) := fun h => hj' (congrArg Prod.fst h)
          rw [Pi.single_eq_of_ne hne, norm_zero, mul_zero, mul_zero]
        · intro h
          exact absurd (mem_univ j) h
      · intro k _ hk
        refine sum_eq_zero fun j' _ => ?_
        have hne : ((j', k) : J × Fin l) ≠ (j, p) := fun h => hk (congrArg Prod.snd h)
        rw [Pi.single_eq_of_ne hne, norm_zero, mul_zero, mul_zero]
      · intro h
        exact absurd (mem_univ p) h
    rw [sum_congr rfl fun k _ => sum_congr rfl fun j' _ => h1 k j']
    simp only [sum_add_distrib]
    rw [h2]
    unfold coefTheta
    rw [sum_mul]
    congr 1
    exact sum_congr rfl fun k _ => (sum_mul _ _ _).symm
  rw [hsa] at hPU
  have htail := expTail_mul_le (l + 1) (y := 1) zero_le_one hx0 hHA
  rw [one_mul] at htail
  have hTv := (ruleDefect P Fi G C A H x).le_opNorm v
  have hΘ := coefTheta_nonneg C L x W
  have he : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hT0 := norm_nonneg (ruleDefect P Fi G C A H x)
  -- collect
  have hb1 : Real.exp 1 * (H * (‖L j‖ * (H ^ (p : ℕ) * ‖y‖) +
      coefTheta C L x W * ((H * ‖A‖) ^ l * ‖v‖))) ≤
      Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) * ‖y‖ +
        Real.exp 1 * coefTheta C L x W * ‖A‖ ^ l * H ^ (l + 1) * (2 * ‖R‖ * ‖y‖) := by
    have h1 : Real.exp 1 * (H * (‖L j‖ * (H ^ (p : ℕ) * ‖y‖) +
        coefTheta C L x W * ((H * ‖A‖) ^ l * ‖v‖))) =
        Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) * ‖y‖ +
          Real.exp 1 * coefTheta C L x W * ‖A‖ ^ l * H ^ (l + 1) * ‖v‖ := by
      rw [mul_pow]
      ring
    rw [h1]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hvn (by positivity))
  have hb2 : expTail (l + 1) (H * ‖A‖) * ‖v‖ ≤
      expTail (l + 1) 1 * ‖A‖ ^ (l + 1) * H ^ (l + 1) * (2 * ‖R‖ * ‖y‖) := by
    have h1 : expTail (l + 1) (H * ‖A‖) * ‖v‖ ≤ (H * ‖A‖) ^ (l + 1) * expTail (l + 1) 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right htail (norm_nonneg v)
    have h2 : (H * ‖A‖) ^ (l + 1) * expTail (l + 1) 1 * ‖v‖ ≤
        (H * ‖A‖) ^ (l + 1) * expTail (l + 1) 1 * (2 * ‖R‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left hvn
        (mul_nonneg (pow_nonneg hx0 _) (expTail_nonneg _ zero_le_one))
    refine (h1.trans h2).trans (le_of_eq ?_)
    rw [mul_pow]
    ring
  have hb3 : ‖ruleDefect P Fi G C A H x v‖ ≤
      ‖ruleDefect P Fi G C A H x‖ * (2 * ‖R‖ * ‖y‖) :=
    hTv.trans (mul_le_mul_of_nonneg_left hvn hT0)
  rw [hkey]
  have hfin : (Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) +
      2 * ‖R‖ * (coefBase A C L x W * H ^ (l + 1) + ‖ruleDefect P Fi G C A H x‖)) * ‖y‖ =
      Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) * ‖y‖ +
        Real.exp 1 * coefTheta C L x W * ‖A‖ ^ l * H ^ (l + 1) * (2 * ‖R‖ * ‖y‖) +
        expTail (l + 1) 1 * ‖A‖ ^ (l + 1) * H ^ (l + 1) * (2 * ‖R‖ * ‖y‖) +
        ‖ruleDefect P Fi G C A H x‖ * (2 * ‖R‖ * ‖y‖) := by
    unfold coefBase
    ring
  rw [hfin]
  have h9 := norm_sub_le (P (exp (H • A) v)) (ruleDefect P Fi G C A H x v)
  linarith

/-- **A small local defect forces bounded coefficients, precise form** (every
`l`). Under the hypotheses of `leading_value_nodes` (coupling row, `‖P‖ ≤ 1`, right inverse `R`
of the stack of `P` and of the `C j A^p`, `0 < H`, `H ‖A‖ ≤ 1`, `H ‖Ai‖ ≤ 1`, `c₁ H ‖R‖ ≤ 1/2`),
every rule `(Fi, G)` satisfies

  `‖G (j, q)‖ ≤ Σ_{p<l} |W j p q| (p!/H^p) (e ‖L j‖ H^{p+1} + 2 ‖R‖ (c_B H^{l+1} + ‖𝒯‖))`. -/
theorem norm_coeff_le (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1)
    {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C x W * H * ‖R‖ ≤ 1 / 2) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (j : J) (q : Fin l) :
    ‖G (j, q)‖ ≤ ∑ p : Fin l, |W j p q| * ((p ! : ℝ) / H ^ (p : ℕ)) *
      (Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) +
        2 * ‖R‖ * (coefBase A C L x W * H ^ (l + 1) + ‖ruleDefect P Fi G C A H x‖)) := by
  have hcB := coefBase_nonneg A C L x W
  have hT0 := norm_nonneg (ruleDefect P Fi G C A H x)
  have hB : ∀ p : Fin l, 0 ≤ Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) +
      2 * ‖R‖ * (coefBase A C L x W * H ^ (l + 1) + ‖ruleDefect P Fi G C A H x‖) :=
    fun p => by positivity
  refine ContinuousLinearMap.opNorm_le_bound _
    (sum_nonneg fun p _ => mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (hB p))
    fun y => ?_
  have h1 := sum_weights_moments (hW j) (fun q' : Fin l => G (j, q') y) q
  have h2 : ∀ p : Fin l, W j p q • ∑ q' : Fin l, x j q' ^ (p : ℕ) • G (j, q') y =
      (W j p q * ((p ! : ℝ) / H ^ (p : ℕ))) •
        ((H ^ (p : ℕ) / (p ! : ℝ)) • ∑ q' : Fin l, x j q' ^ (p : ℕ) • G (j, q') y) := fun p => by
    have hfac : (p ! : ℝ) ≠ 0 := by positivity
    have hHp : H ^ (p : ℕ) ≠ 0 := by positivity
    rw [smul_smul, mul_assoc]
    have h3 : (p ! : ℝ) / H ^ (p : ℕ) * (H ^ (p : ℕ) / (p ! : ℝ)) = 1 := by
      field_simp
    rw [h3, mul_one]
  rw [← h1, sum_congr rfl fun p _ => h2 p, sum_mul]
  refine norm_sum_le_of_le _ fun p _ => ?_
  have h4 := norm_moment_le hA hP hW hR hH hHA hHAi hsmall Fi G j p y
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg (abs_nonneg (W j p q))
    (div_nonneg (Nat.cast_nonneg (p !)) (pow_nonneg hH.le (p : ℕ))))
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p ! : ℝ) / H ^ (p : ℕ))]
  refine h5.trans (le_of_eq ?_)
  ring

/-- **A small local defect forces bounded coefficients** (every `l`, in the
form of the paper). Under the hypotheses of `norm_coeff_le` and `H ≤ 1`, every rule `(Fi, G)`
with local defect `𝒯` satisfies

  `‖G (j, q) ∘ C j‖ ≤ K (H + ‖𝒯‖ / H^{l-1})`,   `K = coefConst A C L x W ‖R‖ j q`. -/
theorem norm_coeff_comp_le (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (hW : ∀ j, W j * Matrix.vandermonde (x j) = 1)
    {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C x W * H * ‖R‖ ≤ 1 / 2) (Fi : F →L[ℝ] F)
    (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (j : J) (q : Fin l) :
    ‖G (j, q) ∘L C j‖ ≤ coefConst A C L x W ‖R‖ j q *
      (H + ‖ruleDefect P Fi G C A H x‖ / H ^ (l - 1)) := by
  set t := ‖ruleDefect P Fi G C A H x‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hcB := coefBase_nonneg A C L x W
  have hR0 := norm_nonneg R
  have hL0 := norm_nonneg (L j)
  have he : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hq0 : 0 ≤ t / H ^ (l - 1) := div_nonneg ht0 (pow_nonneg hH.le _)
  have hterm : ∀ p : Fin l, |W j p q| * ((p ! : ℝ) / H ^ (p : ℕ)) *
      (Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) +
        2 * ‖R‖ * (coefBase A C L x W * H ^ (l + 1) + t)) ≤
      |W j p q| * (p ! : ℝ) * (Real.exp 1 * ‖L j‖ + 2 * ‖R‖ * (coefBase A C L x W + 1)) *
        (H + t / H ^ (l - 1)) := by
    intro p
    have hpl : (p : ℕ) ≤ l - 1 := Nat.le_sub_one_of_lt p.2
    have hHp : 0 < H ^ (p : ℕ) := pow_pos hH _
    -- `H^{l+1} / H^p ≤ H` and `t / H^p ≤ t / H^{l-1}`
    have h1 : H ^ (l + 1) / H ^ (p : ℕ) ≤ H := by
      rw [div_le_iff₀ hHp]
      have h2 : H ^ (l + 1) = H * H ^ (p : ℕ) * H ^ (l - (p : ℕ)) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' p.2.le, pow_succ']
      rw [h2]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hH.le hH1)
    have h3 : t / H ^ (p : ℕ) ≤ t / H ^ (l - 1) :=
      div_le_div_of_nonneg_left ht0 (pow_pos hH _)
        (pow_le_pow_of_le_one hH.le hH1 hpl)
    have h4 : (p ! : ℝ) / H ^ (p : ℕ) * (Real.exp 1 * ‖L j‖ * H ^ ((p : ℕ) + 1) +
        2 * ‖R‖ * (coefBase A C L x W * H ^ (l + 1) + t)) =
        (p ! : ℝ) * (Real.exp 1 * ‖L j‖ * H +
          2 * ‖R‖ * (coefBase A C L x W * (H ^ (l + 1) / H ^ (p : ℕ)) +
            t / H ^ (p : ℕ))) := by
      rw [pow_succ]
      field_simp
    have h5 : Real.exp 1 * ‖L j‖ * H +
        2 * ‖R‖ * (coefBase A C L x W * (H ^ (l + 1) / H ^ (p : ℕ)) + t / H ^ (p : ℕ)) ≤
        (Real.exp 1 * ‖L j‖ + 2 * ‖R‖ * (coefBase A C L x W + 1)) * (H + t / H ^ (l - 1)) := by
      have h6 : coefBase A C L x W * (H ^ (l + 1) / H ^ (p : ℕ)) ≤ coefBase A C L x W * H :=
        mul_le_mul_of_nonneg_left h1 hcB
      have h7 : 2 * ‖R‖ * (coefBase A C L x W * (H ^ (l + 1) / H ^ (p : ℕ)) +
          t / H ^ (p : ℕ)) ≤ 2 * ‖R‖ * (coefBase A C L x W * H + t / H ^ (l - 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add h6 h3) (by positivity)
      have h8 : 0 ≤ Real.exp 1 * ‖L j‖ * (t / H ^ (l - 1)) := by positivity
      have h9 : 0 ≤ 2 * ‖R‖ * H := by positivity
      have h10 : 0 ≤ 2 * ‖R‖ * coefBase A C L x W * (t / H ^ (l - 1)) := by positivity
      nlinarith
    have h13 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (p !))) (abs_nonneg (W j p q))
    rw [← h4] at h13
    convert h13 using 1 <;> ring
  have h11 := norm_coeff_le hA hP hW hR hH hHA hHAi hsmall Fi G j q
  have h12 : ‖G (j, q)‖ ≤ (∑ p : Fin l, |W j p q| * (p ! : ℝ) *
      (Real.exp 1 * ‖L j‖ + 2 * ‖R‖ * (coefBase A C L x W + 1))) * (H + t / H ^ (l - 1)) := by
    rw [sum_mul]
    exact h11.trans (sum_le_sum fun p _ => hterm p)
  calc ‖G (j, q) ∘L C j‖ ≤ ‖G (j, q)‖ * ‖C j‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (∑ p : Fin l, |W j p q| * (p ! : ℝ) *
          (Real.exp 1 * ‖L j‖ + 2 * ‖R‖ * (coefBase A C L x W + 1))) *
          (H + t / H ^ (l - 1)) * ‖C j‖ :=
        mul_le_mul_of_nonneg_right h12 (norm_nonneg _)
    _ = coefConst A C L x W ‖R‖ j q * (H + t / H ^ (l - 1)) := by
        unfold coefConst
        ring

/-- The sample at the node `σ_j - q` of a scheme is the sample `C j ∘ U^{σ_j} ∘ U^{-q}` of the
monolithic system (`shownSample` of `VisibilityConverse` for a partner `j`). -/
theorem nodeSample_scheme (C : ∀ j, E →L[ℝ] Y j) (A : E →L[ℝ] E) (H : ℝ) (σ : J → ℕ)
    (j : J) (q : Fin l) :
    nodeSample C A H (fun j => schemeNodes (σ j) l) (j, q) =
      C j ∘L (exp (H • A) ^ σ j * exp (-(H • A)) ^ (q : ℕ)) := by
  unfold nodeSample schemeNodes
  rw [exp_pow_mul_exp_neg_pow]

/-- **A small local defect forces bounded coefficients, for the samples of a scheme with `l`
held samples in any order of execution**: `norm_coeff_comp_le` for the nodes
`σ_j - q`, `q < l`, with `σ_j = 0` for old samples and `σ_j = 1` if the newest sample of partner
`j` is that of the new instant. -/
theorem norm_coeff_comp_le_scheme (hA : P ∘L A = Ai ∘L P + ∑ j, L j ∘L C j) (hP : ‖P‖ ≤ 1)
    (σ : J → ℕ) {R : F × (∀ k : J × Fin l, Y k.1) →L[ℝ] E}
    (hR : stackedDeriv P C A l ∘L R = ContinuousLinearMap.id ℝ (F × (∀ k : J × Fin l, Y k.1)))
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hHA : H * ‖A‖ ≤ 1) (hHAi : H * ‖Ai‖ ≤ 1)
    (hsmall : kernelConst A C (fun j => schemeNodes (σ j) l) (fun j => schemeWeights (σ j) l) *
      H * ‖R‖ ≤ 1 / 2) (Fi : F →L[ℝ] F) (G : ∀ k : J × Fin l, Y k.1 →L[ℝ] F) (j : J)
    (q : Fin l) :
    ‖G (j, q) ∘L C j‖ ≤
      coefConst A C L (fun j => schemeNodes (σ j) l) (fun j => schemeWeights (σ j) l) ‖R‖ j q *
        (H + ‖ruleDefect P Fi G C A H fun j => schemeNodes (σ j) l‖ / H ^ (l - 1)) :=
  norm_coeff_comp_le hA hP (fun j => schemeWeights_mul (σ j) l) hR hH hH1 hHA hHAi hsmall Fi G
    j q

end Rule

end CoSimFoundations
