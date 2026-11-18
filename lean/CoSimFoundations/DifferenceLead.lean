/-
The difference is the one-step error divided by the macro step, a priori (the paper, Definition
`def:mod`, and Theorem `thm:half`, second statement: "`Δ = (X - U)/H + O(H²)`").

**Paper.** The modified system of a hold with the one-step map `X` is `Ã = (1/H) Log X`, the
difference is `Δ = Ã - A`, and the monolithic step is `U = e^{HA}` with `H A = Log U`. The last
lines of the proof of Theorem `thm:half`: "`H Ã = Log X` and `Log(U + E) - Log U = E + O(H ‖E‖)`
for `E = X - U = O(H²)`, so that `Δ = E/H + O(H²)`."

**What is formalised.** `log` is the logarithm series of Mathlib,
`log x = Σ_{k ≥ 1} (-1)^{k+1}/k · (x - 1)^k`. All constants are explicit and depend only on the
constants of consistency (`‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²`) and on `‖A‖`.

In a real Banach algebra:

1. `norm_log_sub_log_sub_le`: for `‖x - 1‖ ≤ ρ`, `‖y - 1‖ ≤ ρ`, `ρ < 1`,
     `‖log x - log y - (x - y)‖ ≤ ‖x - y‖ ρ / (1 - ρ)`
   (the series, term by term: `‖uᵏ - vᵏ‖ ≤ k ‖u - v‖ ρ^{k-1}` and `|c_k| = 1/k`); hence the
   logarithm is Lipschitz there, `‖log x - log y‖ ≤ ‖x - y‖ / (1 - ρ)` (`norm_log_sub_log_le`).
   This is the paper's `Log(U + E) - Log U = E + O(H ‖E‖)` with its constant.
2. `log_exp_of_norm_le`: `log (exp z) = z` for `‖z‖ ≤ 1/4`. Proof: `‖exp z - 1‖ ≤ 4/3 ‖z‖ ≤ 1/3`,
   so `L = log (exp z)` has `exp L = exp z` (`exp_log`) and `‖L‖ ≤ 1/2` (`norm_log_le`); `L` and `z`
   commute, `exp (L - z) = 1` and `‖L - z‖ ≤ 1`, hence `L = z` (`eq_zero_of_exp_eq_one`).
3. `norm_log_sub_smul_sub_le`: if `H ≥ 0`, `‖x - 1‖ ≤ b H`, `‖x - exp (H A)‖ ≤ c H²`,
   `b H ≤ 1/3` and `H ‖A‖ ≤ 1/4`, then
     `‖log x - H A - (x - exp (H A))‖ ≤ K H³`,  `K = diffLeadC b c ‖A‖ = 3/2 · c · max b (4/3 ‖A‖)`.
   (1 with `y = exp (H A)`, `ρ = max b (4/3 ‖A‖) · H ≤ 1/3`, and 2.)

For matrices on `Fin n` with the spectral norm `‖opE ·‖` (the Banach algebra is the algebra of
matrices with `Matrix.Norms.L2Operator`, whose norm is `‖opE ·‖` by definition):

* `modifiedSystem H X = H⁻¹ • log X`, `difference A H X = modifiedSystem H X - A`,
  `numDamping A H X = -tr (difference A H X)` (the paper's `Ã`, `Δ`, `ν = tr Δ_R = -tr Δ`);
* `exp_smul_modifiedSystem`: `exp (H • Ã) = X` for `H ≠ 0`, `‖X - 1‖ < 1`;
  `norm_opE_modifiedSystem_le`: `‖Ã‖ ≤ 3/2 · b` for `‖X - 1‖ ≤ b H`, `b H ≤ 1/3`, `H > 0`;
* `log_exp_smul`: `log (exp (H • A)) = H • A` for `0 ≤ H`, `H ‖A‖ ≤ 1/4`; hence the modified system
  of the monolithic step is `A` and its difference is zero (`modifiedSystem_exp_smul`,
  `difference_exp_smul`);
* **the a priori passage**, for `H > 0`, `U = exp (H • A)`, `‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²`,
  `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, `K = diffLeadC b c ‖A‖`:
    `‖H • Δ - (X - U)‖ ≤ K H³`            (`norm_opE_smul_difference_sub_le`),
    `‖Δ - H⁻¹ • (X - U)‖ ≤ K H²`          (`norm_opE_difference_sub_le`),
    `‖Δ‖ ≤ (c + K H) H ≤ 3/2 · c H`       (`norm_opE_difference_le`, `norm_opE_difference_le'`),
    `|⟪x, Δ y⟫ - H⁻¹ ⟪x, (X - U) y⟫| ≤ K H² ‖x‖ ‖y‖`   (`abs_inner_difference_sub_le`),
    `|ν + H⁻¹ tr (X - U)| ≤ n K H²`       (`abs_numDamping_add_trace_le`).

Route: the estimate of the logarithm series (1), not the combination of
`norm_exp_smul_sub_exp_smul_sub_le` (`‖X - U - HΔ‖ ≤ H² ‖Δ‖ m e^{Hm}`) with a bound on `‖Ã‖`: (1)
is the paper's argument, needs no division and gives the smaller constant.

Range of the macro step. The paper assumes `H |Im λ| < π` for the eigenvalues of `A` and that `X`
has no eigenvalue on `(-∞, 0]` (principal logarithm). Here the range is `b H ≤ 1/3` and
`H ‖A‖ ≤ 1/4`, where the series converge and 2 holds by the argument above. That the series is the
principal logarithm for `‖X - 1‖ < 1` is a standard fact and is not formalised.
-/
import CoSimFoundations.LosslessEnergy
import CoSimFoundations.NegativeDamping
import CoSimFoundations.Reaction

open NormedSpace Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

/-- The constant of the a priori passage from the one-step error to the difference:
`K = 3/2 · c · max b (4/3 · α)`, with `‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²` and `α = ‖A‖`. -/
noncomputable def diffLeadC (b c α : ℝ) : ℝ := 3 / 2 * c * max b (4 / 3 * α)

/-- `e^{1/4} ≤ 4/3`. -/
theorem exp_quarter_le : Real.exp (1 / 4) ≤ 4 / 3 := by
  refine (Real.exp_bound_div_one_sub_of_interval (x := 1 / 4) (by norm_num)
    (by norm_num)).trans_eq ?_
  norm_num

/-- `ρ / (1 - ρ) ≤ 3/2 · ρ` for `0 ≤ ρ ≤ 1/3`. -/
theorem div_one_sub_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 3) : ρ / (1 - ρ) ≤ 3 / 2 * ρ := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]

/-- The remainder of the passage is at most half the leading term: `K H ≤ c/2` for `c ≥ 0`,
`H ≥ 0`, `b H ≤ 1/3`, `H α ≤ 1/4`. -/
theorem diffLeadC_mul_le {b c α H : ℝ} (hc : 0 ≤ c) (hH : 0 ≤ H) (hbH : b * H ≤ 1 / 3)
    (hαH : H * α ≤ 1 / 4) : diffLeadC b c α * H ≤ c / 2 := by
  have h1 : max b (4 / 3 * α) * H ≤ 1 / 3 := by
    rw [max_mul_of_nonneg _ _ hH]
    exact max_le hbH (by linarith)
  have h2 := mul_le_mul_of_nonneg_left h1 hc
  rw [diffLeadC]
  linarith

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The logarithm against its linear part, for two arguments:** if `‖x - 1‖ ≤ ρ`,
`‖y - 1‖ ≤ ρ` and `ρ < 1`, then `‖log x - log y - (x - y)‖ ≤ ‖x - y‖ ρ / (1 - ρ)`. -/
theorem norm_log_sub_log_sub_le {x y : 𝔸} {ρ : ℝ} (hx : ‖x - 1‖ ≤ ρ) (hy : ‖y - 1‖ ≤ ρ)
    (hρ : ρ < 1) : ‖log x - log y - (x - y)‖ ≤ ‖x - y‖ * (ρ / (1 - ρ)) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hx
  have hfx := OneStep.hasSum_log_one_add (lt_of_le_of_lt hx hρ)
  have hfy := OneStep.hasSum_log_one_add (lt_of_le_of_lt hy hρ)
  rw [add_sub_cancel] at hfx hfy
  have htail := (hasSum_nat_add_iff' 2).2 (hfx.sub hfy)
  have hsum : ∑ k ∈ Finset.range 2,
      (logCoeff k • (x - 1) ^ k - logCoeff k • (y - 1) ^ k) = x - y := by
    simp [Finset.sum_range_succ, logCoeff]
  rw [hsum] at htail
  have hg : HasSum (fun i : ℕ => ‖x - y‖ * ρ * ρ ^ i) (‖x - y‖ * ρ * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ).mul_left _
  have hle := htail.norm_le_of_bounded hg (fun i => by
    have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hc : |logCoeff (i + 2)| = ((i : ℝ) + 2)⁻¹ := by
      rw [logCoeff, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, one_div]
      push_cast
      rfl
    have hp := OneStep.norm_pow_succ_sub_pow_succ_le (x - 1) (y - 1) hx hy (i + 1)
    rw [sub_sub_sub_cancel_right] at hp
    push_cast at hp
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, hc, inv_mul_le_iff₀ hi]
    refine hp.trans_eq ?_
    ring)
  exact hle.trans_eq (by rw [div_eq_mul_inv, mul_assoc])

/-- **The logarithm is Lipschitz near one:** if `‖x - 1‖ ≤ ρ`, `‖y - 1‖ ≤ ρ` and `ρ < 1`, then
`‖log x - log y‖ ≤ ‖x - y‖ / (1 - ρ)`. -/
theorem norm_log_sub_log_le {x y : 𝔸} {ρ : ℝ} (hx : ‖x - 1‖ ≤ ρ) (hy : ‖y - 1‖ ≤ ρ)
    (hρ : ρ < 1) : ‖log x - log y‖ ≤ ‖x - y‖ / (1 - ρ) := by
  have h1 := norm_log_sub_log_sub_le hx hy hρ
  have h2 : ‖log x - log y‖ ≤ ‖log x - log y - (x - y)‖ + ‖x - y‖ := by
    have h := norm_add_le (log x - log y - (x - y)) (x - y)
    rwa [sub_add_cancel] at h
  have hne : (1 - ρ) ≠ 0 := (sub_pos.2 hρ).ne'
  have e : ‖x - y‖ / (1 - ρ) = ‖x - y‖ * (ρ / (1 - ρ)) + ‖x - y‖ := by
    field_simp
    ring
  rw [e]
  linarith

/-- `‖exp z - 1‖ ≤ 4/3 ‖z‖` for `‖z‖ ≤ 1/4`. -/
theorem norm_exp_sub_one_le_of_norm_le {z : 𝔸} (hz : ‖z‖ ≤ 1 / 4) :
    ‖exp z - 1‖ ≤ 4 / 3 * ‖z‖ := by
  have h1 := OneStep.norm_exp_sub_one_le z
  have h2 : Real.exp ‖z‖ ≤ 4 / 3 := (Real.exp_le_exp.2 hz).trans exp_quarter_le
  have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg z)
  linarith

/-- **The logarithm series inverts the exponential near zero:** `log (exp z) = z` for
`‖z‖ ≤ 1/4`. -/
theorem log_exp_of_norm_le {z : 𝔸} (hz : ‖z‖ ≤ 1 / 4) : log (exp z) = z := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have h1 : ‖exp z - 1‖ ≤ 1 / 3 := by
    have h := norm_exp_sub_one_le_of_norm_le hz
    linarith
  have hL : ‖log (exp z)‖ ≤ 1 / 2 := by
    have h := norm_log_le h1 (by norm_num)
    norm_num at h
    exact h
  have he : exp (log (exp z)) = exp z := exp_log (by linarith)
  have hc : Commute (log (exp z)) (-z) := ((Commute.refl z).exp_left.log_left).neg_right
  have h0 : exp (log (exp z) + -z) = 1 := by
    rw [exp_add_of_commute hc, he, ← exp_add_of_commute (Commute.refl z).neg_right,
      add_neg_cancel, exp_zero]
  have hn : ‖log (exp z) + -z‖ ≤ 1 := by
    have h := norm_add_le (log (exp z)) (-z)
    rw [norm_neg] at h
    linarith
  exact add_neg_eq_zero.1 (eq_zero_of_exp_eq_one hn h0)

/-- **The a priori passage in a Banach algebra.** If `H ≥ 0`, `‖x - 1‖ ≤ b H`,
`‖x - exp (H A)‖ ≤ c H²`, `b H ≤ 1/3` and `H ‖A‖ ≤ 1/4`, then
`‖log x - H A - (x - exp (H A))‖ ≤ K H³` with `K = 3/2 · c · max b (4/3 ‖A‖)`. -/
theorem norm_log_sub_smul_sub_le {x A : 𝔸} {H b c : ℝ} (hH : 0 ≤ H) (hb : ‖x - 1‖ ≤ b * H)
    (hc : ‖x - exp (H • A)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3) (hAH : H * ‖A‖ ≤ 1 / 4) :
    ‖log x - H • A - (x - exp (H • A))‖ ≤ diffLeadC b c ‖A‖ * H ^ 3 := by
  have hz : ‖H • A‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_of_nonneg hH]
    exact hAH
  have hU := norm_exp_sub_one_le_of_norm_le hz
  rw [norm_smul, Real.norm_of_nonneg hH] at hU
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = max b (4 / 3 * ‖A‖) := ⟨_, rfl⟩
  have hx' : ‖x - 1‖ ≤ β * H := by
    rw [hβ]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hH)
  have hy' : ‖exp (H • A) - 1‖ ≤ β * H := by
    have h := mul_le_mul_of_nonneg_right (le_max_right b (4 / 3 * ‖A‖)) hH
    rw [hβ]
    linarith
  have hβH : β * H ≤ 1 / 3 := by
    rw [hβ, max_mul_of_nonneg _ _ hH]
    exact max_le hbH (by linarith)
  have hβ0 : 0 ≤ β * H := (norm_nonneg _).trans hx'
  have h1 := norm_log_sub_log_sub_le hx' hy' (by linarith)
  rw [log_exp_of_norm_le hz] at h1
  calc ‖log x - H • A - (x - exp (H • A))‖
      ≤ ‖x - exp (H • A)‖ * (β * H / (1 - β * H)) := h1
    _ ≤ c * H ^ 2 * (3 / 2 * (β * H)) :=
        mul_le_mul hc (div_one_sub_le hβ0 hβH) (div_nonneg hβ0 (by linarith))
          ((norm_nonneg _).trans hc)
    _ = diffLeadC b c ‖A‖ * H ^ 3 := by
        rw [diffLeadC, ← hβ]
        ring

end Algebra

section Matrices

variable {n : ℕ}

/-- **The modified system** `Ã = (1/H) log X` of a one-step map `X` (the paper, Definition
`def:mod`), with the logarithm series; it is a modified system for `‖X - 1‖ < 1`
(`exp_smul_modifiedSystem`). -/
noncomputable def modifiedSystem (H : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  H⁻¹ • log X

/-- **The difference** `Δ = Ã - A` between the co-simulation with the one-step map `X` and the
monolithic system `A` (the paper, Definition `def:mod`, eq. `eq:diff`). -/
noncomputable def difference (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  modifiedSystem H X - A

/-- **The total numerical damping** `ν = tr Δ_R = -tr Δ` (the paper, Definition `def:props` (iii)).
-/
noncomputable def numDamping (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -Matrix.trace (difference A H X)

/-- `H Δ = log X - H A`. -/
theorem smul_difference (A X : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : H ≠ 0) :
    H • difference A H X = log X - H • A := by
  rw [difference, modifiedSystem, smul_sub, smul_smul, mul_inv_cancel₀ hH, one_smul]

/-- The total numerical damping is the trace of the numerical dissipation `Δ_R = -sym Δ`. -/
theorem numDamping_eq_trace_numDissipation (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    numDamping A H X = Matrix.trace (numDissipation A (modifiedSystem H X)) := by
  rw [numDamping, difference, numDissipation, Matrix.trace_neg, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_transpose, smul_eq_mul]
  ring

/-- The logarithm series near one, spectral norm: `‖log X‖ ≤ ρ / (1 - ρ)` for
`‖X - 1‖ ≤ ρ < 1`. -/
theorem norm_opE_log_le {X : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (hX : ‖opE (X - 1)‖ ≤ ρ)
    (hρ : ρ < 1) : ‖opE (log X)‖ ≤ ρ / (1 - ρ) := by
  open scoped Matrix.Norms.L2Operator in
  exact norm_log_le (𝔸 := Matrix (Fin n) (Fin n) ℝ) hX hρ

/-- **The modified system exists for small steps:** `exp (H • Ã) = X` for `Ã = H⁻¹ • log X`,
`H ≠ 0` and `‖X - 1‖ < 1` in the spectral norm. -/
theorem exp_smul_modifiedSystem {X : Matrix (Fin n) (Fin n) ℝ} {H : ℝ} (hH : H ≠ 0)
    (hX : ‖opE (X - 1)‖ < 1) : exp (H • modifiedSystem H X) = X := by
  rw [modifiedSystem, smul_smul, mul_inv_cancel₀ hH, one_smul]
  open scoped Matrix.Norms.L2Operator in
  exact exp_log (𝔸 := Matrix (Fin n) (Fin n) ℝ) hX

/-- **A priori bound on the modified system:** `‖Ã‖ ≤ 3/2 · b` if `‖X - 1‖ ≤ b H`, `H > 0` and
`b H ≤ 1/3`. -/
theorem norm_opE_modifiedSystem_le {X : Matrix (Fin n) (Fin n) ℝ} {H b : ℝ} (hH : 0 < H)
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hbH : b * H ≤ 1 / 3) :
    ‖opE (modifiedSystem H X)‖ ≤ 3 / 2 * b := by
  have h1 := norm_opE_log_le hb (by linarith)
  have h2 := div_one_sub_le ((norm_nonneg _).trans hb) hbH
  rw [modifiedSystem, OneStep.opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le),
    inv_mul_le_iff₀ hH]
  exact (h1.trans h2).trans_eq (by ring)

/-- **The logarithm of the monolithic step:** `log (exp (H • A)) = H • A` for `H ≥ 0` and
`H ‖A‖ ≤ 1/4` in the spectral norm. -/
theorem log_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) : log (exp (H • A)) = H • A := by
  have hz : ‖opE (H • A)‖ ≤ 1 / 4 := by
    rw [OneStep.opE_smul, norm_smul, Real.norm_of_nonneg hH]
    exact hAH
  open scoped Matrix.Norms.L2Operator in
  exact log_exp_of_norm_le (𝔸 := Matrix (Fin n) (Fin n) ℝ) hz

/-- The modified system of the monolithic step is the monolithic system: `H⁻¹ • log U = A` for
`U = exp (H • A)`, `H > 0`, `H ‖A‖ ≤ 1/4`. -/
theorem modifiedSystem_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 < H)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) : modifiedSystem H (exp (H • A)) = A := by
  rw [modifiedSystem, log_exp_smul A hH.le hAH, smul_smul, inv_mul_cancel₀ hH.ne', one_smul]

/-- An exact scheme has no difference: `Δ = 0` for `X = U = exp (H • A)`, `H > 0`,
`H ‖A‖ ≤ 1/4`. -/
theorem difference_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 < H)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) : difference A H (exp (H • A)) = 0 := by
  rw [difference, modifiedSystem_exp_smul A hH hAH, sub_self]

/-- **The difference is `H⁻¹ (log X - log U)`:** `Δ = H⁻¹ • (log X - log U)` for
`U = exp (H • A)`, `H > 0`, `H ‖A‖ ≤ 1/4`. -/
theorem difference_eq_smul_log_sub_log (A X : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 < H)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    difference A H X = H⁻¹ • (log X - log (exp (H • A))) := by
  rw [log_exp_smul A hH.le hAH, smul_sub, smul_smul, inv_mul_cancel₀ hH.ne', one_smul,
    difference, modifiedSystem]

/-- The a priori passage for the logarithm of a matrix, spectral norm:
`‖log X - H A - (X - exp (H A))‖ ≤ K H³`, `K = diffLeadC b c ‖A‖`. -/
theorem norm_opE_log_sub_smul_sub_le {X A : Matrix (Fin n) (Fin n) ℝ} {H b c : ℝ} (hH : 0 ≤ H)
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - exp (H • A))‖ ≤ c * H ^ 2)
    (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (log X - H • A - (X - exp (H • A)))‖ ≤ diffLeadC b c ‖opE A‖ * H ^ 3 := by
  open scoped Matrix.Norms.L2Operator in
  exact norm_log_sub_smul_sub_le (𝔸 := Matrix (Fin n) (Fin n) ℝ) hH hb hc hbH hAH

variable {X A U : Matrix (Fin n) (Fin n) ℝ} {H b c : ℝ}

/-- **The a priori passage, one step** (the paper, Theorem `thm:half`, second statement). If
`H > 0`, `U = exp (H • A)`, `‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²`, `b H ≤ 1/3` and `H ‖A‖ ≤ 1/4`, then
`‖H • Δ - (X - U)‖ ≤ K H³` with `K = 3/2 · c · max b (4/3 ‖A‖)`. -/
theorem norm_opE_smul_difference_sub_le (hH : 0 < H) (hU : U = exp (H • A))
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - U)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (H • difference A H X - (X - U))‖ ≤ diffLeadC b c ‖opE A‖ * H ^ 3 := by
  subst hU
  rw [smul_difference A X hH.ne']
  exact norm_opE_log_sub_smul_sub_le hH.le hb hc hbH hAH

/-- **The difference is the one-step error divided by the macro step, up to `K H²`** (the paper,
Theorem `thm:half`: `Δ = (X - U)/H + O(H²)`). Under the hypotheses of
`norm_opE_smul_difference_sub_le`: `‖Δ - H⁻¹ • (X - U)‖ ≤ K H²`. -/
theorem norm_opE_difference_sub_le (hH : 0 < H) (hU : U = exp (H • A))
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - U)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (difference A H X - H⁻¹ • (X - U))‖ ≤ diffLeadC b c ‖opE A‖ * H ^ 2 := by
  have e : difference A H X - H⁻¹ • (X - U) = H⁻¹ • (H • difference A H X - (X - U)) := by
    rw [smul_sub H⁻¹ (H • difference A H X), smul_smul, inv_mul_cancel₀ hH.ne', one_smul]
  rw [e, OneStep.opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le),
    inv_mul_le_iff₀ hH]
  exact (norm_opE_smul_difference_sub_le hH hU hb hc hbH hAH).trans_eq (by ring)

/-- **The difference of a consistent scheme is of first order, a priori:**
`‖Δ‖ ≤ (c + K H) H` under the hypotheses of `norm_opE_smul_difference_sub_le`. -/
theorem norm_opE_difference_le (hH : 0 < H) (hU : U = exp (H • A))
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - U)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (difference A H X)‖ ≤ (c + diffLeadC b c ‖opE A‖ * H) * H := by
  have h1 := norm_opE_difference_sub_le hH hU hb hc hbH hAH
  have h2 : ‖opE (H⁻¹ • (X - U))‖ ≤ c * H := by
    rw [OneStep.opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le),
      inv_mul_le_iff₀ hH]
    exact hc.trans_eq (by ring)
  have h3 := norm_add_le (opE (difference A H X - H⁻¹ • (X - U))) (opE (H⁻¹ • (X - U)))
  rw [← OneStep.opE_add, sub_add_cancel] at h3
  exact h3.trans ((add_le_add h1 h2).trans_eq (by ring))

/-- `‖Δ‖ ≤ 3/2 · c H` under the hypotheses of `norm_opE_smul_difference_sub_le`. -/
theorem norm_opE_difference_le' (hH : 0 < H) (hU : U = exp (H • A))
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - U)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) : ‖opE (difference A H X)‖ ≤ 3 / 2 * c * H := by
  have hc0 : 0 ≤ c :=
    (mul_nonneg_iff_of_pos_right (pow_pos hH 2)).1 ((norm_nonneg _).trans hc)
  have h1 := norm_opE_difference_le hH hU hb hc hbH hAH
  have h2 := mul_le_mul_of_nonneg_right (diffLeadC_mul_le hc0 hH.le hbH hAH) hH.le
  linarith

/-- **The passage for a matrix element:**
`|⟪x, Δ y⟫ - H⁻¹ ⟪x, (X - U) y⟫| ≤ K H² ‖x‖ ‖y‖` under the hypotheses of
`norm_opE_smul_difference_sub_le`. -/
theorem abs_inner_difference_sub_le (hH : 0 < H) (hU : U = exp (H • A))
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - U)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (difference A H X) y⟫ - H⁻¹ * ⟪x, opE (X - U) y⟫| ≤
      diffLeadC b c ‖opE A‖ * H ^ 2 * (‖x‖ * ‖y‖) := by
  have h1 := OneStep.abs_inner_opE_le (difference A H X - H⁻¹ • (X - U)) x y
  rw [OneStep.inner_opE_sub, OneStep.inner_opE_smul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (norm_opE_difference_sub_le hH hU hb hc hbH hAH)
    (by positivity))

/-- **The passage for a matrix element, read from `y` to `x`:**
`|⟪y, Δ x⟫ - H⁻¹ ⟪y, (X - U) x⟫| ≤ K H² ‖x‖ ‖y‖`, the bound of `abs_inner_difference_sub_le`
with the norms in the order of `x`, `y`. -/
theorem abs_inner_difference_sub_le_swap (hH : 0 < H) (hU : U = exp (H • A))
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - U)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪y, opE (difference A H X) x⟫ - H⁻¹ * ⟪y, opE (X - U) x⟫| ≤
      diffLeadC b c ‖opE A‖ * H ^ 2 * (‖x‖ * ‖y‖) := by
  rw [mul_comm ‖x‖ ‖y‖]
  exact abs_inner_difference_sub_le hH hU hb hc hbH hAH y x

/-- **The passage for the total numerical damping:** `|ν + H⁻¹ tr (X - U)| ≤ n K H²` under the
hypotheses of `norm_opE_smul_difference_sub_le`, `n` the number of states. -/
theorem abs_numDamping_add_trace_le (hH : 0 < H) (hU : U = exp (H • A))
    (hb : ‖opE (X - 1)‖ ≤ b * H) (hc : ‖opE (X - U)‖ ≤ c * H ^ 2) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    |numDamping A H X + H⁻¹ * Matrix.trace (X - U)| ≤
      (n : ℝ) * (diffLeadC b c ‖opE A‖ * H ^ 2) := by
  have h1 := OneStep.abs_trace_le (difference A H X - H⁻¹ • (X - U))
  rw [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h1
  have e : numDamping A H X + H⁻¹ * Matrix.trace (X - U) =
      -(Matrix.trace (difference A H X) - H⁻¹ * Matrix.trace (X - U)) := by
    rw [numDamping]
    ring
  rw [e, abs_neg]
  exact h1.trans (mul_le_mul_of_nonneg_left (norm_opE_difference_sub_le hH hU hb hc hbH hAH)
    (Nat.cast_nonneg n))

end Matrices

end CoSimFoundations
