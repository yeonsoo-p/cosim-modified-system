/-
The negative damping of a held interface in Jacobi mode, in an exact form (the paper,
Proposition 6.2, formula (31): `ν = -H Σ_{links} ‖A_ij‖_F² + O(H²)`, proved there to leading
order).

In Jacobi mode the one-step map is `X = F (1 + Z)` with `Z = F⁻¹ G C`, which vanishes in the
diagonal blocks, so `tr Z = 0`. With signal access `det F = e^{H tr A} = det U`, hence the defect
`D = X U⁻¹` has `det D = det (1 + Z)` and the numerical damping is `H ν = -ln det (1 + Z)`.

1. **Logarithm, third-order remainder.** In a real Banach algebra, for `‖y‖ < 1`:
     `‖log (1 + y) - (y - ½ y²)‖ ≤ ‖y‖³ / (3 (1 - ‖y‖))`
   (tail of the series, compared with a geometric series).

2. **Determinant near the identity.** For a real `n × n` matrix with spectral norm `‖Z‖ < 1`:
   `det (1 + Z) = e^{tr log (1 + Z)} > 0` (`exp_log_one_add` of `ExpLog`, `det_exp` of `DetExp`) and
     `|ln det (1 + Z) - (tr Z - ½ tr Z²)| ≤ n ‖Z‖³ / (3 (1 - ‖Z‖))`,
   since `|tr T| ≤ n ‖T‖`. For `tr Z = 0` and `‖Z‖ ≤ ½`:
     `|ln det (1 + Z) + ½ tr Z²| ≤ ⅔ n ‖Z‖³`.

3. **Formula (31) with its remainder.** If `Z = H K + E₂` with `K` skew (`Kᵀ = -K`: the coupling
   part of `A` in energy coordinates), `‖E₂‖ ≤ e H²`, `tr Z = 0`, `H ≥ 0` and
   `(‖K‖ + e H) H ≤ ½`, then
     `|ln det (1 + Z) - ½H² Σ_{p,q} (K p q)²| ≤ n (⅔ (‖K‖ + e H)³ + ‖K‖ e + ½ e² H) H³`.
   `½ Σ_{p,q} (K p q)² = Σ_{links} ‖A_ij‖_F²`, and `ln det (1 + Z) = -H ν`: the negative damping
   `ν = -H Σ_{links} ‖A_ij‖_F²` holds up to `n (…) H²`.

4. `det D = det (1 + Z)` if `X = F (1 + Z) = D U` and `det F = det U ≠ 0` (signal access).

Not formalised: that `Z = H K + E₂` with a given `e` for the scheme with signal access (the
paper's `F⁻¹ G C = H (A - diag A_i) + O(H²)`).
-/
import CoSimFoundations.ForcedBlock
import CoSimFoundations.ExpLog
import CoSimFoundations.DetExp

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

section Log

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `|cₙ| ≤ 1` for the coefficients `cₙ = (-1)^(n+1)/n` of the logarithm. -/
theorem abs_logCoeff_le_one (k : ℕ) : |logCoeff k| ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [logCoeff]
  · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [logCoeff, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
    exact (div_le_one (by linarith)).2 h1

/-- The terms of the logarithm series are bounded by a geometric series. -/
theorem norm_logCoeff_smul_pow_le (y : 𝔸) (k : ℕ) : ‖logCoeff k • y ^ k‖ ≤ ‖y‖ ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [logCoeff]
  · rw [norm_smul, Real.norm_eq_abs]
    calc |logCoeff k| * ‖y ^ k‖ ≤ 1 * ‖y‖ ^ k :=
          mul_le_mul (abs_logCoeff_le_one k) (norm_pow_le' y hk) (norm_nonneg _) zero_le_one
      _ = ‖y‖ ^ k := one_mul _

/-- The logarithm series converges to `log (1 + y)` for `‖y‖ < 1`. -/
theorem hasSum_log_one_add {y : 𝔸} (hy : ‖y‖ < 1) :
    HasSum (fun k : ℕ => logCoeff k • y ^ k) (NormedSpace.log (1 + y)) := by
  have hs : Summable fun k : ℕ => logCoeff k • y ^ k :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg y) hy)
      (norm_logCoeff_smul_pow_le y)
  have h := log_one_add_smul 1 y
  simp only [one_smul, one_pow, mul_one] at h
  rw [h]
  exact hs.hasSum

/-- **Third-order remainder of the logarithm:** for `‖y‖ < 1`,
`‖log (1 + y) - (y - ½ y²)‖ ≤ ‖y‖³ / (3 (1 - ‖y‖))`. -/
theorem norm_log_one_add_sub_le {y : 𝔸} (hy : ‖y‖ < 1) :
    ‖NormedSpace.log (1 + y) - (y - (2 : ℝ)⁻¹ • y ^ 2)‖ ≤ ‖y‖ ^ 3 / (3 * (1 - ‖y‖)) := by
  have hf := hasSum_log_one_add hy
  have htail := (hasSum_nat_add_iff' 3).2 hf
  have hsum : ∑ k ∈ Finset.range 3, logCoeff k • y ^ k = y - (2 : ℝ)⁻¹ • y ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, logCoeff]
    norm_num
    rw [sub_eq_add_neg]
  rw [hsum] at htail
  have h1y : 0 < 1 - ‖y‖ := by linarith
  have hg : HasSum (fun i : ℕ => ‖y‖ ^ 3 / 3 * ‖y‖ ^ i) (‖y‖ ^ 3 / 3 * (1 - ‖y‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg y) hy).mul_left _
  have hle := htail.norm_le_of_bounded hg (fun i => by
    rw [norm_smul, Real.norm_eq_abs]
    have hc : |logCoeff (i + 3)| ≤ 1 / 3 := by
      have h3 : (3 : ℝ) ≤ ((i + 3 : ℕ) : ℝ) := by
        push_cast
        linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      rw [logCoeff, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
      exact one_div_le_one_div_of_le (by norm_num) h3
    have hp : ‖y ^ (i + 3)‖ ≤ ‖y‖ ^ 3 * ‖y‖ ^ i := by
      rw [← pow_add, add_comm 3 i]
      exact norm_pow_le' y (by omega)
    calc |logCoeff (i + 3)| * ‖y ^ (i + 3)‖ ≤ 1 / 3 * (‖y‖ ^ 3 * ‖y‖ ^ i) :=
          mul_le_mul hc hp (norm_nonneg _) (by norm_num)
      _ = ‖y‖ ^ 3 / 3 * ‖y‖ ^ i := by ring)
  calc ‖NormedSpace.log (1 + y) - (y - (2 : ℝ)⁻¹ • y ^ 2)‖ ≤ ‖y‖ ^ 3 / 3 * (1 - ‖y‖)⁻¹ := hle
    _ = ‖y‖ ^ 3 / (3 * (1 - ‖y‖)) := by
      field_simp

end Log

variable {n : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- **The determinant near the identity:** `det (1 + Z) = e^{tr log (1 + Z)}` for `‖Z‖ < 1`. -/
theorem det_one_add_eq_exp {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : ‖opE Z‖ < 1) :
    (1 + Z).det = Real.exp (NormedSpace.log (1 + Z)).trace := by
  have h := exp_log_one_add (𝔸 := Matrix (Fin n) (Fin n) ℝ) (y := Z) hZ
  rw [← det_exp, h]

/-- `det (1 + Z) > 0` for `‖Z‖ < 1`. -/
theorem det_one_add_pos {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : ‖opE Z‖ < 1) : 0 < (1 + Z).det := by
  rw [det_one_add_eq_exp hZ]
  exact Real.exp_pos _

open scoped Matrix.Norms.L2Operator in
/-- **Logarithm of the determinant near the identity, with its remainder:** for `‖Z‖ < 1`,
`|ln det (1 + Z) - (tr Z - ½ tr Z²)| ≤ n ‖Z‖³ / (3 (1 - ‖Z‖))`. -/
theorem abs_log_det_one_add_sub_le {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : ‖opE Z‖ < 1) :
    |Real.log (1 + Z).det - (Z.trace - (Z * Z).trace / 2)| ≤
      n * (‖opE Z‖ ^ 3 / (3 * (1 - ‖opE Z‖))) := by
  have h1 := norm_log_one_add_sub_le (𝔸 := Matrix (Fin n) (Fin n) ℝ) (y := Z) hZ
  have h2 := abs_trace_le (NormedSpace.log (1 + Z) - (Z - (2 : ℝ)⁻¹ • Z ^ 2))
  have h3 : (NormedSpace.log (1 + Z) - (Z - (2 : ℝ)⁻¹ • Z ^ 2)).trace =
      Real.log (1 + Z).det - (Z.trace - (Z * Z).trace / 2) := by
    rw [det_one_add_eq_exp hZ, Real.log_exp, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_smul, sq, smul_eq_mul]
    ring
  rw [h3] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n))

/-- **Zero trace, `‖Z‖ ≤ ½`:** `|ln det (1 + Z) + ½ tr Z²| ≤ ⅔ n ‖Z‖³`. -/
theorem abs_log_det_one_add_le {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : ‖opE Z‖ ≤ 1 / 2)
    (htr : Z.trace = 0) :
    |Real.log (1 + Z).det + (Z * Z).trace / 2| ≤ n * (2 / 3 * ‖opE Z‖ ^ 3) := by
  have h := abs_log_det_one_add_sub_le (Z := Z) (by linarith)
  rw [htr, zero_sub, sub_neg_eq_add] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  have h0 : 0 ≤ ‖opE Z‖ ^ 3 := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The trace of the square of a skew matrix is minus the sum of the squares of its entries. -/
theorem trace_mul_self_of_skew {K : Matrix (Fin n) (Fin n) ℝ} (hK : Kᵀ = -K) :
    (K * K).trace = -∑ p, ∑ q, K p q ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h := congrFun (congrFun hK p) q
  rw [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h]
  ring

/-- **Formula (31) with its remainder.** `Z = H K + E₂` with `K` skew, `‖E₂‖ ≤ e H²`, `tr Z = 0`,
`H ≥ 0`, `(‖K‖ + e H) H ≤ ½`:
`|ln det (1 + Z) - ½H² Σ_{p,q} (K p q)²| ≤ n (⅔ (‖K‖ + e H)³ + ‖K‖ e + ½ e² H) H³`.
With `ln det (1 + Z) = -H ν` and `½ Σ_{p,q} (K p q)² = Σ_{links} ‖A_ij‖_F²` this is
`ν = -H Σ_{links} ‖A_ij‖_F²` up to `n (…) H²`: the negative damping of a held interface. -/
theorem negative_damping {Z K E₂ : Matrix (Fin n) (Fin n) ℝ} {H e : ℝ} (hH : 0 ≤ H)
    (hZ : Z = H • K + E₂) (hK : Kᵀ = -K) (he : ‖opE E₂‖ ≤ e * H ^ 2) (htr : Z.trace = 0)
    (hsmall : (‖opE K‖ + e * H) * H ≤ 1 / 2) :
    |Real.log (1 + Z).det - H ^ 2 / 2 * ∑ p, ∑ q, K p q ^ 2| ≤
      n * ((2 / 3 * (‖opE K‖ + e * H) ^ 3 + ‖opE K‖ * e + e ^ 2 * H / 2) * H ^ 3) := by
  have heH : 0 ≤ e * H ^ 2 := le_trans (norm_nonneg _) he
  have hZn : ‖opE Z‖ ≤ (‖opE K‖ + e * H) * H := by
    rw [hZ, opE_add, opE_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hH]
    nlinarith
  have h1 := abs_le.1 (abs_log_det_one_add_le (Z := Z) (hZn.trans hsmall) htr)
  have hZ3 : ‖opE Z‖ ^ 3 ≤ ((‖opE K‖ + e * H) * H) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hZn 3
  have htrZ : (Z * Z).trace =
      H ^ 2 * (K * K).trace + 2 * H * (K * E₂).trace + (E₂ * E₂).trace := by
    rw [hZ]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm E₂ K]
    ring
  rw [trace_mul_self_of_skew hK] at htrZ
  have h2 : |(K * E₂).trace| ≤ n * (‖opE K‖ * (e * H ^ 2)) := by
    refine (abs_trace_le _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
    rw [opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))
  have h3 : |(E₂ * E₂).trace| ≤ n * (e * H ^ 2 * (e * H ^ 2)) := by
    refine (abs_trace_le _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
    rw [opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul he he (norm_nonneg _) heH)
  have h2' := abs_le.1 h2
  have h3' := abs_le.1 h3
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hZ3' : (n : ℝ) * (2 / 3 * ‖opE Z‖ ^ 3) ≤
      n * (2 / 3 * ((‖opE K‖ + e * H) * H) ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hn
  have hHt1 : H * (-(n * (‖opE K‖ * (e * H ^ 2)))) ≤ H * (K * E₂).trace :=
    mul_le_mul_of_nonneg_left h2'.1 hH
  have hHt2 : H * (K * E₂).trace ≤ H * (n * (‖opE K‖ * (e * H ^ 2))) :=
    mul_le_mul_of_nonneg_left h2'.2 hH
  have hfin : (n : ℝ) * ((2 / 3 * (‖opE K‖ + e * H) ^ 3 + ‖opE K‖ * e + e ^ 2 * H / 2) * H ^ 3) =
      n * (2 / 3 * ((‖opE K‖ + e * H) * H) ^ 3) + H * (n * (‖opE K‖ * (e * H ^ 2))) +
        n * (e * H ^ 2 * (e * H ^ 2)) / 2 := by ring
  rw [hfin, abs_le]
  constructor <;> linarith [h1.1, h1.2, h3'.1, h3'.2]

/-- **The defect has the determinant of `1 + Z`.** If `X = F (1 + Z) = D U` and
`det F = det U ≠ 0` (signal access: `F = diag(e^{H A_i})`, `det F = e^{H tr A} = det U`), then
`det D = det (1 + Z)`; so `-H ν = ln det D = ln det (1 + Z)`. -/
theorem det_defect_eq {X F Z D U : Matrix (Fin n) (Fin n) ℝ} (hX : X = F * (1 + Z))
    (hD : X = D * U) (hF : F.det = U.det) (hU : U.det ≠ 0) : D.det = (1 + Z).det := by
  have h := congrArg Matrix.det (hX.symm.trans hD)
  rw [Matrix.det_mul, Matrix.det_mul, hF, mul_comm D.det] at h
  exact (mul_left_cancel₀ hU h).symm

end OneStep

end CoSimFoundations
