/-
A lossless monolithic system: conservation of the energy at the communication points and the
numerical dissipation (the paper, Proposition `prop:basis` (iv)).

**Paper.** "If the monolithic system is lossless, `R = 0`, the co-simulation conserves the energy
from every initial state at every communication point if and only if `ΔR = 0`." Here `A = J - R`
with `J` skew and `R` symmetric, so that lossless means `Aᵀ = -A`; the communication points are
`x^k = X^k x^0`, the energy is `½ |x|²`; the modified system is `Ã = (1/H) Log X` with the
principal logarithm, `Δ = Ã - A`, and `ΔR = -sym Δ` (`numDissipation`).

**What is formalised.** Mathlib has no principal logarithm of a matrix, so the statement is
split.

1. Without a logarithm (`energy_conserved_iff_orthogonal`): `X` conserves the energy from every
   initial state at every communication point iff `Xᵀ X = 1`. (One step suffices; a symmetric
   matrix with the quadratic form of the identity is the identity, by polarisation.)
2. For every matrix `Ã` with `exp (H • Ã) = X` (every real logarithm, principal or not) and a
   lossless `A`:
   * `ΔR = 0` iff `Ã` is skew (`numDissipation_eq_zero_iff`);
   * if `ΔR = 0`, the energy is conserved (`energy_conserved_of_numDissipation_eq_zero`): the
     exponential of a skew matrix is orthogonal (`transpose_exp_mul_exp_of_skew`);
   * if the energy is conserved, the total numerical dissipation vanishes, `tr ΔR = 0`
     (`trace_numDissipation_eq_zero_of_energy_conserved`), from `det X = e^{H tr Ã}`.
   The direction "energy conserved implies `ΔR = 0`" is false for a logarithm that is not the
   principal one and needs the uniqueness of the principal logarithm; it is not formalised in
   this generality.
3. For small steps the equivalence is proved with the logarithm series `log X` of Mathlib
   (`lossless_energy_iff_small_step`): if `‖X - 1‖ ≤ 1/3` in the spectral norm, then
   `Ã = H⁻¹ • log X` satisfies `exp (H • Ã) = X`, and the energy is conserved iff `ΔR = 0`. The
   new direction is `transpose_log_eq_neg_of_orthogonal`: the logarithm of an orthogonal matrix
   within `1/3` of the identity is skew. Proof, in a real Banach algebra with a continuous star
   (`star_log_eq_neg_of_unitary`): `star (log x) = log (star x)`; `log (star x)` and `log x`
   commute and `exp (log (star x) + log x) = star x * x = 1`; both logarithms have norm at most
   `1/2` (`norm_log_le`), and the only `z` with `‖z‖ ≤ 1` and `exp z = 1` is `0`
   (`eq_zero_of_exp_eq_one`). That the series is the principal logarithm for `‖X - 1‖ < 1` is a
   standard fact and is not formalised.
-/
import CoSimFoundations.DetExp
import CoSimFoundations.ExpLog
import CoSimFoundations.AdamsConstants
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds

open NormedSpace Matrix Finset
open scoped Nat

namespace CoSimFoundations

section Orthogonal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(X x) · (X y) = x · (Xᵀ X y)`. -/
theorem mulVec_dotProduct_mulVec (X : Matrix n n ℝ) (x y : n → ℝ) :
    (X *ᵥ x) ⬝ᵥ (X *ᵥ y) = x ⬝ᵥ ((Xᵀ * X) *ᵥ y) := by
  rw [← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]

/-- A symmetric matrix whose quadratic form is that of the identity is the identity
(polarisation). -/
theorem eq_one_of_dotProduct_mulVec_self {S : Matrix n n ℝ} (hS : Sᵀ = S)
    (h : ∀ x : n → ℝ, x ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ x) : S = 1 := by
  have hsym : ∀ x y : n → ℝ, y ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ (S *ᵥ y) := by
    intro x y
    rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]
  have hpol : ∀ x y : n → ℝ, x ⬝ᵥ (S *ᵥ y) = x ⬝ᵥ y := by
    intro x y
    have h1 := h (x + y)
    simp only [mulVec_add, add_dotProduct, dotProduct_add] at h1
    rw [h x, h y, hsym x y, dotProduct_comm y x] at h1
    linarith
  ext i j
  have h2 := hpol (Pi.single i 1) (Pi.single j 1)
  rw [single_one_dotProduct, single_one_dotProduct, mulVec_single_one] at h2
  simpa [Matrix.one_apply, Pi.single_apply] using h2

/-- **One step conserves the energy from every state iff the step is orthogonal.** -/
theorem dotProduct_mulVec_self_eq_iff (X : Matrix n n ℝ) :
    (∀ x : n → ℝ, (X *ᵥ x) ⬝ᵥ (X *ᵥ x) = x ⬝ᵥ x) ↔ Xᵀ * X = 1 := by
  constructor
  · intro h
    refine eq_one_of_dotProduct_mulVec_self ?_ fun x => ?_
    · rw [transpose_mul, transpose_transpose]
    · rw [← mulVec_dotProduct_mulVec, h x]
  · intro h x
    rw [mulVec_dotProduct_mulVec, h, one_mulVec]

/-- The powers of an orthogonal matrix are orthogonal. -/
theorem transpose_pow_mul_pow {X : Matrix n n ℝ} (h : Xᵀ * X = 1) (k : ℕ) :
    (X ^ k)ᵀ * X ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, h, Matrix.one_mul, ih]

/-- **Conservation of the energy at every communication point, without a logarithm** (the paper,
Proposition `prop:basis` (iv), the left side of the equivalence): the co-simulation with the
one-step map `X` conserves `|x|²` from every initial state at every communication point,
`|X^k x|² = |x|²`, if and only if `X` is orthogonal, `Xᵀ X = 1`. -/
theorem energy_conserved_iff_orthogonal (X : Matrix n n ℝ) :
    (∀ (k : ℕ) (x : n → ℝ), (X ^ k *ᵥ x) ⬝ᵥ (X ^ k *ᵥ x) = x ⬝ᵥ x) ↔ Xᵀ * X = 1 := by
  constructor
  · intro h
    refine (dotProduct_mulVec_self_eq_iff X).1 fun x => ?_
    have h1 := h 1 x
    rwa [pow_one] at h1
  · intro h k
    exact (dotProduct_mulVec_self_eq_iff (X ^ k)).2 (transpose_pow_mul_pow h k)

/-- **The exponential of a skew matrix is orthogonal.** -/
theorem transpose_exp_mul_exp_of_skew {At : Matrix n n ℝ} (H : ℝ) (h : Atᵀ = -At) :
    (exp (H • At))ᵀ * exp (H • At) = 1 := by
  rw [← exp_transpose, transpose_smul, h, smul_neg,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl (H • At)).neg_left), neg_add_cancel, exp_zero]

/-- **The numerical dissipation** `ΔR = -sym Δ`, `Δ = Ã - A`, of a co-simulation with the
modified system `Ã` of a monolithic system `A` (the paper, Proposition `prop:basis`). -/
noncomputable def numDissipation (A At : Matrix n n ℝ) : Matrix n n ℝ :=
  -((1 / 2 : ℝ) • ((At - A) + (At - A)ᵀ))

/-- For a lossless monolithic system (`Aᵀ = -A`) the numerical dissipation vanishes iff the
modified system is skew. -/
theorem numDissipation_eq_zero_iff {A At : Matrix n n ℝ} (hA : Aᵀ = -A) :
    numDissipation A At = 0 ↔ Atᵀ = -At := by
  unfold numDissipation
  rw [neg_eq_zero, smul_eq_zero_iff_right (by norm_num : (1 / 2 : ℝ) ≠ 0), transpose_sub, hA]
  have h' : At - A + (Atᵀ - -A) = At + Atᵀ := by abel
  rw [h']
  constructor
  · intro h
    exact eq_neg_of_add_eq_zero_right h
  · intro h
    rw [h, add_neg_cancel]

/-- **Proposition `prop:basis` (iv), the direction from the numerical dissipation to the
energy**, for every real logarithm: if the monolithic system is lossless, `Ã` is a matrix with
`exp (H • Ã) = X` and its numerical dissipation vanishes, then the co-simulation conserves the
energy from every initial state at every communication point. -/
theorem energy_conserved_of_numDissipation_eq_zero {A At X : Matrix n n ℝ} {H : ℝ}
    (hA : Aᵀ = -A) (hX : exp (H • At) = X) (hR : numDissipation A At = 0) (k : ℕ) (x : n → ℝ) :
    (X ^ k *ᵥ x) ⬝ᵥ (X ^ k *ᵥ x) = x ⬝ᵥ x := by
  refine (energy_conserved_iff_orthogonal X).2 ?_ k x
  rw [← hX]
  exact transpose_exp_mul_exp_of_skew H ((numDissipation_eq_zero_iff hA).1 hR)

/-- **What the converse gives for every real logarithm:** if the monolithic system is lossless,
`exp (H • Ã) = X`, `H ≠ 0`, and the co-simulation conserves the energy, then the total numerical
dissipation vanishes, `tr ΔR = 0`. (That `ΔR = 0` needs the principal logarithm.) -/
theorem trace_numDissipation_eq_zero_of_energy_conserved {A At X : Matrix n n ℝ} {H : ℝ}
    (hH : H ≠ 0) (hA : Aᵀ = -A) (hX : exp (H • At) = X)
    (hE : ∀ (k : ℕ) (x : n → ℝ), (X ^ k *ᵥ x) ⬝ᵥ (X ^ k *ᵥ x) = x ⬝ᵥ x) :
    (numDissipation A At).trace = 0 := by
  have hO := (energy_conserved_iff_orthogonal X).1 hE
  have hd : X.det * X.det = 1 := by
    have h := congrArg det hO
    rwa [det_mul, det_transpose, det_one] at h
  rw [← hX, det_exp, trace_smul, smul_eq_mul, ← Real.exp_add, Real.exp_eq_one_iff] at hd
  have hAt : At.trace = 0 := by
    have h2 : H * At.trace = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_left hH
  have hAtr : A.trace = 0 := by
    have h := congrArg trace hA
    rw [trace_transpose, trace_neg] at h
    linarith
  unfold numDissipation
  rw [trace_neg, trace_smul, trace_add, trace_transpose, trace_sub, hAt, hAtr]
  simp

end Orthogonal

section StarAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The logarithm series near one: `‖log x‖ ≤ ρ / (1 - ρ)` for `‖x - 1‖ ≤ ρ < 1`. -/
theorem norm_log_le {x : 𝔸} {ρ : ℝ} (hρ : ‖x - 1‖ ≤ ρ) (hρ1 : ρ < 1) :
    ‖log x‖ ≤ ρ / (1 - ρ) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  have hne : 1 - ρ ≠ 0 := (sub_pos.2 hρ1).ne'
  rw [congrFun (log_eq_tsum ℝ) x]
  have hg : HasSum (fun n : ℕ => ρ ^ n - if n = 0 then 1 else 0) (ρ / (1 - ρ)) := by
    have h := (hasSum_geometric_of_lt_one hρ0 hρ1).sub (hasSum_ite_eq 0 (1 : ℝ))
    have e : (1 - ρ)⁻¹ - 1 = ρ / (1 - ρ) := by
      rw [eq_div_iff hne, sub_mul, inv_mul_cancel₀ hne]
      ring
    rwa [e] at h
  refine tsum_of_norm_bounded hg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : ‖((-1 : ℝ) ^ (n + 1) / n)‖ ≤ 1 := by
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast,
        div_le_one (by exact_mod_cast hn)]
      exact_mod_cast hn
    have h2 : ‖(x - 1) ^ n‖ ≤ ρ ^ n :=
      (norm_pow_le' _ hn).trans (pow_le_pow_left₀ (norm_nonneg _) hρ n)
    have h3 : (if n = 0 then (1 : ℝ) else 0) = 0 := by simp [hn.ne']
    rw [h3, sub_zero, norm_smul]
    calc ‖((-1 : ℝ) ^ (n + 1) / n)‖ * ‖(x - 1) ^ n‖ ≤ 1 * ρ ^ n :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = ρ ^ n := one_mul _

/-- The exponential takes the value one only at zero on the unit ball: if `‖z‖ ≤ 1` and
`exp z = 1` then `z = 0`. -/
theorem eq_zero_of_exp_eq_one {z : 𝔸} (hz : ‖z‖ ≤ 1) (h : exp z = 1) : z = 0 := by
  have h1 := norm_exp_sub_sum_le_expTail z (b := 2) (by norm_num)
  have h2 : exp z - ∑ n ∈ range 2, ((n ! : ℝ)⁻¹) • z ^ n = -z := by
    rw [h]
    simp [Finset.sum_range_succ]
  rw [h2, norm_neg] at h1
  have h3 := expTail_mul_le 2 (zero_le_one (α := ℝ)) (norm_nonneg z) hz
  rw [one_mul, expTail_two_one] at h3
  have h4 := Real.exp_one_lt_d9
  have h5 : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  have h6 : ‖z‖ ^ 2 * (Real.exp 1 - 2) ≤ ‖z‖ * (Real.exp 1 - 2) :=
    mul_le_mul_of_nonneg_right h5 (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have h7 := mul_nonneg (norm_nonneg z) (by linarith : (0 : ℝ) ≤ 2.7182818286 - Real.exp 1)
  have h8 : ‖z‖ ≤ 0 := by linarith
  exact norm_le_zero_iff.1 h8

variable [StarRing 𝔸] [ContinuousStar 𝔸]

/-- **The logarithm of a unitary element near one is skew.** In a real Banach algebra with a
continuous star: if `star x * x = 1 = x * star x`, `‖x - 1‖ ≤ 1/3` and `‖star x - 1‖ ≤ 1/3`, then
`star (log x) = -log x`. -/
theorem star_log_eq_neg_of_unitary {x : 𝔸} (h1 : star x * x = 1) (h2 : x * star x = 1)
    (hx : ‖x - 1‖ ≤ 1 / 3) (hx' : ‖star x - 1‖ ≤ 1 / 3) : star (log x) = -log x := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [star_log]
  have ea : exp (log (star x)) = star x := exp_log (by linarith)
  have eb : exp (log x) = x := exp_log (by linarith)
  have hc : Commute (log (star x)) (log x) :=
    Commute.log (show Commute (star x) x from h1.trans h2.symm)
  have hz : exp (log (star x) + log x) = 1 := by
    rw [exp_add_of_commute hc, ea, eb, h1]
  have hn : ‖log (star x) + log x‖ ≤ 1 := by
    have ha := norm_log_le hx' (by norm_num)
    have hb := norm_log_le hx (by norm_num)
    have h3 := norm_add_le (log (star x)) (log x)
    norm_num at ha hb
    linarith
  exact eq_neg_of_add_eq_zero_left (eq_zero_of_exp_eq_one hn hz)

end StarAlgebra

section SmallStep

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The logarithm of an orthogonal matrix near the identity is skew**: if `Xᵀ X = 1` and
`‖X - 1‖ ≤ 1/3` in the spectral norm, then `(log X)ᵀ = -log X`, `log` the logarithm series. -/
theorem transpose_log_eq_neg_of_orthogonal {X : Matrix n n ℝ} (hX : Xᵀ * X = 1)
    (hX1 : ‖X - 1‖ ≤ 1 / 3) : (log X)ᵀ = -log X := by
  have hstar : ∀ M : Matrix n n ℝ, star M = Mᵀ := fun M => by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have h2 : X * Xᵀ = 1 := mul_eq_one_comm.1 hX
  have hn : ‖Xᵀ - 1‖ ≤ 1 / 3 := by
    have e : Xᵀ - 1 = (X - 1)ᴴ := by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one]
    rw [e, l2_opNorm_conjTranspose]
    exact hX1
  have h := star_log_eq_neg_of_unitary (x := X) (by rw [hstar]; exact hX)
    (by rw [hstar]; exact h2) hX1 (by rw [hstar]; exact hn)
  rwa [hstar] at h

/-- **Proposition `prop:basis` (iv) for small steps.** Let the monolithic system be lossless,
`Aᵀ = -A`, let `H ≠ 0`, and let the one-step map satisfy `‖X - 1‖ ≤ 1/3` in the spectral norm.
Then `Ã = H⁻¹ • log X` (the logarithm series) is a modified system, `exp (H • Ã) = X`, and the
co-simulation conserves the energy from every initial state at every communication point if and
only if the numerical dissipation of `Ã` vanishes. -/
theorem lossless_energy_iff_small_step {A X : Matrix n n ℝ} {H : ℝ} (hH : H ≠ 0)
    (hA : Aᵀ = -A) (hX1 : ‖X - 1‖ ≤ 1 / 3) :
    exp (H • (H⁻¹ • log X)) = X ∧
      ((∀ (k : ℕ) (x : n → ℝ), (X ^ k *ᵥ x) ⬝ᵥ (X ^ k *ᵥ x) = x ⬝ᵥ x) ↔
        numDissipation A (H⁻¹ • log X) = 0) := by
  have hexp : exp (H • (H⁻¹ • log X)) = X := by
    rw [smul_smul, mul_inv_cancel₀ hH, one_smul]
    exact exp_log (by linarith)
  refine ⟨hexp, ?_⟩
  rw [energy_conserved_iff_orthogonal, numDissipation_eq_zero_iff hA, transpose_smul]
  constructor
  · intro hO
    rw [transpose_log_eq_neg_of_orthogonal hO hX1, smul_neg]
  · intro hS
    have h := transpose_exp_mul_exp_of_skew H
      (show (H⁻¹ • log X)ᵀ = -(H⁻¹ • log X) by rw [transpose_smul]; exact hS)
    rwa [hexp] at h

end SmallStep

end CoSimFoundations
