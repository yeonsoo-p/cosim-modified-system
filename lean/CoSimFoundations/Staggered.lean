/-
Staggered readout (the paper, Proposition 4.8): the identities, and the second order of the
right-hand side with explicit constants.

Setting. `a`, `b` are elements of a real Banach algebra, in the paper the matrices `A_a` and `A_b`
of the two classes of a bipartite coupling graph, `A = A_a + A_b`. With

  `X = exp (H b) * exp (H a)`,   `W = exp ((H/2) a)`,   `W⁻¹ = exp (-(H/2) a)`,

* `W X W⁻¹ = exp ((H/2) a) * exp (H b) * exp ((H/2) a)` (`staggered_conj`; for matrices with the
  matrix inverse `staggered_conj_matrix`), because `exp (H a) * exp (-(H/2) a) = exp ((H/2) a)`;
* `W X^k W⁻¹ = (exp ((H/2) a) * exp (H b) * exp ((H/2) a))^k` (`staggered_conj_pow`).

The right-hand side is the Strang splitting of `a + b`. Its local error is of third order with an
explicit constant: for `H ≥ 0` and `μ = ‖a‖ + ‖b‖`,

  `‖exp ((H/2) a) * exp (H b) * exp ((H/2) a) - exp (H (a + b))‖ ≤ μ³/3 · e^{H μ} · H³`
  (`norm_staggered_sub_exp_le`), and `≤ μ³ H³` if `H μ ≤ 1` (`norm_staggered_sub_exp_le_of_le_one`).

Proof of the local error. With `p = e^x - 1`, `q = e^y - 1`, `α = e^x - 1 - x`, `β = e^y - 1 - y`
and the third-order remainders `ρ(z) = e^z - 1 - z - z²/2`,

  `e^x e^y e^x - e^{2x+y} = α q + x β + α p + x α + β p + y α + p q p + 2 ρ(x) + ρ(y) - ρ(2x+y)`
  (`strang_identity`: the terms of degree at most two cancel), and with the Taylor remainders of
`ForcedBlock` every term is at most its monomial in `u = ‖x‖`, `v = ‖y‖` times `e^{2u+v}`; the
monomials add up to `(2u+v)³/3` (`strang_scalar_bound`).

Over a run (the last statement of the proposition), in a Banach algebra with `‖1‖ = 1`: for
`k H ≤ T`,

  `‖W X^k W⁻¹ - exp (H (a + b))^k‖ ≤ (μ³/3 · T · e^{μ T}) · H²`
  (`norm_staggered_pow_sub_exp_pow_le`), by telescoping (`OneStep.norm_pow_succ_sub_pow_succ_le`).

Not formalised here: that the zero-order hold which executes class `a` and then class `b` has the
one-step map `exp (H A_b) * exp (H A_a)`.
-/
import CoSimFoundations.ForcedParts
import CoSimFoundations.BarrierConstants

open NormedSpace

namespace CoSimFoundations

section Identity

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp x * exp (-x) = 1`. -/
theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.refl x).neg_right, add_neg_cancel, exp_zero]

/-- `exp (-x) * exp x = 1`. -/
theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.refl x).neg_left, neg_add_cancel, exp_zero]

/-- **Staggered readout, the identity** (the paper, Proposition 4.8, equation (staggered)): with
`X = exp (H b) * exp (H a)` and `W = exp ((H/2) a)`, whose inverse is `exp (-(H/2) a)`
(`exp_mul_exp_neg`, `exp_neg_mul_exp`), `W X W⁻¹ = exp ((H/2) a) * exp (H b) * exp ((H/2) a)`. -/
theorem staggered_conj (a b : 𝔸) (H : ℝ) :
    exp ((H / 2) • a) * (exp (H • b) * exp (H • a)) * exp (-((H / 2) • a)) =
      exp ((H / 2) • a) * exp (H • b) * exp ((H / 2) • a) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hc : Commute (H • a) (-((H / 2) • a)) :=
    (((Commute.refl a).smul_left H).smul_right (H / 2)).neg_right
  have h1 : exp (H • a) * exp (-((H / 2) • a)) = exp ((H / 2) • a) := by
    rw [← exp_add_of_commute hc]
    congr 1
    module
  rw [mul_assoc, mul_assoc, h1, ← mul_assoc]

/-- Conjugation commutes with powers. -/
theorem mul_pow_mul_eq_pow {R : Type*} [Monoid R] {W W' : R} (h : W' * W = 1) (h' : W * W' = 1)
    (X : R) (k : ℕ) : W * X ^ k * W' = (W * X * W') ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, h']
  | succ k ih =>
    have hz : ∀ z : R, W' * (W * z) = z := fun z => by rw [← mul_assoc, h, one_mul]
    rw [pow_succ, pow_succ, ← ih]
    simp only [mul_assoc, hz]

/-- **Staggered readout over a run:** `W X^k W⁻¹` is the `k`-th power of
`exp ((H/2) a) * exp (H b) * exp ((H/2) a)`. -/
theorem staggered_conj_pow (a b : 𝔸) (H : ℝ) (k : ℕ) :
    exp ((H / 2) • a) * (exp (H • b) * exp (H • a)) ^ k * exp (-((H / 2) • a)) =
      (exp ((H / 2) • a) * exp (H • b) * exp ((H / 2) • a)) ^ k := by
  rw [mul_pow_mul_eq_pow (exp_neg_mul_exp _) (exp_mul_exp_neg _), staggered_conj]

open scoped Matrix.Norms.Operator in
/-- **Staggered readout for matrices** (the paper, Proposition 4.8), with the matrix inverse:
`W X W⁻¹ = e^{H A_a / 2} e^{H A_b} e^{H A_a / 2}` for `X = e^{H A_b} e^{H A_a}`,
`W = e^{H A_a / 2}`. -/
theorem staggered_conj_matrix {n : Type*} [Fintype n] [DecidableEq n] (Aa Ab : Matrix n n ℝ)
    (H : ℝ) :
    exp ((H / 2) • Aa) * (exp (H • Ab) * exp (H • Aa)) * (exp ((H / 2) • Aa))⁻¹ =
      exp ((H / 2) • Aa) * exp (H • Ab) * exp ((H / 2) • Aa) := by
  rw [← Matrix.exp_neg]
  exact staggered_conj Aa Ab H

end Identity

section Local

/-- The algebra of the local error: the terms of degree at most two cancel. Here `ex`, `ey`, `ez`
stand for `e^x`, `e^y`, `e^{2x+y}` and `hx`, `hy`, `hz` for `x²/2`, `y²/2`, `(2x+y)²/2`. -/
theorem strang_identity {R : Type*} [Ring R] (ex ey ez x y hx hy hz : R)
    (h : hz = hx + hx + x * x + x * y + y * x + hy) :
    ex * ey * ex - ez =
      (ex - 1 - x) * (ey - 1) + x * (ey - 1 - y) + (ex - 1 - x) * (ex - 1) + x * (ex - 1 - x) +
        (ey - 1 - y) * (ex - 1) + y * (ex - 1 - x) + (ex - 1) * (ey - 1) * (ex - 1) +
        (ex - 1 - x - hx) + (ex - 1 - x - hx) + (ey - 1 - y - hy) -
        (ez - 1 - (x + x + y) - hz) := by
  subst h
  noncomm_ring

/-- The scalar side of the local error: the bounds of the terms of `strang_identity` add up to
`(2u+v)³/3 · A² B`, where `A = e^u ≥ 1` and `B = e^v ≥ 1`. -/
theorem strang_scalar_bound {u v A B : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    u ^ 2 / 2 * A * (v * B) + u * (v ^ 2 / 2 * B) + u ^ 2 / 2 * A * (u * A) +
        u * (u ^ 2 / 2 * A) + v ^ 2 / 2 * B * (u * A) + v * (u ^ 2 / 2 * A) +
        u * A * (v * B) * (u * A) + u ^ 3 / 6 * A + u ^ 3 / 6 * A + v ^ 3 / 6 * B +
        (2 * u + v) ^ 3 / 6 * (A * A * B) ≤ (2 * u + v) ^ 3 / 3 * (A * A * B) := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hAA : A ≤ A * A := le_mul_of_one_le_left hA0 hA
  have k3 : A * A ≤ A * A * B := le_mul_of_one_le_right (mul_nonneg hA0 hA0) hB
  have k4 : A ≤ A * A * B := hAA.trans k3
  have k1 : A * B ≤ A * A * B := mul_le_mul_of_nonneg_right hAA hB0
  have k2 : B ≤ A * A * B := by
    have h := mul_le_mul_of_nonneg_right (hA.trans hAA) hB0
    rwa [one_mul] at h
  have m1 : u ^ 2 * v * (A * B) ≤ u ^ 2 * v * (A * A * B) :=
    mul_le_mul_of_nonneg_left k1 (by positivity)
  have m2 : u * v ^ 2 * B ≤ u * v ^ 2 * (A * A * B) :=
    mul_le_mul_of_nonneg_left k2 (by positivity)
  have m3 : u ^ 3 * (A * A) ≤ u ^ 3 * (A * A * B) :=
    mul_le_mul_of_nonneg_left k3 (by positivity)
  have m4 : u ^ 3 * A ≤ u ^ 3 * (A * A * B) := mul_le_mul_of_nonneg_left k4 (by positivity)
  have m5 : u * v ^ 2 * (A * B) ≤ u * v ^ 2 * (A * A * B) :=
    mul_le_mul_of_nonneg_left k1 (by positivity)
  have m6 : u ^ 2 * v * A ≤ u ^ 2 * v * (A * A * B) :=
    mul_le_mul_of_nonneg_left k4 (by positivity)
  have m7 : v ^ 3 * B ≤ v ^ 3 * (A * A * B) := mul_le_mul_of_nonneg_left k2 (by positivity)
  nlinarith [m1, m2, m3, m4, m5, m6, m7]

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `(2x+y)²/2` in terms of `x²/2`, `y²/2` and the products. -/
theorem half_sq_add (x y : 𝔸) :
    (2 : ℝ)⁻¹ • (x + x + y) ^ 2 =
      (2 : ℝ)⁻¹ • x ^ 2 + (2 : ℝ)⁻¹ • x ^ 2 + x * x + x * y + y * x + (2 : ℝ)⁻¹ • y ^ 2 := by
  rw [pow_two, pow_two, pow_two]
  simp only [add_mul, mul_add]
  module

/-- **The local error of the symmetric product:** for `x`, `y` in a real Banach algebra,
`‖e^x e^y e^x - e^{2x+y}‖ ≤ (2‖x‖+‖y‖)³/3 · e^{2‖x‖+‖y‖}`. -/
theorem norm_exp_mul_exp_mul_exp_sub_le (x y : 𝔸) :
    ‖exp x * exp y * exp x - exp (x + x + y)‖ ≤
      (2 * ‖x‖ + ‖y‖) ^ 3 / 3 * Real.exp (2 * ‖x‖ + ‖y‖) := by
  have hp : ‖exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := OneStep.norm_exp_sub_one_le x
  have hq : ‖exp y - 1‖ ≤ ‖y‖ * Real.exp ‖y‖ := OneStep.norm_exp_sub_one_le y
  have hα : ‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 / 2 * Real.exp ‖x‖ := by
    have h := OneStep.norm_exp_sub_linear_le x
    rwa [← sub_sub] at h
  have hβ : ‖exp y - 1 - y‖ ≤ ‖y‖ ^ 2 / 2 * Real.exp ‖y‖ := by
    have h := OneStep.norm_exp_sub_linear_le y
    rwa [← sub_sub] at h
  have h1 : ‖exp x - 1 - x - (2 : ℝ)⁻¹ • x ^ 2‖ ≤ ‖x‖ ^ 3 / 6 * Real.exp ‖x‖ := by
    have h := OneStep.norm_exp_sub_quadratic_le x
    rwa [← sub_sub, ← sub_sub] at h
  have h2 : ‖exp y - 1 - y - (2 : ℝ)⁻¹ • y ^ 2‖ ≤ ‖y‖ ^ 3 / 6 * Real.exp ‖y‖ := by
    have h := OneStep.norm_exp_sub_quadratic_le y
    rwa [← sub_sub, ← sub_sub] at h
  have hE : Real.exp (2 * ‖x‖ + ‖y‖) = Real.exp ‖x‖ * Real.exp ‖x‖ * Real.exp ‖y‖ := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hz : ‖x + x + y‖ ≤ 2 * ‖x‖ + ‖y‖ := by
    have e1 := norm_add_le (x + x) y
    have e2 := norm_add_le x x
    linarith
  have h3 : ‖exp (x + x + y) - 1 - (x + x + y) - (2 : ℝ)⁻¹ • (x + x + y) ^ 2‖ ≤
      (2 * ‖x‖ + ‖y‖) ^ 3 / 6 * (Real.exp ‖x‖ * Real.exp ‖x‖ * Real.exp ‖y‖) := by
    have h := OneStep.norm_exp_sub_quadratic_le (x + x + y)
    rw [← sub_sub, ← sub_sub] at h
    refine h.trans ?_
    rw [← hE]
    gcongr
  have b1 : ‖(exp x - 1 - x) * (exp y - 1)‖ ≤
      ‖x‖ ^ 2 / 2 * Real.exp ‖x‖ * (‖y‖ * Real.exp ‖y‖) :=
    (norm_mul_le _ _).trans (mul_le_mul hα hq (norm_nonneg _) (by positivity))
  have b2 : ‖x * (exp y - 1 - y)‖ ≤ ‖x‖ * (‖y‖ ^ 2 / 2 * Real.exp ‖y‖) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hβ (norm_nonneg _))
  have b3 : ‖(exp x - 1 - x) * (exp x - 1)‖ ≤
      ‖x‖ ^ 2 / 2 * Real.exp ‖x‖ * (‖x‖ * Real.exp ‖x‖) :=
    (norm_mul_le _ _).trans (mul_le_mul hα hp (norm_nonneg _) (by positivity))
  have b4 : ‖x * (exp x - 1 - x)‖ ≤ ‖x‖ * (‖x‖ ^ 2 / 2 * Real.exp ‖x‖) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hα (norm_nonneg _))
  have b5 : ‖(exp y - 1 - y) * (exp x - 1)‖ ≤
      ‖y‖ ^ 2 / 2 * Real.exp ‖y‖ * (‖x‖ * Real.exp ‖x‖) :=
    (norm_mul_le _ _).trans (mul_le_mul hβ hp (norm_nonneg _) (by positivity))
  have b6 : ‖y * (exp x - 1 - x)‖ ≤ ‖y‖ * (‖x‖ ^ 2 / 2 * Real.exp ‖x‖) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hα (norm_nonneg _))
  have b7 : ‖(exp x - 1) * (exp y - 1) * (exp x - 1)‖ ≤
      ‖x‖ * Real.exp ‖x‖ * (‖y‖ * Real.exp ‖y‖) * (‖x‖ * Real.exp ‖x‖) :=
    (norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) (by positivity))) hp
      (norm_nonneg _) (by positivity))
  rw [strang_identity (exp x) (exp y) (exp (x + x + y)) x y ((2 : ℝ)⁻¹ • x ^ 2)
    ((2 : ℝ)⁻¹ • y ^ 2) ((2 : ℝ)⁻¹ • (x + x + y) ^ 2) (half_sq_add x y), hE]
  refine (norm_sub_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le b1 b2) b3) b4) b5) b6) b7) h1) h1) h2) h3).trans ?_
  exact strang_scalar_bound (norm_nonneg x) (norm_nonneg y) (Real.one_le_exp (norm_nonneg x))
    (Real.one_le_exp (norm_nonneg y))

/-- **Staggered readout, the local error** (the paper, Proposition 4.8): for `H ≥ 0`,
`‖e^{(H/2)a} e^{Hb} e^{(H/2)a} - e^{H(a+b)}‖ ≤ (‖a‖+‖b‖)³/3 · e^{H(‖a‖+‖b‖)} · H³`. -/
theorem norm_staggered_sub_exp_le (a b : 𝔸) {H : ℝ} (hH : 0 ≤ H) :
    ‖exp ((H / 2) • a) * exp (H • b) * exp ((H / 2) • a) - exp (H • (a + b))‖ ≤
      (‖a‖ + ‖b‖) ^ 3 / 3 * Real.exp (H * (‖a‖ + ‖b‖)) * H ^ 3 := by
  have h := norm_exp_mul_exp_mul_exp_sub_le ((H / 2) • a) (H • b)
  have e1 : (H / 2) • a + (H / 2) • a + H • b = H • (a + b) := by module
  have e2 : 2 * ‖(H / 2) • a‖ + ‖H • b‖ = H * (‖a‖ + ‖b‖) := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hH, Real.norm_of_nonneg (by positivity)]
    ring
  rw [e1, e2] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Staggered readout, the local error with a constant free of `H`:** if
`H (‖a‖ + ‖b‖) ≤ 1`, then
`‖e^{(H/2)a} e^{Hb} e^{(H/2)a} - e^{H(a+b)}‖ ≤ (‖a‖+‖b‖)³ · H³`. -/
theorem norm_staggered_sub_exp_le_of_le_one (a b : 𝔸) {H : ℝ} (hH : 0 ≤ H)
    (h1 : H * (‖a‖ + ‖b‖) ≤ 1) :
    ‖exp ((H / 2) • a) * exp (H • b) * exp ((H / 2) • a) - exp (H • (a + b))‖ ≤
      (‖a‖ + ‖b‖) ^ 3 * H ^ 3 := by
  refine (norm_staggered_sub_exp_le a b hH).trans ?_
  have he : Real.exp (H * (‖a‖ + ‖b‖)) ≤ 3 :=
    (Real.exp_le_exp.2 h1).trans (by linarith [Real.exp_one_lt_d9])
  calc (‖a‖ + ‖b‖) ^ 3 / 3 * Real.exp (H * (‖a‖ + ‖b‖)) * H ^ 3
      ≤ (‖a‖ + ‖b‖) ^ 3 / 3 * 3 * H ^ 3 := by gcongr
    _ = (‖a‖ + ‖b‖) ^ 3 * H ^ 3 := by ring

end Local

section Global

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- `‖exp Z‖ ≤ e^{‖Z‖}` in a Banach algebra with `‖1‖ = 1`. -/
theorem norm_exp_le_exp_norm (Z : 𝔸) : ‖exp Z‖ ≤ Real.exp ‖Z‖ := by
  have h := norm_exp_sub_one_le_exp_norm Z
  have h2 : ‖exp Z - 1 + 1‖ ≤ ‖exp Z - 1‖ + ‖(1 : 𝔸)‖ := norm_add_le _ _
  rw [sub_add_cancel, norm_one] at h2
  linarith

/-- **Staggered readout, second order over a run** (the paper, Proposition 4.8, last statement), in
a Banach algebra with `‖1‖ = 1`: for `H ≥ 0` and `k H ≤ T`,
`‖W X^k W⁻¹ - e^{H(a+b)k}‖ ≤ C H²` with `C = (‖a‖+‖b‖)³/3 · T · e^{(‖a‖+‖b‖) T}`. -/
theorem norm_staggered_pow_sub_exp_pow_le (a b : 𝔸) {H T : ℝ} (hH : 0 ≤ H) (k : ℕ)
    (hk : (k : ℝ) * H ≤ T) :
    ‖exp ((H / 2) • a) * (exp (H • b) * exp (H • a)) ^ k * exp (-((H / 2) • a)) -
        exp (H • (a + b)) ^ k‖ ≤
      (‖a‖ + ‖b‖) ^ 3 / 3 * T * Real.exp ((‖a‖ + ‖b‖) * T) * H ^ 2 := by
  have hT : 0 ≤ T := le_trans (by positivity) hk
  have hμ : 0 ≤ ‖a‖ + ‖b‖ := by positivity
  rw [staggered_conj_pow]
  cases k with
  | zero =>
    rw [pow_zero, pow_zero, sub_self, norm_zero]
    positivity
  | succ k =>
    have hS : ‖exp ((H / 2) • a) * exp (H • b) * exp ((H / 2) • a)‖ ≤
        Real.exp (H * (‖a‖ + ‖b‖)) := by
      have ha : ‖exp ((H / 2) • a)‖ ≤ Real.exp (H / 2 * ‖a‖) := by
        have h := norm_exp_le_exp_norm ((H / 2) • a)
        rwa [norm_smul, Real.norm_of_nonneg (by positivity)] at h
      have hb : ‖exp (H • b)‖ ≤ Real.exp (H * ‖b‖) := by
        have h := norm_exp_le_exp_norm (H • b)
        rwa [norm_smul, Real.norm_of_nonneg hH] at h
      have hE : Real.exp (H * (‖a‖ + ‖b‖)) =
          Real.exp (H / 2 * ‖a‖) * Real.exp (H * ‖b‖) * Real.exp (H / 2 * ‖a‖) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hE]
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))) ha
        (norm_nonneg _) (by positivity))
    have hU : ‖exp (H • (a + b))‖ ≤ Real.exp (H * (‖a‖ + ‖b‖)) := by
      refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
      rw [norm_smul, Real.norm_of_nonneg hH]
      exact mul_le_mul_of_nonneg_left (norm_add_le a b) hH
    have hloc := norm_staggered_sub_exp_le a b hH
    have hmain := OneStep.norm_pow_succ_sub_pow_succ_le _ _ hS hU k
    have hpow : Real.exp (H * (‖a‖ + ‖b‖)) * Real.exp (H * (‖a‖ + ‖b‖)) ^ k ≤
        Real.exp ((‖a‖ + ‖b‖) * T) := by
      rw [← pow_succ', ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      have h0 := mul_le_mul_of_nonneg_right hk hμ
      linarith
    have hkH : ((k + 1 : ℕ) : ℝ) * H *
        (Real.exp (H * (‖a‖ + ‖b‖)) * Real.exp (H * (‖a‖ + ‖b‖)) ^ k) ≤
        T * Real.exp ((‖a‖ + ‖b‖) * T) :=
      mul_le_mul hk hpow (by positivity) hT
    calc ‖(exp ((H / 2) • a) * exp (H • b) * exp ((H / 2) • a)) ^ (k + 1) -
          exp (H • (a + b)) ^ (k + 1)‖
        ≤ ((k : ℝ) + 1) *
            ‖exp ((H / 2) • a) * exp (H • b) * exp ((H / 2) • a) - exp (H • (a + b))‖ *
            Real.exp (H * (‖a‖ + ‖b‖)) ^ k := hmain
      _ ≤ ((k : ℝ) + 1) * ((‖a‖ + ‖b‖) ^ 3 / 3 * Real.exp (H * (‖a‖ + ‖b‖)) * H ^ 3) *
            Real.exp (H * (‖a‖ + ‖b‖)) ^ k := by gcongr
      _ = (‖a‖ + ‖b‖) ^ 3 / 3 * H ^ 2 * (((k + 1 : ℕ) : ℝ) * H *
            (Real.exp (H * (‖a‖ + ‖b‖)) * Real.exp (H * (‖a‖ + ‖b‖)) ^ k)) := by
        push_cast
        ring
      _ ≤ (‖a‖ + ‖b‖) ^ 3 / 3 * H ^ 2 * (T * Real.exp ((‖a‖ + ‖b‖) * T)) :=
        mul_le_mul_of_nonneg_left hkH (by positivity)
      _ = (‖a‖ + ‖b‖) ^ 3 / 3 * T * Real.exp ((‖a‖ + ‖b‖) * T) * H ^ 2 := by ring

end Global

end CoSimFoundations
