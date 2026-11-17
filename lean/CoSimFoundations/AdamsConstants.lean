/-
Constants for the bound with `l` held samples (the paper, Theorem 4.10 `thm:memory`; used by
`MemoryLead.lean`).

1. **Tail of the exponential series.** `expTail b x = e^x - Σ_{n<b} xⁿ/n! = Σ_{p≥b} xᵖ/p!`.
   For `x ≥ 0` it is nonnegative; `expTail b 0 = 0` for `b ≥ 1`; and for `y ≥ 0`, `0 ≤ x ≤ 1`:
   `expTail b (y x) ≤ xᵇ expTail b y` (term by term). In a real Banach algebra, for `b ≥ 1`,

     `‖exp Z - Σ_{n<b} Zⁿ/n!‖ ≤ expTail b ‖Z‖`

   (the series of norms; sharper than `norm_exp_sub_sum_le` of `OrderBarrier.lean`).

2. **Node polynomial of the ages `0, …, l-1`.** `∏_{r<l} (s + r)` is Mathlib's rising factorial
   `ascPochhammer ℝ l`; `adamsCoeff l m` is its coefficient of `sᵐ`. It is monic of degree `l`,
   has no constant term for `l ≥ 1`, and vanishes at `s = -r`, `r < l`:
   `(-r)ˡ = -Σ_{1≤m<l} adamsCoeff l m (-r)ᵐ`. (The paper writes the polynomial as
   `sˡ - Σ_{m<l} s_m sᵐ`, so `s_m = -adamsCoeff l m`.)

3. **The Adams–Bashforth error constant.**
   `adamsGamma l = (1/l!) Σ_{m≤l} adamsCoeff l m / (m+1) = (1/l!) ∫₀¹ ∏_{r<l} (s + r) ds`,
   the `γ_l` of the paper; `γ_1 = 1/2`, `γ_2 = 5/12`, `γ_3 = 3/8`, `γ_4 = 251/720`.
-/
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import CoSimFoundations.OrderBarrier

open NormedSpace Finset Polynomial
open scoped Nat

namespace CoSimFoundations

/-- The tail of the exponential series: `expTail b x = e^x - Σ_{n<b} xⁿ/n!`. -/
noncomputable def expTail (b : ℕ) (x : ℝ) : ℝ :=
  Real.exp x - ∑ n ∈ range b, x ^ n / (n ! : ℝ)

/-- `expTail b x = Σ_{n≥0} x^{n+b}/(n+b)!`. -/
theorem hasSum_expTail (b : ℕ) (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + b) / ((n + b)! : ℝ)) (expTail b x) := by
  have h : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact expSeries_div_hasSum_exp x
  exact (hasSum_nat_add_iff' b).2 h

/-- The tail is nonnegative for a nonnegative argument. -/
theorem expTail_nonneg (b : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ expTail b x :=
  sub_nonneg.2 (Real.sum_le_exp_of_nonneg hx b)

/-- The tail from the order `b ≥ 1` on vanishes at zero. -/
theorem expTail_zero {b : ℕ} (hb : 0 < b) : expTail b 0 = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  simp [expTail, sum_range_succ']

/-- Scaling of the tail: `expTail b (y x) ≤ xᵇ expTail b y` for `y ≥ 0` and `0 ≤ x ≤ 1`. -/
theorem expTail_mul_le (b : ℕ) {x y : ℝ} (hy : 0 ≤ y) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    expTail b (y * x) ≤ x ^ b * expTail b y := by
  refine hasSum_le (fun n => ?_) (hasSum_expTail b (y * x))
    ((hasSum_expTail b y).mul_left (x ^ b))
  have h1 : x ^ (n + b) ≤ x ^ b := by
    rw [pow_add]
    exact mul_le_of_le_one_left (pow_nonneg hx0 b) (pow_le_one₀ hx0 hx1)
  have h2 : 0 ≤ y ^ (n + b) / ((n + b)! : ℝ) := by positivity
  calc (y * x) ^ (n + b) / ((n + b)! : ℝ)
      = x ^ (n + b) * (y ^ (n + b) / ((n + b)! : ℝ)) := by rw [mul_pow]; ring
    _ ≤ x ^ b * (y ^ (n + b) / ((n + b)! : ℝ)) := mul_le_mul_of_nonneg_right h1 h2

/-- The tail against its value at one: `expTail b x ≤ expTail b 1 · xᵇ` for `0 ≤ x ≤ 1`. -/
theorem expTail_le_mul_pow (b : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    expTail b x ≤ expTail b 1 * x ^ b := by
  have h := expTail_mul_le b zero_le_one hx0 hx1
  rwa [one_mul, mul_comm] at h

/-- `expTail 2 1 = e - 2`. -/
theorem expTail_two_one : expTail 2 1 = Real.exp 1 - 2 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- `expTail 3 1 = e - 5/2`. -/
theorem expTail_three_one : expTail 3 1 = Real.exp 1 - 5 / 2 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- `expTail 4 1 = e - 8/3`. -/
theorem expTail_four_one : expTail 4 1 = Real.exp 1 - 8 / 3 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Taylor remainder of the exponential, as the tail of the series of norms:**
`‖exp Z - Σ_{n<b} Zⁿ/n!‖ ≤ Σ_{p≥b} ‖Z‖ᵖ/p!` for `b ≥ 1`. -/
theorem norm_exp_sub_sum_le_expTail (Z : 𝔸) {b : ℕ} (hb : 0 < b) :
    ‖exp Z - ∑ n ∈ range b, ((n ! : ℝ)⁻¹) • Z ^ n‖ ≤ expTail b ‖Z‖ := by
  have htail := (hasSum_nat_add_iff' b).2 (exp_series_hasSum_exp' (𝕂 := ℝ) Z)
  refine htail.norm_le_of_bounded (hasSum_expTail b ‖Z‖) (fun i => ?_)
  rw [norm_smul, norm_inv, Real.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' Z (by omega)) (inv_nonneg.2 (Nat.cast_nonneg _))

end Algebra

/-- The coefficient of `sᵐ` in the node polynomial `∏_{r<l} (s + r)` of the ages `0, …, l-1`
(an unsigned Stirling number of the first kind). -/
noncomputable def adamsCoeff (l m : ℕ) : ℝ :=
  (ascPochhammer ℝ l).coeff m

/-- The node polynomial of no sample is `1`. -/
theorem adamsCoeff_zero_zero : adamsCoeff 0 0 = 1 := by
  simp [adamsCoeff]

/-- The node polynomial of no sample is `1`: no higher coefficients. -/
theorem adamsCoeff_zero_succ (m : ℕ) : adamsCoeff 0 (m + 1) = 0 := by
  simp [adamsCoeff, coeff_one]

/-- Recursion for the constant coefficient, from `∏_{r≤l} (s + r) = ∏_{r<l} (s + r) · (s + l)`. -/
theorem adamsCoeff_succ_zero (l : ℕ) : adamsCoeff (l + 1) 0 = l * adamsCoeff l 0 := by
  unfold adamsCoeff
  rw [ascPochhammer_succ_right, mul_add, coeff_add, coeff_mul_X_zero, coeff_mul_natCast,
    zero_add, mul_comm]

/-- Recursion for the coefficients, from `∏_{r≤l} (s + r) = ∏_{r<l} (s + r) · (s + l)`. -/
theorem adamsCoeff_succ_succ (l m : ℕ) :
    adamsCoeff (l + 1) (m + 1) = adamsCoeff l m + l * adamsCoeff l (m + 1) := by
  unfold adamsCoeff
  rw [ascPochhammer_succ_right, mul_add, coeff_add, coeff_mul_X, coeff_mul_natCast, mul_comm]

/-- The node polynomial is monic of degree `l`. -/
theorem adamsCoeff_self (l : ℕ) : adamsCoeff l l = 1 := by
  have h := (monic_ascPochhammer (S := ℝ) l).coeff_natDegree
  rwa [ascPochhammer_natDegree] at h

/-- For `l ≥ 1` the node polynomial has no constant term (the age `0` is a node). -/
theorem adamsCoeff_zero {l : ℕ} (hl : 1 ≤ l) : adamsCoeff l 0 = 0 := by
  have hl0 : l ≠ 0 := by omega
  simp [adamsCoeff, coeff_zero_eq_eval_zero, hl0]

/-- The node polynomial vanishes at the ages: `Σ_{m≤l} adamsCoeff l m (-r)ᵐ = 0` for `r < l`. -/
theorem sum_adamsCoeff_mul_neg_pow {l r : ℕ} (hr : r < l) :
    ∑ m ∈ range (l + 1), adamsCoeff l m * (-(r : ℝ)) ^ m = 0 := by
  have h := eval_eq_sum_range (p := ascPochhammer ℝ l) (-(r : ℝ))
  rw [ascPochhammer_natDegree, ascPochhammer_eval_neg_coe_nat_of_lt hr] at h
  exact h.symm

/-- A sum over `0, …, l` split into the first term, the middle and the last term. -/
theorem sum_range_succ_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) {l : ℕ} (hl : 1 ≤ l) :
    ∑ m ∈ range (l + 1), f m = f 0 + ∑ m ∈ Ico 1 l, f m + f l := by
  rw [sum_range_succ, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < l)]

/-- **The relation between the powers of the ages** (Step 2 of the proof of Theorem 4.10):
`(-r)ˡ = -Σ_{1≤m<l} adamsCoeff l m (-r)ᵐ` for every age `r < l`. -/
theorem neg_pow_eq_neg_sum {l r : ℕ} (hl : 1 ≤ l) (hr : r < l) :
    (-(r : ℝ)) ^ l = -∑ m ∈ Ico 1 l, adamsCoeff l m * (-(r : ℝ)) ^ m := by
  have h := sum_adamsCoeff_mul_neg_pow hr
  rw [sum_range_succ_split _ hl, adamsCoeff_zero hl, adamsCoeff_self, zero_mul, zero_add,
    one_mul] at h
  linarith

/-- The Adams–Bashforth error constant `γ_l = (1/l!) Σ_{m≤l} adamsCoeff l m / (m+1)`, which is
`(1/l!) ∫₀¹ ∏_{r<l} (s + r) ds` (`adamsGamma_eq_integral`). -/
noncomputable def adamsGamma (l : ℕ) : ℝ :=
  ((l ! : ℝ))⁻¹ * ∑ m ∈ range (l + 1), adamsCoeff l m / ((m : ℝ) + 1)

/-- The rising factorial as a product: `ascPochhammer ℝ l` at `s` is `∏_{r<l} (s + r)`. -/
theorem ascPochhammer_eval_eq_prod_range (l : ℕ) (s : ℝ) :
    (ascPochhammer ℝ l).eval s = ∏ r ∈ range l, (s + r) := by
  induction l with
  | zero => simp
  | succ l ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

/-- The integral of a polynomial over `[0, 1]`:
`∫₀¹ Σ_{m ∈ s} c_m xᵐ dx = Σ_{m ∈ s} c_m / (m + 1)`. -/
theorem integral_sum_mul_pow (s : Finset ℕ) (c : ℕ → ℝ) :
    ∫ x in (0 : ℝ)..1, ∑ m ∈ s, c m * x ^ m = ∑ m ∈ s, c m / ((m : ℝ) + 1) := by
  have hint : ∀ m ∈ s,
      IntervalIntegrable (fun x : ℝ => c m * x ^ m) MeasureTheory.volume 0 1 :=
    fun m _ => (continuous_const.mul (continuous_pow m)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint]
  refine sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp [div_eq_mul_inv]

/-- The weight of a coefficient of the node polynomial in the error constant:
`c m!/l! · h/(m+1)! = (1/l!) h · c/(m+1)`. -/
theorem mul_factorial_div_mul_div (c h : ℝ) (l m : ℕ) :
    c * (m ! : ℝ) / (l ! : ℝ) * (h / ((m + 1)! : ℝ)) =
      (l ! : ℝ)⁻¹ * h * (c / ((m : ℝ) + 1)) := by
  have hl : (l ! : ℝ) ≠ 0 := by positivity
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **The constant of the paper:** `γ_l = (1/l!) ∫₀¹ ∏_{r<l} (s + r) ds`. -/
theorem adamsGamma_eq_integral (l : ℕ) :
    adamsGamma l = ((l ! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1, ∏ r ∈ range l, (s + r) := by
  have h : ∀ s : ℝ, ∏ r ∈ range l, (s + r) = ∑ m ∈ range (l + 1), adamsCoeff l m * s ^ m := by
    intro s
    rw [← ascPochhammer_eval_eq_prod_range, eval_eq_sum_range, ascPochhammer_natDegree]
    rfl
  simp_rw [h]
  rw [integral_sum_mul_pow]
  rfl

/-- The constants `γ_1, …, γ_4`, from the recursion for the coefficients of the node
polynomial: `γ_1 = 1/2`, `γ_2 = 5/12`, `γ_3 = 3/8`, `γ_4 = 251/720`. -/
theorem adamsGamma_one_to_four :
    adamsGamma 1 = 1 / 2 ∧ adamsGamma 2 = 5 / 12 ∧ adamsGamma 3 = 3 / 8 ∧
      adamsGamma 4 = 251 / 720 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [adamsGamma, sum_range_succ, adamsCoeff_succ_succ, adamsCoeff_succ_zero,
      adamsCoeff_zero_zero, adamsCoeff_zero_succ, Nat.factorial]
    norm_num

/-- `γ_1 = 1/2`. -/
theorem adamsGamma_one : adamsGamma 1 = 1 / 2 :=
  adamsGamma_one_to_four.1

/-- `γ_2 = 5/12`. -/
theorem adamsGamma_two : adamsGamma 2 = 5 / 12 :=
  adamsGamma_one_to_four.2.1

/-- `γ_3 = 3/8`. -/
theorem adamsGamma_three : adamsGamma 3 = 3 / 8 :=
  adamsGamma_one_to_four.2.2.1

/-- `γ_4 = 251/720`. -/
theorem adamsGamma_four : adamsGamma 4 = 251 / 720 :=
  adamsGamma_one_to_four.2.2.2

/-- The node polynomial of two samples is `s² + s`: its coefficient of `s` is `1`. -/
theorem adamsCoeff_two_one : adamsCoeff 2 1 = 1 := by
  simp [adamsCoeff_succ_succ, adamsCoeff_succ_zero, adamsCoeff_zero_zero, adamsCoeff_zero_succ]

end CoSimFoundations
