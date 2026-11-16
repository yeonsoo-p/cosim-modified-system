/-
The error constant of `l` nodes (the paper, eq. `eq:gamma`, as it enters Theorem `thm:memory`
(i) through `DividedDifference` and `LeadingDefect`).

For nodes `x : Fin l → ℝ` and the inverse `W` of their Vandermonde matrix, `DividedDifference`
defines `β_p = Σ_q W p q x_q^l` and `γ = (1/l!) (1/(l+1) - Σ_p β_p/(p+1))` (`ddGamma`).

**Statements.**
* `prod_sub_node_eq`: `∏_q (s - x_q) = s^l - Σ_p β_p s^p`, the node polynomial. Proof: both
  sides are monic of degree `l` and agree at the `l` distinct nodes, where `x_q^l = Σ_p β_p x_q^p`
  (`pow_node_eq_sum`).
* `ddGamma_eq_integral`: `γ = (1/l!) ∫₀¹ ∏_q (s - x_q) ds`.
* The nodes of a scheme with `l` held samples are `σ - q`, `q < l` (`schemeNodes`), with `σ = 0`
  for old samples and `σ = 1` if the newest sample is that of the new instant; `schemeGamma σ l`
  is their constant, the paper's `γ_l^σ = ∫₀¹ binom(s + l - 1 - σ, l) ds`
  (`schemeGamma_eq_integral`). `schemeGamma 0 l = adamsGamma l` (explicit Adams,
  `schemeGamma_zero`) and `schemeGamma 1 l = lateGamma l` for `l ≥ 1` (implicit Adams,
  `schemeGamma_one`), the constants of `MemoryLead` and `MemoryLate`.
-/
import Mathlib.LinearAlgebra.Lagrange
import CoSimFoundations.DividedDifference
import CoSimFoundations.MemoryLateConstants

open Finset Polynomial
open scoped Nat

namespace CoSimFoundations

section NodePolynomial

variable {l : ℕ} {x : Fin l → ℝ} {W : Matrix (Fin l) (Fin l) ℝ}

/-- Nodes whose Vandermonde matrix has an inverse are distinct. -/
theorem injective_of_mul_vandermonde (hW : W * Matrix.vandermonde x = 1) :
    Function.Injective x := by
  rw [← Matrix.det_vandermonde_ne_zero_iff]
  intro h
  have h1 := congrArg Matrix.det hW
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

/-- At the nodes `s^l` is the combination of the lower powers: `x_q^l = Σ_p β_p x_q^p`. -/
theorem pow_node_eq_sum (hW : W * Matrix.vandermonde x = 1) (q : Fin l) :
    x q ^ l = ∑ p : Fin l, ddBeta x W p * x q ^ (p : ℕ) := by
  have hV : Matrix.vandermonde x * W = 1 := mul_eq_one_comm.1 hW
  have h1 : ∀ q' : Fin l, ∑ p : Fin l, x q ^ (p : ℕ) * W p q' = if q = q' then 1 else 0 :=
    fun q' => by
      have h2 := congrFun (congrFun hV q) q'
      rw [Matrix.mul_apply, Matrix.one_apply] at h2
      exact h2
  calc x q ^ l = ∑ q' : Fin l, (if q = q' then (1 : ℝ) else 0) * x q' ^ l := by simp
    _ = ∑ q' : Fin l, (∑ p : Fin l, x q ^ (p : ℕ) * W p q') * x q' ^ l :=
        sum_congr rfl fun q' _ => by rw [h1]
    _ = ∑ p : Fin l, ∑ q' : Fin l, x q ^ (p : ℕ) * W p q' * x q' ^ l := by
        rw [sum_comm]
        exact sum_congr rfl fun q' _ => by rw [sum_mul]
    _ = ∑ p : Fin l, ddBeta x W p * x q ^ (p : ℕ) :=
        sum_congr rfl fun p _ => by
          unfold ddBeta
          rw [sum_mul]
          exact sum_congr rfl fun q' _ => by ring

/-- **The node polynomial:** `∏_q (s - x_q) = s^l - Σ_p β_p s^p`. -/
theorem prod_sub_node_eq (hW : W * Matrix.vandermonde x = 1) (s : ℝ) :
    ∏ q, (s - x q) = s ^ l - ∑ p : Fin l, ddBeta x W p * s ^ (p : ℕ) := by
  set g : ℝ[X] := ∑ p : Fin l, C (ddBeta x W p) * X ^ (p : ℕ) with hg
  have hgdeg : g.degree < (l : WithBot ℕ) := degree_sum_fin_lt _
  have hpoly : ∏ q : Fin l, (X - C (x q)) = X ^ l - g := by
    have hm1 : (∏ q : Fin l, (X - C (x q))).Monic := monic_prod_X_sub_C x univ
    have hm2 : (X ^ l - g).Monic := monic_X_pow_sub hgdeg
    have hd2 : (X ^ l - g).degree = (l : WithBot ℕ) := by
      rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    have hd1 : (∏ q : Fin l, (X - C (x q))).degree = (l : WithBot ℕ) := by
      rw [degree_prod_of_monic _ _ fun q _ => monic_X_sub_C (x q)]
      simp
    refine eq_of_degree_le_of_eval_index_eq (v := x) univ
      (injective_of_mul_vandermonde hW).injOn ?_ (hd1.trans hd2.symm)
      (hm1.leadingCoeff.trans hm2.leadingCoeff.symm) fun q _ => ?_
    · rw [hd1]
      simp
    · have h1 : (∏ q' : Fin l, (X - C (x q'))).eval (x q) = 0 := by
        rw [eval_prod]
        exact prod_eq_zero (mem_univ q) (by simp)
      have h2 : (X ^ l - g).eval (x q) = 0 := by
        rw [hg, eval_sub, eval_pow, eval_X, eval_finsetSum, pow_node_eq_sum hW q, sub_eq_zero]
        exact sum_congr rfl fun p _ => by simp
      rw [h1, h2]
  have h := congrArg (Polynomial.eval s) hpoly
  rw [eval_prod, hg, eval_sub, eval_pow, eval_X, eval_finsetSum] at h
  simpa using h

/-- **The error constant as an integral:** `γ = (1/l!) ∫₀¹ ∏_q (s - x_q) ds`. -/
theorem ddGamma_eq_integral (hW : W * Matrix.vandermonde x = 1) :
    ddGamma x W = ((l ! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1, ∏ q, (s - x q) := by
  simp_rw [prod_sub_node_eq hW]
  have hint : ∀ p ∈ (univ : Finset (Fin l)),
      IntervalIntegrable (fun s : ℝ => ddBeta x W p * s ^ (p : ℕ)) MeasureTheory.volume 0 1 :=
    fun p _ => (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  have hsum : IntervalIntegrable (fun s : ℝ => ∑ p : Fin l, ddBeta x W p * s ^ (p : ℕ))
      MeasureTheory.volume 0 1 :=
    (continuous_finsetSum _ fun p _ =>
      continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub ((continuous_pow l).intervalIntegrable _ _) hsum,
    integral_pow, intervalIntegral.integral_finsetSum hint]
  unfold ddGamma
  congr 2
  · simp
  · refine sum_congr rfl fun p _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]

end NodePolynomial

section SchemeNodes

/-- The nodes of a scheme with `l` held samples, in units of the macro step: `σ - q`, `q < l`,
with `σ = 0` if the newest sample is that of `t_k` and `σ = 1` if it is that of `t_{k+1}`. -/
def schemeNodes (σ l : ℕ) : Fin l → ℝ := fun q => (σ : ℝ) - (q : ℕ)

/-- The nodes of a scheme are distinct. -/
theorem schemeNodes_injective (σ l : ℕ) : Function.Injective (schemeNodes σ l) := by
  intro q q' h
  unfold schemeNodes at h
  have h1 : ((q : ℕ) : ℝ) = ((q' : ℕ) : ℝ) := by linarith
  exact Fin.ext (Nat.cast_injective h1)

/-- The inverse of the Vandermonde matrix of the nodes of a scheme. -/
noncomputable def schemeWeights (σ l : ℕ) : Matrix (Fin l) (Fin l) ℝ :=
  (Matrix.vandermonde (schemeNodes σ l))⁻¹

/-- The weights are the inverse of the Vandermonde matrix of the nodes. -/
theorem schemeWeights_mul (σ l : ℕ) :
    schemeWeights σ l * Matrix.vandermonde (schemeNodes σ l) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2
    (Matrix.det_vandermonde_ne_zero_iff.2 (schemeNodes_injective σ l)))

/-- **The constant `γ_l^σ` of the paper** (eq. `eq:gamma`), for the nodes `σ - q`, `q < l`. -/
noncomputable def schemeGamma (σ l : ℕ) : ℝ :=
  ddGamma (schemeNodes σ l) (schemeWeights σ l)

/-- `γ_l^σ = (1/l!) ∫₀¹ ∏_{q<l} (s - σ + q) ds = ∫₀¹ binom(s + l - 1 - σ, l) ds`. -/
theorem schemeGamma_eq_integral (σ l : ℕ) :
    schemeGamma σ l = ((l ! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1, ∏ q ∈ range l, (s - σ + q) := by
  unfold schemeGamma
  rw [ddGamma_eq_integral (schemeWeights_mul σ l)]
  congr 2
  funext s
  rw [← Fin.prod_univ_eq_prod_range (fun q => s - (σ : ℝ) + (q : ℝ)) l]
  exact prod_congr rfl fun q _ => by
    unfold schemeNodes
    ring

/-- For old samples the constant is that of the explicit Adams methods. -/
theorem schemeGamma_zero (l : ℕ) : schemeGamma 0 l = adamsGamma l := by
  rw [schemeGamma_eq_integral, adamsGamma_eq_integral]
  simp

/-- With the new sample the constant is that of the implicit Adams methods. -/
theorem schemeGamma_one {l : ℕ} (hl : 1 ≤ l) : schemeGamma 1 l = lateGamma l := by
  rw [schemeGamma_eq_integral, lateGamma_eq_integral hl]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hl
  congr 2
  funext s
  rw [prod_range_succ', Nat.add_sub_cancel, mul_comm]
  congr 1
  · simp
  · exact prod_congr rfl fun k _ => by
      push_cast
      ring

end SchemeNodes

end CoSimFoundations
