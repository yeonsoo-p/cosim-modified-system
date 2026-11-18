/-
The φ-functions and the moment formula:

  φ_b(Z) = Σ_{j ≥ 0} Z^j / (j + b)!,
  ∫₀^τ sᵃ exp((τ - s) Z) ds = a! τ^{a+1} φ_{a+1}(τ Z).

With `Z = H A_K` and `τ = 1` this is the `a`-th term of the paper's
`M^r = H Σ_a a! φ_{a+1}(H A_K) B_K V^r_[a]`; the sum over `a` with the factors `B_K V^r_[a]` (and
the rescaling from the step to `[0, 1]`) is not formalized here. Stated in any real Banach algebra.

The scalar ingredient is the Beta integral for natural exponents:
  ∫₀^τ sᵃ (τ - s)ʲ ds = j! a! τ^{j+a+1} / (j + a + 1)!.
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact

open Nat intervalIntegral

namespace CoSimFoundations

/-- **Beta integral for natural exponents.** -/
theorem integral_pow_mul_sub_pow (τ : ℝ) :
    ∀ j a : ℕ, ∫ s in (0 : ℝ)..τ, s ^ a * (τ - s) ^ j =
      ((j ! * a ! : ℕ) : ℝ) / ((j + a + 1)! : ℕ) * τ ^ (j + a + 1)
  | 0, a => by
    simp only [pow_zero, mul_one, integral_pow, zero_add, factorial_zero, one_mul]
    rw [zero_pow (by omega), sub_zero, factorial_succ]
    push_cast
    have : (a ! : ℝ) ≠ 0 := by exact_mod_cast (factorial_pos a).ne'
    field_simp
  | j + 1, a => by
    have ih := integral_pow_mul_sub_pow τ j (a + 1)
    -- F s = s^(a+1) (τ - s)^(j+1) / (a+1) has F' = s^a (τ-s)^(j+1) - (j+1)/(a+1) s^(a+1) (τ-s)^j
    set F : ℝ → ℝ := fun s => s ^ (a + 1) * (τ - s) ^ (j + 1) / (a + 1) with hF
    set F' : ℝ → ℝ := fun s =>
      s ^ a * (τ - s) ^ (j + 1) - (j + 1) / (a + 1) * (s ^ (a + 1) * (τ - s) ^ j) with hF'
    have hderiv : ∀ s, HasDerivAt F (F' s) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => s ^ (a + 1)) ((a + 1 : ℕ) * s ^ a) s := by
        simpa using hasDerivAt_pow (a + 1) s
      have h2 : HasDerivAt (fun s : ℝ => (τ - s) ^ (j + 1)) ((j + 1 : ℕ) * (τ - s) ^ j * (-1)) s := by
        have := ((hasDerivAt_id s).const_sub τ).fun_pow (j + 1)
        simpa using this
      have h := (h1.mul h2).div_const ((a : ℝ) + 1)
      convert h using 1
      simp only [hF']
      push_cast
      field_simp
      ring
    have hcont : Continuous F' := by simp only [hF']; fun_prop
    have hftc := integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hcont.intervalIntegrable 0 τ)
    have hF0 : F τ - F 0 = 0 := by simp [hF]
    rw [hF0] at hftc
    simp only [hF'] at hftc
    rw [integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), integral_const_mul, ih] at hftc
    have hsplit : ∫ s in (0 : ℝ)..τ, s ^ a * (τ - s) ^ (j + 1) =
        (j + 1) / (a + 1) * (((j ! * (a + 1)! : ℕ) : ℝ) / ((j + (a + 1) + 1)! : ℕ) *
          τ ^ (j + (a + 1) + 1)) := by linarith
    rw [hsplit, show j + (a + 1) + 1 = j + 1 + a + 1 by ring]
    rw [factorial_succ a, factorial_succ j]
    push_cast
    have : (a ! : ℝ) ≠ 0 := by exact_mod_cast (factorial_pos a).ne'
    field_simp

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `φ_b(Z) = Σ_j Z^j / (j + b)!`. -/
noncomputable def phi (b : ℕ) (Z : 𝔸) : 𝔸 := ∑' j : ℕ, (((j + b)! : ℕ) : ℝ)⁻¹ • Z ^ j

/-- `exp((τ - s) Z) = Σ_n ((τ - s)^n / n!) Z^n`. -/
theorem exp_smul_eq_tsum (c : ℝ) (Z : 𝔸) :
    NormedSpace.exp (c • Z) = ∑' n : ℕ, (c ^ n / (n ! : ℝ)) • Z ^ n := by
  rw [congrFun (NormedSpace.exp_eq_tsum ℝ) (c • Z)]
  refine tsum_congr fun n => ?_
  rw [smul_pow, smul_smul, div_eq_mul_inv, mul_comm]

/-- **The moment formula.** `∫₀^τ sᵃ exp((τ - s) Z) ds = a! τ^{a+1} φ_{a+1}(τ Z)`. -/
theorem moment_formula (Z : 𝔸) (τ : ℝ) (a : ℕ) :
    ∫ s in (0 : ℝ)..τ, (s ^ a) • NormedSpace.exp ((τ - s) • Z) =
      ((a ! : ℝ) * τ ^ (a + 1)) • phi (a + 1) (τ • Z) := by
  -- the n-th term of the integrand, as a continuous map
  let g : ℕ → C(ℝ, 𝔸) := fun n =>
    ⟨fun s => (s ^ a * ((τ - s) ^ n / (n ! : ℝ))) • Z ^ n, by fun_prop⟩
  have hint : ∀ s, (s ^ a) • NormedSpace.exp ((τ - s) • Z) = ∑' n, g n s := by
    intro s
    rw [exp_smul_eq_tsum, ← tsum_const_smul'']
    refine tsum_congr fun n => ?_
    simp only [g, ContinuousMap.coe_mk, smul_smul]
  -- summable sup norms on [0, τ]
  have hsum : Summable fun n =>
      ‖(g n).restrict (⟨Set.uIcc 0 τ, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    have hb := (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (|τ| • Z)).mul_left (|τ| ^ a)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hb
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun ⟨s, hs⟩ => ?_
    have hs' : |s| ≤ |τ| ∧ |τ - s| ≤ |τ| := by
      rcases Set.mem_uIcc.1 hs with h | h
      · exact ⟨by rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2,
          by rw [abs_of_nonneg (sub_nonneg.2 h.2), abs_of_nonneg (h.1.trans h.2)]; linarith⟩
      · exact ⟨by rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]; linarith,
          by rw [abs_of_nonpos (sub_nonpos.2 h.1), abs_of_nonpos (h.1.trans h.2)]; linarith⟩
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, g, norm_smul, smul_pow,
      Real.norm_eq_abs, abs_mul, abs_pow, abs_div, Nat.abs_cast, abs_inv, abs_abs]
    have h1 : |s| ^ a ≤ |τ| ^ a := pow_le_pow_left₀ (abs_nonneg _) hs'.1 a
    have h2 : |τ - s| ^ n / (n ! : ℝ) ≤ |τ| ^ n / (n ! : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hs'.2 n) (by positivity)
    calc |s| ^ a * (|τ - s| ^ n / (n ! : ℝ)) * ‖Z ^ n‖
        ≤ |τ| ^ a * (|τ| ^ n / (n ! : ℝ)) * ‖Z ^ n‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity))
            (norm_nonneg _)
      _ = |τ| ^ a * ((n ! : ℝ)⁻¹ * (|τ| ^ n * ‖Z ^ n‖)) := by ring
  rw [show (fun s => (s ^ a) • NormedSpace.exp ((τ - s) • Z)) = fun s => ∑' n, g n s from
    funext hint, ← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum]
  -- each term
  have hterm : ∀ n, ∫ s in (0 : ℝ)..τ, g n s =
      ((a ! : ℝ) * τ ^ (a + 1)) • ((((n + (a + 1))! : ℕ) : ℝ)⁻¹ • (τ • Z) ^ n) := by
    intro n
    simp only [g, ContinuousMap.coe_mk]
    rw [intervalIntegral.integral_smul_const]
    have hI : ∫ s in (0 : ℝ)..τ, s ^ a * ((τ - s) ^ n / (n ! : ℝ)) =
        (∫ s in (0 : ℝ)..τ, s ^ a * (τ - s) ^ n) / (n ! : ℝ) := by
      rw [← intervalIntegral.integral_div]; congr 1; ext s; ring
    rw [hI, integral_pow_mul_sub_pow, smul_pow, smul_smul, smul_smul]
    congr 1
    rw [show n + (a + 1) = n + a + 1 by ring]
    push_cast
    have : (n ! : ℝ) ≠ 0 := by exact_mod_cast (factorial_pos n).ne'
    field_simp
    ring
  rw [tsum_congr hterm, tsum_const_smul'', phi]

/-- The φ-series converges absolutely. -/
theorem summable_phi (b : ℕ) (Z : 𝔸) :
    Summable fun j : ℕ => (((j + b)! : ℕ) : ℝ)⁻¹ • Z ^ j := by
  refine Summable.of_norm_bounded (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) Z) fun j => ?_
  rw [norm_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  simp only [Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  have hj : (0 : ℝ) < (j ! : ℕ) := by exact_mod_cast factorial_pos j
  exact inv_anti₀ hj (by exact_mod_cast factorial_le (Nat.le_add_right j b))

/-- `φ₀ = exp`. -/
theorem phi_zero (Z : 𝔸) : phi 0 Z = NormedSpace.exp Z := by
  rw [phi, congrFun (NormedSpace.exp_eq_tsum ℝ) Z]
  simp

/-- **The φ-recursion** `φ_b(Z) = 1/b! + Z φ_{b+1}(Z)`. -/
theorem phi_succ (b : ℕ) (Z : 𝔸) :
    phi b Z = ((b ! : ℕ) : ℝ)⁻¹ • (1 : 𝔸) + Z * phi (b + 1) Z := by
  rw [phi, (summable_phi b Z).tsum_eq_zero_add, phi, ← (summable_phi (b + 1) Z).tsum_mul_left]
  congr 1
  · simp
  · refine tsum_congr fun j => ?_
    rw [mul_smul_comm, _root_.pow_succ', show j + 1 + b = j + (b + 1) by ring]

end Algebra

end CoSimFoundations
