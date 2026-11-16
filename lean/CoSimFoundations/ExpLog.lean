/-
`exp (log x) = x` for `‖x - 1‖ < 1` in a real Banach algebra (a TODO in Mathlib's
`Mathlib/Analysis/Normed/Algebra/Logarithm.lean`). For matrices this is the existence of a real
logarithm near the identity: the modified system, for small steps, has
generator `(1/H) log Φ̃` when `‖Φ̃ - 1‖ < 1`.

Proof. Put `y = x - 1`, `L t = log (1 + t y) = Σ cₙ tⁿ yⁿ` with `cₙ = (-1)^(n+1)/n`.
Termwise, `L' t = Σ (-t y)^m y`, and the geometric series gives `L' t (1 + t y) = y`.
All `L t` commute, so `d/dt exp(-L t) = exp(-L t) (-L' t)`, and `g t = exp(-L t) (1 + t y)` has
`g' = 0`; hence `g 1 = g 0 = 1`, i.e. `exp (L 1) = 1 + y`.
-/
import Mathlib.Analysis.Normed.Algebra.Logarithm
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

open NormedSpace

namespace CoSimFoundations

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Chain rule for `exp` along a curve whose values commute with its value at `t`. -/
theorem hasDerivAt_exp_of_commute {f : ℝ → 𝔸} {f' : 𝔸} {t : ℝ} (hf : HasDerivAt f f' t)
    (hc : ∀ s, Commute (f t) (f s)) :
    HasDerivAt (fun s => exp (f s)) (exp (f t) * f') t := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hD : HasDerivAt (fun s => f s - f t) f' t := hf.sub_const (f t)
  have h0 : HasFDerivAt exp (1 : 𝔸 →L[ℝ] 𝔸) (f t - f t) := by
    rw [sub_self]; exact hasFDerivAt_exp_zero
  have hE : HasDerivAt (fun s => exp (f s - f t)) f' t := by
    have := HasFDerivAt.comp_hasDerivAt t h0 hD
    exact this
  have hfun : (fun s => exp (f s)) = fun s => exp (f t) * exp (f s - f t) := by
    funext s
    rw [← exp_add_of_commute ((hc s).sub_right (Commute.refl _)), add_sub_cancel]
  rw [hfun]
  exact hE.const_mul (exp (f t))

/-- The coefficients `cₙ = (-1)^(n+1)/n` of the logarithm. -/
noncomputable def logCoeff (n : ℕ) : ℝ := (-1) ^ (n + 1) / n

/-- `log (1 + t y) = Σ (cₙ tⁿ) yⁿ`. -/
theorem log_one_add_smul (t : ℝ) (y : 𝔸) :
    log (1 + t • y) = ∑' n : ℕ, (logCoeff n * t ^ n) • y ^ n := by
  rw [congrFun (log_eq_tsum ℝ) (1 + t • y), add_sub_cancel_left]
  refine tsum_congr fun n => ?_
  rw [smul_pow, smul_smul, logCoeff, mul_comm]

theorem logCoeff_mul_cast {n : ℕ} (hn : n ≠ 0) : logCoeff n * n = (-1) ^ (n + 1) := by
  rw [logCoeff, div_mul_cancel₀]; exact_mod_cast hn

/-- Termwise derivative of `t ↦ log (1 + t y)` for `‖y‖ < 1`, on `|t| < R`, `R = 2 / (1 + ‖y‖)`. -/
theorem hasDerivAt_log_one_add_smul {y : 𝔸} (hy : ‖y‖ < 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (-(2 / (1 + ‖y‖))) (2 / (1 + ‖y‖))) :
    HasDerivAt (fun s => log (1 + s • y))
      (∑' n : ℕ, (logCoeff n * (n * t ^ (n - 1))) • y ^ n) t := by
  set R := 2 / (1 + ‖y‖) with hR
  have hny : 0 ≤ ‖y‖ := norm_nonneg y
  have hR1 : 1 < R := by rw [hR, lt_div_iff₀ (by linarith)]; linarith
  have hRy : R * ‖y‖ < 1 := by
    rw [hR, div_mul_eq_mul_div, div_lt_one (by linarith)]; nlinarith
  have hR0 : 0 ≤ R := by linarith
  let g : ℕ → ℝ → 𝔸 := fun n s => (logCoeff n * s ^ n) • y ^ n
  let g' : ℕ → ℝ → 𝔸 := fun n s => (logCoeff n * (n * s ^ (n - 1))) • y ^ n
  have hfun : (fun s => log (1 + s • y)) = fun s => ∑' n, g n s :=
    funext fun s => log_one_add_smul s y
  rw [hfun]
  have hu : Summable fun n : ℕ => (R * ‖y‖) ^ n :=
    summable_geometric_of_lt_one (by positivity) hRy
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-R) R := Set.mem_Ioo.2 ⟨by linarith, by linarith⟩
  refine hasDerivAt_tsum_of_isPreconnected (g := g) (g' := g') (y₀ := 0) hu isOpen_Ioo
    isPreconnected_Ioo (fun n s _ => ?_) (fun n s hs => ?_) h0mem ?_ ht
  · exact ((hasDerivAt_pow n s).const_mul (logCoeff n)).smul_const (y ^ n)
  · -- the bound ‖g' n s‖ ≤ (R ‖y‖)^n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [g', logCoeff]
    have hs' : |s| ≤ R := abs_le.2 ⟨(Set.mem_Ioo.1 hs).1.le, (Set.mem_Ioo.1 hs).2.le⟩
    have hc : |logCoeff n * n| = 1 := by
      rw [logCoeff_mul_cast hn.ne', abs_pow, abs_neg, abs_one, one_pow]
    calc ‖(logCoeff n * (n * s ^ (n - 1))) • y ^ n‖
        = |logCoeff n * n| * |s| ^ (n - 1) * ‖y ^ n‖ := by
          rw [norm_smul, Real.norm_eq_abs, ← mul_assoc, abs_mul, abs_pow]
      _ ≤ 1 * R ^ (n - 1) * ‖y‖ ^ n := by
          rw [hc]
          gcongr
          exact norm_pow_le' y hn
      _ ≤ R ^ n * ‖y‖ ^ n := by
          rw [one_mul]
          gcongr
          · exact hR1.le
          · omega
      _ = (R * ‖y‖) ^ n := (mul_pow R ‖y‖ n).symm
  · -- summable at 0
    have : (fun n => g n 0) = fun _ => (0 : 𝔸) := by
      funext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [g, logCoeff]
      · simp [g, zero_pow hn.ne']
    rw [this]; exact summable_zero

/-- The termwise derivative is `(Σ (-t y)^m) y`. -/
theorem deriv_series_eq {y : 𝔸} (hy : ‖y‖ < 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (-(2 / (1 + ‖y‖))) (2 / (1 + ‖y‖))) :
    ∑' n : ℕ, (logCoeff n * (n * t ^ (n - 1))) • y ^ n = (∑' m : ℕ, (-(t • y)) ^ m) * y := by
  set R := 2 / (1 + ‖y‖) with hR
  have hny : 0 ≤ ‖y‖ := norm_nonneg y
  have hRy : R * ‖y‖ < 1 := by
    rw [hR, div_mul_eq_mul_div, div_lt_one (by linarith)]; nlinarith
  have htR : |t| < R := abs_lt.2 ⟨(Set.mem_Ioo.1 ht).1, (Set.mem_Ioo.1 ht).2⟩
  have hty : ‖-(t • y)‖ < 1 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖y‖ ≤ R * ‖y‖ := mul_le_mul_of_nonneg_right htR.le hny
      _ < 1 := hRy
  have hgeo : Summable fun m : ℕ => (-(t • y)) ^ m :=
    summable_geometric_of_norm_lt_one hty
  have hterm : ∀ m : ℕ, (logCoeff (m + 1) * ((m + 1 : ℕ) * t ^ (m + 1 - 1))) • y ^ (m + 1) =
      (-(t • y)) ^ m * y := by
    intro m
    have hc : logCoeff (m + 1) * (((m + 1 : ℕ) : ℝ) * t ^ (m + 1 - 1)) = (-t) ^ m := by
      rw [← mul_assoc, logCoeff_mul_cast (Nat.succ_ne_zero m), Nat.add_sub_cancel, neg_pow t m,
        _root_.pow_succ, _root_.pow_succ]
      ring
    rw [hc, show -(t • y) = (-t) • y by rw [neg_smul], smul_pow, smul_mul_assoc,
      ← _root_.pow_succ]
  have hsum : Summable fun n : ℕ => (logCoeff n * (n * t ^ (n - 1))) • y ^ n := by
    rw [← summable_nat_add_iff 1]
    simp only [hterm]
    exact hgeo.mul_right y
  rw [hsum.tsum_eq_zero_add]
  simp only [hterm]
  rw [hgeo.tsum_mul_right]
  simp

/-- **`exp (log (1 + y)) = 1 + y` for `‖y‖ < 1`.** -/
theorem exp_log_one_add {y : 𝔸} (hy : ‖y‖ < 1) : exp (log (1 + y)) = 1 + y := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set R := 2 / (1 + ‖y‖) with hR
  have hny : 0 ≤ ‖y‖ := norm_nonneg y
  have hR1 : 1 < R := by rw [hR, lt_div_iff₀ (by linarith)]; linarith
  set L : ℝ → 𝔸 := fun s => log (1 + s • y) with hL
  set D : ℝ → 𝔸 := fun s => (∑' m : ℕ, (-(s • y)) ^ m) * y with hD
  have hcomm : ∀ s t : ℝ, Commute (L s) (L t) := by
    intro s t
    refine Commute.log ?_
    have hst : Commute (s • y) (t • y) := ((Commute.refl y).smul_left s).smul_right t
    exact (Commute.one_left _).add_left ((Commute.one_right _).add_right hst)
  set G : ℝ → 𝔸 := fun s => exp (-L s) * (1 + s • y) with hG
  have hGd : ∀ t ∈ Set.Ioo (-R) R, HasDerivAt G 0 t := by
    intro t ht
    have hLd : HasDerivAt L (D t) t := by
      have := hasDerivAt_log_one_add_smul hy ht
      rwa [deriv_series_eq hy ht] at this
    have hE := hasDerivAt_exp_of_commute hLd.neg fun s => ((hcomm t s).neg_left).neg_right
    have hlin : HasDerivAt (fun s : ℝ => 1 + s • y) y t := by
      simpa using ((hasDerivAt_id t).smul_const y).const_add 1
    have h := hE.mul hlin
    convert h using 1
    -- 0 = exp(-L t) (-D t) (1 + t y) + exp(-L t) y
    have hty : ‖-(t • y)‖ < 1 := by
      have htR : |t| < R := abs_lt.2 ⟨(Set.mem_Ioo.1 ht).1, (Set.mem_Ioo.1 ht).2⟩
      have hRy : R * ‖y‖ < 1 := by
        rw [hR, div_mul_eq_mul_div, div_lt_one (by linarith)]; nlinarith
      rw [norm_neg, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖y‖ ≤ R * ‖y‖ := mul_le_mul_of_nonneg_right htR.le hny
        _ < 1 := hRy
    have hgeo := geom_series_mul_neg (-(t • y)) hty
    have hkey : D t * (1 + t • y) = y := by
      simp only [hD]
      have hyc : y * (1 + t • y) = (1 + t • y) * y := by
        rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
      rw [mul_assoc, hyc, ← mul_assoc, show (1 : 𝔸) + t • y = 1 - -(t • y) by abel, hgeo, one_mul]
    rw [mul_assoc, neg_mul, hkey, ← mul_add, neg_add_cancel, mul_zero]
  -- G is constant on [0, 1]
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-R) R := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hconst := constant_of_has_deriv_right_zero
    (fun s hs => (hGd s (hsub hs)).continuousAt.continuousWithinAt)
    (fun s hs => (hGd s (hsub (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt)
    1 ⟨zero_le_one, le_rfl⟩
  have hG0 : G 0 = 1 := by simp [hG, hL, log_one, exp_zero]
  have hG1 : exp (-L 1) * (1 + y) = 1 := by
    have := hconst; rw [hG0] at this; simpa [hG] using this
  have hinv : exp (L 1) * exp (-L 1) = 1 := by
    rw [← exp_add_of_commute ((Commute.refl _).neg_right), add_neg_cancel, exp_zero]
  calc exp (log (1 + y)) = exp (L 1) := by simp [hL]
    _ = exp (L 1) * (exp (-L 1) * (1 + y)) := by rw [hG1, mul_one]
    _ = 1 + y := by rw [← mul_assoc, hinv, one_mul]

/-- **`exp (log x) = x` for `‖x - 1‖ < 1`.** -/
theorem exp_log {x : 𝔸} (hx : ‖x - 1‖ < 1) : exp (log x) = x := by
  have := exp_log_one_add hx
  rwa [add_sub_cancel] at this

end CoSimFoundations
