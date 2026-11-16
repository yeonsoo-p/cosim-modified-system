/-
Extremal energy ratios: the step-defect properties are attained maxima and minima.

With the step defect `D = Φ U⁻¹` (`U` invertible) and `S(x) = ½ xᵀ Q x`:
  `α  = ‖D - I‖_Q        = max_{x ≠ 0} ‖Φx - Ux‖_Q / ‖Ux‖_Q`,
  `ε  = ‖D‖_Q² - 1       = max_{x ≠ 0} (S(Φx) - S(Ux)) / S(Ux)`,
  `ε₋ = σ_min(D)² - 1     = min_{x ≠ 0} (S(Φx) - S(Ux)) / S(Ux)`   (the minimum exists).
`EnergyNorm.energy_le_opNorm_sq` gave only the bound; here the extrema are attained. The generic
facts (finite-dimensional real normed spaces): the operator norm is attained on the unit sphere,
and so is the minimum of `‖T x‖` there.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import CoSimFoundations.EnergyNorm

open Matrix

namespace CoSimFoundations

section Generic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]

/-- **The operator norm is attained** in a finite-dimensional real normed space. -/
theorem exists_norm_apply_eq_opNorm (T : V →L[ℝ] V) : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  have hne : (Metric.sphere (0 : V) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : V) 1).exists_isMaxOn hne
    (continuous_norm.comp T.continuous).continuousOn
  have hx1 : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx1, le_antisymm ?_ ?_⟩
  · simpa [hx1] using T.le_opNorm x
  · refine T.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy => ?_
    exact hmax (show y ∈ Metric.sphere (0 : V) 1 by simpa using hy)

/-- **The smallest stretch is attained:** some unit `x` has `‖T x‖ ‖y‖ ≤ ‖T y‖` for all `y`. -/
theorem exists_min_norm_apply (T : V →L[ℝ] V) :
    ∃ x, ‖x‖ = 1 ∧ ∀ y, ‖T x‖ * ‖y‖ ≤ ‖T y‖ := by
  have hne : (Metric.sphere (0 : V) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨x, hx, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hne
    (continuous_norm.comp T.continuous).continuousOn
  have hx1 : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx1, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hu : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hpos.ne']
    have h : ‖T x‖ ≤ ‖T (‖y‖⁻¹ • y)‖ := hmin hu
    rw [map_smul, norm_smul, norm_inv, norm_norm] at h
    calc ‖T x‖ * ‖y‖ ≤ ‖y‖⁻¹ * ‖T y‖ * ‖y‖ := mul_le_mul_of_nonneg_right h hpos.le
      _ = ‖T y‖ := by field_simp

end Generic

namespace QSpace

variable {n : Type*} [Fintype n] [DecidableEq n] {E : EnergyForm n}

instance [Nonempty n] : Nontrivial (QSpace E) := inferInstanceAs (Nontrivial (n → ℝ))

/-- The energy `S(x) = ½ xᵀ Q x`. -/
noncomputable def energy (E : EnergyForm n) (x : n → ℝ) : ℝ := (1 / 2 : ℝ) * (x ⬝ᵥ (E.Q *ᵥ x))

theorem toVec_ofVec (x : n → ℝ) : toVec E (ofVec E x) = x := rfl

theorem energy_eq (x : n → ℝ) : energy E x = ‖ofVec E x‖ ^ 2 / 2 := by
  rw [energy, norm_sq_eq, toVec_ofVec]
  ring

/-- Substitution `y = U x` for invertible `U`: `Φ x = (Φ U⁻¹) y`. -/
theorem mulVec_eq_stepDefect {U : Matrix n n ℝ} (hU : IsUnit U.det) (Φ : Matrix n n ℝ)
    (x : n → ℝ) : Φ *ᵥ x = (Φ * U⁻¹) *ᵥ (U *ᵥ x) := by
  rw [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one]

theorem mulVec_ne_zero {U : Matrix n n ℝ} (hU : IsUnit U.det) {x : n → ℝ} (hx : x ≠ 0) :
    U *ᵥ x ≠ 0 := by
  intro h
  apply hx
  rw [← one_mulVec x, ← nonsing_inv_mul _ hU, ← mulVec_mulVec, h, mulVec_zero]

/-- **Accuracy (Def. 10.1).** `α = ‖Φ U⁻¹ - I‖_Q` is the largest relative one-step state error
`‖Φx - Ux‖_Q / ‖Ux‖_Q`, and it is attained. -/
theorem isGreatest_accuracy [Nonempty n] {U : Matrix n n ℝ} (hU : IsUnit U.det)
    (Φ : Matrix n n ℝ) :
    IsGreatest {r | ∃ x ≠ 0, r = ‖ofVec E (Φ *ᵥ x - U *ᵥ x)‖ / ‖ofVec E (U *ᵥ x)‖}
      ‖op (E := E) (Φ * U⁻¹ - 1)‖ := by
  set T := op (E := E) (Φ * U⁻¹ - 1)
  have hTy : ∀ x, ofVec E (Φ *ᵥ x - U *ᵥ x) = T (ofVec E (U *ᵥ x)) := fun x => by
    show Φ *ᵥ x - U *ᵥ x = (Φ * U⁻¹ - 1) *ᵥ (U *ᵥ x)
    rw [sub_mulVec, one_mulVec, ← mulVec_eq_stepDefect hU]
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy1, hTy1⟩ := exists_norm_apply_eq_opNorm T
    have hUy : U *ᵥ (U⁻¹ *ᵥ toVec E y) = toVec E y := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
    have hx0 : U⁻¹ *ᵥ toVec E y ≠ 0 := fun h0 => by
      rw [h0, mulVec_zero] at hUy
      have : y = 0 := hUy.symm
      simp [this] at hy1
    refine ⟨U⁻¹ *ᵥ toVec E y, hx0, ?_⟩
    rw [hTy, hUy]
    show ‖T‖ = ‖T y‖ / ‖y‖
    rw [hTy1, hy1, div_one]
  · rintro r ⟨x, hx, rfl⟩
    have hpos : 0 < ‖ofVec E (U *ᵥ x)‖ := norm_pos_iff.2 (mulVec_ne_zero hU hx)
    rw [hTy, div_le_iff₀ hpos]
    exact T.le_opNorm _

/-- **Energy added (Def. 10.1).** `ε = ‖Φ U⁻¹‖_Q² - 1` is the largest relative energy added in one
step, `(S(Φx) - S(Ux)) / S(Ux)`, and it is attained. -/
theorem isGreatest_energyAdded [Nonempty n] {U : Matrix n n ℝ} (hU : IsUnit U.det)
    (Φ : Matrix n n ℝ) :
    IsGreatest {r | ∃ x ≠ 0, r = (energy E (Φ *ᵥ x) - energy E (U *ᵥ x)) / energy E (U *ᵥ x)}
      (‖op (E := E) (Φ * U⁻¹)‖ ^ 2 - 1) := by
  set T := op (E := E) (Φ * U⁻¹)
  have hTy : ∀ x, ofVec E (Φ *ᵥ x) = T (ofVec E (U *ᵥ x)) := fun x =>
    mulVec_eq_stepDefect hU Φ x
  have hratio : ∀ x, x ≠ 0 → (energy E (Φ *ᵥ x) - energy E (U *ᵥ x)) / energy E (U *ᵥ x) =
      (‖T (ofVec E (U *ᵥ x))‖ / ‖ofVec E (U *ᵥ x)‖) ^ 2 - 1 := fun x hx => by
    have hpos : 0 < ‖ofVec E (U *ᵥ x)‖ := norm_pos_iff.2 (mulVec_ne_zero hU hx)
    rw [energy_eq, energy_eq, hTy, div_pow]
    field_simp
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy1, hTy1⟩ := exists_norm_apply_eq_opNorm T
    have hUy : U *ᵥ (U⁻¹ *ᵥ toVec E y) = toVec E y := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
    have hx0 : U⁻¹ *ᵥ toVec E y ≠ 0 := fun h0 => by
      rw [h0, mulVec_zero] at hUy
      have : y = 0 := hUy.symm
      simp [this] at hy1
    refine ⟨U⁻¹ *ᵥ toVec E y, hx0, ?_⟩
    rw [hratio _ hx0, hUy]
    show ‖T‖ ^ 2 - 1 = (‖T y‖ / ‖y‖) ^ 2 - 1
    rw [hTy1, hy1, div_one]
  · rintro r ⟨x, hx, rfl⟩
    rw [hratio x hx]
    have hpos : 0 < ‖ofVec E (U *ᵥ x)‖ := norm_pos_iff.2 (mulVec_ne_zero hU hx)
    have hle : ‖T (ofVec E (U *ᵥ x))‖ / ‖ofVec E (U *ᵥ x)‖ ≤ ‖T‖ := by
      rw [div_le_iff₀ hpos]; exact T.le_opNorm _
    have h0 : 0 ≤ ‖T (ofVec E (U *ᵥ x))‖ / ‖ofVec E (U *ᵥ x)‖ := by positivity
    have := pow_le_pow_left₀ h0 hle 2
    linarith

/-- **Energy removed (Def. 10.1).** The least relative energy change in one step,
`ε₋ = min_{x ≠ 0} (S(Φx) - S(Ux)) / S(Ux)`, exists; it equals `σ² - 1` with
`σ = min_{‖y‖_Q = 1} ‖Φ U⁻¹ y‖_Q` (the paper's `σ_min(D)`). -/
theorem exists_isLeast_energyRemoved [Nonempty n] {U : Matrix n n ℝ} (hU : IsUnit U.det)
    (Φ : Matrix n n ℝ) :
    ∃ y : QSpace E, ‖y‖ = 1 ∧
      IsLeast {r | ∃ x ≠ 0, r = (energy E (Φ *ᵥ x) - energy E (U *ᵥ x)) / energy E (U *ᵥ x)}
        (‖op (E := E) (Φ * U⁻¹) y‖ ^ 2 - 1) := by
  set T := op (E := E) (Φ * U⁻¹)
  have hTy : ∀ x, ofVec E (Φ *ᵥ x) = T (ofVec E (U *ᵥ x)) := fun x =>
    mulVec_eq_stepDefect hU Φ x
  have hratio : ∀ x, x ≠ 0 → (energy E (Φ *ᵥ x) - energy E (U *ᵥ x)) / energy E (U *ᵥ x) =
      (‖T (ofVec E (U *ᵥ x))‖ / ‖ofVec E (U *ᵥ x)‖) ^ 2 - 1 := fun x hx => by
    have hpos : 0 < ‖ofVec E (U *ᵥ x)‖ := norm_pos_iff.2 (mulVec_ne_zero hU hx)
    rw [energy_eq, energy_eq, hTy, div_pow]
    field_simp
  obtain ⟨y, hy1, hmin⟩ := exists_min_norm_apply T
  refine ⟨y, hy1, ?_, ?_⟩
  · have hUy : U *ᵥ (U⁻¹ *ᵥ toVec E y) = toVec E y := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
    have hx0 : U⁻¹ *ᵥ toVec E y ≠ 0 := fun h0 => by
      rw [h0, mulVec_zero] at hUy
      have : y = 0 := hUy.symm
      simp [this] at hy1
    refine ⟨U⁻¹ *ᵥ toVec E y, hx0, ?_⟩
    rw [hratio _ hx0, hUy]
    show ‖T y‖ ^ 2 - 1 = (‖T y‖ / ‖y‖) ^ 2 - 1
    rw [hy1, div_one]
  · rintro r ⟨x, hx, rfl⟩
    rw [hratio x hx]
    have hpos : 0 < ‖ofVec E (U *ᵥ x)‖ := norm_pos_iff.2 (mulVec_ne_zero hU hx)
    have hle : ‖T y‖ ≤ ‖T (ofVec E (U *ᵥ x))‖ / ‖ofVec E (U *ᵥ x)‖ := by
      rw [le_div_iff₀ hpos]; exact hmin _
    have := pow_le_pow_left₀ (norm_nonneg _) hle 2
    linarith

end QSpace

end CoSimFoundations
