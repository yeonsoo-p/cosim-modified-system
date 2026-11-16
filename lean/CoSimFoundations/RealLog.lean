/-
Existence of a logarithm along a segment of units (the paper, Prop 3.2 (i): the modified system
exists).

In a real Banach algebra, if `(1 - t) • 1 + t • x` is a unit for every `t ∈ [0, 1]` (for a real
matrix: `x` has no eigenvalue on `(-∞, 0]`), then `x = exp L` with

  `L = ∫₀¹ (x - 1) * ((1 - u) • 1 + u • x)⁻¹ du`.

Hence a one-step map `X` without eigenvalues on `(-∞, 0]` is the time-`H` flow of the modified
system `Ã = L / H`.

Plan of proof: with `y = x - 1` and `L s = ∫₀ˢ y * (1 + u • y)⁻¹ du`, all `L s` commute with `y`,
`d/ds L s = y * (1 + s • y)⁻¹`, and `s ↦ exp (L s) * (1 + s • y)⁻¹` has derivative zero and the
value `1` at `s = 0`.

Not here: uniqueness in the strip `|Im λ| < π` (the principal logarithm).
-/
import CoSimFoundations.ExpLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open NormedSpace

namespace CoSimFoundations

/-- An element commuting with `a` commutes with `Ring.inverse a` (which is `0` off the units). -/
theorem commute_ringInverse_right {M₀ : Type*} [MonoidWithZero M₀] {c a : M₀}
    (h : Commute c a) : Commute c (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ ha]
    exact Commute.zero_right c

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- An element commuting with every value of a continuous curve commutes with its integral. -/
theorem commute_intervalIntegral {f : ℝ → 𝔸} (hf : Continuous f) {c : 𝔸}
    (hc : ∀ u, Commute c (f u)) (a b : ℝ) : Commute c (∫ u in a..b, f u) := by
  have h1 : c * ∫ u in a..b, f u = ∫ u in a..b, c * f u :=
    ((ContinuousLinearMap.mul ℝ 𝔸 c).intervalIntegral_comp_comm (hf.intervalIntegrable a b)).symm
  have h2 : (∫ u in a..b, f u) * c = ∫ u in a..b, f u * c :=
    (((ContinuousLinearMap.mul ℝ 𝔸).flip c).intervalIntegral_comp_comm
      (hf.intervalIntegrable a b)).symm
  change c * _ = _ * c
  rw [h1, h2]
  exact intervalIntegral.integral_congr fun u _ => (hc u).eq

/-- **A logarithm exists along a segment of units.** -/
theorem exists_exp_eq_of_isUnit_segment (x : 𝔸)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit ((1 - t) • (1 : 𝔸) + t • x)) :
    ∃ L : 𝔸, exp L = x := by
  set y : 𝔸 := x - 1 with hy
  have hseg : ∀ t : ℝ, (1 - t) • (1 : 𝔸) + t • x = 1 + t • y := fun t => by
    rw [hy, smul_sub, sub_smul, one_smul]; abel
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 + t • y) := fun t ht => by
    rw [← hseg]; exact h t ht
  -- the clamp to `[0, 1]` makes the integrand continuous on all of `ℝ`
  set p : ℝ → ℝ := fun u => max 0 (min u 1) with hp
  have hpc : Continuous p := continuous_const.max (continuous_id.min continuous_const)
  have hpI : ∀ u, p u ∈ Set.Icc (0 : ℝ) 1 := fun u =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hpeq : ∀ u ∈ Set.Icc (0 : ℝ) 1, p u = u := fun u hu => by
    simp only [hp, min_eq_left hu.2, max_eq_right hu.1]
  set f : ℝ → 𝔸 := fun u => y * Ring.inverse (1 + p u • y) with hf
  have hfc : Continuous f := by
    show Continuous fun u => y * Ring.inverse (1 + p u • y)
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun u => ?_)
    obtain ⟨w, hw⟩ := hU (p u) (hpI u)
    have hi : ContinuousAt Ring.inverse (1 + p u • y) := by
      rw [← hw]; exact NormedRing.inverse_continuousAt w
    exact hi.comp (f := fun u => 1 + p u • y)
      (continuous_const.add (hpc.smul continuous_const)).continuousAt
  -- all values of `f` and of `L` commute
  have hyf : ∀ u, Commute y (f u) := fun u =>
    (Commute.refl y).mul_right (commute_ringInverse_right
      ((Commute.one_right y).add_right ((Commute.refl y).smul_right (p u))))
  set L : ℝ → 𝔸 := fun s => ∫ u in (0 : ℝ)..s, f u with hL
  have hyL : ∀ s, Commute y (L s) := fun s => commute_intervalIntegral hfc hyf 0 s
  have hLf : ∀ s u, Commute (L s) (f u) := fun s u =>
    (hyL s).symm.mul_right (commute_ringInverse_right
      ((Commute.one_right (L s)).add_right ((hyL s).symm.smul_right (p u))))
  have hLL : ∀ s s', Commute (L s) (L s') := fun s s' =>
    commute_intervalIntegral hfc (hLf s) 0 s'
  have hLd : ∀ s, HasDerivAt L (f s) s := fun s =>
    (hfc.integral_hasStrictDerivAt 0 s).hasDerivAt
  -- `g s = exp (L s) * (1 + s • y)⁻¹` has derivative zero on `[0, 1]`
  set g : ℝ → 𝔸 := fun s => exp (L s) * Ring.inverse (1 + s • y) with hg
  have hgd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g 0 s := by
    intro s hs
    obtain ⟨w, hw⟩ := hU s hs
    have hE := hasDerivAt_exp_of_commute (hLd s) (hLL s)
    have hlin : HasDerivAt (fun s : ℝ => 1 + s • y) y s := by
      simpa using ((hasDerivAt_id s).smul_const y).const_add 1
    have hinv : HasFDerivAt Ring.inverse
        (-ContinuousLinearMap.mulLeftRight ℝ 𝔸 ↑w⁻¹ ↑w⁻¹) (1 + s • y) := by
      rw [← hw]; exact hasFDerivAt_ringInverse w
    have hI : HasDerivAt (fun s : ℝ => Ring.inverse (1 + s • y))
        ((-ContinuousLinearMap.mulLeftRight ℝ 𝔸 ↑w⁻¹ ↑w⁻¹) y) s := by
      have h' := hinv.comp_hasDerivAt s hlin
      exact h'
    have hprod : HasDerivAt g (exp (L s) * f s * Ring.inverse (1 + s • y) +
        exp (L s) * (-ContinuousLinearMap.mulLeftRight ℝ 𝔸 ↑w⁻¹ ↑w⁻¹) y) s :=
      hE.mul hI
    have hyw : y * ↑w⁻¹ = (↑w⁻¹ : 𝔸) * y := by
      have hc : Commute y (w : 𝔸) := by
        rw [hw]; exact (Commute.one_right y).add_right ((Commute.refl y).smul_right s)
      exact hc.units_inv_right.eq
    have hfs : f s = y * ↑w⁻¹ := by
      show y * Ring.inverse (1 + p s • y) = y * ↑w⁻¹
      rw [hpeq s hs, ← hw, Ring.inverse_unit]
    have hD : exp (L s) * f s * Ring.inverse (1 + s • y) +
        exp (L s) * (-ContinuousLinearMap.mulLeftRight ℝ 𝔸 ↑w⁻¹ ↑w⁻¹) y = 0 := by
      rw [hfs, ← hw, Ring.inverse_unit, neg_apply, ContinuousLinearMap.mulLeftRight_apply, hyw]
      noncomm_ring
    rwa [hD] at hprod
  have hconst := constant_of_has_deriv_right_zero
    (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hgd s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    1 ⟨zero_le_one, le_rfl⟩
  have hg0 : g 0 = 1 := by
    simp only [hg, hL, intervalIntegral.integral_same, exp_zero, zero_smul, add_zero,
      Ring.inverse_one, mul_one]
  have hx1 : (1 : 𝔸) + y = x := by rw [hy, add_sub_cancel]
  have hxU : IsUnit x := by
    have := hU 1 ⟨zero_le_one, le_rfl⟩
    rwa [one_smul, hx1] at this
  have hg1 : exp (L 1) * Ring.inverse x = 1 := by
    have h1 : g 1 = exp (L 1) * Ring.inverse x := by
      simp only [hg, one_smul, hx1]
    rw [← h1, hconst, hg0]
  refine ⟨L 1, ?_⟩
  calc exp (L 1) = exp (L 1) * (Ring.inverse x * x) := by
        rw [Ring.inverse_mul_cancel x hxU, mul_one]
    _ = x := by rw [← mul_assoc, hg1, one_mul]

/-- **The modified system exists:** a one-step map on a segment of units from the identity is the
time-`H` flow of a generator. -/
theorem exists_modified_system (X : 𝔸) {H : ℝ} (hH : H ≠ 0)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit ((1 - t) • (1 : 𝔸) + t • X)) :
    ∃ At : 𝔸, exp (H • At) = X := by
  obtain ⟨L, hL⟩ := exists_exp_eq_of_isUnit_segment X h
  exact ⟨H⁻¹ • L, by rw [smul_smul, mul_inv_cancel₀ hH, one_smul, hL]⟩

/-- For real matrices the hypothesis is a determinant condition: no eigenvalue on `(-∞, 0]`. -/
theorem exists_modified_system_matrix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : H ≠ 0)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • X).det ≠ 0) :
    ∃ At : Matrix (Fin n) (Fin n) ℝ, exp (H • At) = X := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.linftyOpNormedAlgebra
  exact exists_modified_system X hH fun t ht =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (h t ht))

end CoSimFoundations
