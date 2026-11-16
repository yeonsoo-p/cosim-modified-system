/-
The Bauer–Fike theorem, in the form used for the spectral bounds:

* normal case: in a C⋆-algebra, if `a` is normal then every `μ ∈ σ(a + b)` lies within `‖b‖` of
  `σ(a)`;
* unitary case: if `u` is unitary then every `μ ∈ σ(u + b)` has `|‖μ‖ - 1| ≤ ‖b‖`;
* diagonalisable case with a condition number: for operators `a = e d e⁻¹` on a Hilbert space with
  `d` normal on another one, every `μ ∈ σ(a + b)` lies within `‖e‖ ‖e⁻¹‖ ‖b‖` of `σ(d) = σ(a)`.

Not in Mathlib. The proof is the resolvent argument: if `μ` is farther than `‖b‖` from `σ(a)`, the
resolvent `(μ - a)⁻¹` is normal, so its norm is its spectral radius `1 / dist(μ, σ a) < 1 / ‖b‖`,
and `μ - (a + b) = (μ - a)(1 - (μ - a)⁻¹ b)` is a product of units (Neumann series).
-/
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

open scoped NNReal ENNReal

namespace CoSimFoundations

section CStar

variable {A : Type*} [CStarAlgebra A]

/-- `μ - a` is normal when `a` is. -/
theorem isStarNormal_algebraMap_sub (μ : ℂ) (a : A) [IsStarNormal a] :
    IsStarNormal (algebraMap ℂ A μ - a) := by
  have : IsStarNormal (algebraMap ℂ A μ) :=
    ⟨by rw [← algebraMap_star_comm]; exact Algebra.commutes _ _⟩
  have hc : Commute (algebraMap ℂ A μ) (star a) := Algebra.commutes μ (star a)
  exact hc.isStarNormal_sub

/-- **Bauer–Fike, normal case.** If `a` is normal, every point of `σ(a + b)` lies within `‖b‖` of
a point of `σ(a)`. -/
theorem exists_mem_spectrum_norm_sub_le {a : A} [IsStarNormal a] (b : A) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (a + b)) : ∃ l ∈ spectrum ℂ a, ‖μ - l‖ ≤ ‖b‖ := by
  have hnt : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    simp [spectrum.of_subsingleton] at hμ
  by_contra! h
  -- `μ` is not in `σ a`, so `μ - a` is a unit
  have hμa : μ ∉ spectrum ℂ a := fun hm => by
    have := h μ hm
    rw [sub_self, norm_zero] at this
    exact (norm_nonneg b).not_gt this
  obtain ⟨u, hu⟩ := spectrum.notMem_iff.1 hμa
  have : IsStarNormal (u : A) := hu ▸ isStarNormal_algebraMap_sub μ a
  -- the norm of the resolvent is attained on its spectrum
  obtain ⟨z, hz, hzr⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty (↑u⁻¹ : A))
  rw [IsStarNormal.spectralRadius_eq_nnnorm, ENNReal.coe_inj] at hzr
  have hz' : z ∈ (spectrum ℂ (u : A))⁻¹ := by rw [spectrum.map_inv]; exact hz
  rw [Set.mem_inv, hu, ← spectrum.singleton_sub_eq] at hz'
  obtain ⟨x, hx, l, hl, hxl⟩ := hz'
  rw [Set.mem_singleton_iff] at hx
  rw [hx] at hxl
  -- `z⁻¹ = μ - l`, `‖b‖ < ‖μ - l‖`
  have hlt := h l hl
  rw [show μ - l = z⁻¹ from hxl] at hlt
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [inv_zero, norm_zero] at hlt
    exact (norm_nonneg b).not_gt hlt
  have hnorm : ‖(↑u⁻¹ : A)‖ * ‖b‖ < 1 := by
    have he : ‖(↑u⁻¹ : A)‖ = ‖z‖ := congrArg NNReal.toReal hzr.symm
    rw [he]
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    calc ‖z‖ * ‖b‖ < ‖z‖ * ‖z⁻¹‖ := mul_lt_mul_of_pos_left hlt hpos
      _ = 1 := by rw [norm_inv, mul_inv_cancel₀ hpos.ne']
  -- `μ - (a + b) = u (1 - u⁻¹ b)` is a unit
  have hfac : algebraMap ℂ A μ - (a + b) = (u : A) * (1 - (↑u⁻¹ : A) * b) := by
    rw [mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hu]
    abel
  apply spectrum.mem_iff.1 hμ
  rw [hfac]
  exact u.isUnit.mul (isUnit_one_sub_of_norm_lt_one ((norm_mul_le _ _).trans_lt hnorm))

/-- **Bauer–Fike, unitary case.** If `u` is unitary, every `μ ∈ σ(u + b)` has
`|‖μ‖ - 1| ≤ ‖b‖`. -/
theorem abs_norm_sub_one_le_of_unitary {u : A} (hu : u ∈ unitary A) (b : A) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (u + b)) : |‖μ‖ - 1| ≤ ‖b‖ := by
  have : IsStarNormal u := Unitary.coe_isStarNormal ⟨u, hu⟩
  obtain ⟨l, hl, hle⟩ := exists_mem_spectrum_norm_sub_le b hμ
  have h1 : ‖l‖ = 1 := spectrum.norm_eq_one_of_unitary hu hl
  calc |‖μ‖ - 1| = |‖μ‖ - ‖l‖| := by rw [h1]
    _ ≤ ‖μ - l‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖b‖ := hle

end CStar

section Operators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Bauer–Fike with a condition number.** Let `a = e d e⁻¹` where `d` is a normal operator on
`E` and `e : E ≃ F`. Every `μ ∈ σ(a + b)` lies within `‖e‖ ‖e⁻¹‖ ‖b‖` of a point of `σ(d)`
(which is `σ(a)`, `spectrum_conj`). -/
theorem exists_mem_spectrum_norm_sub_le_conj (e : E ≃L[ℂ] F) (d : E →L[ℂ] E) [IsStarNormal d]
    (b : F →L[ℂ] F) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (e.conjContinuousAlgEquiv d + b)) :
    ∃ l ∈ spectrum ℂ d, ‖μ - l‖ ≤ ‖(e : E →L[ℂ] F)‖ * ‖(e.symm : F →L[ℂ] E)‖ * ‖b‖ := by
  set φ := e.conjContinuousAlgEquiv
  have hsplit : φ d + b = φ (d + φ.symm b) := by
    rw [map_add, ContinuousAlgEquiv.apply_symm_apply]
  rw [hsplit, AlgEquiv.spectrum_eq] at hμ
  obtain ⟨l, hl, hle⟩ := exists_mem_spectrum_norm_sub_le (φ.symm b) hμ
  refine ⟨l, hl, hle.trans ?_⟩
  have hb : φ.symm b = (e.symm : F →L[ℂ] E) ∘L b ∘L (e : E →L[ℂ] F) := by
    ext x; rfl
  rw [hb]
  calc ‖(e.symm : F →L[ℂ] E) ∘L b ∘L (e : E →L[ℂ] F)‖
      ≤ ‖(e.symm : F →L[ℂ] E)‖ * (‖b‖ * ‖(e : E →L[ℂ] F)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖(e : E →L[ℂ] F)‖ * ‖(e.symm : F →L[ℂ] E)‖ * ‖b‖ := by ring

/-- Conjugation does not change the spectrum. -/
theorem spectrum_conj (e : E ≃L[ℂ] F) (d : E →L[ℂ] E) :
    spectrum ℂ (e.conjContinuousAlgEquiv d) = spectrum ℂ d :=
  AlgEquiv.spectrum_eq _ _

end Operators

end CoSimFoundations
