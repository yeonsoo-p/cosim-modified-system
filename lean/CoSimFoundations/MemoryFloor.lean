/-
The memory floor (the paper, Thm 6.5), in its min–max form.

If `B` has rank at most `r` and `W` is a subspace of dimension larger than `r`, some unit vector of
`W` lies in the kernel of `B`; hence `‖A - B‖ ≥ ‖A v‖` for that vector: no map of rank `≤ r` is
closer to `A` than the least stretch of `A` on any subspace of dimension `r + 1`. Taking `W` spanned
by the `r + 1` leading right singular vectors of `A` gives `‖A - B‖ ≥ σ_{r+1}(A)`
(Eckart–Young–Mirsky); that identification of the best `W` with singular vectors is not formalised
here.

In the paper `A = U_{i,≠i}` is what the reference sends into subsystem `i` in one step, `B` the
corresponding block row of the step matrix of a rule with `ℓ` held samples (rank `≤ ℓ m`), and
`‖A - B‖ ≤ α ‖U‖`.
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module

namespace CoSimFoundations

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A map of rank smaller than `dim W` kills a unit vector of `W`. -/
theorem exists_unit_mem_ker_of_finrank_lt (B : E →L[ℝ] F) (W : Submodule ℝ E)
    (h : finrank ℝ (LinearMap.range (B : E →ₗ[ℝ] F)) < finrank ℝ W) :
    ∃ v ∈ W, ‖v‖ = 1 ∧ B v = 0 := by
  let g : W →ₗ[ℝ] F := (B : E →ₗ[ℝ] F).domRestrict W
  have hker : LinearMap.ker g ≠ ⊥ := by
    intro hk
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [hk, finrank_bot, add_zero] at h1
    have h2 : finrank ℝ (LinearMap.range g) ≤ finrank ℝ (LinearMap.range (B : E →ₗ[ℝ] F)) :=
      Submodule.finrank_mono (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
    omega
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hwE : (w : E) ≠ 0 := fun h0 => hw0 (Subtype.ext h0)
  have hBw : B (w : E) = 0 := hw
  refine ⟨‖(w : E)‖⁻¹ • (w : E), W.smul_mem _ w.2, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hwE)]
  · rw [map_smul, hBw, smul_zero]

/-- **Memory floor, min–max form.** If `B` has rank smaller than `dim W`, then some unit vector
`v ∈ W` has `‖A v‖ ≤ ‖A - B‖`. -/
theorem memory_floor (A B : E →L[ℝ] F) (W : Submodule ℝ E)
    (h : finrank ℝ (LinearMap.range (B : E →ₗ[ℝ] F)) < finrank ℝ W) :
    ∃ v ∈ W, ‖v‖ = 1 ∧ ‖A v‖ ≤ ‖A - B‖ := by
  obtain ⟨v, hv, hn, hB⟩ := exists_unit_mem_ker_of_finrank_lt B W h
  refine ⟨v, hv, hn, ?_⟩
  have h1 : A v = (A - B) v := by simp [hB]
  rw [h1]
  simpa [hn] using (A - B).le_opNorm v

end CoSimFoundations
