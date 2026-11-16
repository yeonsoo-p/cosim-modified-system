/-
The two floors for the scheme class, end to end (the paper, Thm 6.2 and Cor 6.3).

`Floor` proves the floors for operators on an inner product space, `ScalarStores` derives the class
`𝒳` of step matrices from the differential equations of the stores. Here the two are joined for
matrices on Euclidean space (energy coordinates): for every scheme of the class with step matrix
`X = D * U`, where `U` is the reference step and `D` the one-step defect, and `α = ‖D - 1‖`:

* stores `i ≠ j` that are not partners: `|U i j| ≤ α ‖U e_j‖`   (link floor);
* every store `i`:                      `-U i i ≤ α ‖U e_i‖`     (turning floor);
* the class contains a scheme with step matrix `U` if and only if `U ∈ 𝒳`.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import CoSimFoundations.Floor
import CoSimFoundations.ScalarStores

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {n : ℕ}

/-- The operator of a matrix on Euclidean space. -/
noncomputable abbrev opE (M : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M

/-- The `j`-th unit vector of Euclidean space. -/
noncomputable abbrev unitE (j : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1

theorem norm_unitE (j : Fin n) : ‖unitE j‖ = 1 := by simp [unitE]

theorem inner_unitE_opE (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪unitE i, opE M (unitE j)⟫ = M i j := by
  simp [unitE, opE, EuclideanSpace.inner_single_left, ofLp_toEuclideanCLM]

theorem opE_mul_apply (D U : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    opE (D * U) v = opE D (opE U v) := by
  simp [opE, map_mul]

/-- **Turning floor, matrix form.** If the step matrix `X = D * U` has `0 ≤ X i i`, then
`-U i i ≤ ‖D - 1‖ ‖U e_i‖`. -/
theorem turning_floor_matrix (D U : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (h : 0 ≤ (D * U) i i) : -U i i ≤ ‖opE D - 1‖ * ‖opE U (unitE i)‖ := by
  have h0 : 0 ≤ ⟪unitE i, opE D (opE U (unitE i))⟫ := by
    rw [← opE_mul_apply, inner_unitE_opE]; exact h
  have := turning_floor (opE D) (opE U) (norm_unitE i) h0
  rwa [inner_unitE_opE] at this

/-- **Link floor, matrix form.** If the step matrix `X = D * U` has `X i j = 0`, then
`|U i j| ≤ ‖D - 1‖ ‖U e_j‖`. -/
theorem link_floor_matrix (D U : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (h : (D * U) i j = 0) : |U i j| ≤ ‖opE D - 1‖ * ‖opE U (unitE j)‖ := by
  have h0 : ⟪unitE i, opE D (opE U (unitE j))⟫ = 0 := by
    rw [← opE_mul_apply, inner_unitE_opE]; exact h
  have := link_floor (opE D) (opE U) (norm_unitE i) (unitE j) h0
  rwa [inner_unitE_opE] at this

/-- **Sharp link floor, operator form.** If the step `D * U` sends `c` to a vector with zero
`i`-th component, then `|(U c)_i| ≤ ‖D - 1‖ ‖U c‖`. Taking the supremum over `c` in a subspace gives
the norm of the projection of `e_i` onto its image under `U`. -/
theorem link_floor_vec (D U : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (c : EuclideanSpace ℝ (Fin n)) (h : ⟪unitE i, opE (D * U) c⟫ = 0) :
    |⟪unitE i, opE U c⟫| ≤ ‖opE D - 1‖ * ‖opE U c‖ := by
  rw [opE_mul_apply] at h
  exact link_floor (opE D) (opE U) (norm_unitE i) c h

theorem inner_unitE_opE_apply (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (c : EuclideanSpace ℝ (Fin n)) : ⟪unitE i, opE M c⟫ = ∑ j, M i j * c j := by
  simp [unitE, opE, EuclideanSpace.inner_single_left, ofLp_toEuclideanCLM, Matrix.mulVec,
    dotProduct]

namespace ScalarNet

variable (N : ScalarNet n)

/-- **The floors of the class (Thm 6.2).** For every Jacobi scheme with one held sample, weights
on the coupling graph and any gains, at any macro step `H > 0`: if its step matrix is `D * U`,
then `|U i j| ≤ ‖D - 1‖ ‖U e_j‖` for stores that are not partners, and
`-U i i ≤ ‖D - 1‖ ‖U e_i‖` for every store. -/
theorem floors {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ i j, ¬ N.partner i j → w i j = 0) (D U : Matrix (Fin n) (Fin n) ℝ)
    (hX : N.jacobiStep H k w = D * U) :
    (∀ i j, i ≠ j → ¬ N.partner i j → |U i j| ≤ ‖opE D - 1‖ * ‖opE U (unitE j)‖) ∧
      ∀ i, -U i i ≤ ‖opE D - 1‖ * ‖opE U (unitE i)‖ := by
  have hmem : N.jacobiStep H k w ∈ N.classX := by
    rw [← N.range_jacobiStep hH]; exact ⟨k, w, hw, rfl⟩
  refine ⟨fun i j hij hp => link_floor_matrix D U i j ?_, fun i => turning_floor_matrix D U i ?_⟩
  · rw [← hX]; exact hmem.2 i j hij hp
  · rw [← hX]; exact (hmem.1 i).le

/-- **The sharp link floor of the class (Thm 6.2).** For every scheme of the class with step
`D * U` and every vector `c` supported on the stores that are neither `i` nor partners of `i`:
`|(U c)_i| ≤ ‖D - 1‖ ‖U c‖`. -/
theorem sharp_link_floor {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ i j, ¬ N.partner i j → w i j = 0) (D U : Matrix (Fin n) (Fin n) ℝ)
    (hX : N.jacobiStep H k w = D * U) (i : Fin n) (c : EuclideanSpace ℝ (Fin n))
    (hc : ∀ j, j = i ∨ N.partner i j → c j = 0) :
    |⟪unitE i, opE U c⟫| ≤ ‖opE D - 1‖ * ‖opE U c‖ := by
  have hmem : N.jacobiStep H k w ∈ N.classX := by
    rw [← N.range_jacobiStep hH]; exact ⟨k, w, hw, rfl⟩
  refine link_floor_vec D U i c ?_
  rw [inner_unitE_opE_apply, ← hX]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = i ∨ N.partner i j
  · rw [hc j hj, mul_zero]
  · have hji : i ≠ j := fun h => hj (Or.inl h.symm)
    rw [hmem.2 i j hji (fun hp => hj (Or.inr hp)), zero_mul]

/-- **When nothing has to be traded (Cor 6.3).** The class contains a scheme whose step matrix is
`U` if and only if `U ∈ 𝒳`. -/
theorem exists_exact_iff {H : ℝ} (hH : 0 < H) (U : Matrix (Fin n) (Fin n) ℝ) :
    (∃ k w, (∀ i j, ¬ N.partner i j → w i j = 0) ∧ U = N.jacobiStep H k w) ↔ U ∈ N.classX := by
  rw [← N.range_jacobiStep hH]; rfl

/-- **The threshold for fully coupled stores (Thm 7.3, Jacobi mode).** If every pair of distinct
stores is coupled, the class contains a scheme with step matrix `U` if and only if `U` has a
positive diagonal: every store is turned by less than a right angle. -/
theorem exists_exact_iff_of_fullyCoupled {H : ℝ} (hH : 0 < H)
    (hfull : ∀ i j, i ≠ j → N.partner i j) (U : Matrix (Fin n) (Fin n) ℝ) :
    (∃ k w, (∀ i j, ¬ N.partner i j → w i j = 0) ∧ U = N.jacobiStep H k w) ↔ ∀ i, 0 < U i i := by
  rw [N.exists_exact_iff hH]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i j hij hp => absurd (hfull i j hij) hp⟩⟩

end ScalarNet

end CoSimFoundations
