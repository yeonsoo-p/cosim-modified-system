/-
The memory floor in singular-value form (the paper, Thm 6.6): the Eckart–Young–Mirsky lower
bound in the operator norm.

`A`, `B` linear maps between finite-dimensional real inner product spaces. If `B` has rank at most
`k`, then the singular value of `A` with index `k` (0-based: the `(k+1)`-st largest,
Mathlib's `LinearMap.singularValues`) is at most `‖A - B‖`.

In the paper `A` is the block row `U_{i,≠i}` of the reference step, `B` the same block of a rule
whose subsystem `i` remembers `k` numbers, and the conclusion is `α ‖U‖ ≥ σ_{k+1}(U_{i,≠i})`.
The floor is zero as soon as `k ≥ min (dim E) (dim F)`; in particular for a scalar store.

Plan of proof: the span `W` of `k + 1` orthonormal eigenvectors of `A† A` for the `k + 1` largest
eigenvalues has dimension `k + 1`, and `‖A v‖ ≥ σ_k ‖v‖` on `W`; apply `memory_floor`.
-/
import CoSimFoundations.MemoryFloor
import Mathlib.Analysis.InnerProductSpace.SingularValues

open Module
open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Given an orthonormal basis `b` of eigenvectors of `T† T` with eigenvalues `μ` in decreasing
order, the span of the first `k + 1` of them has dimension `k + 1`, and on it
`μ_k ‖v‖² ≤ ‖T v‖²`. -/
theorem exists_finrank_eq_mul_norm_sq_le (T : E →ₗ[ℝ] F) {n k : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (μ : Fin n → ℝ) (hμ : Antitone μ)
    (hb : ∀ i, LinearMap.adjoint T (T (b i)) = μ i • b i) (hk : k + 1 ≤ n) :
    ∃ W : Submodule ℝ E, finrank ℝ W = k + 1 ∧ ∀ v ∈ W, μ ⟨k, hk⟩ * ‖v‖ ^ 2 ≤ ‖T v‖ ^ 2 := by
  refine ⟨Submodule.span ℝ (Set.range (b ∘ Fin.castLE hk)), ?_, fun v hv => ?_⟩
  · exact (finrank_span_eq_card (b.orthonormal.linearIndependent.comp _
      (Fin.castLE_injective hk))).trans (Fintype.card_fin _)
  -- the coordinates of `v` beyond `k` vanish
  have hzero : ∀ i : Fin n, k < i.val → ⟪b i, v⟫ = 0 := by
    intro i hi
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine b.orthonormal.2 fun h => ?_
      have h1 : i.val = j.val := congrArg Fin.val h
      have h2 := j.isLt
      omega
    | zero => exact inner_zero_right _
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hS : ∀ i, ⟪b i, LinearMap.adjoint T (T v)⟫ = μ i * ⟪b i, v⟫ := by
    intro i
    rw [LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_left, hb, real_inner_smul_left]
  have hTv : ‖T v‖ ^ 2 = ∑ i, ⟪v, b i⟫ * (μ i * ⟪b i, v⟫) := by
    rw [← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_right,
      ← b.sum_inner_mul_inner v (LinearMap.adjoint T (T v))]
    simp only [hS]
  have hv2 : ‖v‖ ^ 2 = ∑ i, ⟪v, b i⟫ * ⟪b i, v⟫ := by
    rw [b.sum_inner_mul_inner, real_inner_self_eq_norm_sq]
  rw [hTv, hv2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [real_inner_comm (b i) v]
  by_cases hi : k < i.val
  · rw [hzero i hi]
    simp
  · have h2 : i ≤ ⟨k, hk⟩ := Fin.le_def.2 (show i.val ≤ k by omega)
    have h1 : μ ⟨k, hk⟩ ≤ μ i := hμ h2
    nlinarith [mul_le_mul_of_nonneg_right h1 (mul_self_nonneg ⟪b i, v⟫)]

/-- Some subspace of dimension `k + 1` on which `T` stretches every vector by at least `σ_k`
(the span of the `k + 1` leading right singular vectors). -/
theorem exists_finrank_eq_singularValues_mul_le (T : E →ₗ[ℝ] F) {k : ℕ}
    (hk : k < finrank ℝ E) :
    ∃ W : Submodule ℝ E, finrank ℝ W = k + 1 ∧ ∀ v ∈ W, T.singularValues k * ‖v‖ ≤ ‖T v‖ := by
  obtain ⟨W, hW, hWv⟩ := exists_finrank_eq_mul_norm_sq_le T
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
    (T.isSymmetric_adjoint_comp_self.eigenvalues rfl)
    (T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl)
    (fun i => T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i) hk
  refine ⟨W, hW, fun v hv => le_of_sq_le_sq ?_ (norm_nonneg _)⟩
  rw [mul_pow, T.sq_singularValues_of_lt rfl hk]
  exact hWv v hv

/-- **Memory floor, singular-value form.** A map of rank at most `k` is at least `σ_{k+1}(A)` away
from `A` in the operator norm. -/
theorem singularValues_le_norm_sub_of_rank_le (A B : E →L[ℝ] F) {k : ℕ}
    (hB : finrank ℝ (LinearMap.range (B : E →ₗ[ℝ] F)) ≤ k) :
    (A : E →ₗ[ℝ] F).singularValues k ≤ ‖A - B‖ := by
  rcases le_or_gt (finrank ℝ E) k with hk | hk
  · rw [(A : E →ₗ[ℝ] F).singularValues_of_finrank_le hk]
    exact norm_nonneg _
  obtain ⟨W, hW, hWσ⟩ := exists_finrank_eq_singularValues_mul_le (A : E →ₗ[ℝ] F) hk
  obtain ⟨v, hv, hv1, hAv⟩ := memory_floor A B W (by omega)
  have h1 := hWσ v hv
  rw [hv1, mul_one] at h1
  exact h1.trans hAv

/-- The floor vanishes when the memory is at least the dimension of the source. -/
theorem singularValues_eq_zero_of_finrank_le (A : E →L[ℝ] F) {k : ℕ} (hk : finrank ℝ E ≤ k) :
    (A : E →ₗ[ℝ] F).singularValues k = 0 :=
  (A : E →ₗ[ℝ] F).singularValues_of_finrank_le hk

end CoSimFoundations
