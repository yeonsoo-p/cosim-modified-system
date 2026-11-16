/-
The visibility floor: what a subsystem cannot answer to within one macro step.

Setting, for one subsystem `i` of a linear non-iterative co-simulation with any memory, in Jacobi
or Gauss–Seidel mode, with any output maps:

* `E` the states, `Eᵢ` the states of subsystem `i`, `Pr : E → Eᵢ` the projection onto them;
* `U` the reference step and `P` the step of the scheme (on its invariant graph);
* a finite family of pieces of information `k` (a partner `j` and an age `r` of the sample):
  the scheme uses `M k = C_j ∘ P^{s - r}`, the reference would provide `N k = C_j ∘ U^{s - r}`;
* the rule of subsystem `i`: `Pr ∘ P = F ∘ Pr + Σ_k G k ∘ M k`, with a local map `F` and
  coefficients `G k`.

Then, for these `F`, `G`,

  `‖Pr ∘ U - F ∘ Pr - Σ_k G k ∘ N k‖ ≤ ‖Pr ∘ (P - U)‖ + Σ_k ‖G k‖ ‖M k - N k‖`.

The left side is at least the *visibility floor* `f`: the distance of the block row `Pr ∘ U` of the
reference from everything a rule of this form can build out of the reference's own information.
Hence `f ≤ ‖Pr ∘ (P - U)‖ + Σ_k ‖G k‖ ‖M k - N k‖`. Current samples (`M k = N k`) drop out. For one
held sample in Jacobi mode every piece is current and the floor is a floor under the one-step
error: this is the link floor, the floor from the kernel of an output map, and the floor of a
scheme without gains, in one statement. With memory, an error below the floor has to be paid with
large coefficients on old samples.
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul

namespace CoSimFoundations

variable {E Ei : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Ei] [NormedSpace ℝ Ei]
  {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ k, NormedAddCommGroup (Y k)]
  [∀ k, NormedSpace ℝ (Y k)]

/-- **The identity behind the visibility floor.** What the reference's block row lacks of the
rule's form is the block row of the error plus the rule's coefficients on the errors of the
information. -/
theorem visibility_identity (Pr : E →L[ℝ] Ei) (P U : E →L[ℝ] E) (F : Ei →L[ℝ] Ei)
    (G : ∀ k, Y k →L[ℝ] Ei) (M N : ∀ k, E →L[ℝ] Y k)
    (hstep : Pr.comp P = F.comp Pr + ∑ k, (G k).comp (M k)) :
    Pr.comp U - F.comp Pr - ∑ k, (G k).comp (N k) =
      -(Pr.comp (P - U)) + ∑ k, (G k).comp (M k - N k) := by
  have h1 : F.comp Pr = Pr.comp P - ∑ k, (G k).comp (M k) := by
    rw [hstep]; abel
  have h2 : ∑ k, (G k).comp (M k - N k) =
      ∑ k, (G k).comp (M k) - ∑ k, (G k).comp (N k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => ContinuousLinearMap.comp_sub _ _ _
  rw [h1, h2, ContinuousLinearMap.comp_sub]
  abel

/-- **Theorem M (visibility floor), for the rule at hand.** -/
theorem visibility_bound (Pr : E →L[ℝ] Ei) (P U : E →L[ℝ] E) (F : Ei →L[ℝ] Ei)
    (G : ∀ k, Y k →L[ℝ] Ei) (M N : ∀ k, E →L[ℝ] Y k)
    (hstep : Pr.comp P = F.comp Pr + ∑ k, (G k).comp (M k)) :
    ‖Pr.comp U - F.comp Pr - ∑ k, (G k).comp (N k)‖ ≤
      ‖Pr.comp (P - U)‖ + ∑ k, ‖G k‖ * ‖M k - N k‖ := by
  rw [visibility_identity Pr P U F G M N hstep]
  calc ‖-(Pr.comp (P - U)) + ∑ k, (G k).comp (M k - N k)‖
      ≤ ‖-(Pr.comp (P - U))‖ + ‖∑ k, (G k).comp (M k - N k)‖ := norm_add_le _ _
    _ ≤ ‖Pr.comp (P - U)‖ + ∑ k, ‖(G k).comp (M k - N k)‖ := by
        rw [norm_neg]
        exact add_le_add le_rfl (norm_sum_le _ _)
    _ ≤ ‖Pr.comp (P - U)‖ + ∑ k, ‖G k‖ * ‖M k - N k‖ :=
        add_le_add le_rfl (Finset.sum_le_sum fun k _ => ContinuousLinearMap.opNorm_comp_le _ _)

/-- **Theorem M (visibility floor).** If `f` is a lower bound for the distance of the reference's
block row from every rule of the class built on the reference's own information, then every scheme
of the class satisfies `f ≤ ‖Pr ∘ (P - U)‖ + Σ_k ‖G k‖ ‖M k - N k‖`. The set `S` describes the
class: the admissible pairs of a local map and coefficients. -/
theorem visibility_floor (Pr : E →L[ℝ] Ei) (P U : E →L[ℝ] E)
    (S : Set ((Ei →L[ℝ] Ei) × (∀ k, Y k →L[ℝ] Ei))) (N : ∀ k, E →L[ℝ] Y k) {f : ℝ}
    (hf : ∀ FG ∈ S, f ≤ ‖Pr.comp U - FG.1.comp Pr - ∑ k, (FG.2 k).comp (N k)‖)
    (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei) (hFG : (F, G) ∈ S) (M : ∀ k, E →L[ℝ] Y k)
    (hstep : Pr.comp P = F.comp Pr + ∑ k, (G k).comp (M k)) :
    f ≤ ‖Pr.comp (P - U)‖ + ∑ k, ‖G k‖ * ‖M k - N k‖ :=
  (hf (F, G) hFG).trans (visibility_bound Pr P U F G M N hstep)

/-- **One held sample, every sample current** (Jacobi mode): the visibility floor is a floor under
the block row of the one-step error, whatever the coefficients. -/
theorem visibility_floor_current (Pr : E →L[ℝ] Ei) (P U : E →L[ℝ] E)
    (S : Set ((Ei →L[ℝ] Ei) × (∀ k, Y k →L[ℝ] Ei))) (N : ∀ k, E →L[ℝ] Y k) {f : ℝ}
    (hf : ∀ FG ∈ S, f ≤ ‖Pr.comp U - FG.1.comp Pr - ∑ k, (FG.2 k).comp (N k)‖)
    (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei) (hFG : (F, G) ∈ S)
    (hstep : Pr.comp P = F.comp Pr + ∑ k, (G k).comp (N k)) :
    f ≤ ‖Pr.comp (P - U)‖ := by
  have h := visibility_floor Pr P U S N hf F G hFG N hstep
  simpa using h

/-- In terms of the defect `D` with `P = D ∘ U`: `‖Pr ∘ (P - U)‖ ≤ ‖Pr‖ ‖D - 1‖ ‖U‖`. -/
theorem norm_comp_step_sub_le (Pr : E →L[ℝ] Ei) (D U : E →L[ℝ] E) :
    ‖Pr.comp (D.comp U - U)‖ ≤ ‖Pr‖ * (‖D - 1‖ * ‖U‖) := by
  have h : D.comp U - U = (D - 1).comp U := by
    ext x; simp
  rw [h]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

end CoSimFoundations
