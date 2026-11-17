/-
The universal region: the accuracy cannot beat the distance from `1` of the largest stretch, nor
that of the geometric mean of the other stretches (the paper, Thm 5.3, necessity).

For `T` on a finite-dimensional real inner product space of dimension `n ≥ 1`, with singular values
`σ₀ ≥ σ₁ ≥ …` (Mathlib's `LinearMap.singularValues`), largest stretch `‖T‖`, a lower bound `m` on
all stretches and `α = ‖T - 1‖`:

* every singular value lies between `m` and `‖T‖`, and `σ₀ = ‖T‖`;
* `‖T‖ · m ^ (n-1) ≤ |det T| ≤ ‖T‖ ^ n`;
* hence, with `t ^ (n-1) = |det T| / ‖T‖`: `(1 - α) ^ (n-1) ≤ t ^ (n-1) ≤ (1 + α) ^ (n-1)`.

Together with `Chain` (`1 - α ≤ ‖T‖ ≤ 1 + α`) this is `max{|s - 1|, |t - 1|} ≤ α`.
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import CoSimFoundations.Chain

open Module
open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An eigenvalue of `T† T` is the squared stretch of a unit vector. -/
theorem exists_unit_norm_sq_eq_of_hasEigenvalue (T : E →L[ℝ] E) {μ : ℝ}
    (h : End.HasEigenvalue (LinearMap.adjoint (T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E)) μ) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖T v‖ ^ 2 = μ := by
  obtain ⟨w, hw⟩ := h.exists_hasEigenvector
  have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw.2
  have hw1 : LinearMap.adjoint (T : E →ₗ[ℝ] E) (T w) = μ • w := hw.apply_eq_smul
  have key : ‖T w‖ ^ 2 = μ * ‖w‖ ^ 2 := by
    have h1 : ⟪w, LinearMap.adjoint (T : E →ₗ[ℝ] E) (T w)⟫ = ⟪T w, T w⟫ := by
      rw [LinearMap.adjoint_inner_right]; rfl
    rw [hw1, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
    linarith
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0]
  · rw [map_smul, norm_smul, norm_inv, norm_norm, mul_pow, key]
    field_simp

/-- Every singular value is the stretch of a unit vector. -/
theorem exists_unit_norm_apply_eq_singularValues (T : E →L[ℝ] E) {i : ℕ}
    (hi : i < finrank ℝ E) : ∃ v : E, ‖v‖ = 1 ∧ ‖T v‖ = (T : E →ₗ[ℝ] E).singularValues i := by
  obtain ⟨v, hv, hTv⟩ := exists_unit_norm_sq_eq_of_hasEigenvalue T
    ((T : E →ₗ[ℝ] E).hasEigenvalue_adjoint_comp_self_sq_singularValues hi)
  exact ⟨v, hv,
    (sq_eq_sq₀ (norm_nonneg _) ((T : E →ₗ[ℝ] E).singularValues_nonneg i)).1 hTv⟩

/-- Every singular value is at most the largest stretch. -/
theorem singularValues_le_opNorm (T : E →L[ℝ] E) {i : ℕ} (hi : i < finrank ℝ E) :
    (T : E →ₗ[ℝ] E).singularValues i ≤ ‖T‖ := by
  obtain ⟨v, hv, h3⟩ := exists_unit_norm_apply_eq_singularValues T hi
  have h1 : ‖T v‖ ≤ ‖T‖ := by simpa [hv] using T.le_opNorm v
  exact h3.ge.trans h1

/-- Every singular value is at least any lower bound on the stretches. -/
theorem le_singularValues (T : E →L[ℝ] E) {m : ℝ} (h : ∀ y, m * ‖y‖ ≤ ‖T y‖)
    {i : ℕ} (hi : i < finrank ℝ E) : m ≤ (T : E →ₗ[ℝ] E).singularValues i := by
  obtain ⟨v, hv, h3⟩ := exists_unit_norm_apply_eq_singularValues T hi
  have h1 : m ≤ ‖T v‖ := by simpa [hv] using h v
  exact h1.trans h3.le

/-- **The largest singular value is the operator norm.** -/
theorem singularValues_zero_eq_opNorm [Nontrivial E] (T : E →L[ℝ] E) :
    (T : E →ₗ[ℝ] E).singularValues 0 = ‖T‖ := by
  have hpos : 0 < finrank ℝ E := finrank_pos
  refine le_antisymm (singularValues_le_opNorm T hpos) ?_
  set S : E →ₗ[ℝ] E := LinearMap.adjoint (T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E) with hS
  have hsym : S.IsSymmetric := (T : E →ₗ[ℝ] E).isSymmetric_adjoint_comp_self
  have hval : ∀ x : E, ⟪S x, x⟫ = ‖T x‖ ^ 2 := by
    intro x
    have : ⟪LinearMap.adjoint (T : E →ₗ[ℝ] E) (T x), x⟫ = ⟪T x, T x⟫ := by
      rw [LinearMap.adjoint_inner_left]; rfl
    rw [← real_inner_self_eq_norm_sq, ← this]; rfl
  -- the supremum of the Rayleigh quotient is an eigenvalue, and it is `‖T‖²`
  have hbdd : BddAbove (Set.range fun x : { x : E // x ≠ 0 } =>
      RCLike.re ⟪S x, x⟫ / ‖(x : E)‖ ^ 2) := by
    refine ⟨‖T‖ ^ 2, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx : 0 < ‖(x : E)‖ ^ 2 := by have := norm_pos_iff.2 x.2; positivity
    have h1 : ‖T x‖ ≤ ‖T‖ * ‖(x : E)‖ := T.le_opNorm x
    simp only [RCLike.re_to_real, hval]
    rw [div_le_iff₀ hx]
    nlinarith [norm_nonneg (T x), norm_nonneg T, norm_nonneg (x : E)]
  obtain ⟨x0, hx0, hTx0⟩ := exists_norm_apply_eq_opNorm T
  have hx0ne : x0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hx0; exact zero_ne_one hx0
  have hle : ‖T‖ ^ 2 ≤ ⨆ x : { x : E // x ≠ 0 }, RCLike.re ⟪S x, x⟫ / ‖(x : E)‖ ^ 2 := by
    refine le_ciSup_of_le hbdd ⟨x0, hx0ne⟩ ?_
    simp [hval, hx0, hTx0]
  obtain ⟨i, hi⟩ := hsym.exists_eigenvalues_eq rfl hsym.hasEigenvalue_iSup_of_finiteDimensional
  have hσ : (T : E →ₗ[ℝ] E).singularValues i ^ 2 =
      ⨆ x : { x : E // x ≠ 0 }, RCLike.re ⟪S x, x⟫ / ‖(x : E)‖ ^ 2 := by
    rw [(T : E →ₗ[ℝ] E).sq_singularValues_fin rfl i]
    exact_mod_cast hi
  have h0 : (T : E →ₗ[ℝ] E).singularValues i ≤ (T : E →ₗ[ℝ] E).singularValues 0 :=
    (T : E →ₗ[ℝ] E).singularValues_antitone (Nat.zero_le _)
  have h1 := (T : E →ₗ[ℝ] E).singularValues_nonneg i
  nlinarith [norm_nonneg T]

/-- **The determinant against the largest and the least stretch:**
`‖T‖ · m ^ (n - 1) ≤ |det T|`. -/
theorem opNorm_mul_pow_le_abs_det [Nontrivial E] (T : E →L[ℝ] E) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ y, m * ‖y‖ ≤ ‖T y‖) :
    ‖T‖ * m ^ (finrank ℝ E - 1) ≤ |LinearMap.det (T : E →ₗ[ℝ] E)| := by
  obtain ⟨k, hk⟩ : ∃ k, finrank ℝ E = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := E)).ne'
  rw [← LinearMap.normDet_eq_abs_det, LinearMap.normDet_eq_prod_singularValues, hk,
    Finset.prod_range_succ', singularValues_zero_eq_opNorm, Nat.add_sub_cancel, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg T)
  calc m ^ k = ∏ _i ∈ Finset.range k, m := by simp
    _ ≤ ∏ i ∈ Finset.range k, (T : E →ₗ[ℝ] E).singularValues (i + 1) := by
        refine Finset.prod_le_prod₀ (fun _ _ => hm) fun i hi => ?_
        refine le_singularValues T h ?_
        have := Finset.mem_range.1 hi
        omega

/-- **Region, lower side:** `‖T‖ · (1 - α) ^ (n - 1) ≤ |det T|` when `α = ‖T - 1‖ ≤ 1`. -/
theorem opNorm_mul_one_sub_pow_le_abs_det [Nontrivial E] (T : E →L[ℝ] E) (hα : ‖T - 1‖ ≤ 1) :
    ‖T‖ * (1 - ‖T - 1‖) ^ (finrank ℝ E - 1) ≤ |LinearMap.det (T : E →ₗ[ℝ] E)| :=
  opNorm_mul_pow_le_abs_det T (sub_nonneg.2 hα) (one_sub_mul_norm_le T)

/-- **Region, upper side:** `|det T| ≤ ‖T‖ · (1 + α) ^ (n - 1)`. -/
theorem abs_det_le_opNorm_mul_one_add_pow [Nontrivial E] (T : E →L[ℝ] E) :
    |LinearMap.det (T : E →ₗ[ℝ] E)| ≤ ‖T‖ * (1 + ‖T - 1‖) ^ (finrank ℝ E - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, finrank ℝ E = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := E)).ne'
  have h1 := abs_det_le_opNorm_pow T
  rw [hk, pow_succ, mul_comm] at h1
  rw [hk, Nat.add_sub_cancel]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg T))
  exact pow_le_pow_left₀ (norm_nonneg T) (opNorm_le_one_add T) k

end CoSimFoundations
