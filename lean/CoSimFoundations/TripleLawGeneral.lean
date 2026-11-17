/-
The triple law for any orthonormal pair (the paper, Theorem 5.2 `thm:triple`, as printed).

**Theorem.** Let `S` be a real symmetric `n × n` matrix and `e`, `f` orthonormal vectors. If `lam`
is a lower bound of the quadratic form of `S` (`lam · xᵀ x ≤ xᵀ S x` for all `x`; the largest such
number is `λ_min (S)`), then

  `tr S - n · lam ≥ 2 |eᵀ S f|`.

Without symmetry the same proof gives `tr S - n · lam ≥ |eᵀ S f + fᵀ S e|`.

Proof (the paper's). Test the form on `e + f` and on `e - f` (squared length `2`):
`eᵀ S e + fᵀ S f - 2 lam ≥ |eᵀ S f + fᵀ S e|`. Extend `{e, f}` to an orthonormal basis `u`
(`Orthonormal.exists_orthonormalBasis_extension`); the trace is the sum of `xᵀ S x` over `x ∈ u`
(`LinearMap.trace_eq_sum_inner`), every term is at least `lam`, and `u` has `n` elements. The
proof is carried out for a linear map on a finite-dimensional real inner product space and then
read on Euclidean space for a matrix.

`TripleLaw.lean` has the case of two coordinate vectors, in the sign convention of the difference
`Δ` (an upper bound `lam` of the form of `Δ`): `|Δ i j + Δ j i| ≤ n lam - tr Δ`. Here
`triple_law_general` is that statement for any orthonormal pair.

**The paper's sign convention.** `Δ_R = -sym Δ` (numerical dissipation), `ν = tr Δ_R` (numerical
damping), `ι = -λ_min (Δ_R)` (injection rate). In the statements `ι` is any number with
`-ι · xᵀ x ≤ xᵀ Δ_R x` for all `x`, of which `-λ_min (Δ_R)` is the least. Then

* `ν + n ι ≥ 2 |eᵀ Δ_R f|`                         (26);
* `ι ≤ 0  ⟹  ν ≥ 2 |eᵀ Δ_R f|`                     (never injecting costs damping);
* `ν ≤ 0  ⟹  ι ≥ (2/n) |eᵀ Δ_R f|`                 (adding no damping costs injection).

The signs of the printed theorem are correct.
-/
import Mathlib.Analysis.InnerProductSpace.Trace
import CoSimFoundations.Setting
import CoSimFoundations.FloorMatrix
import CoSimFoundations.TripleLaw

open Module Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

section Pair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit vector differs from every vector orthogonal to it. -/
theorem ne_of_norm_eq_one_of_inner_eq_zero {e f : E} (he : ‖e‖ = 1) (hef : ⟪e, f⟫ = 0) :
    e ≠ f := by
  intro h
  rw [← h, real_inner_self_eq_norm_sq, he] at hef
  norm_num at hef

/-- **The local form for a linear map and an orthonormal pair.** If `-ι ‖x‖² ≤ ⟪x, T x⟫` for all
`x`, then `|⟪e, T f⟫ + ⟪f, T e⟫| ≤ ⟪e, T e⟫ + ⟪f, T f⟫ + 2 ι` for orthonormal `e`, `f`. Only the
lower bound is used, on `e + f` and on `e - f`. -/
theorem abs_inner_add_inner_le_local (T : E →ₗ[ℝ] E) {ι : ℝ}
    (hlo : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) :
    |⟪e, T f⟫ + ⟪f, T e⟫| ≤ ⟪e, T e⟫ + ⟪f, T f⟫ + 2 * ι := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal he hf hef
  have lp := hlo (e + f)
  have lm := hlo (e - f)
  rw [hp, map_add, inner_add_left, inner_add_right, inner_add_right] at lp
  rw [hm, map_sub, inner_sub_left, inner_sub_right, inner_sub_right] at lm
  rw [abs_le]
  constructor <;> linarith

/-- For a self-adjoint linear map the bilinear form is symmetric: `⟪f, T e⟫ = ⟪e, T f⟫`. -/
theorem inner_apply_comm_of_isSymmetric {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (e f : E) :
    ⟪f, T e⟫ = ⟪e, T f⟫ := by
  rw [← hT f e]
  exact real_inner_comm e (T f)

end Pair

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Two orthonormal vectors, as an orthonormal set. -/
theorem orthonormal_pair {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    Orthonormal ℝ ((↑) : ({e, f} : Set E) → E) := by
  classical
  have hne : e ≠ f := ne_of_norm_eq_one_of_inner_eq_zero he hef
  rw [orthonormal_subtype_iff_ite]
  intro v hv w hw
  have hv' : v = e ∨ v = f := hv
  have hw' : w = e ∨ w = f := hw
  rcases hv' with hv' | hv' <;> rcases hw' with hw' | hw' <;> rw [hv', hw']
  · rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, he, one_pow]
  · rw [ite_eq_right hne, hef]
  · rw [ite_eq_right hne.symm, real_inner_comm, hef]
  · rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, hf, one_pow]

/-- **The trace against the form on an orthonormal set.** If `lam ‖x‖² ≤ ⟪x, T x⟫` for all `x` and
the vectors of a finite set `v` are orthonormal, then `Σ_{x ∈ v} (⟪x, T x⟫ - lam) ≤ tr T - n lam`,
`n` the dimension: the set extends to an orthonormal basis, over which the sum is `tr T - n lam`,
and every term is nonnegative. -/
theorem sum_inner_sub_le_trace_sub (T : E →ₗ[ℝ] E) {lam : ℝ}
    (hlam : ∀ x : E, lam * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) {v : Finset E}
    (hv : Orthonormal ℝ ((↑) : ((v : Set E)) → E)) :
    ∑ x ∈ v, (⟪x, T x⟫ - lam) ≤ LinearMap.trace ℝ E T - (finrank ℝ E : ℝ) * lam := by
  classical
  -- an orthonormal basis that contains `v`
  obtain ⟨u, b, hsub, hb⟩ := hv.exists_orthonormalBasis_extension
  have hbi : ∀ i : u, b i = (i : E) := fun i => congrFun hb i
  have htr : LinearMap.trace ℝ E T = ∑ x ∈ u, ⟪x, T x⟫ := by
    rw [LinearMap.trace_eq_sum_inner T b, ← Finset.sum_coe_sort u (fun x => ⟪x, T x⟫)]
    exact Finset.sum_congr rfl fun i _ => by rw [hbi i]
  have hcard : finrank ℝ E = u.card := by
    rw [finrank_eq_card_basis b.toBasis, Fintype.card_coe]
  have hunit : ∀ x ∈ u, ‖x‖ = 1 := fun x hx => by
    have h := b.orthonormal.1 ⟨x, hx⟩
    rwa [hbi] at h
  have hterm : ∀ x ∈ u, 0 ≤ ⟪x, T x⟫ - lam := fun x hx => by
    have h := hlam x
    rw [hunit x hx] at h
    linarith
  have hsum : ∑ x ∈ u, (⟪x, T x⟫ - lam) = LinearMap.trace ℝ E T - (finrank ℝ E : ℝ) * lam := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, htr, hcard]
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.coe_subset.1 hsub)
    (fun x hx _ => hterm x hx)

/-- **The triple law for a linear map and any orthonormal pair.** If `lam ‖x‖² ≤ ⟪x, T x⟫` for all
`x`, then `|⟪e, T f⟫ + ⟪f, T e⟫| ≤ tr T - n lam` for orthonormal `e`, `f`. -/
theorem abs_inner_add_inner_le_trace_sub (T : E →ₗ[ℝ] E) {lam : ℝ}
    (hlam : ∀ x : E, lam * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) :
    |⟪e, T f⟫ + ⟪f, T e⟫| ≤ LinearMap.trace ℝ E T - (finrank ℝ E : ℝ) * lam := by
  classical
  have hon : Orthonormal ℝ ((↑) : ((({e, f} : Finset E) : Set E)) → E) := by
    rw [Finset.coe_pair]
    exact orthonormal_pair he hf hef
  have hpair := sum_inner_sub_le_trace_sub T hlam hon
  rw [Finset.sum_pair (ne_of_norm_eq_one_of_inner_eq_zero he hef)] at hpair
  -- the form on `e + f` and on `e - f`
  have hloc := abs_inner_add_inner_le_local T (ι := -lam)
    (fun x => by rw [neg_neg]; exact hlam x) he hf hef
  linarith

end Operator

variable {n : ℕ}

/-- The bilinear form of a matrix as an inner product on Euclidean space. -/
theorem inner_opE_eq_dotProduct (S : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE S y⟫ = WithLp.ofLp x ⬝ᵥ (S *ᵥ WithLp.ofLp y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, star_trivial,
    dotProduct_comm]

/-- The inner product of Euclidean space is the dot product. -/
theorem inner_eq_dotProduct (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, y⟫ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- A vector of dot-product square `1` is a unit vector of Euclidean space. -/
theorem norm_toLp_eq_one_of_dotProduct_self {v : Fin n → ℝ} (hv : v ⬝ᵥ v = 1) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have h : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    exact hv
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h, one_pow])

namespace OneStep

/-- `⟪y, T x⟫ = ⟪x, Tᵀ y⟫`. -/
theorem inner_opE_transpose (T : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, opE T x⟫ = ⟪x, opE Tᵀ y⟫ := by
  rw [inner_opE_eq_dotProduct, inner_opE_eq_dotProduct, dot_mulVec_swap]

end OneStep

/-- The operator of a symmetric matrix is self-adjoint. -/
theorem isSymmetric_opE {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm) :
    ((opE T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := fun x y => by
  rw [ContinuousLinearMap.coe_coe, real_inner_comm, OneStep.inner_opE_transpose T x y, hT.eq]

/-- For a symmetric matrix the bilinear form on Euclidean space is symmetric:
`⟪y, T x⟫ = ⟪x, T y⟫`. -/
theorem inner_opE_comm_of_isSymm {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm)
    (x y : EuclideanSpace ℝ (Fin n)) : ⟪y, opE T x⟫ = ⟪x, opE T y⟫ :=
  inner_apply_comm_of_isSymmetric (isSymmetric_opE hT) x y

/-- A lower bound of the quadratic form of a matrix on dot products is a lower bound of the form
of its operator on Euclidean space: if `lam · xᵀ x ≤ xᵀ S x` for all `x`, then
`lam ‖x‖² ≤ ⟪x, S x⟫` for all `x`. -/
theorem le_inner_opE_of_le_dotProduct (S : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) (x : EuclideanSpace ℝ (Fin n)) :
    lam * ‖x‖ ^ 2 ≤
      ⟪x, ((opE S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) x⟫ := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct, ContinuousLinearMap.coe_coe,
    inner_opE_eq_dotProduct]
  exact hlam _

/-- An upper bound of the quadratic form of a matrix on dot products is an upper bound of the form
of its operator on Euclidean space: if `xᵀ S x ≤ μ · xᵀ x` for all `x`, then
`⟪x, S x⟫ ≤ μ ‖x‖²` for all `x`. -/
theorem inner_opE_le_of_dotProduct_le (S : Matrix (Fin n) (Fin n) ℝ) {μ : ℝ}
    (hμ : ∀ x : Fin n → ℝ, x ⬝ᵥ (S *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, ((opE S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) x⟫ ≤ μ * ‖x‖ ^ 2 := by
  rw [ContinuousLinearMap.coe_coe, inner_opE_eq_dotProduct, ← real_inner_self_eq_norm_sq,
    inner_eq_dotProduct]
  exact hμ _

/-- The trace of the operator of a matrix is the trace of the matrix. -/
theorem trace_opE (S : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      ((opE S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = S.trace := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply]
  exact inner_unitE_opE S i i

/-- **The triple law for any matrix and any orthonormal pair**, with a lower bound `lam` of the
quadratic form: `|eᵀ S f + fᵀ S e| ≤ tr S - n lam`. -/
theorem triple_law_lower (S : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    |e ⬝ᵥ (S *ᵥ f) + f ⬝ᵥ (S *ᵥ e)| ≤ S.trace - n * lam := by
  have h := abs_inner_add_inner_le_trace_sub _ (le_inner_opE_of_le_dotProduct S hlam)
    (norm_toLp_eq_one_of_dotProduct_self he) (norm_toLp_eq_one_of_dotProduct_self hf)
    ((inner_eq_dotProduct _ _).trans hef)
  rw [trace_opE, finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe,
    inner_opE_eq_dotProduct, inner_opE_eq_dotProduct] at h
  exact h

/-- For a symmetric matrix the bilinear form is symmetric. -/
theorem dotProduct_mulVec_comm_of_isSymm {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsSymm)
    (e f : Fin n → ℝ) : f ⬝ᵥ (S *ᵥ e) = e ⬝ᵥ (S *ᵥ f) := by
  have h := inner_opE_comm_of_isSymm hS (WithLp.toLp 2 e) (WithLp.toLp 2 f)
  rwa [inner_opE_eq_dotProduct, inner_opE_eq_dotProduct] at h

/-- **Theorem 5.2, inequality (25).** For a real symmetric matrix `S`, a lower bound `lam` of its
quadratic form (as `λ_min (S)`) and orthonormal vectors `e`, `f`:
`2 |eᵀ S f| ≤ tr S - n lam`. -/
theorem triple_law_symm (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 * |e ⬝ᵥ (S *ᵥ f)| ≤ S.trace - n * lam := by
  have h := triple_law_lower S hlam he hf hef
  rw [dotProduct_mulVec_comm_of_isSymm hS e f, ← two_mul, abs_mul, abs_two] at h
  exact h

/-- **The triple law of `TripleLaw.lean` for any orthonormal pair**, in the sign convention of
the difference `Δ`: if `xᵀ Δ x ≤ lam · xᵀ x` for all `x`, then
`|eᵀ Δ f + fᵀ Δ e| ≤ n lam - tr Δ`. For two coordinate vectors this is `triple_law`. -/
theorem triple_law_general (Δ : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    |e ⬝ᵥ (Δ *ᵥ f) + f ⬝ᵥ (Δ *ᵥ e)| ≤ n * lam - Δ.trace := by
  have hneg : ∀ x : Fin n → ℝ, -lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((-Δ) *ᵥ x) := by
    intro x
    have h := hlam x
    rw [neg_mulVec, dotProduct_neg]
    linarith
  have h := triple_law_lower (-Δ) hneg he hf hef
  rw [neg_mulVec, neg_mulVec, dotProduct_neg, dotProduct_neg, ← neg_add, abs_neg,
    trace_neg] at h
  linarith

section PaperConvention

/-- The numerical dissipation `Δ_R = -sym Δ` is symmetric. -/
theorem isSymm_neg_sym (Δ : Matrix (Fin n) (Fin n) ℝ) : (-sym Δ).IsSymm := by
  unfold Matrix.IsSymm sym
  rw [transpose_neg, transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- The numerical damping: `ν = tr Δ_R = -tr Δ`. -/
theorem trace_neg_sym (Δ : Matrix (Fin n) (Fin n) ℝ) : (-sym Δ).trace = -Δ.trace := by
  unfold sym
  rw [trace_neg, trace_smul, trace_add, trace_transpose, smul_eq_mul]
  ring

/-- **Theorem `thm:triple` for the operator of a symmetric matrix** (eq. `eq:triplenu`). If `T` is
symmetric and `-ι ‖v‖² ≤ ⟪v, T v⟫` for all `v` (as `ι = -λ_min (T)`), then for orthonormal `e`,
`f`: `2 |⟪e, T f⟫| ≤ tr T + n ι`. -/
theorem two_mul_abs_inner_opE_le_trace_add {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm)
    {ι : ℝ} (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE T v⟫)
    {e f : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    2 * |⟪e, opE T f⟫| ≤ T.trace + (n : ℝ) * ι := by
  have h := abs_inner_add_inner_le_trace_sub
    ((opE T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (lam := -ι) hlo he hf hef
  rw [trace_opE, finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe,
    inner_opE_comm_of_isSymm hT e f, ← two_mul, abs_mul, abs_two] at h
  linarith

/-- **Theorem 5.2, inequality (26):** `ν + n ι ≥ 2 |eᵀ Δ_R f|`, for a symmetric matrix `S = Δ_R`,
`ν = tr S`, and `ι` with `-ι · xᵀ x ≤ xᵀ S x` for all `x` (as `ι = -λ_min (S)`). -/
theorem damping_add_injection_ge (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 * |e ⬝ᵥ (S *ᵥ f)| ≤ S.trace + n * ι := by
  have h := two_mul_abs_inner_opE_le_trace_add hS (le_inner_opE_of_le_dotProduct S hι)
    (norm_toLp_eq_one_of_dotProduct_self he) (norm_toLp_eq_one_of_dotProduct_self hf)
    ((inner_eq_dotProduct _ _).trans hef)
  rwa [inner_opE_eq_dotProduct] at h

/-- **Theorem 5.2, first consequence:** a co-simulation that never injects energy, `ι ≤ 0`, has a
numerical damping `ν ≥ 2 |eᵀ Δ_R f|`. -/
theorem damping_ge_of_injection_nonpos (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) (hι0 : ι ≤ 0) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 * |e ⬝ᵥ (S *ᵥ f)| ≤ S.trace := by
  have h := damping_add_injection_ge S hS hι he hf hef
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- **Theorem 5.2, second consequence:** a co-simulation that adds no damping, `ν ≤ 0`, injects
energy at the rate `ι ≥ (2/n) |eᵀ Δ_R f|`. -/
theorem injection_ge_of_damping_nonpos (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) (hν : S.trace ≤ 0) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 / n * |e ⬝ᵥ (S *ᵥ f)| ≤ ι := by
  have h := damping_add_injection_ge S hS hι he hf hef
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at he
    · exact_mod_cast hn
  rw [div_mul_eq_mul_div, div_le_iff₀ hn]
  linarith

/-- **Theorem 5.2 for the difference `Δ` of a co-simulation,** with `Δ_R = -sym Δ`, `ν = -tr Δ`
and `ι` with `xᵀ Δ x ≤ ι · xᵀ x` for all `x` (which is `-ι · xᵀ x ≤ xᵀ Δ_R x`):
`ν + n ι ≥ 2 |eᵀ Δ_R f|`. -/
theorem damping_add_injection_ge_of_difference (Δ : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ ι * (x ⬝ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 * |e ⬝ᵥ ((-sym Δ) *ᵥ f)| ≤ -Δ.trace + n * ι := by
  have hι' : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((-sym Δ) *ᵥ x) := by
    intro x
    have h := hι x
    rw [neg_mulVec, dotProduct_neg, dotProduct_mulVec_sym]
    linarith
  have h := damping_add_injection_ge (-sym Δ) (isSymm_neg_sym Δ) hι' he hf hef
  rwa [trace_neg_sym] at h

end PaperConvention

end CoSimFoundations
