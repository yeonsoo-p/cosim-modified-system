/-
The forced choice of the Jacobi class with one held sample, end to end.

For a network of scalar stores (`ScalarStores.lean`), every Jacobi scheme with one held sample,
weights on the coupling graph and any local gains, at any macro step `H > 0`, with step matrix
`D * U`, and two stores `i ≠ j` that are not partners of each other:

* **accuracy against energy gain:**
  `|U i j + U j i| ≤ (‖D‖ - 1) + ‖D - 1‖ (1 + η)`,
  `η = ‖U e_i - e_i‖ + ‖U e_j - e_j‖`;
* **never injecting costs damping:** if `‖D‖ ≤ 1` then
  `(det D)² ≤ 1 + ‖D - 1‖² - 2 (|U i j + U j i| - ‖D - 1‖ η)`.

These are `link_tradeoff` (`TradeOff.lean`) and `det_sq_le_of_no_gain` (`NoInjection.lean`) for the
class, in the same way as `ScalarNet.floors` (`FloorMatrix.lean`) is `link_floor` for the class.

The file also proves the **shear law**, for every operator: if `‖D‖ ≤ 1` and
`e₁`, `e₂` are orthonormal, then `(det D)² ≤ 1 - 2 |⟪D e₁, D e₂⟫|`; for matrices,
`(det D)² ≤ 1 - 2 |(Dᵀ D) i j|` and `(det D)² ≤ 1 - 2 |(D Dᵀ) i j|` for `i ≠ j`. Proof:
polarisation on `e₁ ± e₂` and `|det D| ≤ ‖D v‖` (no Fischer inequality needed).
-/
import CoSimFoundations.NoInjection
import CoSimFoundations.FloorMatrix

open scoped Matrix RealInnerProductSpace

namespace CoSimFoundations

section Shear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Shear law.** A scheme that never injects (`‖D‖ ≤ 1`) and shears two orthonormal directions
against each other, `g = ⟪D e₁, D e₂⟫ ≠ 0`, damps: `(det D)² ≤ 1 - 2 |g|`.

Proof: `‖D (e₁ + e₂)‖² - ‖D (e₁ - e₂)‖² = 4 g` and both are at most `‖e₁ ± e₂‖² = 2`, so one of
them is at most `2 - 4 |g|`; then `|det D| ≤ ‖D v‖` for the unit vector `v` along it. -/
theorem det_sq_le_one_sub_two_abs_inner [Nontrivial E] (D : E →L[ℝ] E) (hD : ‖D‖ ≤ 1)
    {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) :
    LinearMap.det (D : E →ₗ[ℝ] E) ^ 2 ≤ 1 - 2 * |⟪D e₁, D e₂⟫| := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have hle : ∀ x : E, ‖D x‖ ^ 2 ≤ ‖x‖ ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _)
      ((D.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) hD)) 2
  have np : ‖D (e₁ + e₂)‖ ^ 2 = ‖D e₁‖ ^ 2 + 2 * ⟪D e₁, D e₂⟫ + ‖D e₂‖ ^ 2 := by
    rw [map_add, norm_add_sq_real]
  have nm : ‖D (e₁ - e₂)‖ ^ 2 = ‖D e₁‖ ^ 2 - 2 * ⟪D e₁, D e₂⟫ + ‖D e₂‖ ^ 2 := by
    rw [map_sub, norm_sub_sq_real]
  have bp := hle (e₁ + e₂)
  have bm := hle (e₁ - e₂)
  rw [hp] at bp
  rw [hm] at bm
  -- one of `e₁ ± e₂` loses energy
  obtain ⟨w, hw, hDw⟩ : ∃ w : E, ‖w‖ ^ 2 = 2 ∧ ‖D w‖ ^ 2 ≤ 2 * (1 - 2 * |⟪D e₁, D e₂⟫|) := by
    rcases abs_cases ⟪D e₁, D e₂⟫ with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ⟨e₁ - e₂, hm, by rw [ha]; linarith⟩
    · exact ⟨e₁ + e₂, hp, by rw [ha]; linarith⟩
  have hw0 : ‖w‖ ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hv : ‖‖w‖⁻¹ • w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0]
  have hDv : ‖D (‖w‖⁻¹ • w)‖ ^ 2 ≤ 1 - 2 * |⟪D e₁, D e₂⟫| := by
    rw [map_smul, norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, hw,
      inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact hDw
  have h := abs_det_le_norm_apply_of_opNorm_le_one D hD hv
  calc LinearMap.det (D : E →ₗ[ℝ] E) ^ 2 = |LinearMap.det (D : E →ₗ[ℝ] E)| ^ 2 :=
        (sq_abs _).symm
    _ ≤ ‖D (‖w‖⁻¹ • w)‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ ≤ _ := hDv

end Shear

variable {n : ℕ}

/-- Two distinct unit vectors of Euclidean space are orthogonal. -/
theorem inner_unitE_of_ne {i j : Fin n} (hij : i ≠ j) : ⟪unitE i, unitE j⟫ = 0 :=
  EuclideanSpace.orthonormal_single.2 hij

/-- The determinant of the operator of a matrix is the determinant of the matrix. -/
theorem det_opE (M : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det ((opE M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = M.det := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- The inner product of two columns of a matrix is an entry of its Gram matrix `Mᵀ M`. -/
theorem inner_opE_unitE (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪opE M (unitE i), opE M (unitE j)⟫ = (Mᵀ * M) i j := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) M, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← opE_mul_apply, inner_unitE_opE]

/-- **Shear law, matrix form.** If `‖D‖ ≤ 1`, then `(det D)² ≤ 1 - 2 |(Dᵀ D) i j|` for any two
distinct stores `i ≠ j`: a defect that never injects and makes two columns non-orthogonal damps. -/
theorem det_sq_le_one_sub_two_abs_gram (D : Matrix (Fin n) (Fin n) ℝ) (hD : ‖opE D‖ ≤ 1)
    {i j : Fin n} (hij : i ≠ j) :
    D.det ^ 2 ≤ 1 - 2 * |(Dᵀ * D) i j| := by
  have hne : unitE i ≠ 0 := by
    intro h0
    have h1 := norm_unitE i
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := nontrivial_of_ne _ _ hne
  have h := det_sq_le_one_sub_two_abs_inner (opE D) hD (norm_unitE i) (norm_unitE j)
    (inner_unitE_of_ne hij)
  rwa [det_opE, inner_opE_unitE] at h

/-- **Shear law, rows.** If `‖D‖ ≤ 1`, then
`(det D)² ≤ 1 - 2 |(D Dᵀ) i j|` for any two distinct stores `i ≠ j`. -/
theorem det_sq_le_one_sub_two_abs_gram_rows (D : Matrix (Fin n) (Fin n) ℝ) (hD : ‖opE D‖ ≤ 1)
    {i j : Fin n} (hij : i ≠ j) :
    D.det ^ 2 ≤ 1 - 2 * |(D * Dᵀ) i j| := by
  have hstar : opE Dᵀ = star (opE D) := by
    rw [← map_star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) D, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hT : ‖opE Dᵀ‖ ≤ 1 := by
    rw [hstar, ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact hD
  have h := det_sq_le_one_sub_two_abs_gram Dᵀ hT hij
  rwa [Matrix.det_transpose, Matrix.transpose_transpose] at h

namespace ScalarNet

variable (N : ScalarNet n)

/-- A Jacobi scheme with one held sample moves nothing from store `j` to a store `i` that is not
its partner: with step matrix `D * U`, `⟪e_i, D (U e_j)⟫ = 0`. -/
theorem inner_unitE_opE_opE_eq_zero {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ)
    (w : Matrix (Fin n) (Fin n) ℝ) (hw : ∀ i j, ¬ N.partner i j → w i j = 0)
    (D U : Matrix (Fin n) (Fin n) ℝ) (hX : N.jacobiStep H k w = D * U) {i j : Fin n}
    (hij : i ≠ j) (hp : ¬ N.partner i j) :
    ⟪unitE i, opE D (opE U (unitE j))⟫ = 0 := by
  have hmem : N.jacobiStep H k w ∈ N.classX := by
    rw [← N.range_jacobiStep hH]; exact ⟨k, w, hw, rfl⟩
  rw [← opE_mul_apply, inner_unitE_opE, ← hX]
  exact hmem.2 i j hij hp

/-- **Accuracy against energy gain, for the class.** -/
theorem tradeoff {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ i j, ¬ N.partner i j → w i j = 0) (D U : Matrix (Fin n) (Fin n) ℝ)
    (hX : N.jacobiStep H k w = D * U) {i j : Fin n} (hij : i ≠ j)
    (hp : ¬ N.partner i j) (hp' : ¬ N.partner j i) :
    |U i j + U j i| ≤ (‖opE D‖ - 1) + ‖opE D - 1‖ *
      (1 + (‖opE U (unitE i) - unitE i‖ + ‖opE U (unitE j) - unitE j‖)) := by
  have h := link_tradeoff (opE D) (opE U) (norm_unitE i) (norm_unitE j) (inner_unitE_of_ne hij)
    (N.inner_unitE_opE_opE_eq_zero hH k w hw D U hX hij hp)
    (N.inner_unitE_opE_opE_eq_zero hH k w hw D U hX hij.symm hp')
  rwa [inner_unitE_opE, inner_unitE_opE] at h

/-- **Never injecting costs damping, for the class.** -/
theorem no_injection_costs_damping {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ)
    (w : Matrix (Fin n) (Fin n) ℝ) (hw : ∀ i j, ¬ N.partner i j → w i j = 0)
    (D U : Matrix (Fin n) (Fin n) ℝ) (hX : N.jacobiStep H k w = D * U) {i j : Fin n}
    (hij : i ≠ j) (hp : ¬ N.partner i j) (hp' : ¬ N.partner j i) (hD : ‖opE D‖ ≤ 1) :
    D.det ^ 2 ≤ 1 + ‖opE D - 1‖ ^ 2 - 2 * (|U i j + U j i| -
      ‖opE D - 1‖ * (‖opE U (unitE i) - unitE i‖ + ‖opE U (unitE j) - unitE j‖)) := by
  have hne : unitE i ≠ 0 := by
    intro h0
    have h1 := norm_unitE i
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := nontrivial_of_ne _ _ hne
  have h := det_sq_le_of_no_gain (opE D) (opE U) (norm_unitE i) (norm_unitE j)
    (inner_unitE_of_ne hij) (N.inner_unitE_opE_opE_eq_zero hH k w hw D U hX hij hp)
    (N.inner_unitE_opE_opE_eq_zero hH k w hw D U hX hij.symm hp') hD
  rwa [det_opE, inner_unitE_opE, inner_unitE_opE] at h

end ScalarNet

end CoSimFoundations
