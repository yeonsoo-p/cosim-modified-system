/-
The damped chain (the paper, Proposition 5.7, its exact part, and the construction after it).

Exact part of the proposition. Let `D` be orthogonal (`Dᵀ D = 1`), `U` a matrix, `X = D U`, and
`q = Dᵀ e_i` (`defectRow D i`, the `i`-th row of `D`). Then, in any dimension,

* `‖q‖ = 1`                                              (`norm_defectRow`),
* `⟪q, U e_j⟫ = X i j`                                   (`inner_defectRow_opE`),
* `⟪q, U⁻ᵀ e_j⟫ = (X⁻¹) j i`                             (`inner_defectRow_opE_inv_transpose`),
* `‖q - e_i‖ ≤ ‖Dᵀ - 1‖ = ‖D - 1‖`                       (`norm_defectRow_sub_le`).

For three stores, `i = 1`, `j = 3` (indices `0`, `2`): if `X 1 3 = 0` and `(X⁻¹) 3 1 = 0`, then `q`
is a unit vector orthogonal to `U e_3` and to `U⁻ᵀ e_3`, and `‖D - 1‖ ≥ ‖q - e_1‖`
(`damped_chain_exact`). The expansion `|q - e_1| = h/3 (1 + O(h))` of the paper is not formalised.

The two structural facts. The one-step map of a scheme that executes three scalar stores in the
order `1, 2, 3` with one held sample (`InfoForm`), stores `1` and `3` not being partners, has
`X 1 3 = 0` (`infoStep_three_apply_zero_two`) and `X 2 1 · X 3 2 = X 2 2 · X 3 1`
(`infoStep_three_minor`): row `1` is `(F_1, G_12, 0)`, and row `3` is `G_32 · (row 2) + F_3 e_3`.
For an invertible `3 × 3` matrix the second relation is `(X⁻¹) 3 1 = 0`
(`inv_three_apply_two_zero`: the entry is the cofactor divided by the determinant). Together:
`infoStep_three_pattern`.

The construction after the proposition. For a diagonal matrix `S = diagonal s` with `s i ≠ 0`
and any scheme with one held sample, `S X S` is again the one-step map of such a scheme with the
same stages, the local coefficients `S K S` and sample coefficients with the same zero pattern
(`diagonal_mul_infoStep_mul_diagonal`, `scaleG_eq_zero_iff`): from `(1 - N) X = K + M`,
`(1 - S N S⁻¹) (S X S) = S K S + S M S`. Applied to the sweep `Q` of `Sweep`
(`diagonal_mul_sweep_mul_diagonal`, positive local coefficients `sweepF_scaled_pos`, realisation
by gains and weights `ScalarNet.exists_gsStep_eq_scaled_sweep`). Determinants:
`det (S Q S) = (det S)² det Q` (`det_diagonal_mul_mul_diagonal`), `det Q = 1` for the sweep
(`det_sweep`, here under the hypothesis `cos φ_k ≠ 0` of `sweep_eq_infoStep`, from
`det Q = ∏ F_k` and the telescoping product), and for `S = exp (-(H/2) R)`, `R = diagonal r`:
`S = diagonal (e^{-H r_i / 2})` (`exp_smul_diagonal`) and `det (S Q S) = e^{-H tr R}`
(`det_exp_mul_sweep_mul_exp`), so that this scheme has total numerical damping zero.
-/
import CoSimFoundations.Sweep
import CoSimFoundations.FloorMatrix
import CoSimFoundations.DetExp

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

section Exact

variable {n : ℕ}

/-- The operator of the transposed matrix is the adjoint. -/
theorem opE_transpose (M : Matrix (Fin n) (Fin n) ℝ) : opE Mᵀ = star (opE M) := by
  have h : Mᵀ = star M := by rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [h]
  exact map_star (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) M

/-- The transposed matrix moves to the other side of the inner product. -/
theorem inner_opE_transpose (M : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪opE Mᵀ x, y⟫ = ⟪x, opE M y⟫ := by
  rw [opE_transpose, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- `‖Dᵀ - 1‖ = ‖D - 1‖` in the operator norm of Euclidean space. -/
theorem norm_opE_transpose_sub_one (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE Mᵀ - 1‖ = ‖opE M - 1‖ := by
  have h : opE Mᵀ - 1 = ContinuousLinearMap.adjoint (opE M - 1) := by
    rw [map_sub, ContinuousLinearMap.adjoint_one, opE_transpose,
      ContinuousLinearMap.star_eq_adjoint]
  rw [h, LinearIsometryEquiv.norm_map]

/-- The vector `q = Dᵀ e_i` of the paper: the `i`-th row of `D` as a vector of Euclidean space. -/
noncomputable def defectRow (D : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  opE Dᵀ (unitE i)

/-- The components of `q = Dᵀ e_i` are the entries of the row `i` of `D`. -/
theorem defectRow_apply (D : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    defectRow D i j = D i j := by
  have h := inner_unitE_opE Dᵀ j i
  rw [transpose_apply] at h
  rw [← h]
  simp [defectRow, unitE, EuclideanSpace.inner_single_left]

/-- **`q` is a unit vector** if `D` is orthogonal. -/
theorem norm_defectRow {D : Matrix (Fin n) (Fin n) ℝ} (hD : Dᵀ * D = 1) (i : Fin n) :
    ‖defectRow D i‖ = 1 := by
  have hD' : D * Dᵀ = 1 := mul_eq_one_comm.1 hD
  have h : ⟪defectRow D i, defectRow D i⟫ = 1 := by
    rw [defectRow, inner_opE_transpose, ← opE_mul_apply, inner_unitE_opE, hD', one_apply_eq]
  rw [real_inner_self_eq_norm_sq] at h
  have h0 := norm_nonneg (defectRow D i)
  exact le_antisymm (by nlinarith) (by nlinarith)

/-- **The first condition in terms of `q`:** `⟪q, U e_j⟫ = (D U) i j`. -/
theorem inner_defectRow_opE (D U : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪defectRow D i, opE U (unitE j)⟫ = (D * U) i j := by
  rw [defectRow, inner_opE_transpose, ← opE_mul_apply, inner_unitE_opE]

/-- **The second condition in terms of `q`:** `⟪q, U⁻ᵀ e_j⟫ = ((D U)⁻¹) j i` if `D` is
orthogonal. -/
theorem inner_defectRow_opE_inv_transpose {D : Matrix (Fin n) (Fin n) ℝ} (hD : Dᵀ * D = 1)
    (U : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪defectRow D i, opE U⁻¹ᵀ (unitE j)⟫ = (D * U)⁻¹ j i := by
  rw [real_inner_comm, inner_opE_transpose, defectRow, ← opE_mul_apply, inner_unitE_opE,
    Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hD]

/-- **The one-step error is at least `|q - e_i|`:** `‖q - e_i‖ ≤ ‖D - 1‖`, for every matrix
`D`. -/
theorem norm_defectRow_sub_le (D : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ‖defectRow D i - unitE i‖ ≤ ‖opE D - 1‖ := by
  have h : defectRow D i - unitE i = (opE Dᵀ - 1) (unitE i) := rfl
  rw [h, ← norm_opE_transpose_sub_one]
  calc ‖(opE Dᵀ - 1) (unitE i)‖ ≤ ‖opE Dᵀ - 1‖ * ‖unitE i‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖opE Dᵀ - 1‖ := by rw [norm_unitE, mul_one]

/-- **Damped chain, exact part** (the paper, Proposition 5.7). Let `D` be an orthogonal `3 × 3`
matrix, `X = D U`, `X 1 3 = 0` and `(X⁻¹) 3 1 = 0` (indices `0`, `2` here). Then `q = Dᵀ e_1` is
a unit vector orthogonal to `U e_3` and to `U⁻ᵀ e_3`, and `‖D - 1‖ ≥ ‖q - e_1‖`. (The
invertibility of `U` is not needed for these statements. Not formalised: the expansion
`|q - e_1| = h/3 (1 + O(h))` for the chain of the paper.) -/
theorem damped_chain_exact {D U : Matrix (Fin 3) (Fin 3) ℝ} (hD : Dᵀ * D = 1)
    (h13 : (D * U) 0 2 = 0) (h31 : (D * U)⁻¹ 2 0 = 0) :
    ‖defectRow D 0‖ = 1 ∧ ⟪defectRow D 0, opE U (unitE 2)⟫ = 0 ∧
      ⟪defectRow D 0, opE U⁻¹ᵀ (unitE 2)⟫ = 0 ∧ ‖defectRow D 0 - unitE 0‖ ≤ ‖opE D - 1‖ :=
  ⟨norm_defectRow hD 0, (inner_defectRow_opE D U 0 2).trans h13,
    (inner_defectRow_opE_inv_transpose hD U 0 2).trans h31, norm_defectRow_sub_le D 0⟩

end Exact

section Three

/-- **Store `1` receives nothing from store `3`:** the one-step map of a scheme with one held
sample that executes three scalar stores in the order `1, 2, 3`, the stores `1` and `3` not being
partners (`G 1 3 = 0`), has `X 1 3 = 0`. -/
theorem infoStep_three_apply_zero_two (F : Fin 3 → ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ)
    (h02 : G 0 2 = 0) : infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G 0 2 = 0 := by
  have h := infoStep_eq_add (fun i : Fin 3 => (i : ℕ)) (diagonal F) G
  rw [congrFun (congrFun h 0) 2]
  simp [Matrix.add_apply, Matrix.mul_apply, infoNew_apply, infoOld_apply, h02]

/-- **Store `3` receives the states of the stores `1` and `2` only through the new sample of
store `2`:** for the same scheme, the stores `1` and `3` not being partners (`G 3 1 = 0`),
`X 2 1 · X 3 2 = X 2 2 · X 3 1`. -/
theorem infoStep_three_minor (F : Fin 3 → ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) (h20 : G 2 0 = 0) :
    infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G 1 0 *
        infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G 2 1 =
      infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G 1 1 *
        infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G 2 0 := by
  have h := infoStep_eq_add (fun i : Fin 3 => (i : ℕ)) (diagonal F) G
  generalize infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G = X at h ⊢
  have e20 : X 2 0 = G 2 1 * X 1 0 := by
    refine (congrFun (congrFun h 2) 0).trans ?_
    simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, infoNew_apply, infoOld_apply,
      h20]
  have e21 : X 2 1 = G 2 1 * X 1 1 := by
    refine (congrFun (congrFun h 2) 1).trans ?_
    simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, infoNew_apply, infoOld_apply,
      h20]
  rw [e20, e21]
  ring

/-- **The cofactor:** for an invertible `3 × 3` matrix, `(X⁻¹) 3 1 = 0` if and only if
`X 2 1 · X 3 2 = X 2 2 · X 3 1`. -/
theorem inv_three_apply_two_zero {X : Matrix (Fin 3) (Fin 3) ℝ} (hX : X.det ≠ 0) :
    X⁻¹ 2 0 = 0 ↔ X 1 0 * X 2 1 = X 1 1 * X 2 0 := by
  have hadj : X.adjugate 2 0 = X 1 0 * X 2 1 - X 1 1 * X 2 0 := by
    rw [adjugate_apply, det_fin_three]
    simp [updateRow_apply]
  rw [Matrix.inv_def, Matrix.smul_apply, hadj, smul_eq_mul, Ring.inverse_eq_inv', mul_eq_zero,
    sub_eq_zero]
  simp [hX]

/-- **The zero pattern of a scheme on three stores executed from end to end** (the paper, proof of
Proposition 5.7): with nonzero local coefficients and the stores `1` and `3` not partners, the
one-step map has `X 1 3 = 0` and `(X⁻¹) 3 1 = 0`. -/
theorem infoStep_three_pattern (F : Fin 3 → ℝ) (hF : ∀ i, F i ≠ 0)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : ∀ i, G i i = 0) (h02 : G 0 2 = 0) (h20 : G 2 0 = 0) :
    infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G 0 2 = 0 ∧
      (infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G)⁻¹ 2 0 = 0 := by
  refine ⟨infoStep_three_apply_zero_two F G h02, ?_⟩
  have hdet : (infoStep (fun i : Fin 3 => (i : ℕ)) (diagonal F) G).det ≠ 0 := by
    rw [det_infoStep_gs _ Fin.val_injective F G hG]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hF i
  exact (inv_three_apply_two_zero hdet).2 (infoStep_three_minor F G h20)

end Three

section Scaling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sample coefficients of the scaled scheme `S X S`, `S = diagonal s`: `s_i G_ij / s_j` for
a new sample, `s_i G_ij s_j` for an old one. -/
noncomputable def scaleG (stage : ι → ℕ) (s : ι → ℝ) (G : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if stage j < stage i then s i * G i j / s j else s i * G i j * s j

/-- The scaled sample coefficients have the same zero pattern. -/
theorem scaleG_eq_zero_iff (stage : ι → ℕ) {s : ι → ℝ} (hs : ∀ i, s i ≠ 0) (G : Matrix ι ι ℝ)
    (i j : ι) : scaleG stage s G i j = 0 ↔ G i j = 0 := by
  by_cases h : stage j < stage i
  · simp [scaleG, h, hs i, hs j]
  · simp [scaleG, h, hs i, hs j]

/-- The new samples of the scaled scheme: `S N S⁻¹`. -/
theorem infoNew_scaleG (stage : ι → ℕ) (s : ι → ℝ) (G : Matrix ι ι ℝ) :
    infoNew stage (scaleG stage s G) =
      diagonal s * infoNew stage G * diagonal fun i => (s i)⁻¹ := by
  ext i j
  rw [infoNew_apply, mul_diagonal, diagonal_mul, infoNew_apply]
  by_cases h : stage j < stage i
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [scaleG, of_apply, ite_eq_left h]
    rw [div_eq_mul_inv]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, zero_mul]

/-- The old samples of the scaled scheme: `S M S`. -/
theorem infoOld_scaleG (stage : ι → ℕ) (s : ι → ℝ) (G : Matrix ι ι ℝ) :
    infoOld stage (scaleG stage s G) = diagonal s * infoOld stage G * diagonal s := by
  ext i j
  rw [infoOld_apply, mul_diagonal, diagonal_mul, infoOld_apply]
  by_cases h : stage j < stage i
  · rw [ite_eq_left h, ite_eq_left h, mul_zero, zero_mul]
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [scaleG, of_apply, ite_eq_right h]

/-- **A diagonal scaling of a scheme is a scheme of the same kind.** If `X` is the one-step map
of a scheme with one held sample (stages `stage`, local coefficients `K`, sample coefficients
`G`) and `S = diagonal s` with `s i ≠ 0`, then `S X S` is the one-step map of the scheme with the
same stages, the local coefficients `S K S` and the sample coefficients `scaleG stage s G`. -/
theorem diagonal_mul_infoStep_mul_diagonal (stage : ι → ℕ) {s : ι → ℝ} (hs : ∀ i, s i ≠ 0)
    (K G : Matrix ι ι ℝ) :
    diagonal s * infoStep stage K G * diagonal s =
      infoStep stage (diagonal s * K * diagonal s) (scaleG stage s G) := by
  rw [eq_infoStep_iff, infoNew_scaleG, infoOld_scaleG]
  have hinv : (diagonal fun i => (s i)⁻¹) * diagonal s = (1 : Matrix ι ι ℝ) := by
    have h1 : (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℝ) :=
      funext fun i => inv_mul_cancel₀ (hs i)
    rw [diagonal_mul_diagonal, h1, diagonal_one]
  have hX := one_sub_infoNew_mul_infoStep stage K G
  generalize infoStep stage K G = X at hX ⊢
  have h2 : diagonal s * infoNew stage G * (diagonal fun i => (s i)⁻¹) *
      (diagonal s * X * diagonal s) = diagonal s * (infoNew stage G * X) * diagonal s := by
    calc diagonal s * infoNew stage G * (diagonal fun i => (s i)⁻¹) *
          (diagonal s * X * diagonal s)
        = diagonal s * infoNew stage G * ((diagonal fun i => (s i)⁻¹) * diagonal s) * X *
          diagonal s := by simp only [Matrix.mul_assoc]
      _ = diagonal s * (infoNew stage G * X) * diagonal s := by
        rw [hinv, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  have hX' : X - infoNew stage G * X = K + infoOld stage G := by
    rw [← hX, Matrix.sub_mul, Matrix.one_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, h2, ← Matrix.sub_mul, ← Matrix.mul_sub, hX',
    Matrix.mul_add, Matrix.add_mul]

/-- For scalar stores the scaled local coefficients are `s_i F_i s_i`. -/
theorem diagonal_mul_infoStep_diagonal_mul_diagonal (stage : ι → ℕ) {s : ι → ℝ}
    (hs : ∀ i, s i ≠ 0) (F : ι → ℝ) (G : Matrix ι ι ℝ) :
    diagonal s * infoStep stage (diagonal F) G * diagonal s =
      infoStep stage (diagonal fun i => s i * F i * s i) (scaleG stage s G) := by
  rw [diagonal_mul_infoStep_mul_diagonal stage hs, diagonal_mul_diagonal, diagonal_mul_diagonal]

/-- **`det (S Q S) = (det S)² det Q`.** -/
theorem det_diagonal_mul_mul_diagonal (s : ι → ℝ) (Q : Matrix ι ι ℝ) :
    (diagonal s * Q * diagonal s).det = (diagonal s).det ^ 2 * Q.det := by
  rw [det_mul, det_mul]
  ring

/-- The exponential of a diagonal matrix: `exp (c R) = diagonal (e^{c r_i})` for
`R = diagonal r`. -/
theorem exp_smul_diagonal (c : ℝ) (r : ι → ℝ) :
    NormedSpace.exp (c • diagonal r) = diagonal fun i => Real.exp (c * r i) := by
  rw [← diagonal_smul, exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Real.exp_eq_exp_ℝ, Pi.smul_apply, smul_eq_mul]

end Scaling

section DampedSweep

open Real

/-- The local coefficients of the sweep multiply to one. -/
theorem prod_sweepF (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, cos (φ k) ≠ 0) :
    ∏ i, sweepF φ m i = 1 := by
  set f : ℕ → ℝ := fun i =>
    if i = 0 then cos (φ 0) else if i = m + 1 then 1 / cos (φ m) else cos (φ i) / cos (φ (i - 1))
    with hf
  have hpart : ∀ j, j ≤ m → ∏ i ∈ Finset.range (j + 1), f i = cos (φ j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Finset.prod_range_one, hf]
      simp
    | succ j ih =>
      intro hj
      have hfj : f (j + 1) = cos (φ (j + 1)) / cos (φ j) := by
        rw [hf]
        simp only
        rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]
      rw [Finset.prod_range_succ, ih (by omega), hfj]
      field_simp [hc j (by omega)]
  have hlast : f (m + 1) = 1 / cos (φ m) := by
    rw [hf]
    simp
  have hF : ∀ i : Fin (m + 2), sweepF φ m i = f i := fun i => rfl
  rw [Finset.prod_congr rfl fun i _ => hF i, Fin.prod_univ_eq_prod_range f (m + 2),
    Finset.prod_range_succ, hpart m le_rfl, hlast]
  field_simp [hc m le_rfl]

/-- **The sweep has determinant one** (for `cos φ_k ≠ 0`, the hypothesis under which it is the
one-step map of the end-to-end scheme). -/
theorem det_sweep (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, cos (φ k) ≠ 0) : (sweep φ m).det = 1 := by
  rw [sweep_eq_infoStep φ m hc, det_infoStep_gs _ Fin.val_injective _ _ (sweepG_diag φ m),
    prod_sweepF φ m hc]

/-- **The damped sweep is a scheme of the same kind** (the paper, after Proposition 5.7): for
`S = diagonal s` with `s i ≠ 0`, `S Q S` with `Q` the sweep is the one-step map of the
Gauss–Seidel scheme with one held sample that executes the stores in the order `0, …, m + 1`,
with the local coefficients `s_i² F_i` and the sample coefficients `scaleG`, which vanish where
those of the sweep do (`scaleG_eq_zero_iff`). -/
theorem diagonal_mul_sweep_mul_diagonal (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, cos (φ k) ≠ 0)
    {s : Fin (m + 2) → ℝ} (hs : ∀ i, s i ≠ 0) :
    diagonal s * sweep φ m * diagonal s =
      infoStep (fun i : Fin (m + 2) => (i : ℕ)) (diagonal fun i => s i * sweepF φ m i * s i)
        (scaleG (fun i : Fin (m + 2) => (i : ℕ)) s (sweepG φ m)) := by
  rw [sweep_eq_infoStep φ m hc, diagonal_mul_infoStep_diagonal_mul_diagonal _ hs]

/-- The local coefficients of the damped sweep are positive. -/
theorem sweepF_scaled_pos (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, 0 < cos (φ k))
    {s : Fin (m + 2) → ℝ} (hs : ∀ i, s i ≠ 0) (i : Fin (m + 2)) :
    0 < s i * sweepF φ m i * s i := by
  have h1 := sweepF_pos φ m hc i
  have h2 : 0 < s i * s i := mul_self_pos.2 (hs i)
  nlinarith

/-- **The damped sweep is the step of a Gauss–Seidel scheme with output feedback,** for every
network of `m + 2` scalar stores and every macro step `H > 0`: gains `k` and weights `w` on the
links of the chain exist whose Gauss–Seidel step matrix is `S Q S`. -/
theorem ScalarNet.exists_gsStep_eq_scaled_sweep {m : ℕ} (N : ScalarNet (m + 2)) {H : ℝ}
    (hH : 0 < H) (φ : ℕ → ℝ) (hc : ∀ k ≤ m, 0 < cos (φ k)) {s : Fin (m + 2) → ℝ}
    (hs : ∀ i, s i ≠ 0) :
    ∃ k w, (∀ i j : Fin (m + 2), (j : ℕ) + 1 ≠ i → (i : ℕ) + 1 ≠ j → w i j = 0) ∧
      N.gsStep H k w = diagonal s * sweep φ m * diagonal s := by
  have hdiag : ∀ i, scaleG (fun i : Fin (m + 2) => (i : ℕ)) s (sweepG φ m) i i = 0 := fun i =>
    (scaleG_eq_zero_iff _ hs _ i i).2 (sweepG_diag φ m i)
  obtain ⟨k, w, hw, h⟩ := N.exists_gsStep_eq_infoStep hH (fun i => s i * sweepF φ m i * s i)
    (sweepF_scaled_pos φ m hc hs) _ hdiag
  refine ⟨k, w, fun i j h1 h2 => hw i j ((scaleG_eq_zero_iff _ hs _ i j).2 ?_), ?_⟩
  · have h2' : ¬ (j : ℕ) = (i : ℕ) + 1 := fun h => h2 h.symm
    simp only [sweepG, of_apply, ite_eq_right h1, ite_eq_right h2']
  · rw [h, diagonal_mul_sweep_mul_diagonal φ m (fun k hk => (hc k hk).ne') hs]

/-- **The determinant of the damped sweep:** `det (S Q S) = (∏ s_i)²`. -/
theorem det_diagonal_mul_sweep_mul_diagonal (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, cos (φ k) ≠ 0)
    (s : Fin (m + 2) → ℝ) : (diagonal s * sweep φ m * diagonal s).det = (∏ i, s i) ^ 2 := by
  rw [det_diagonal_mul_mul_diagonal, det_sweep φ m hc, det_diagonal, mul_one]

/-- **The damped sweep has total numerical damping zero** (the paper, equation (dampedsweep)):
`det (e^{-HR/2} Q e^{-HR/2}) = e^{-H tr R}` for `R = diagonal r`, which is the determinant of
the monolithic step `e^{HA}` when `tr A = -tr R`. -/
theorem det_exp_mul_sweep_mul_exp (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, cos (φ k) ≠ 0)
    (r : Fin (m + 2) → ℝ) (H : ℝ) :
    (NormedSpace.exp ((-(H / 2)) • diagonal r) * sweep φ m *
      NormedSpace.exp ((-(H / 2)) • diagonal r)).det = Real.exp (-(H * (diagonal r).trace)) := by
  rw [exp_smul_diagonal, det_diagonal_mul_sweep_mul_diagonal φ m hc, ← Real.exp_sum, sq,
    ← Real.exp_add, trace_diagonal, ← Finset.mul_sum]
  congr 1
  ring

end DampedSweep

end CoSimFoundations
