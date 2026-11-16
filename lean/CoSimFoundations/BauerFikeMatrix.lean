/-
Bauer–Fike for real matrices in the energy norm, in the forms used for the spectral bounds:

* Thm 9.3(ii): if `A = V diag(d) V⁻¹`, every eigenvalue of `A + Δ` lies within
  `κ_Q(V) ‖Δ‖_Q` of some `d j`, with `κ_Q(V) = ‖V‖_{2→Q} ‖V⁻¹‖_{Q→2}` (the paper's
  `‖Q^{1/2} V‖₂ ‖V⁻¹ Q^{-1/2}‖₂`); hence `Re μ ≤ Re d j + κ_Q(V) ‖Δ‖_Q`, i.e.
  `γ_p ≥ γ_ref - κ_Q(V) ‖ΔA‖_Q`;
* the `Q`-normal case `κ = 1`: every eigenvalue of `A + Δ` lies within `‖Δ‖_Q` of `σ(A)`;
* Thm 9.3(ii), first bound: if `xᵀ sym(QA) x ≤ c xᵀQx` for all `x`, every eigenvalue of `A` has
  `Re μ ≤ c`; if `sym(QA)` is negative definite, every eigenvalue has `Re μ < 0`;
* (J3) of the joint trade-off theorem (Thm 9.13(i)): for a `Q`-orthogonal reference step `U` and
  any graph step matrix `Φ` (the paper's `Φ̃`, `n × n`), every eigenvalue `μ` of `Φ` has
  `|‖μ‖ - 1| ≤ ‖Φ U⁻¹ - I‖_Q = α`; a lossless plant (`sym(Q A_ref) = 0`) has a `Q`-orthogonal
  reference step `U = exp(H A_ref)`.

Eigenvalues of a real matrix `A` are `spectrum ℂ (cx A)`; `‖·‖_Q` is the real energy operator norm
`‖QSpace.op _‖`.
-/
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import CoSimFoundations.BauerFike
import CoSimFoundations.EnergyNormC

open Matrix NormedSpace
open scoped ComplexOrder

namespace CoSimFoundations

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace QSpace

variable {E : EnergyForm n}

theorem op_mul (M N : Matrix n n ℝ) : op (E := E) (M * N) = (op (E := E) M).comp (op N) := by
  ext x : 1
  show (M * N) *ᵥ toVec E x = M *ᵥ (N *ᵥ toVec E x)
  rw [mulVec_mulVec]

/-- **A `Q`-orthogonal matrix is a `Q`-isometry:** `Uᵀ Q U = Q` gives `‖U‖_Q ≤ 1`. -/
theorem opNorm_le_one_of_orthogonal {U : Matrix n n ℝ} (hU : Uᵀ * E.Q * U = E.Q) :
    ‖op (E := E) U‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have h : ‖op (E := E) U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq, toVec_op, mulVec_mulVec,
      dot_mulVec_swap (U *ᵥ toVec E x) (E.Q * U) (toVec E x), mulVec_mulVec, transpose_mul,
      Q_symm, hU]
  rw [one_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h.le

end QSpace

namespace QSpaceC

/-- **Bauer–Fike, `Q`-normal case.** If `A` is `Q`-normal (`A⋆A = AA⋆`, `A⋆ = Q⁻¹AᵀQ`), every
eigenvalue of `A + Δ` lies within `‖Δ‖_Q` of an eigenvalue of `A`. -/
theorem exists_eigenvalue_near_of_qNormal (E : EnergyForm n) {A Δ : Matrix n n ℝ}
    (hA : Commute (qAdj E.Q A) A) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx (A + Δ))) :
    ∃ l ∈ spectrum ℂ (cx A), ‖μ - l‖ ≤ ‖QSpace.op (E := E) Δ‖ := by
  have := isStarNormal_opC_cx (E := E) hA
  rw [map_add, ← spectrum_opC (E := E), opC_add] at hμ
  obtain ⟨l, hl, hle⟩ := exists_mem_spectrum_norm_sub_le _ hμ
  rw [spectrum_opC] at hl
  exact ⟨l, hl, hle.trans (norm_opC_cx_le Δ)⟩

/-- The growth-rate form of the `Q`-normal case: `Re μ ≤ Re l + ‖Δ‖_Q` for some `l ∈ σ(A)`. -/
theorem re_le_of_qNormal (E : EnergyForm n) {A Δ : Matrix n n ℝ}
    (hA : Commute (qAdj E.Q A) A) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx (A + Δ))) :
    ∃ l ∈ spectrum ℂ (cx A), μ.re ≤ l.re + ‖QSpace.op (E := E) Δ‖ := by
  obtain ⟨l, hl, hle⟩ := exists_eigenvalue_near_of_qNormal E hA hμ
  refine ⟨l, hl, ?_⟩
  have := Complex.re_le_norm (μ - l)
  rw [Complex.sub_re] at this
  linarith

/-- **(J3), first form.** If `U` is `Q`-orthogonal, every eigenvalue `μ` of `Φ` has
`|‖μ‖ - 1| ≤ ‖Φ - U‖_Q`. -/
theorem abs_norm_sub_one_le (E : EnergyForm n) {U Φ : Matrix n n ℝ} (hU : Uᵀ * E.Q * U = E.Q)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx Φ)) : |‖μ‖ - 1| ≤ ‖QSpace.op (E := E) (Φ - U)‖ := by
  have hΦ : Φ = U + (Φ - U) := by abel
  rw [hΦ, map_add, ← spectrum_opC (E := E), opC_add] at hμ
  exact (abs_norm_sub_one_le_of_unitary (opC_cx_mem_unitary hU) _ hμ).trans (norm_opC_cx_le _)

/-- **(J3).** If the reference step `U` is `Q`-orthogonal (lossless plant), every eigenvalue `μ`
of the graph step matrix `Φ` (the paper's `Φ̃`) satisfies `|‖μ‖ - 1| ≤ α = ‖D - I‖_Q` with the step defect `D = Φ U⁻¹`. With
`‖μ‖ = e^{H δ}` this is `|e^{H δ} - 1| ≤ α`. -/
theorem abs_norm_sub_one_le_stepDefect (E : EnergyForm n) {U Φ : Matrix n n ℝ}
    (hU : Uᵀ * E.Q * U = E.Q) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx Φ)) :
    |‖μ‖ - 1| ≤ ‖QSpace.op (E := E) (Φ * U⁻¹ - 1)‖ := by
  refine (abs_norm_sub_one_le E hU hμ).trans ?_
  have h1 := qAdj_mul_self_of_orthogonal hU
  have hinv : U⁻¹ = qAdj E.Q U := inv_eq_left_inv h1
  have hfac : Φ - U = (Φ * U⁻¹ - 1) * U := by
    rw [sub_mul, Matrix.mul_assoc, hinv, h1, Matrix.mul_one, Matrix.one_mul]
  rw [hfac, QSpace.op_mul]
  calc ‖(QSpace.op (E := E) (Φ * U⁻¹ - 1)).comp (QSpace.op U)‖
      ≤ ‖QSpace.op (E := E) (Φ * U⁻¹ - 1)‖ * ‖QSpace.op (E := E) U‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖QSpace.op (E := E) (Φ * U⁻¹ - 1)‖ * 1 :=
        mul_le_mul_of_nonneg_left (QSpace.opNorm_le_one_of_orthogonal hU) (norm_nonneg _)
    _ = _ := mul_one _

/-- The eigenvector matrix `V` as an equivalence `ℂⁿ (standard product) → QSpaceC E`. -/
noncomputable def eigvecEquiv (E : EnergyForm n) {V : Matrix n n ℂ} (hV : IsUnit V.det) :
    QSpaceC (EnergyForm.one (n := n)) ≃L[ℂ] QSpaceC E :=
  ContinuousLinearEquiv.equivOfInverse (opC V) (opC V⁻¹)
    (fun x => by
      show V⁻¹ *ᵥ (V *ᵥ toVec _ x) = toVec _ x
      rw [mulVec_mulVec, nonsing_inv_mul _ hV, one_mulVec])
    (fun x => by
      show V *ᵥ (V⁻¹ *ᵥ toVec _ x) = toVec _ x
      rw [mulVec_mulVec, mul_nonsing_inv _ hV, one_mulVec])

theorem QC_one : (EnergyForm.one (n := n)).QC = 1 := map_one cx

/-- Diagonal matrices are normal operators for the standard product. -/
theorem isStarNormal_opC_diagonal (d : n → ℂ) :
    IsStarNormal (opC (E := EnergyForm.one (n := n)) (F := EnergyForm.one) (diagonal d)) := by
  constructor
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_opC, QC_one, inv_one, Matrix.one_mul,
    Matrix.mul_one, diagonal_conjTranspose]
  show opCAlg _ (diagonal (star d)) * opCAlg _ (diagonal d) =
    opCAlg _ (diagonal d) * opCAlg _ (diagonal (star d))
  rw [← map_mul, ← map_mul, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  funext i
  exact mul_comm _ _

/-- **Bauer–Fike with the condition number (Thm 9.3(ii)).** If `A = V diag(d) V⁻¹` over `ℂ`, every
eigenvalue `μ` of `A + Δ` satisfies `‖μ - d j‖ ≤ κ_Q(V) ‖Δ‖_Q` for some `j`, where
`κ_Q(V) = ‖V‖_{2→Q} ‖V⁻¹‖_{Q→2}`. -/
theorem exists_eigenvalue_near_of_diagonalizable (E : EnergyForm n) {A Δ : Matrix n n ℝ}
    {V : Matrix n n ℂ} (hV : IsUnit V.det) {d : n → ℂ} (hA : cx A = V * diagonal d * V⁻¹)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx (A + Δ))) :
    ∃ j, ‖μ - d j‖ ≤ ‖opC (E := EnergyForm.one) (F := E) V‖ *
      ‖opC (E := E) (F := EnergyForm.one) V⁻¹‖ * ‖QSpace.op (E := E) Δ‖ := by
  set e := eigvecEquiv E hV
  have := isStarNormal_opC_diagonal d
  have hconj : e.conjContinuousAlgEquiv
      (opC (E := EnergyForm.one) (F := EnergyForm.one) (diagonal d)) =
      opC (E := E) (F := E) (cx A) := by
    ext x : 1
    show V *ᵥ (diagonal d *ᵥ (V⁻¹ *ᵥ toVec E x)) = cx A *ᵥ toVec E x
    rw [hA, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  rw [map_add, ← spectrum_opC (E := E), opC_add, ← hconj] at hμ
  obtain ⟨l, hl, hle⟩ := exists_mem_spectrum_norm_sub_le_conj e _ _ hμ
  rw [spectrum_opC, spectrum_diagonal] at hl
  obtain ⟨j, rfl⟩ := hl
  have he1 : (e : QSpaceC EnergyForm.one →L[ℂ] QSpaceC E) = opC V := rfl
  have he2 : (e.symm : QSpaceC E →L[ℂ] QSpaceC EnergyForm.one) = opC V⁻¹ := rfl
  rw [he1, he2] at hle
  exact ⟨j, hle.trans (mul_le_mul_of_nonneg_left (norm_opC_cx_le Δ) (by positivity))⟩

/-- The growth-rate form: `Re μ ≤ Re d j + κ_Q(V) ‖Δ‖_Q`, i.e. `γ_p ≥ γ_ref - κ_Q(V) ‖ΔA‖_Q`. -/
theorem re_le_of_diagonalizable (E : EnergyForm n) {A Δ : Matrix n n ℝ}
    {V : Matrix n n ℂ} (hV : IsUnit V.det) {d : n → ℂ} (hA : cx A = V * diagonal d * V⁻¹)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx (A + Δ))) :
    ∃ j, μ.re ≤ (d j).re + ‖opC (E := EnergyForm.one) (F := E) V‖ *
      ‖opC (E := E) (F := EnergyForm.one) V⁻¹‖ * ‖QSpace.op (E := E) Δ‖ := by
  obtain ⟨j, hj⟩ := exists_eigenvalue_near_of_diagonalizable E hV hA hμ
  refine ⟨j, ?_⟩
  have := Complex.re_le_norm (μ - d j)
  rw [Complex.sub_re] at this
  linarith

/-- An eigenvalue of a complex matrix has an eigenvector. -/
theorem exists_mulVec_eq_smul {M : Matrix n n ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ M) :
    ∃ v ≠ 0, M *ᵥ v = μ • v := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' (R := ℂ) (n := n)) M,
    ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  have := Module.End.mem_eigenspace_iff.1 hv.1
  simpa [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply] using this

/-- For an eigenpair `A v = μ v` of a real matrix: `Re μ · (v* Q v) = Re (v* Q A v)`, with
`v* Q v = (Re v)ᵀQ(Re v) + (Im v)ᵀQ(Im v) > 0` and
`Re (v* Q A v) = (Re v)ᵀ sym(QA) (Re v) + (Im v)ᵀ sym(QA) (Im v)`. -/
theorem re_mul_energy_eq (E : EnergyForm n) {A : Matrix n n ℝ} {μ : ℂ} {v : n → ℂ}
    (hv : cx A *ᵥ v = μ • v) :
    μ.re * (reV v ⬝ᵥ (E.Q *ᵥ reV v) + imV v ⬝ᵥ (E.Q *ᵥ imV v)) =
      reV v ⬝ᵥ (sym (E.Q * A) *ᵥ reV v) + imV v ⬝ᵥ (sym (E.Q * A) *ᵥ imV v) := by
  have h1 : star v ⬝ᵥ (cx (E.Q * A) *ᵥ v) =
      μ * ((reV v ⬝ᵥ (E.Q *ᵥ reV v) + imV v ⬝ᵥ (E.Q *ᵥ imV v) : ℝ) : ℂ) := by
    rw [map_mul, ← mulVec_mulVec, hv, mulVec_smul, dotProduct_smul, smul_eq_mul,
      ← EnergyForm.star_dotProduct_QC, EnergyForm.QC]
  have h2 := congrArg Complex.re h1
  rw [re_star_dotProduct_cx, Complex.re_mul_ofReal] at h2
  rw [dotProduct_mulVec_sym, dotProduct_mulVec_sym, h2]

theorem energy_pos_of_ne_zero (E : EnergyForm n) {v : n → ℂ} (hv : v ≠ 0) :
    0 < reV v ⬝ᵥ (E.Q *ᵥ reV v) + imV v ⬝ᵥ (E.Q *ᵥ imV v) := by
  have h := E.posDef_QC.dotProduct_mulVec_pos hv
  rw [EnergyForm.star_dotProduct_QC, Complex.zero_lt_real] at h
  exact h

/-- **Thm 9.3(ii), first bound.** If `xᵀ sym(QA) x ≤ c xᵀ Q x` for all real `x`, every eigenvalue
of `A` has `Re μ ≤ c`: the growth rate is bounded by the largest numerical power rate. -/
theorem re_le_of_sym_le (E : EnergyForm n) {A : Matrix n n ℝ} {c : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ (sym (E.Q * A) *ᵥ x) ≤ c * (x ⬝ᵥ (E.Q *ᵥ x)))
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx A)) : μ.re ≤ c := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_smul hμ
  have hs := energy_pos_of_ne_zero E hv0
  have heq := re_mul_energy_eq E hv
  have hle : μ.re * (reV v ⬝ᵥ (E.Q *ᵥ reV v) + imV v ⬝ᵥ (E.Q *ᵥ imV v)) ≤
      c * (reV v ⬝ᵥ (E.Q *ᵥ reV v) + imV v ⬝ᵥ (E.Q *ᵥ imV v)) := by
    rw [heq, mul_add]
    exact add_le_add (h _) (h _)
  exact le_of_mul_le_mul_right hle hs

/-- **Stability from the power form (Thm 9.3(ii)).** If `sym(QA)` is negative definite, every
eigenvalue of `A` has `Re μ < 0` (`γ_p > 0`). -/
theorem re_neg_of_sym_negDef (E : EnergyForm n) {A : Matrix n n ℝ}
    (h : ∀ x : n → ℝ, x ≠ 0 → x ⬝ᵥ (sym (E.Q * A) *ᵥ x) < 0)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx A)) : μ.re < 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_smul hμ
  have hs := energy_pos_of_ne_zero E hv0
  have heq := re_mul_energy_eq E hv
  have hle : ∀ x : n → ℝ, x ⬝ᵥ (sym (E.Q * A) *ᵥ x) ≤ 0 := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (h x hx).le
  have hlt : reV v ⬝ᵥ (sym (E.Q * A) *ᵥ reV v) + imV v ⬝ᵥ (sym (E.Q * A) *ᵥ imV v) < 0 := by
    by_cases hre : reV v = 0
    · have him : imV v ≠ 0 := by
        intro him
        apply hv0
        funext i
        apply Complex.ext
        · exact congrFun hre i
        · exact congrFun him i
      exact add_neg_of_nonpos_of_neg (hle _) (h _ him)
    · exact add_neg_of_neg_of_nonpos (h _ hre) (hle _)
  rw [← heq] at hlt
  exact neg_of_mul_neg_left hlt hs.le

/-- **A lossless reference step is `Q`-orthogonal:** if `QA` is skew (`sym(QA) = 0`), then
`U = exp(H A)` satisfies `Uᵀ Q U = Q`. -/
theorem transpose_exp_mul_Q_mul_exp (E : EnergyForm n) {A : Matrix n n ℝ}
    (hA : (E.Q * A)ᵀ = -(E.Q * A)) (H : ℝ) :
    (exp (H • A))ᵀ * E.Q * exp (H • A) = E.Q := by
  have hQ : IsUnit E.Q := E.posDef.isUnit
  have hQd : IsUnit E.Q.det := (Matrix.isUnit_iff_isUnit_det _).1 hQ
  have h1 : Aᵀ * E.Q = -(E.Q * A) := by
    rw [← hA, transpose_mul, QSpace.Q_symm]
  have h2 : Aᵀ = -(E.Q * A) * E.Q⁻¹ := by
    rw [← h1, Matrix.mul_assoc, mul_nonsing_inv _ hQd, Matrix.mul_one]
  have hT : (H • A)ᵀ = E.Q * (-(H • A)) * E.Q⁻¹ := by
    rw [transpose_smul, h2]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hexpT : (exp (H • A))ᵀ = E.Q * exp (-(H • A)) * E.Q⁻¹ := by
    rw [← Matrix.exp_transpose, hT, Matrix.exp_conj _ _ hQ]
  have hE : IsUnit (exp (H • A)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [hexpT, Matrix.mul_assoc (E.Q * exp (-(H • A))) E.Q⁻¹ E.Q, nonsing_inv_mul _ hQd,
    Matrix.mul_one, Matrix.mul_assoc, Matrix.exp_neg, nonsing_inv_mul _ hE, Matrix.mul_one]

/-- **(J3) for a lossless plant.** If `sym(Q A_ref) = 0`, every eigenvalue `μ` of the graph step
matrix `Φ` has `|‖μ‖ - 1| ≤ α = ‖Φ exp(H A_ref)⁻¹ - I‖_Q`. -/
theorem abs_norm_sub_one_le_lossless (E : EnergyForm n) {Aref Φ : Matrix n n ℝ}
    (hA : (E.Q * Aref)ᵀ = -(E.Q * Aref)) (H : ℝ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cx Φ)) :
    |‖μ‖ - 1| ≤ ‖QSpace.op (E := E) (Φ * (exp (H • Aref))⁻¹ - 1)‖ :=
  abs_norm_sub_one_le_stepDefect E (transpose_exp_mul_Q_mul_exp E hA H) hμ

end QSpaceC

end CoSimFoundations
