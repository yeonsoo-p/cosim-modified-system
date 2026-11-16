/-
The complex energy space: `ℂⁿ` with `⟪z, w⟫_Q = z* Q w` for a real energy matrix `Q ≻ 0`.

The paper's eigenvalues of real matrices are complex, and its spectral bounds (Bauer–Fike)
are stated with the real energy operator norm `‖X‖_Q`. This file provides the bridge:

* `QSpaceC E` is a complex Hilbert space, so its operators form a C⋆-algebra;
* `opC M` is a complex matrix as an operator; `opCAlg` identifies `Matrix n n ℂ` with these
  operators as algebras, so `σ(opC M) = σ(M)` (`spectrum_opC`);
* the energy splits over real and imaginary parts, `‖z‖² = ‖Re z‖_Q² + ‖Im z‖_Q²`, hence the complex
  operator norm of a real matrix is at most its real energy operator norm (`norm_opC_cx_le`);
* the adjoint of `opC M` is `opC (Q⁻¹ Mᴴ Q)`; for real `A` this is the `Q`-adjoint `Q⁻¹ Aᵀ Q`, so
  a `Q`-normal real matrix gives a normal operator and a `Q`-orthogonal one a unitary operator.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Order.Star.Real
import CoSimFoundations.EnergyNorm

open Matrix
open scoped ComplexOrder

namespace CoSimFoundations

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complexification of real matrices. -/
noncomputable abbrev cx : Matrix n n ℝ →+* Matrix n n ℂ := (algebraMap ℝ ℂ).mapMatrix

theorem cx_apply (A : Matrix n n ℝ) (i j : n) : cx A i j = (A i j : ℂ) := rfl

theorem conjTranspose_cx (A : Matrix n n ℝ) : (cx A)ᴴ = cx Aᵀ := by
  ext i j
  simp [cx_apply, conjTranspose_apply]

theorem cx_inv (A : Matrix n n ℝ) : cx A⁻¹ = (cx A)⁻¹ := by
  by_cases h : IsUnit A.det
  · symm
    refine inv_eq_left_inv ?_
    rw [← map_mul, nonsing_inv_mul _ h, map_one]
  · have h' : ¬ IsUnit (cx A).det := by
      show ¬IsUnit ((algebraMap ℝ ℂ).mapMatrix A).det
      rw [← RingHom.map_det, isUnit_iff_ne_zero, ne_eq,
        map_eq_zero_iff _ (algebraMap ℝ ℂ).injective, ← ne_eq, ← isUnit_iff_ne_zero]
      exact h
    rw [nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit _ h', map_zero]

/-- Real part of a complex vector. -/
def reV (z : n → ℂ) : n → ℝ := fun i => (z i).re

/-- Imaginary part of a complex vector. -/
def imV (z : n → ℂ) : n → ℝ := fun i => (z i).im

/-- For any real `M`, `Re (z* M z) = (Re z)ᵀ M (Re z) + (Im z)ᵀ M (Im z)`. -/
theorem re_star_dotProduct_cx (M : Matrix n n ℝ) (z : n → ℂ) :
    (star z ⬝ᵥ (cx M *ᵥ z)).re = reV z ⬝ᵥ (M *ᵥ reV z) + imV z ⬝ᵥ (M *ᵥ imV z) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, cx_apply,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, reV, imV, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

namespace EnergyForm

variable (E : EnergyForm n)

/-- The energy matrix as a complex matrix. -/
noncomputable def QC : Matrix n n ℂ := cx E.Q

/-- **The complex energy splits over real and imaginary parts:**
`z* Q z = (Re z)ᵀ Q (Re z) + (Im z)ᵀ Q (Im z)` (the cross terms cancel since `Q` is symmetric). -/
theorem star_dotProduct_QC (z : n → ℂ) :
    star z ⬝ᵥ (E.QC *ᵥ z) =
      ((reV z ⬝ᵥ (E.Q *ᵥ reV z) + imV z ⬝ᵥ (E.Q *ᵥ imV z) : ℝ) : ℂ) := by
  have hQ : ∀ i j, E.Q j i = E.Q i j := fun i j => by
    have := congrFun (congrFun (QSpace.Q_symm (E := E)) i) j
    simpa [transpose_apply] using this
  apply Complex.ext
  · simp only [QC, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, cx_apply,
      Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, reV, imV, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [QC, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.im_sum, cx_apply,
      Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    -- `Σ_ij Q_ij (x_i y_j - y_i x_j) = 0`
    have h : ∑ i, ∑ j, E.Q i j * ((z i).re * (z j).im) =
        ∑ i, ∑ j, E.Q i j * ((z i).im * (z j).re) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hQ]; ring
    have e : ∀ i j, ((z i).re * (E.Q i j * (z j).im + 0 * (z j).re) +
        -(z i).im * (E.Q i j * (z j).re - 0 * (z j).im)) =
        E.Q i j * ((z i).re * (z j).im) - E.Q i j * ((z i).im * (z j).re) := fun i j => by ring
    simp only [e, Finset.sum_sub_distrib, h, sub_self]

/-- The complexified energy matrix is positive definite. -/
theorem posDef_QC : E.QC.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun z hz => ?_
  · show (cx E.Q)ᴴ = cx E.Q
    rw [conjTranspose_cx, QSpace.Q_symm (E := E)]
  · rw [star_dotProduct_QC, Complex.zero_lt_real]
    have h0 : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (E.Q *ᵥ x) := fun x => by
      simpa [star_trivial] using E.posDef.posSemidef.dotProduct_mulVec_nonneg x
    have hpos : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (E.Q *ᵥ x) := fun x hx => by
      simpa [star_trivial] using E.posDef.dotProduct_mulVec_pos hx
    by_cases hre : reV z = 0
    · have him : imV z ≠ 0 := by
        intro him
        apply hz
        funext i
        apply Complex.ext
        · exact congrFun hre i
        · exact congrFun him i
      exact add_pos_of_nonneg_of_pos (h0 _) (hpos _ him)
    · exact add_pos_of_pos_of_nonneg (hpos _ hre) (h0 _)

theorem isUnit_det_QC : IsUnit E.QC.det := E.posDef_QC.isUnit.map Matrix.detMonoidHom

theorem conjTranspose_QC : E.QCᴴ = E.QC := E.posDef_QC.isHermitian.eq

/-- The identity energy form (the standard Hermitian product). -/
def one : EnergyForm n := ⟨1, PosDef.one⟩

end EnergyForm

/-- `ℂⁿ` with the energy inner product `z* Q w` of `E`. -/
def QSpaceC (_E : EnergyForm n) : Type _ := n → ℂ

namespace QSpaceC

variable (E : EnergyForm n)

noncomputable instance : NormedAddCommGroup (QSpaceC E) := E.QC.toNormedAddCommGroup E.posDef_QC
noncomputable instance : InnerProductSpace ℂ (QSpaceC E) :=
  E.QC.toInnerProductSpace E.posDef_QC.posSemidef

/-- Coordinates. -/
def ofVec (x : n → ℂ) : QSpaceC E := x
def toVec (x : QSpaceC E) : n → ℂ := x

instance : FiniteDimensional ℂ (QSpaceC E) := inferInstanceAs (FiniteDimensional ℂ (n → ℂ))
instance : CompleteSpace (QSpaceC E) := FiniteDimensional.complete ℂ _

variable {E}

theorem inner_eq (x y : QSpaceC E) :
    (inner ℂ x y : ℂ) = star (toVec E x) ⬝ᵥ (E.QC *ᵥ toVec E y) := by
  show (E.QC *ᵥ toVec E y) ⬝ᵥ star (toVec E x) = _
  rw [dotProduct_comm]

/-- **`‖z‖_Q² = ‖Re z‖_Q² + ‖Im z‖_Q²`.** -/
theorem norm_sq_eq (z : QSpaceC E) :
    ‖z‖ ^ 2 = ‖QSpace.ofVec E (reV (toVec E z))‖ ^ 2 + ‖QSpace.ofVec E (imV (toVec E z))‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_eq, EnergyForm.star_dotProduct_QC, QSpace.norm_sq_eq,
    QSpace.norm_sq_eq]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  rfl

variable {F G : EnergyForm n}

/-- A complex matrix as an operator `QSpaceC E → QSpaceC F`. -/
noncomputable def opC (M : Matrix n n ℂ) : QSpaceC E →L[ℂ] QSpaceC F :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ofVec F (M *ᵥ toVec E x)
      map_add' := fun x y => mulVec_add M x y
      map_smul' := fun c x => mulVec_smul M c x }

theorem toVec_opC (M : Matrix n n ℂ) (x : QSpaceC E) :
    toVec F (opC (E := E) (F := F) M x) = M *ᵥ toVec E x := rfl

theorem opC_mul (M N : Matrix n n ℂ) :
    opC (E := E) (F := G) (M * N) = (opC (E := F) (F := G) M).comp (opC (E := E) (F := F) N) := by
  ext x : 1
  show (M * N) *ᵥ toVec E x = M *ᵥ (N *ᵥ toVec E x)
  rw [mulVec_mulVec]

theorem opC_one : opC (E := E) (F := E) (1 : Matrix n n ℂ) = ContinuousLinearMap.id ℂ _ := by
  ext x : 1
  show (1 : Matrix n n ℂ) *ᵥ toVec E x = toVec E x
  rw [one_mulVec]

theorem opC_add (M N : Matrix n n ℂ) :
    opC (E := E) (F := F) (M + N) = opC M + opC N := by
  ext x : 1
  show (M + N) *ᵥ toVec E x = M *ᵥ toVec E x + N *ᵥ toVec E x
  rw [add_mulVec]

theorem opC_zero : opC (E := E) (F := F) (0 : Matrix n n ℂ) = 0 := by
  ext x : 1
  show (0 : Matrix n n ℂ) *ᵥ toVec E x = 0
  rw [zero_mulVec]

theorem opC_injective : Function.Injective (opC (E := E) (F := F)) := by
  intro M N h
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact congrArg (toVec F) (DFunLike.congr_fun h (ofVec E x))

theorem opC_surjective : Function.Surjective (opC (E := E) (F := F)) := by
  intro T
  let L : (n → ℂ) →ₗ[ℂ] (n → ℂ) :=
    { toFun := fun v => toVec F (T (ofVec E v))
      map_add' := fun v w => T.map_add (ofVec E v) (ofVec E w)
      map_smul' := fun c v => T.map_smul c (ofVec E v) }
  refine ⟨LinearMap.toMatrix' L, ?_⟩
  ext x : 1
  show LinearMap.toMatrix' L *ᵥ toVec E x = T x
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

variable (E) in
/-- **Matrices are the operators on `QSpaceC E`**, as algebras. -/
noncomputable def opCAlg : Matrix n n ℂ ≃ₐ[ℂ] (QSpaceC E →L[ℂ] QSpaceC E) :=
  AlgEquiv.ofBijective
    { toFun := opC (E := E) (F := E)
      map_one' := opC_one
      map_mul' := fun M N => opC_mul M N
      map_zero' := opC_zero
      map_add' := opC_add
      commutes' := fun c => by
        ext x : 1
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        show (c • (1 : Matrix n n ℂ)) *ᵥ toVec E x = c • toVec E x
        rw [smul_mulVec, one_mulVec] }
    ⟨opC_injective, opC_surjective⟩

theorem opCAlg_apply (M : Matrix n n ℂ) : opCAlg E M = opC M := rfl

/-- **The spectrum of a matrix is the spectrum of its operator.** -/
theorem spectrum_opC (M : Matrix n n ℂ) :
    spectrum ℂ (opC (E := E) (F := E) M) = spectrum ℂ M :=
  AlgEquiv.spectrum_eq (opCAlg E) M

/-- **The adjoint of `opC M` is `opC (Q_E⁻¹ Mᴴ Q_F)`.** -/
theorem adjoint_opC (M : Matrix n n ℂ) :
    ContinuousLinearMap.adjoint (opC (E := E) (F := F) M) =
      opC (E := F) (F := E) (E.QC⁻¹ * Mᴴ * F.QC) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  set B := E.QC⁻¹ * Mᴴ * F.QC
  have hB : Bᴴ * E.QC = F.QC * M := by
    simp only [B, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose,
      EnergyForm.conjTranspose_QC, Matrix.mul_assoc, nonsing_inv_mul _ E.isUnit_det_QC,
      Matrix.mul_one]
  rw [inner_eq, inner_eq, toVec_opC, toVec_opC, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, hB]

/-! ### Real matrices -/

theorem reV_opC_cx (A : Matrix n n ℝ) (z : QSpaceC E) :
    reV (toVec F (opC (E := E) (F := F) (cx A) z)) = A *ᵥ reV (toVec E z) := by
  funext i
  simp [toVec_opC, reV, mulVec, dotProduct, Complex.re_sum]

theorem imV_opC_cx (A : Matrix n n ℝ) (z : QSpaceC E) :
    imV (toVec F (opC (E := E) (F := F) (cx A) z)) = A *ᵥ imV (toVec E z) := by
  funext i
  simp [toVec_opC, imV, mulVec, dotProduct, Complex.im_sum]

/-- **The complex energy norm of a real matrix is at most its real energy norm.** -/
theorem norm_opC_cx_le (A : Matrix n n ℝ) :
    ‖opC (E := E) (F := E) (cx A)‖ ≤ ‖QSpace.op (E := E) A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  set T := QSpace.op (E := E) A
  have sq : ∀ x : QSpace E, ‖T x‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖x‖ ^ 2 := fun x => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 2
  have key : ‖opC (E := E) (F := E) (cx A) z‖ ^ 2 ≤ (‖T‖ * ‖z‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq (opC _ z), norm_sq_eq z, reV_opC_cx, imV_opC_cx, mul_add]
    exact add_le_add (sq (QSpace.ofVec E (reV (toVec E z))))
      (sq (QSpace.ofVec E (imV (toVec E z))))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

theorem qAdj_cx (A : Matrix n n ℝ) : E.QC⁻¹ * (cx A)ᴴ * E.QC = cx (qAdj E.Q A) := by
  rw [conjTranspose_cx, EnergyForm.QC, ← cx_inv, qAdj, map_mul, map_mul]

/-- The operator adjoint of a real matrix is its `Q`-adjoint `Q⁻¹ Aᵀ Q`. -/
theorem star_opC_cx (A : Matrix n n ℝ) :
    star (opC (E := E) (F := E) (cx A)) = opC (cx (qAdj E.Q A)) := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_opC, qAdj_cx]

/-- **A `Q`-normal real matrix is a normal operator.** -/
theorem isStarNormal_opC_cx {A : Matrix n n ℝ} (hA : Commute (qAdj E.Q A) A) :
    IsStarNormal (opC (E := E) (F := E) (cx A)) := by
  constructor
  rw [star_opC_cx]
  exact (hA.map cx).map (opCAlg E)

/-- A `Q`-orthogonal matrix (`Uᵀ Q U = Q`) has `Q`-adjoint `U⁻¹`. -/
theorem qAdj_mul_self_of_orthogonal {U : Matrix n n ℝ} (hU : Uᵀ * E.Q * U = E.Q) :
    qAdj E.Q U * U = 1 := by
  have hQ : IsUnit E.Q.det := E.posDef.isUnit.map Matrix.detMonoidHom
  rw [qAdj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, nonsing_inv_mul _ hQ]

/-- **A `Q`-orthogonal real matrix is a unitary operator.** -/
theorem opC_cx_mem_unitary {U : Matrix n n ℝ} (hU : Uᵀ * E.Q * U = E.Q) :
    opC (E := E) (F := E) (cx U) ∈ unitary (QSpaceC E →L[ℂ] QSpaceC E) := by
  have h1 := qAdj_mul_self_of_orthogonal hU
  have h2 : U * qAdj E.Q U = 1 := mul_eq_one_comm.1 h1
  rw [Unitary.mem_iff, star_opC_cx]
  refine ⟨?_, ?_⟩
  · show opCAlg E (cx (qAdj E.Q U)) * opCAlg E (cx U) = 1
    rw [← map_mul, ← map_mul, h1, map_one, map_one]
  · show opCAlg E (cx U) * opCAlg E (cx (qAdj E.Q U)) = 1
    rw [← map_mul, ← map_mul, h2, map_one, map_one]

end QSpaceC

end CoSimFoundations
