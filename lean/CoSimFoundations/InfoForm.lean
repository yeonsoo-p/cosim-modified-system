/-
The one-step map of a scheme with one held sample (the paper, Definition 2.1, equations (4)
and (5); the determinant statement of Proposition 6.2).

A scheme with one held sample advances every store by a linear function of its own state and of
one sample of each partner: the new sample if the partner runs at an earlier stage, the old one
otherwise,

  `x_i' = (K x)_i + Σ_j G i j · (x_j' if stage j < stage i, else x_j)`.

Here `K` holds the local coefficients (`K = diagonal F` for scalar stores, block diagonal for
subsystems with several states) and `G` the coefficients of the partner samples (the outputs are
the states, as in `ScalarStores`; for output maps `C` put `G * C` in the place of `G`). With

  `N i j = G i j` if `stage j < stage i`, `0` otherwise   (`infoNew`: new samples),
  `M = G - N`                                           (`infoOld`: old samples),

the update reads `x' = K x + N x' + M x`, that is `(1 - N) X = K + M` for the one-step map `X`.

Statements.
* `1 - N` is invertible, with determinant `1`: its transpose is block triangular for the stages
  with identity diagonal blocks (`det_one_sub_infoNew`).
* The one-step map `X = (1 - N)⁻¹ (K + M)` (`infoStep`) is the only matrix with
  `(1 - N) X = K + M` (`eq_infoStep_iff`), and `X x` is the only vector that satisfies the update
  store by store (`eq_infoStep_mulVec_iff`, `infoStep_mulVec_apply`).
* Gauss–Seidel mode (`stage` injective on the subsystems, `G` zero inside the subsystems, `K` block
  diagonal): `det X = ∏ det K_a` (`det_infoStep_block`); for scalar stores `det X = ∏ F i`
  (`det_infoStep_gs`). Proof: in the order of the stages `K + M` is block upper triangular with the
  diagonal blocks of `K`.
  Hence, if `X = exp (H • Ã)` and all `F i > 0`: `H · tr Ã = Σ log (F i)`
  (`trace_modified_infoStep_gs`).
* With output maps `C` (block diagonal) and coefficients `G` on the outputs, the one-step map of
  the paper, `(1 - G^new C)⁻¹ (K + G^old C)`, is `infoStep` with `G * C` (`infoStep_mul_output`),
  and in Gauss–Seidel mode its determinant is `∏ det K_a` (`det_infoStep_output`).
* Jacobi mode (`stage` constant): `X = K + G` (`infoStep_jacobi`).
* The step matrices of `ScalarStores` and `GaussSeidel` are instances
  (`ScalarNet.jacobiStep_eq_infoStep`, `ScalarNet.gsStep_eq_infoStep`), and for scalar stores
  executed in their natural order output feedback realises every scheme of this form with positive
  local coefficients (`ScalarNet.exists_gsStep_eq_infoStep`).
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CoSimFoundations.GaussSeidelTwo

open Matrix

namespace CoSimFoundations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficients of the new samples: `G i j` if `j` runs at an earlier stage than `i`. -/
def infoNew (stage : ι → ℕ) (G : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if stage j < stage i then G i j else 0

/-- The coefficients of the old samples: `G i j` if `j` does not run at an earlier stage than
`i`. -/
def infoOld (stage : ι → ℕ) (G : Matrix ι ι ℝ) : Matrix ι ι ℝ := G - infoNew stage G

/-- The one-step map of the scheme with local coefficients `K` and sample coefficients `G`:
`X = (1 - N)⁻¹ (K + M)` (the paper, equation (5)). -/
noncomputable def infoStep (stage : ι → ℕ) (K G : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 - infoNew stage G)⁻¹ * (K + infoOld stage G)

/-- Entries of the matrix of the new samples. -/
theorem infoNew_apply (stage : ι → ℕ) (G : Matrix ι ι ℝ) (i j : ι) :
    infoNew stage G i j = if stage j < stage i then G i j else 0 := rfl

/-- Entries of the matrix of the old samples. -/
theorem infoOld_apply (stage : ι → ℕ) (G : Matrix ι ι ℝ) (i j : ι) :
    infoOld stage G i j = if stage j < stage i then 0 else G i j := by
  simp only [infoOld, Matrix.sub_apply, infoNew_apply]
  split_ifs <;> simp

/-- **`1 - N` is unipotent:** `det (1 - N) = 1` for every assignment of stages. -/
theorem det_one_sub_infoNew (stage : ι → ℕ) (G : Matrix ι ι ℝ) :
    (1 - infoNew stage G).det = 1 := by
  have hT : (1 - infoNew stage G)ᵀ.BlockTriangular stage := by
    intro i j hij
    have hne : j ≠ i := fun h => by
      subst h
      exact lt_irrefl _ hij
    simp [infoNew_apply, hne, hij.not_gt]
  rw [← det_transpose, hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have h1 : (1 - infoNew stage G)ᵀ.toSquareBlock stage a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toSquareBlock_def, infoNew_apply, Matrix.one_apply, hi, hj]
  rw [h1, det_one]

/-- **`1 - N` is invertible.** -/
theorem isUnit_det_one_sub_infoNew (stage : ι → ℕ) (G : Matrix ι ι ℝ) :
    IsUnit (1 - infoNew stage G).det := by
  rw [det_one_sub_infoNew]
  exact isUnit_one

/-- **The one-step map satisfies the relation of the scheme:** `(1 - N) X = K + M`. -/
theorem one_sub_infoNew_mul_infoStep (stage : ι → ℕ) (K G : Matrix ι ι ℝ) :
    (1 - infoNew stage G) * infoStep stage K G = K + infoOld stage G := by
  rw [infoStep, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_one_sub_infoNew stage G),
    Matrix.one_mul]

/-- **The one-step map is the only matrix that satisfies the relation of the scheme.** -/
theorem eq_infoStep_iff (stage : ι → ℕ) (K G X : Matrix ι ι ℝ) :
    X = infoStep stage K G ↔ (1 - infoNew stage G) * X = K + infoOld stage G := by
  constructor
  · rintro rfl
    exact one_sub_infoNew_mul_infoStep stage K G
  · intro h
    rw [infoStep, ← h, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_det_one_sub_infoNew stage G), Matrix.one_mul]

/-- The relation in the form of the update: `X = K + N X + M`. -/
theorem infoStep_eq_add (stage : ι → ℕ) (K G : Matrix ι ι ℝ) :
    infoStep stage K G = K + infoNew stage G * infoStep stage K G + infoOld stage G := by
  have h := one_sub_infoNew_mul_infoStep stage K G
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at h
  rw [add_right_comm]
  exact h

/-- The samples that store `i` uses, split into new and old ones. -/
theorem sum_mul_sample (stage : ι → ℕ) (G : Matrix ι ι ℝ) (a b : ι → ℝ) (i : ι) :
    ∑ j, G i j * (if stage j < stage i then a j else b j) =
      (infoNew stage G *ᵥ a) i + (infoOld stage G *ᵥ b) i := by
  simp only [mulVec, dotProduct, infoNew_apply, infoOld_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **The one-step map is the update, store by store.** A vector `x'` is `X x` if and only if every
store obeys `x_i' = (K x)_i + Σ_j G i j · (x_j' if j runs at an earlier stage than i, else x_j)`:
the update in the order of the stages has exactly one solution, and `X` gives it. -/
theorem eq_infoStep_mulVec_iff (stage : ι → ℕ) (K G : Matrix ι ι ℝ) (x x' : ι → ℝ) :
    x' = infoStep stage K G *ᵥ x ↔
      ∀ i, x' i = (K *ᵥ x) i + ∑ j, G i j * (if stage j < stage i then x' j else x j) := by
  have hu := isUnit_det_one_sub_infoNew stage G
  have key : (∀ i, x' i = (K *ᵥ x) i + ∑ j, G i j * (if stage j < stage i then x' j else x j)) ↔
      (1 - infoNew stage G) *ᵥ x' = (K + infoOld stage G) *ᵥ x := by
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    rw [sum_mul_sample, sub_mulVec, one_mulVec, add_mulVec]
    simp only [Pi.sub_apply, Pi.add_apply]
    constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · rintro rfl
    rw [mulVec_mulVec, one_sub_infoNew_mul_infoStep]
  · intro h
    have h2 := congrArg (fun v => (1 - infoNew stage G)⁻¹ *ᵥ v) h
    simp only [mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, one_mulVec] at h2
    rw [h2, infoStep]

/-- **The one-step map reproduces the update of every store** (general local coefficients). -/
theorem infoStep_mulVec_apply (stage : ι → ℕ) (K G : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    (infoStep stage K G *ᵥ x) i = (K *ᵥ x) i +
      ∑ j, G i j * (if stage j < stage i then (infoStep stage K G *ᵥ x) j else x j) :=
  (eq_infoStep_mulVec_iff stage K G x _).1 rfl i

/-- **The one-step map reproduces the update of every scalar store** (the paper, equation (4)):
`(X x)_i = F i · x_i + Σ_j G i j · ((X x)_j if j runs at an earlier stage than i, else x_j)`. -/
theorem infoStep_diagonal_mulVec_apply (stage : ι → ℕ) (F : ι → ℝ) (G : Matrix ι ι ℝ)
    (x : ι → ℝ) (i : ι) :
    (infoStep stage (diagonal F) G *ᵥ x) i = F i * x i +
      ∑ j, G i j * (if stage j < stage i then (infoStep stage (diagonal F) G *ᵥ x) j else x j) := by
  have h := infoStep_mulVec_apply stage (diagonal F) G x i
  rwa [mulVec_diagonal] at h

/-- The determinant of the one-step map is that of the old-sample factor, in every mode. -/
theorem det_infoStep (stage : ι → ℕ) (K G : Matrix ι ι ℝ) :
    (infoStep stage K G).det = (K + infoOld stage G).det := by
  have h := congrArg det (one_sub_infoNew_mul_infoStep stage K G)
  rwa [det_mul, det_one_sub_infoNew, one_mul] at h

/-- **Gauss–Seidel mode, subsystems with several states** (the paper, Proposition 6.2, first
sentence). The states `ι` are grouped into subsystems by `sub : ι → α`, the subsystems have
pairwise different stages, the local coefficients `K` are block diagonal and the sample
coefficients `G` vanish inside every subsystem. Then `det X = ∏_a det K_a`, whatever `G` is. -/
theorem det_infoStep_block {α : Type*} [Fintype α] [DecidableEq α] (sub : ι → α) (stage : α → ℕ)
    (hinj : Function.Injective stage) (K G : Matrix ι ι ℝ)
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0) (hG : ∀ i j, sub i = sub j → G i j = 0) :
    (infoStep (stage ∘ sub) K G).det = ∏ a, (K.toSquareBlock sub a).det := by
  let _ : LinearOrder α := LinearOrder.lift' stage hinj
  have hT : (K + infoOld (stage ∘ sub) G).BlockTriangular sub := by
    intro i j hij
    have hs : stage (sub j) < stage (sub i) := hij
    have hne : sub i ≠ sub j := fun h => by
      rw [h] at hs
      exact lt_irrefl _ hs
    simp [infoOld_apply, hK i j hne, hs]
  rw [det_infoStep, hT.det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp [toSquareBlock_def, infoOld_apply, hG i j (hi.trans hj.symm)]

/-- **Gauss–Seidel mode, scalar stores** (the paper, Proposition 6.2, first sentence): if the stages
are pairwise different and `G` has zero diagonal, then `det X = ∏ F i`, for every order of
execution and all coefficients `G`. -/
theorem det_infoStep_gs (stage : ι → ℕ) (hinj : Function.Injective stage) (F : ι → ℝ)
    (G : Matrix ι ι ℝ) (hG : ∀ i, G i i = 0) :
    (infoStep stage (diagonal F) G).det = ∏ i, F i := by
  have h := det_infoStep_block (sub := id) stage hinj (diagonal F) G
    (fun i j hij => diagonal_apply_ne _ hij) (fun i j hij => by
      have hij' : i = j := hij
      subst hij'
      exact hG i)
  rw [Function.comp_id] at h
  rw [h]
  exact Finset.prod_congr rfl fun i _ => by rw [det_toSquareBlock_id, diagonal_apply_eq]

open scoped Matrix.Norms.Operator in
/-- **Total damping in Gauss–Seidel mode** (the paper, Proposition 6.2, for scalar stores, every order
of execution and full access): if the one-step map has a modified system, `X = exp (H • Ã)`, and
the local coefficients are positive, then `H · tr Ã = Σ log (F i)`, whatever the sample
coefficients are. With `F i = e^{λ_i H}` this is `ScalarNet.trace_modified_gs`. -/
theorem trace_modified_infoStep_gs (stage : ι → ℕ) (hinj : Function.Injective stage) (F : ι → ℝ)
    (hF : ∀ i, 0 < F i) (G : Matrix ι ι ℝ) (hG : ∀ i, G i i = 0) (H : ℝ) (At : Matrix ι ι ℝ)
    (h : infoStep stage (diagonal F) G = NormedSpace.exp (H • At)) :
    H * At.trace = ∑ i, Real.log (F i) := by
  have h1 := det_infoStep_gs stage hinj F G hG
  rw [h, det_exp, trace_smul, smul_eq_mul] at h1
  rw [← Real.log_prod fun i _ => (hF i).ne', ← h1, Real.log_exp]

section Output

variable {κ α : Type*} [Fintype κ]

/-- The coefficients of the new output samples (the paper's `G^new`): `G i p` if the subsystem of
the output `p` runs at an earlier stage than the subsystem of the state `i`. Here `G` has one
column for every output variable, `sub` assigns the states and `subO` the outputs to the
subsystems. -/
def outNew (sub : ι → α) (subO : κ → α) (stage : α → ℕ) (G : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  Matrix.of fun i p => if stage (subO p) < stage (sub i) then G i p else 0

/-- With output maps `C` that are block diagonal (every output reads the states of its own
subsystem), the coefficients of the new samples in terms of the states are `G^new C`. -/
theorem infoNew_mul_output (sub : ι → α) (subO : κ → α) (stage : α → ℕ) (G : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (hC : ∀ p j, subO p ≠ sub j → C p j = 0) :
    infoNew (stage ∘ sub) (G * C) = outNew sub subO stage G * C := by
  ext i j
  simp only [infoNew_apply, Function.comp_apply, Matrix.mul_apply, outNew, of_apply]
  by_cases h : stage (sub j) < stage (sub i)
  · rw [ite_eq_left h]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : subO p = sub j
    · rw [hp, ite_eq_left h]
    · rw [hC p j hp, mul_zero, mul_zero]
  · rw [ite_eq_right h]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    by_cases hp : subO p = sub j
    · rw [hp, ite_eq_right h, zero_mul]
    · rw [hC p j hp, mul_zero]

/-- **The one-step map with output maps** (the paper, equation (5)):
`X = (1 - G^new C)⁻¹ (K + G^old C)`, `G^old = G - G^new`, is the one-step map `infoStep` with the
sample coefficients `G * C`. -/
theorem infoStep_mul_output (sub : ι → α) (subO : κ → α) (stage : α → ℕ) (K : Matrix ι ι ℝ)
    (G : Matrix ι κ ℝ) (C : Matrix κ ι ℝ) (hC : ∀ p j, subO p ≠ sub j → C p j = 0) :
    infoStep (stage ∘ sub) K (G * C) =
      (1 - outNew sub subO stage G * C)⁻¹ * (K + (G - outNew sub subO stage G) * C) := by
  rw [infoStep, infoOld, infoNew_mul_output sub subO stage G C hC, Matrix.sub_mul]

/-- **Gauss–Seidel mode with output maps** (the paper, Proposition 6.2, first sentence, in the form of
equation (5)): subsystems with pairwise different stages, `K` block diagonal, block diagonal output
maps `C`, and no coefficient on a subsystem's own outputs. Then
`det ((1 - G^new C)⁻¹ (K + G^old C)) = ∏_a det K_a`. -/
theorem det_infoStep_output [Fintype α] [DecidableEq α] (sub : ι → α) (subO : κ → α)
    (stage : α → ℕ) (hinj : Function.Injective stage) (K : Matrix ι ι ℝ) (G : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (hK : ∀ i j, sub i ≠ sub j → K i j = 0)
    (hG : ∀ i p, sub i = subO p → G i p = 0) (hC : ∀ p j, subO p ≠ sub j → C p j = 0) :
    ((1 - outNew sub subO stage G * C)⁻¹ * (K + (G - outNew sub subO stage G) * C)).det =
      ∏ a, (K.toSquareBlock sub a).det := by
  rw [← infoStep_mul_output sub subO stage K G C hC]
  refine det_infoStep_block sub stage hinj K (G * C) hK fun i j hij => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : subO p = sub j
  · rw [hG i p (hij.trans hp.symm), zero_mul]
  · rw [hC p j hp, mul_zero]

end Output

/-- In Jacobi mode no sample is new. -/
theorem infoNew_eq_zero_of_const (stage : ι → ℕ) (h : ∀ i j, stage i = stage j)
    (G : Matrix ι ι ℝ) : infoNew stage G = 0 := by
  ext i j
  simp [infoNew_apply, h j i]

/-- **Jacobi mode** (all stores at one stage): `X = K + G`; for scalar stores
`X = diagonal F + G`. -/
theorem infoStep_jacobi (stage : ι → ℕ) (h : ∀ i j, stage i = stage j) (K G : Matrix ι ι ℝ) :
    infoStep stage K G = K + G := by
  rw [infoStep, infoOld, infoNew_eq_zero_of_const stage h, sub_zero, sub_zero, inv_one,
    Matrix.one_mul]

namespace ScalarNet

variable {n : ℕ} (N : ScalarNet n)

/-- The sample coefficients of a scheme for scalar stores with weights `w` and gains `k`:
`G i j = γ_i · w i j · c_j` off the diagonal. -/
noncomputable def infoG (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then 0 else N.inGain H k i * w i j * N.c j

/-- **The Jacobi step matrix of `ScalarStores` is an instance:** stages constant,
`F i = e^{λ_i H}`. -/
theorem jacobiStep_eq_infoStep (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    N.jacobiStep H k w =
      infoStep (fun _ => 0) (diagonal fun i => Real.exp (N.rate k i * H)) (N.infoG H k w) := by
  rw [infoStep_jacobi _ (fun _ _ => rfl)]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [jacobiStep, infoG]
  · simp [jacobiStep, infoG, inGain, hij]

/-- **The Gauss–Seidel step matrix of `GaussSeidel` is an instance:** the stage of store `i` is
`i`, `F i = e^{λ_i H}`. Hence `ScalarNet.det_gsStep` is `det_infoStep_gs` for this order, and
`ScalarNet.gs_step_eq` derives the relation of this scheme from the differential equations. -/
theorem gsStep_eq_infoStep (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    N.gsStep H k w = infoStep (fun i : Fin n => (i : ℕ))
      (diagonal fun i => Real.exp (N.rate k i * H)) (N.infoG H k w) := by
  have h1 : N.gsLo H k w = 1 - infoNew (fun i : Fin n => (i : ℕ)) (N.infoG H k w) := by
    ext i j
    simp only [gsLo, Matrix.sub_apply, Matrix.one_apply, infoNew_apply, infoG, of_apply,
      Fin.val_fin_lt]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have h2 : N.gsR H k w = (diagonal fun i => Real.exp (N.rate k i * H)) +
      infoOld (fun i : Fin n => (i : ℕ)) (N.infoG H k w) := by
    ext i j
    simp only [gsR, Matrix.add_apply, infoOld_apply, infoG, of_apply, Fin.val_fin_lt]
    by_cases hij : i = j
    · subst hij
      simp
    · have h3 : ¬ j < i ↔ i < j := by
        rw [not_lt]
        exact ⟨fun h => lt_of_le_of_ne h hij, le_of_lt⟩
      by_cases hlt : i < j
      · simp [hij, hlt, hlt.not_gt]
      · simp [hij, hlt, not_not.1 (mt h3.1 hlt)]
  rw [gsStep, infoStep, h1, h2]

/-- **Output feedback realises every scheme of scalar stores with positive local coefficients**
(order of execution `0, 1, …, n-1`): for `F i > 0` and `G` with zero diagonal there are gains and
weights, the weights supported where `G` is, whose Gauss–Seidel step matrix is the one-step map
with the coefficients `F`, `G`. -/
theorem exists_gsStep_eq_infoStep {H : ℝ} (hH : 0 < H) (F : Fin n → ℝ) (hF : ∀ i, 0 < F i)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i, G i i = 0) :
    ∃ k w, (∀ i j, G i j = 0 → w i j = 0) ∧
      N.gsStep H k w = infoStep (fun i : Fin n => (i : ℕ)) (diagonal F) G := by
  choose k hk using fun i => N.exists_gain hH i (hF i)
  have hc : ∀ i, N.c i ≠ 0 := fun i => right_ne_zero_of_mul (N.hbc i)
  refine ⟨k, Matrix.of fun i j => G i j / (N.inGain H k i * N.c j), fun i j h => by simp [h], ?_⟩
  rw [gsStep_eq_infoStep]
  congr 1
  · congr 1
    funext i
    exact hk i
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [infoG, hG]
    · have h1 := N.inGain_ne_zero hH k i
      have h2 := hc j
      simp only [infoG, of_apply, hij, ite_false]
      field_simp

end ScalarNet

end CoSimFoundations
