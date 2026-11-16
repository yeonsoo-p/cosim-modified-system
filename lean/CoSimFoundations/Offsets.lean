/-
Offsets of the subsystems ("staggered clocks"; the paper, Sections `sec:half` and "Energy
stored and energy created": the signed coupling as a
commutator and on the eigenvalue equation `eq:tree`).

**Offsets.** `S.IsOffset q`: real numbers `q_s` with `q_s - q_t = ς_st` for every pair of
partners `s ≠ t`. `S.IsStageOffset p`: integers `p_s` such that every pair of partners runs at
different stages and `p` is larger by one at the partner that runs later (the hypothesis of
`det_sq_sub_X_of_potential`; the stage potential of `TreeDeterminant` on the partners). An
integer stage offset is an offset (`IsStageOffset.isOffset`); it exists if the partners are
linked in an acyclic graph and no two partners share a stage (`exists_isStageOffset`); in a
reversed assignment of stages `-p` is one (`IsStageOffset.restage`).

**(a) The signed coupling is a commutator** (`signedCoupling_eq_commutator`). With
`P = diag(q_{sub r})` (`offsetP`) and `A` without blocks between subsystems that are not
partners: `A_ς = P A - A P`. No hypothesis on the ports.

**(d) Left and right eigenvectors** (`dotProduct_commutator_eq_zero`,
`dotProduct_signedCoupling_eq_zero`). If `wᵀ A = μ wᵀ` and `A v = μ v` (over a field `𝕜 ⊇ ℝ`;
`w` is the row vector `w^*` of the paper), then `wᵀ A_ς v = wᵀ (P A - A P) v = (μ - μ) wᵀ P v = 0`.

**The eigenvalue equation with offsets alone** (`det_sq_sub_zoh_X_of_offset`,
`exists_eigenvector_X_iff_of_offset`, `charpoly_zoh_restage_eq_of_offset`). The paper's
`det(ξ - F - √ξ G C) = 0` for a scheme with one held sample needs only a stage offset, no
acyclic graph: `det_sq_sub_X_of_potential` of `TreeDeterminantScheme` is that statement
(`det(s² - X) = det(s² - F - s (N + M))`); here it is restated with the predicate
(`det_sq_sub_X_of_offset`), for the zero-order hold, as an equivalence for eigenvectors, and as
the equality of the characteristic polynomials of the zero-order holds in two assignments of
stages that both have a stage offset.

**(c) `X(H)` and `X(-H)⁻¹` have the same characteristic polynomial**
(`charpoly_zoh_eq_charpoly_inv_neg`), for the zero-order hold with a stage offset: `X(-H)⁻¹` is
the one-step map in the reversed order (`zoh_reversed_eq_inv`), whose offset is `-p`.
-/
import CoSimFoundations.TreeDeterminantScheme
import CoSimFoundations.ReversedAdjoint

open Matrix

namespace CoSimFoundations

/-- **A commutator between a left and a right eigenvector to one eigenvalue vanishes:** if
`wᵀ A = μ wᵀ` and `A v = μ v`, then `wᵀ (P A - A P) v = 0` for every matrix `P`. -/
theorem dotProduct_commutator_eq_zero {R : Type*} [CommRing R] {m : Type*} [Fintype m]
    (A P : Matrix m m R) {w v : m → R} {μ : R} (hw : w ᵥ* A = μ • w) (hv : A *ᵥ v = μ • v) :
    w ⬝ᵥ ((P * A - A * P) *ᵥ v) = 0 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, dotProduct_smul, Matrix.dotProduct_mulVec w A, hw, smul_dotProduct,
    sub_self]

namespace HeldScheme

variable {n : ℕ} {κ : Type*} (S : HeldScheme n κ)

/-! ### Offsets -/

/-- **Offsets of the subsystems:** `q_s - q_t = ς_st` for every pair of partners `s ≠ t`
(`ς_st = +1` if `t` runs at an earlier stage than `s`, else `-1`). -/
def IsOffset (q : κ → ℝ) : Prop := ∀ s t, s ≠ t → S.partner s t → q s - q t = S.sg s t

/-- **A stage offset:** integers `p_s` such that every pair of partners runs at different stages
and `p` is larger by one at the partner that runs later. -/
def IsStageOffset (p : κ → ℤ) : Prop :=
  ∀ s t, S.partner s t → (S.stage t < S.stage s ∧ p s = p t + 1) ∨
    (S.stage s < S.stage t ∧ p t = p s + 1)

variable {S}

/-- A stage offset is an offset. -/
theorem IsStageOffset.isOffset {p : κ → ℤ} (hp : S.IsStageOffset p) :
    S.IsOffset fun s => (p s : ℝ) := by
  intro s t _ hst
  rcases hp s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · show ((p s : ℤ) : ℝ) - ((p t : ℤ) : ℝ) = S.sg s t
    rw [sg, ite_eq_left h1, h2]
    push_cast
    ring
  · show ((p s : ℤ) : ℝ) - ((p t : ℤ) : ℝ) = S.sg s t
    rw [sg, ite_eq_right (lt_asymm h1), h2]
    push_cast
    ring

/-- With a stage offset, partners run at different stages. -/
theorem IsStageOffset.stage_ne {p : κ → ℤ} (hp : S.IsStageOffset p) {s t : κ}
    (h : S.partner s t) : S.stage s ≠ S.stage t := by
  rcases hp s t h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1.ne'
  · exact h1.ne

/-- In a reversed assignment of stages, `-p` is a stage offset. -/
theorem IsStageOffset.restage {p : κ → ℤ} (hp : S.IsStageOffset p) {st : κ → ℕ}
    (hrev : S.Reversed st) : (S.restage st).IsStageOffset fun s => -p s := by
  intro s t hst
  rcases hp s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨(hrev s t).2 h1, show -p t = -p s + 1 by omega⟩
  · exact Or.inl ⟨(hrev t s).2 h1, show -p s = -p t + 1 by omega⟩

variable (S)

/-- **Stage offsets exist on a tree:** if the partners are linked in an acyclic graph on
finitely many subsystems and no two partners share a stage, there is a stage offset. -/
theorem exists_isStageOffset [Fintype κ] {Gr : SimpleGraph κ} (hGr : Gr.IsAcyclic)
    (hpart : ∀ s t, S.partner s t → Gr.Adj s t)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t) :
    ∃ p : κ → ℤ, S.IsStageOffset p := by
  obtain ⟨p, hp⟩ := exists_stagePotential hGr S.stage
  refine ⟨p, fun a b hab => ?_⟩
  have hadj := hpart a b hab
  have hne := hns a b (Gr.ne_of_adj hadj) hab
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr ⟨h, hp b a hadj.symm h⟩
  · exact Or.inl ⟨h, hp a b hadj h⟩

/-- The block-diagonal matrix of the offsets: `q_s` on the states of subsystem `s`. -/
def offsetP (q : κ → ℝ) : Matrix (Fin n) (Fin n) ℝ := diagonal fun r => q (S.sub r)

/-! ### The eigenvalue equation with a stage offset -/

section Field

variable {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜]

/-- **The eigenvalue equation of a scheme with one held sample, with a stage offset** (the paper,
equation `eq:tree`, without a hypothesis on the coupling graph): over every field `𝕜 ⊇ ℝ` and
for every `s : 𝕜`, `det(s² - X) = det(s² - F - s (N + M))`. This is
`det_sq_sub_X_of_potential`. -/
theorem det_sq_sub_X_of_offset {p : κ → ℤ} (hp : S.IsStageOffset p) (s : 𝕜) :
    (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.X.map (algebraMap ℝ 𝕜)).det =
      (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.F.map (algebraMap ℝ 𝕜) -
        s • (S.N + S.M).map (algebraMap ℝ 𝕜)).det :=
  S.det_sq_sub_X_of_potential p hp s

/-- **`s²` is an eigenvalue of the one-step map if and only if `det(s² - F - s (N + M)) = 0`**
(the paper, equation `eq:tree`), for a scheme with a stage offset and every `s` in a field
`𝕜 ⊇ ℝ`. -/
theorem exists_eigenvector_X_iff_of_offset {p : κ → ℤ} (hp : S.IsStageOffset p) (s : 𝕜) :
    (∃ v : Fin n → 𝕜, v ≠ 0 ∧ S.X.map (algebraMap ℝ 𝕜) *ᵥ v = s ^ 2 • v) ↔
      (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.F.map (algebraMap ℝ 𝕜) -
        s • (S.N + S.M).map (algebraMap ℝ 𝕜)).det = 0 := by
  rw [← S.det_sq_sub_X_of_offset hp s, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]

end Field

variable [DecidableEq κ]

/-- **The eigenvalue equation of the zero-order hold, with a stage offset** (the paper, equation
`eq:tree`): over every field `𝕜 ⊇ ℝ` and for every `s : 𝕜`,
`det(s² - X) = det(s² - e^{H A₀} - s G° C)`, `G° C = (∫₀ᴴ e^{τ A₀} dτ) A_c`. -/
theorem det_sq_sub_zoh_X_of_offset {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜] {p : κ → ℤ}
    (hp : S.IsStageOffset p) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (s : 𝕜) :
    (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - (S.zoh A hA H).X.map (algebraMap ℝ 𝕜)).det =
      (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) -
        (NormedSpace.exp (H • S.blockDiag A)).map (algebraMap ℝ 𝕜) -
        s • (S.zohCoupling A H).map (algebraMap ℝ 𝕜)).det := by
  have h := (S.zoh A hA H).det_sq_sub_X_of_potential (𝕜 := 𝕜) p hp s
  rw [add_comm, S.zoh_M_add_N] at h
  exact h

/-- **Two orders with stage offsets have the same eigenvalues** (the paper, Section "Energy stored
and energy created"): if the stages of `S` and the stages `st` both have a stage offset, the
one-step maps of the zero-order hold in the two assignments have the same characteristic
polynomial, for every macro step `H`. -/
theorem charpoly_zoh_restage_eq_of_offset {p p' : κ → ℤ} (hp : S.IsStageOffset p)
    {st : κ → ℕ} (hp' : (S.restage st).IsStageOffset p') {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    ((S.restage st).zoh A hA H).X.charpoly = (S.zoh A hA H).X.charpoly :=
  charpoly_eq_of_det_sq_sub_eq fun s => by
    rw [(S.restage st).det_sq_sub_zoh_X_of_offset hp' hA H s,
      S.det_sq_sub_zoh_X_of_offset hp hA H s]
    rfl

/-- **`X(H)` and `X(-H)⁻¹` have the same characteristic polynomial:** for the zero-order hold of
finitely many subsystems with a stage offset, the one-step map with the macro step `H` and the
inverse of the one-step map with the macro step `-H` (the one-step map in the reversed order,
`zoh_reversed_eq_inv`) have the same eigenvalues with the same multiplicities. -/
theorem charpoly_zoh_eq_charpoly_inv_neg [Fintype κ] {p : κ → ℤ} (hp : S.IsStageOffset p)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (S.zoh A hA H).X.charpoly = ((S.zoh A hA (-H)).X)⁻¹.charpoly := by
  have hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t :=
    fun s t _ h => hp.stage_ne h
  have hrev := S.reversed_revStage_sup
  rw [← S.zoh_reversed_eq_inv hA hns hrev H]
  exact (S.charpoly_zoh_restage_eq_of_offset hp (hp.restage hrev) hA H).symm

/-! ### The signed coupling as a commutator -/

/-- **The signed coupling is the commutator with the offsets:** if `q` is an offset and `A` has
no block between subsystems that are not partners, `A_ς = P A - A P` with `P = diag(q)`
(`offsetP`). No hypothesis on the ports. -/
theorem signedCoupling_eq_commutator {q : κ → ℝ} (hq : S.IsOffset q)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) :
    S.signedCoupling A = S.offsetP q * A - A * S.offsetP q := by
  ext r c
  rw [S.signedCoupling_apply, Matrix.sub_apply, offsetP, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases h : S.sub r = S.sub c
  · rw [ite_eq_left h, h]
    ring
  · rw [ite_eq_right h]
    by_cases hpc : S.partner (S.sub r) (S.sub c)
    · rw [← hq _ _ h hpc]
      ring
    · rw [hA r c h hpc]
      ring

/-- **A left and a right eigenvector of the monolithic system to one eigenvalue do not see the
signed coupling** (the first-order term of `eq:mode` vanishes): if `q` is an offset, `A` has no
block between subsystems that are not partners, `wᵀ A = μ wᵀ` and `A v = μ v` over a field
`𝕜 ⊇ ℝ` (`w` the row vector `w^*`), then `wᵀ A_ς v = 0`. -/
theorem dotProduct_signedCoupling_eq_zero {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜] {q : κ → ℝ}
    (hq : S.IsOffset q) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {w v : Fin n → 𝕜} {μ : 𝕜} (hw : w ᵥ* A.map (algebraMap ℝ 𝕜) = μ • w)
    (hv : A.map (algebraMap ℝ 𝕜) *ᵥ v = μ • v) :
    w ⬝ᵥ ((S.signedCoupling A).map (algebraMap ℝ 𝕜) *ᵥ v) = 0 := by
  have h := congrArg (algebraMap ℝ 𝕜).mapMatrix (S.signedCoupling_eq_commutator hq hA)
  simp only [map_sub, map_mul, RingHom.mapMatrix_apply] at h
  rw [h]
  exact dotProduct_commutator_eq_zero _ _ hw hv

/-- The real form: for real `w`, `v`, `μ` with `wᵀ A = μ wᵀ` and `A v = μ v`, `wᵀ A_ς v = 0`. -/
theorem dotProduct_signedCoupling_eq_zero_real {q : κ → ℝ} (hq : S.IsOffset q)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {w v : Fin n → ℝ} {μ : ℝ} (hw : w ᵥ* A = μ • w) (hv : A *ᵥ v = μ • v) :
    w ⬝ᵥ (S.signedCoupling A *ᵥ v) = 0 := by
  rw [S.signedCoupling_eq_commutator hq hA]
  exact dotProduct_commutator_eq_zero _ _ hw hv

end HeldScheme

end CoSimFoundations
