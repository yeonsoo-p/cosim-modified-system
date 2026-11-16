/-
The eigenvalue equation of a sequential scheme on a tree (the paper, Section "Energy stored and
energy created", equation `eq:tree` and the paragraph around it): the eigenvalues `ξ` of the
one-step map `X = (1 - G^new C)⁻¹ (F + G^old C)` are the roots of `det(ξ - F - √ξ G C) = 0`, in
every sequential order.

**The scaling** (`det_scaled_eq_of_ne_zero`, `det_add_of_potential`, `det_scaled_eq`). Matrices
over a field, `N` the new samples, `M` the old samples, and a potential `q` of the states with
  `F i j = 0` unless `q i = q j`,   `N i j = 0` unless `q i = q j + 1`,
  `M i j = 0` unless `q j = q i + 1`.
Then for every `s`
  `det(s² (1 - N) - F - M) = det(s² - F - s (N + M))`.
Proof. For `s ≠ 0` let `D = diag(s^{q i})`. Entry by entry
`(s² (1 - N) - F - M) D = D (s² - F - s (N + M))`: an entry of `s² N` gets `s^{q j}` on the left
and `s^{q i} = s^{q j} s` on the right, an entry of `M` gets `s^{q j} = s^{q i} s` on the left;
`det D ≠ 0` cancels. For `s = 0` both sides are `det(-F)`: `-F - M` is block triangular in the
blocks of `q` with the diagonal blocks of `-F`.

**The one-step map** (`det_one_sub_of_potential`, `det_sq_sub_eq_of_potential`). `1 - N` is block
triangular with unit diagonal blocks, `det(1 - N) = 1`, and `(1 - N)(s² - X) = s² (1 - N) - F - M`
if `(1 - N) X = F + M`. Hence `det(s² - X) = det(s² - F - s (N + M))`.

**The potential on a forest** (`IsStagePotential`, `exists_stagePotential`). For a graph `Gr` on
the subsystems and stages `stage`, `p` is a potential if `p a = p b + 1` for every link `a b`
with `stage b < stage a`. On an acyclic graph with finitely many vertices every assignment of
stages has a potential. Proof: induction on the number of vertices of a finite set `t`; `t` has a
vertex `a` with at most one neighbour `b` in `t` (`exists_mem_adj_unique_of_isAcyclic`); take a
potential on `t` without `a` and set `p a = p b ± 1`.

**In the representation of `InfoForm`** (`det_sq_sub_infoStep_of_potential`,
`det_sq_sub_infoStep`, `aeval_sq_charpoly_infoStep`, `exists_eigenvector_infoStep_iff`,
`charpoly_infoStep_eq_of_isAcyclic`, `det_sq_sub_infoStep_one`). States `ι` grouped into
subsystems by `sub`, real matrices `K` (block diagonal, the paper's `F`) and `G` (the paper's
`G C`, zero unless the two subsystems are linked in `Gr`), `X = infoStep (stage ∘ sub) K G`, and
no link of `Gr` within a stage. Over every field `𝕜 ⊇ ℝ` (in particular `ℂ`) and for every
`s : 𝕜`, with a potential, hence on every acyclic `Gr`:
  `det(s² - X) = det(s² - K - s G)`,   `χ_X(s²) = det(s² - K - s G)`,
`s²` is an eigenvalue of `X` if and only if `det(s² - K - s G) = 0`, and the characteristic
polynomial of `X` is the same for any two assignments of stages without a link within a stage.
For `K = 1` and `s ≠ 0`: `det(s² - X) = s^n det((s - s⁻¹) - G)`.
-/
import CoSimFoundations.SimilarOrders
import CoSimFoundations.InfoForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix

namespace CoSimFoundations

/-! ### The scaling -/

section Scaling

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [Field 𝕜]

/-- **The scaling, `s ≠ 0`.** Let `q` be a potential of the states with `F i j = 0` unless
`q i = q j`, `N i j = 0` unless `q i = q j + 1` and `M i j = 0` unless `q j = q i + 1`. Then for
`s ≠ 0`: `det(s² (1 - N) - F - M) = det(s² - F - s (N + M))`. -/
theorem det_scaled_eq_of_ne_zero {F N M : Matrix ι ι 𝕜} (q : ι → ℤ)
    (hF : ∀ i j, q i ≠ q j → F i j = 0) (hN : ∀ i j, q i ≠ q j + 1 → N i j = 0)
    (hM : ∀ i j, q j ≠ q i + 1 → M i j = 0) {s : 𝕜} (hs : s ≠ 0) :
    (s ^ 2 • (1 - N) - F - M).det = (s ^ 2 • (1 : Matrix ι ι 𝕜) - F - s • (N + M)).det := by
  have hD : (diagonal fun i => s ^ q i : Matrix ι ι 𝕜).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hs
  have key : (s ^ 2 • (1 - N) - F - M) * (diagonal fun i => s ^ q i) =
      (diagonal fun i => s ^ q i) * (s ^ 2 • (1 : Matrix ι ι 𝕜) - F - s • (N + M)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    have e1 : (1 : Matrix ι ι 𝕜) i j * s ^ q j = s ^ q i * (1 : Matrix ι ι 𝕜) i j := by
      by_cases h : i = j
      · rw [h, mul_comm]
      · rw [Matrix.one_apply_ne h, zero_mul, mul_zero]
    have eF : F i j * s ^ q j = s ^ q i * F i j := by
      by_cases h : q i = q j
      · rw [h, mul_comm]
      · rw [hF i j h, zero_mul, mul_zero]
    have eN : s ^ 2 * N i j * s ^ q j = s ^ q i * (s * N i j) := by
      by_cases h : q i = q j + 1
      · rw [h, zpow_add_one₀ hs]
        ring
      · rw [hN i j h, mul_zero, mul_zero, zero_mul, mul_zero]
    have eM : M i j * s ^ q j = s ^ q i * (s * M i j) := by
      by_cases h : q j = q i + 1
      · rw [h, zpow_add_one₀ hs]
        ring
      · rw [hM i j h, mul_zero, zero_mul, mul_zero]
    linear_combination s ^ 2 * e1 - eN - eF - eM
  have h := congrArg Matrix.det key
  rw [det_mul, det_mul, mul_comm] at h
  exact mul_left_cancel₀ hD h

/-- **Old samples do not change the determinant:** if `F i j = 0` unless `q i = q j` and
`M i j = 0` unless `q j = q i + 1`, then `det(F + M) = det F` (`F + M` is block triangular in
the blocks of `q`, with the diagonal blocks of `F`). -/
theorem det_add_of_potential {F M : Matrix ι ι 𝕜} (q : ι → ℤ)
    (hF : ∀ i j, q i ≠ q j → F i j = 0) (hM : ∀ i j, q j ≠ q i + 1 → M i j = 0) :
    (F + M).det = F.det := by
  have h1 : (F + M).BlockTriangular q := fun i j hij => by
    rw [Matrix.add_apply, hF i j (by omega), hM i j (by omega), add_zero]
  have h2 : F.BlockTriangular q := fun i j hij => hF i j (by omega)
  rw [h1.det, h2.det]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.add_apply]
  rw [hM i.1 j.1 (by omega), add_zero]

/-- **The scaling, every `s`.** With a potential `q` as in `det_scaled_eq_of_ne_zero`,
`det(s² (1 - N) - F - M) = det(s² - F - s (N + M))` for every `s` (for `s = 0` both sides are
`det(-F)`). -/
theorem det_scaled_eq {F N M : Matrix ι ι 𝕜} (q : ι → ℤ)
    (hF : ∀ i j, q i ≠ q j → F i j = 0) (hN : ∀ i j, q i ≠ q j + 1 → N i j = 0)
    (hM : ∀ i j, q j ≠ q i + 1 → M i j = 0) (s : 𝕜) :
    (s ^ 2 • (1 - N) - F - M).det = (s ^ 2 • (1 : Matrix ι ι 𝕜) - F - s • (N + M)).det := by
  by_cases hs : s = 0
  · have h := det_add_of_potential (F := -F) (M := -M) q
      (fun i j h => by rw [Matrix.neg_apply, hF i j h, neg_zero])
      (fun i j h => by rw [Matrix.neg_apply, hM i j h, neg_zero])
    rw [hs, zero_pow two_ne_zero, zero_smul, zero_smul, zero_smul, zero_sub, sub_zero,
      sub_eq_add_neg]
    exact h
  · exact det_scaled_eq_of_ne_zero q hF hN hM hs

/-- **`1 - N` is unipotent:** if `N i j = 0` unless `q i = q j + 1`, then `det(1 - N) = 1`. -/
theorem det_one_sub_of_potential {N : Matrix ι ι 𝕜} (q : ι → ℤ)
    (hN : ∀ i j, q i ≠ q j + 1 → N i j = 0) : (1 - N).det = 1 := by
  have h := det_add_of_potential (F := (1 : Matrix ι ι 𝕜)) (M := -N) (fun i => -q i)
    (fun i j h => Matrix.one_apply_ne fun e => h (by rw [e]))
    (fun i j h => by rw [Matrix.neg_apply, hN i j (by omega), neg_zero])
  rw [← sub_eq_add_neg, det_one] at h
  exact h

/-- **The eigenvalue equation with a potential.** Let `(1 - N) X = F + M` and let `q` be a
potential of the states with `F i j = 0` unless `q i = q j`, `N i j = 0` unless `q i = q j + 1`
and `M i j = 0` unless `q j = q i + 1`. Then `det(s² - X) = det(s² - F - s (N + M))` for every
`s`. -/
theorem det_sq_sub_eq_of_potential {F N M X : Matrix ι ι 𝕜} (q : ι → ℤ)
    (hF : ∀ i j, q i ≠ q j → F i j = 0) (hN : ∀ i j, q i ≠ q j + 1 → N i j = 0)
    (hM : ∀ i j, q j ≠ q i + 1 → M i j = 0) (hX : (1 - N) * X = F + M) (s : 𝕜) :
    (s ^ 2 • (1 : Matrix ι ι 𝕜) - X).det =
      (s ^ 2 • (1 : Matrix ι ι 𝕜) - F - s • (N + M)).det := by
  have e : (1 - N) * (s ^ 2 • (1 : Matrix ι ι 𝕜) - X) = s ^ 2 • (1 - N) - F - M := by
    rw [mul_sub, hX, mul_smul_comm, mul_one, sub_sub]
  have h := congrArg Matrix.det e
  rw [det_mul, det_one_sub_of_potential q hN, one_mul] at h
  rw [h]
  exact det_scaled_eq q hF hN hM s

end Scaling

/-! ### The potential on a forest -/

section Potential

variable {α : Type*}

/-- **A potential of an assignment of stages on a coupling graph:** along every link, `p` is
larger by one at the end that runs later. -/
def IsStagePotential (Gr : SimpleGraph α) (stage : α → ℕ) (p : α → ℤ) : Prop :=
  ∀ a b, Gr.Adj a b → stage b < stage a → p a = p b + 1

/-- On every finite set of vertices of an acyclic graph, every assignment of stages has a
potential. -/
theorem exists_stagePotential_on {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic) (stage : α → ℕ)
    (t : Finset α) :
    ∃ p : α → ℤ, ∀ a ∈ t, ∀ b ∈ t, Gr.Adj a b → stage b < stage a → p a = p b + 1 := by
  classical
  suffices h : ∀ (k : ℕ) (t : Finset α), t.card = k →
      ∃ p : α → ℤ, ∀ a ∈ t, ∀ b ∈ t, Gr.Adj a b → stage b < stage a → p a = p b + 1 from
    h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [Finset.card_eq_zero] at ht
    exact ⟨fun _ => 0, fun a ha => by rw [ht] at ha; exact absurd ha (Finset.notMem_empty a)⟩
  | succ k ih =>
    intro t ht
    have hne : t.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨a, hat, hleaf⟩ := exists_mem_adj_unique_of_isAcyclic hGr t hne
    obtain ⟨p, hp⟩ := ih (t.erase a) (by rw [Finset.card_erase_of_mem hat, ht]; rfl)
    by_cases hnb : ∃ b ∈ t, Gr.Adj a b
    · obtain ⟨b, hbt, hab⟩ := hnb
      have hba : b ≠ a := fun h => Gr.irrefl (h ▸ hab)
      refine ⟨Function.update p a (if stage b < stage a then p b + 1 else p b - 1), ?_⟩
      intro x hx y hy hxy hst
      by_cases hxa : x = a
      · have hyb : y = b := hleaf y hy b hbt (hxa ▸ hxy) hab
        rw [hxa, hyb] at hst ⊢
        rw [Function.update_self, Function.update_of_ne hba, ite_eq_left hst]
      · by_cases hya : y = a
        · have hxb : x = b := hleaf x hx b hbt (hya ▸ hxy.symm) hab
          rw [hya, hxb] at hst ⊢
          rw [Function.update_of_ne hba, Function.update_self, ite_eq_right (by omega)]
          ring
        · rw [Function.update_of_ne hxa, Function.update_of_ne hya]
          exact hp x (Finset.mem_erase.2 ⟨hxa, hx⟩) y (Finset.mem_erase.2 ⟨hya, hy⟩) hxy hst
    · refine ⟨p, fun x hx y hy hxy hst => ?_⟩
      have hxa : x ≠ a := fun h => hnb ⟨y, hy, h ▸ hxy⟩
      have hya : y ≠ a := fun h => hnb ⟨x, hx, h ▸ hxy.symm⟩
      exact hp x (Finset.mem_erase.2 ⟨hxa, hx⟩) y (Finset.mem_erase.2 ⟨hya, hy⟩) hxy hst

/-- **On a tree such a scaling exists** (the paper, Section "Energy stored and energy created"): on
an acyclic coupling graph with finitely many subsystems every assignment of stages has a
potential. -/
theorem exists_stagePotential [Fintype α] {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic)
    (stage : α → ℕ) : ∃ p : α → ℤ, IsStagePotential Gr stage p := by
  obtain ⟨p, hp⟩ := exists_stagePotential_on hGr stage Finset.univ
  exact ⟨p, fun a b hab hst => hp a (Finset.mem_univ a) b (Finset.mem_univ b) hab hst⟩

end Potential

/-! ### The one-step map of `InfoForm` -/

section InfoStep

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜]

/-- **The eigenvalue equation of a sequential scheme, with a potential.** States `ι` grouped
into subsystems by `sub`, a graph `Gr` on the subsystems without a link within a stage, a
potential `p` of the stages, `K` block diagonal and `G` zero unless the two subsystems are
linked. Then over every field `𝕜 ⊇ ℝ` and for every `s : 𝕜`, the one-step map
`X = (1 - N)⁻¹ (K + M)` obeys `det(s² - X) = det(s² - K - s G)`. -/
theorem det_sq_sub_infoStep_of_potential {Gr : SimpleGraph α} (sub : ι → α) {stage : α → ℕ}
    {p : α → ℤ} (hp : IsStagePotential Gr stage p)
    (hseq : ∀ a b, Gr.Adj a b → stage a ≠ stage b) {K G : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0) (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0)
    (s : 𝕜) :
    (s ^ 2 • (1 : Matrix ι ι 𝕜) - (infoStep (stage ∘ sub) K G).map (algebraMap ℝ 𝕜)).det =
      (s ^ 2 • (1 : Matrix ι ι 𝕜) - K.map (algebraMap ℝ 𝕜) - s • G.map (algebraMap ℝ 𝕜)).det := by
  have hX := congrArg (algebraMap ℝ 𝕜).mapMatrix
    (one_sub_infoNew_mul_infoStep (stage ∘ sub) K G)
  simp only [map_mul, map_sub, map_add, map_one, RingHom.mapMatrix_apply] at hX
  have hsum : (infoNew (stage ∘ sub) G).map (algebraMap ℝ 𝕜) +
      (infoOld (stage ∘ sub) G).map (algebraMap ℝ 𝕜) = G.map (algebraMap ℝ 𝕜) := by
    ext i j
    rw [Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, ← map_add,
      infoOld, Matrix.sub_apply, add_sub_cancel]
  have hF' : ∀ i j, p (sub i) ≠ p (sub j) → (K.map (algebraMap ℝ 𝕜)) i j = 0 := fun i j h => by
    rw [Matrix.map_apply, hK i j fun e => h (by rw [e]), map_zero]
  have hN' : ∀ i j, p (sub i) ≠ p (sub j) + 1 →
      ((infoNew (stage ∘ sub) G).map (algebraMap ℝ 𝕜)) i j = 0 := fun i j h => by
    rw [Matrix.map_apply, infoNew_apply]
    by_cases hst : (stage ∘ sub) j < (stage ∘ sub) i
    · rw [ite_eq_left hst, hG i j fun hadj => h (hp _ _ hadj hst), map_zero]
    · rw [ite_eq_right hst, map_zero]
  have hM' : ∀ i j, p (sub j) ≠ p (sub i) + 1 →
      ((infoOld (stage ∘ sub) G).map (algebraMap ℝ 𝕜)) i j = 0 := fun i j h => by
    rw [Matrix.map_apply, infoOld_apply]
    by_cases hst : (stage ∘ sub) j < (stage ∘ sub) i
    · rw [ite_eq_left hst, map_zero]
    · rw [ite_eq_right hst, hG i j fun hadj => h (hp _ _ hadj.symm ?_), map_zero]
      have hne := hseq _ _ hadj
      simp only [Function.comp_apply] at hst
      omega
  rw [det_sq_sub_eq_of_potential (fun i => p (sub i)) hF' hN' hM' hX s, hsum]

/-- **The eigenvalue equation of a sequential scheme on a tree** (the paper, equation `eq:tree`).
States `ι` grouped into subsystems by `sub`, an acyclic coupling graph `Gr` on the subsystems,
stages without a link within a stage, `K` block diagonal and `G` zero unless the two subsystems
are linked. Then over every field `𝕜 ⊇ ℝ` and for every `s : 𝕜`, the one-step map
`X = (1 - N)⁻¹ (K + M)` obeys `det(s² - X) = det(s² - K - s G)`. -/
theorem det_sq_sub_infoStep [Fintype α] {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic) (sub : ι → α)
    {stage : α → ℕ} (hseq : ∀ a b, Gr.Adj a b → stage a ≠ stage b) {K G : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0) (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0)
    (s : 𝕜) :
    (s ^ 2 • (1 : Matrix ι ι 𝕜) - (infoStep (stage ∘ sub) K G).map (algebraMap ℝ 𝕜)).det =
      (s ^ 2 • (1 : Matrix ι ι 𝕜) - K.map (algebraMap ℝ 𝕜) - s • G.map (algebraMap ℝ 𝕜)).det := by
  obtain ⟨p, hp⟩ := exists_stagePotential hGr stage
  exact det_sq_sub_infoStep_of_potential sub hp hseq hK hG s

/-- The determinant `det(t - X)` over `𝕜` is the characteristic polynomial of the real matrix
`X` at `t`. -/
theorem aeval_charpoly_eq_det (X : Matrix ι ι ℝ) (t : 𝕜) :
    Polynomial.aeval t X.charpoly = (t • (1 : Matrix ι ι 𝕜) - X.map (algebraMap ℝ 𝕜)).det := by
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

/-- **The eigenvalues of a sequential scheme on a tree are the roots of
`det(ξ - K - √ξ G) = 0`, with their multiplicities** (the paper, equation `eq:tree`): under the
hypotheses of `det_sq_sub_infoStep`, the characteristic polynomial of the one-step map at `s²`
is `det(s² - K - s G)`, for every `s` in a field `𝕜 ⊇ ℝ`. -/
theorem aeval_sq_charpoly_infoStep [Fintype α] {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic)
    (sub : ι → α) {stage : α → ℕ} (hseq : ∀ a b, Gr.Adj a b → stage a ≠ stage b)
    {K G : Matrix ι ι ℝ} (hK : ∀ i j, sub i ≠ sub j → K i j = 0)
    (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0) (s : 𝕜) :
    Polynomial.aeval (s ^ 2) (infoStep (stage ∘ sub) K G).charpoly =
      (s ^ 2 • (1 : Matrix ι ι 𝕜) - K.map (algebraMap ℝ 𝕜) - s • G.map (algebraMap ℝ 𝕜)).det := by
  rw [aeval_charpoly_eq_det]
  exact det_sq_sub_infoStep hGr sub hseq hK hG s

/-- **`s²` is an eigenvalue of the one-step map if and only if `det(s² - K - s G) = 0`** (the paper,
equation `eq:tree`): under the hypotheses of `det_sq_sub_infoStep`, for every `s` in a field
`𝕜 ⊇ ℝ`, there is `v ≠ 0` with `X v = s² v` if and only if `det(s² - K - s G) = 0`. -/
theorem exists_eigenvector_infoStep_iff [Fintype α] {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic)
    (sub : ι → α) {stage : α → ℕ} (hseq : ∀ a b, Gr.Adj a b → stage a ≠ stage b)
    {K G : Matrix ι ι ℝ} (hK : ∀ i j, sub i ≠ sub j → K i j = 0)
    (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0) (s : 𝕜) :
    (∃ v : ι → 𝕜, v ≠ 0 ∧
        (infoStep (stage ∘ sub) K G).map (algebraMap ℝ 𝕜) *ᵥ v = s ^ 2 • v) ↔
      (s ^ 2 • (1 : Matrix ι ι 𝕜) - K.map (algebraMap ℝ 𝕜) -
        s • G.map (algebraMap ℝ 𝕜)).det = 0 := by
  rw [← det_sq_sub_infoStep hGr sub hseq hK hG s, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]

/-- Two real matrices with `det(s² - X₁) = det(s² - X₂)` for every complex `s` have the same
characteristic polynomial. -/
theorem charpoly_eq_of_det_sq_sub_eq {X₁ X₂ : Matrix ι ι ℝ}
    (h : ∀ s : ℂ, (s ^ 2 • (1 : Matrix ι ι ℂ) - X₁.map (algebraMap ℝ ℂ)).det =
      (s ^ 2 • (1 : Matrix ι ι ℂ) - X₂.map (algebraMap ℝ ℂ)).det) :
    X₁.charpoly = X₂.charpoly := by
  refine Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective ?_
  refine Polynomial.funext fun r => ?_
  obtain ⟨s, rfl⟩ := IsAlgClosed.exists_pow_nat_eq r (n := 2) zero_lt_two
  rw [Polynomial.eval_map, Polynomial.eval_map, ← Polynomial.aeval_def, ← Polynomial.aeval_def,
    aeval_charpoly_eq_det, aeval_charpoly_eq_det]
  exact h s

/-- **On a tree the order of execution of a sequential scheme changes no eigenvalue** (the paper,
Section "Energy stored and energy created"). States `ι` grouped into subsystems by `sub`, an
acyclic coupling graph `Gr` on the subsystems, `K` block diagonal and `G` zero unless the two
subsystems are linked, the same `K` and `G` in both orders. For any two assignments of stages
without a link within a stage the one-step maps have the same characteristic polynomial. -/
theorem charpoly_infoStep_eq_of_isAcyclic [Fintype α] {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic)
    (sub : ι → α) {K G : Matrix ι ι ℝ} (hK : ∀ i j, sub i ≠ sub j → K i j = 0)
    (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0) {st₁ st₂ : α → ℕ}
    (h₁ : ∀ a b, Gr.Adj a b → st₁ a ≠ st₁ b) (h₂ : ∀ a b, Gr.Adj a b → st₂ a ≠ st₂ b) :
    (infoStep (st₁ ∘ sub) K G).charpoly = (infoStep (st₂ ∘ sub) K G).charpoly :=
  charpoly_eq_of_det_sq_sub_eq fun s => by
    rw [det_sq_sub_infoStep hGr sub h₁ hK hG s, det_sq_sub_infoStep hGr sub h₂ hK hG s]

/-- **Subsystems without dynamics of their own** (the paper, after equation `eq:tree`): for `K = 1`
and `s ≠ 0`, under the hypotheses of `det_sq_sub_infoStep`,
`det(s² - X) = s^n det((s - s⁻¹) - G)`: `s²` is an eigenvalue of the one-step map exactly if
`s - 1/s` is an eigenvalue of `G`. -/
theorem det_sq_sub_infoStep_one [Fintype α] {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic)
    (sub : ι → α) {stage : α → ℕ} (hseq : ∀ a b, Gr.Adj a b → stage a ≠ stage b)
    {G : Matrix ι ι ℝ} (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0) {s : 𝕜}
    (hs : s ≠ 0) :
    (s ^ 2 • (1 : Matrix ι ι 𝕜) - (infoStep (stage ∘ sub) 1 G).map (algebraMap ℝ 𝕜)).det =
      s ^ Fintype.card ι *
        ((s - s⁻¹) • (1 : Matrix ι ι 𝕜) - G.map (algebraMap ℝ 𝕜)).det := by
  have h := det_sq_sub_infoStep (𝕜 := 𝕜) (K := (1 : Matrix ι ι ℝ)) hGr sub hseq
    (fun i j hij => Matrix.one_apply_ne fun e => hij (congrArg sub e)) hG s
  have e : s ^ 2 • (1 : Matrix ι ι 𝕜) - (1 : Matrix ι ι ℝ).map (algebraMap ℝ 𝕜) -
      s • G.map (algebraMap ℝ 𝕜) =
      s • ((s - s⁻¹) • (1 : Matrix ι ι 𝕜) - G.map (algebraMap ℝ 𝕜)) := by
    have h1 : s * (s - s⁻¹) = s ^ 2 - 1 := by
      field_simp
    rw [Matrix.map_one _ (map_zero _) (map_one _), smul_sub, smul_smul, h1, sub_smul, one_smul]
  rw [h, e, det_smul]

end InfoStep

end CoSimFoundations
