/-
Sequential orders on a tree, for schemes of scalar stores (the paper, Proposition 5.10): the
link between `SimilarOrders` (products of commuting maps) and `InfoForm` (the one-step map of a
scheme with one held sample).

Every store advances by the same rule in every order of execution,
`x_i' = F i · x_i + Σ_j G i j · (sample of j)`. Let `E i` (`storeStep F G i`) replace the state of
store `i` by this update computed from the current states and leave the other states unchanged:
row `i` of `E i` is `F i e_i + G i ·`, the other rows are those of the identity. Then:

* `E i` and `E j` commute if `G i j = 0` and `G j i = 0` (`commute_storeStep`);
* `E i` is invertible if `F i ≠ 0` and `G i i = 0` (`isUnit_storeStep`);
* if the list `π` contains every store and is ordered by the stages, then the one-step map of
  the Gauss–Seidel scheme with these stages is the product `E π_N * ⋯ * E π_1`
  (`orderProd_storeStep_eq_infoStep`). Proof: by induction over the stores executed so far, the
  rows of the stores not yet executed are those of the identity and the rows of the executed
  stores satisfy the update with the new samples of the stores executed before
  (`orderProd_storeStep_rows`); for all stores this is the relation `(1 - N) X = K + M`.

Hence Proposition 5.10 for scalar stores: if the coupling graph is acyclic (a tree or a forest),
`G` vanishes off the graph and all `F i ≠ 0`, the one-step maps for any two orders of execution
(any two injective assignments of stages) are similar, `c X₁ c⁻¹ = X₂`
(`exists_units_conj_infoStep`), and have the same characteristic polynomial, hence the same
eigenvalues (`charpoly_infoStep_eq`). Not formalised: subsystems with several states.
-/
import CoSimFoundations.SimilarOrders
import CoSimFoundations.InfoForm
import Mathlib.Data.Finset.Sort

open Matrix

namespace CoSimFoundations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The map `E i` that executes store `i` alone: row `i` is `F i e_i + G i ·`, the other rows are
those of the identity. -/
def storeStep (F : ι → ℝ) (G : Matrix ι ι ℝ) (i : ι) : Matrix ι ι ℝ :=
  Matrix.of fun a b =>
    if a = i then F i * (1 : Matrix ι ι ℝ) i b + G i b else (1 : Matrix ι ι ℝ) a b

/-- Row `i` of `E i`. -/
theorem storeStep_apply_self (F : ι → ℝ) (G : Matrix ι ι ℝ) (i b : ι) :
    storeStep F G i i b = F i * (1 : Matrix ι ι ℝ) i b + G i b := by
  simp only [storeStep, of_apply, ↓reduceIte]

/-- The other rows of `E i`. -/
theorem storeStep_apply_of_ne (F : ι → ℝ) (G : Matrix ι ι ℝ) {i a : ι} (h : a ≠ i) (b : ι) :
    storeStep F G i a b = (1 : Matrix ι ι ℝ) a b := by
  simp only [storeStep, of_apply, ite_eq_right h]

/-- Executing store `i` replaces row `i` by the update. -/
theorem storeStep_mul_apply_self (F : ι → ℝ) (G : Matrix ι ι ℝ) (i : ι) (Y : Matrix ι ι ℝ)
    (b : ι) : (storeStep F G i * Y) i b = F i * Y i b + (G * Y) i b := by
  have h : ∀ c, storeStep F G i i c * Y c b =
      F i * ((1 : Matrix ι ι ℝ) i c * Y c b) + G i c * Y c b := fun c => by
    rw [storeStep_apply_self]
    ring
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_congr rfl fun c _ => h c,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Matrix.mul_apply, Matrix.one_mul]

/-- Executing store `i` leaves the other rows unchanged. -/
theorem storeStep_mul_apply_of_ne (F : ι → ℝ) (G : Matrix ι ι ℝ) {i a : ι} (h : a ≠ i)
    (Y : Matrix ι ι ℝ) (b : ι) : (storeStep F G i * Y) a b = Y a b := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [storeStep_apply_of_ne F G h],
    ← Matrix.mul_apply, Matrix.one_mul]

/-- A row that does not use store `i` is not changed by `E i` on the right. -/
theorem mul_storeStep_apply (F : ι → ℝ) (G : Matrix ι ι ℝ) {i a : ι} (A : Matrix ι ι ℝ)
    (h : A a i = 0) (b : ι) : (A * storeStep F G i) a b = A a b := by
  have hc : ∀ c, A a c * storeStep F G i c b = A a c * (1 : Matrix ι ι ℝ) c b := fun c => by
    by_cases hci : c = i
    · rw [hci, h, zero_mul, zero_mul]
    · rw [storeStep_apply_of_ne F G hci]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => hc c, ← Matrix.mul_apply, Matrix.mul_one]

/-- Executing `j` and then `i`, when store `i` does not use store `j`: both rows are replaced. -/
theorem storeStep_mul_storeStep_apply (F : ι → ℝ) (G : Matrix ι ι ℝ) {i j : ι} (hij : i ≠ j)
    (h : G i j = 0) (a b : ι) :
    (storeStep F G i * storeStep F G j) a b =
      if a = i then storeStep F G i i b else storeStep F G j a b := by
  by_cases hai : a = i
  · rw [ite_eq_left hai, hai, storeStep_mul_apply_self, storeStep_apply_of_ne F G hij,
      mul_storeStep_apply F G G h, storeStep_apply_self]
  · rw [ite_eq_right hai, storeStep_mul_apply_of_ne F G hai]

/-- **Stores that are not partners commute:** if `G i j = 0` and `G j i = 0`, then `E i` and
`E j` commute. -/
theorem commute_storeStep (F : ι → ℝ) (G : Matrix ι ι ℝ) {i j : ι} (hij : i ≠ j)
    (h1 : G i j = 0) (h2 : G j i = 0) : Commute (storeStep F G i) (storeStep F G j) := by
  ext a b
  rw [storeStep_mul_storeStep_apply F G hij h1, storeStep_mul_storeStep_apply F G hij.symm h2]
  by_cases hai : a = i
  · have haj : a ≠ j := fun h => hij (hai.symm.trans h)
    rw [ite_eq_left hai, ite_eq_right haj, hai]
  · rw [ite_eq_right hai]
    by_cases haj : a = j
    · rw [ite_eq_left haj, haj]
    · rw [ite_eq_right haj, storeStep_apply_of_ne F G hai, storeStep_apply_of_ne F G haj]

/-- **`E i` is invertible** if `F i ≠ 0` and `G i i = 0`. -/
theorem isUnit_storeStep (F : ι → ℝ) (G : Matrix ι ι ℝ) {i : ι} (hF : F i ≠ 0)
    (hG : G i i = 0) : IsUnit (storeStep F G i) := by
  have hmul : storeStep F G i *
      storeStep (fun k => (F k)⁻¹) (Matrix.of fun a b => -((F a)⁻¹ * G a b)) i = 1 := by
    ext a b
    by_cases hai : a = i
    · rw [hai, storeStep_mul_apply_self, mul_storeStep_apply _ _ G hG, storeStep_apply_self,
        of_apply]
      field_simp
      ring
    · rw [storeStep_mul_apply_of_ne F G hai, storeStep_apply_of_ne _ _ hai]
  have hdet : (storeStep F G i).det *
      (storeStep (fun k => (F k)⁻¹) (Matrix.of fun a b => -((F a)⁻¹ * G a b)) i).det = 1 := by
    rw [← det_mul, hmul, det_one]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.of_mul_eq_one _ hdet)

/-- **The rows of a partial execution.** For a list `l` of stores ordered by the stages, the
product `E l_k * ⋯ * E l_1` has the rows of the identity at the stores not in `l`, and at every
store `a` of `l` its row satisfies the update with the rows of the stores executed before. -/
theorem orderProd_storeStep_rows (stage : ι → ℕ) (F : ι → ℝ) (G : Matrix ι ι ℝ) (l : List ι) :
    l.Pairwise (fun i j => stage i < stage j) →
      (∀ a, a ∉ l → ∀ b, orderProd (storeStep F G) l a b = (1 : Matrix ι ι ℝ) a b) ∧
      ∀ a, a ∈ l → ∀ b, orderProd (storeStep F G) l a b = F a * (1 : Matrix ι ι ℝ) a b +
        ∑ j, G a j * (if j ∈ l ∧ stage j < stage a then orderProd (storeStep F G) l j b
          else (1 : Matrix ι ι ℝ) j b) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨fun a _ b => by rw [orderProd_nil], fun a ha => ?_⟩
    simp at ha
  | append_singleton l i ih =>
    intro hp
    rw [List.pairwise_append] at hp
    obtain ⟨hl, -, hli⟩ := hp
    have hlt : ∀ j ∈ l, stage j < stage i := fun j hj => hli j hj i (List.mem_singleton.2 rfl)
    have hi : i ∉ l := fun h => lt_irrefl _ (hlt i h)
    obtain ⟨ih1, ih2⟩ := ih hl
    have hY : orderProd (storeStep F G) (l ++ [i]) =
        storeStep F G i * orderProd (storeStep F G) l := by
      rw [orderProd_append, orderProd_cons, orderProd_nil, one_mul]
    rw [hY]
    generalize orderProd (storeStep F G) l = Y at ih1 ih2 ⊢
    have hne : ∀ a, a ≠ i → ∀ b, (storeStep F G i * Y) a b = Y a b := fun a ha b =>
      storeStep_mul_apply_of_ne F G ha Y b
    refine ⟨fun a ha b => ?_, fun a ha b => ?_⟩
    · have ha1 : a ∉ l := fun h => ha (List.mem_append_left _ h)
      have ha2 : a ≠ i := fun h => ha (List.mem_append_right _ (List.mem_singleton.2 h))
      rw [hne a ha2, ih1 a ha1]
    · by_cases hai : a = i
      · rw [hai, storeStep_mul_apply_self, ih1 i hi, Matrix.mul_apply]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j ∈ l
        · have hji : j ≠ i := by
            rintro rfl
            exact hi hj
          have hc : j ∈ l ++ [i] ∧ stage j < stage i := ⟨List.mem_append_left _ hj, hlt j hj⟩
          rw [ite_eq_left hc, hne j hji]
        · have hc : ¬ (j ∈ l ++ [i] ∧ stage j < stage i) := by
            rintro ⟨h1, h2⟩
            rcases List.mem_append.1 h1 with h | h
            · exact hj h
            · rw [List.mem_singleton.1 h] at h2
              exact lt_irrefl _ h2
          rw [ite_eq_right hc, ih1 j hj]
      · have hal : a ∈ l := by
          rcases List.mem_append.1 ha with h | h
          · exact h
          · exact absurd (List.mem_singleton.1 h) hai
        rw [hne a hai, ih2 a hal]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j ∈ l
        · have hji : j ≠ i := by
            rintro rfl
            exact hi hj
          by_cases hs : stage j < stage a
          · have hc1 : j ∈ l ∧ stage j < stage a := ⟨hj, hs⟩
            have hc2 : j ∈ l ++ [i] ∧ stage j < stage a := ⟨List.mem_append_left _ hj, hs⟩
            rw [ite_eq_left hc1, ite_eq_left hc2, hne j hji]
          · have hc1 : ¬ (j ∈ l ∧ stage j < stage a) := fun h => hs h.2
            have hc2 : ¬ (j ∈ l ++ [i] ∧ stage j < stage a) := fun h => hs h.2
            rw [ite_eq_right hc1, ite_eq_right hc2]
        · have hc1 : ¬ (j ∈ l ∧ stage j < stage a) := fun h => hj h.1
          have hc2 : ¬ (j ∈ l ++ [i] ∧ stage j < stage a) := by
            rintro ⟨h1, h2⟩
            rcases List.mem_append.1 h1 with h | h
            · exact hj h
            · rw [List.mem_singleton.1 h] at h2
              exact lt_asymm h2 (hlt a hal)
          rw [ite_eq_right hc1, ite_eq_right hc2]

/-- **The Gauss–Seidel one-step map is the product of the store maps** (the paper, proof of
Proposition 5.10): if the list `π` contains every store and is ordered by the stages, then
`X = E π_N * ⋯ * E π_1`. -/
theorem orderProd_storeStep_eq_infoStep (stage : ι → ℕ) (F : ι → ℝ) (G : Matrix ι ι ℝ)
    {π : List ι} (hπ : π.Pairwise (fun i j => stage i < stage j)) (hall : ∀ i, i ∈ π) :
    orderProd (storeStep F G) π = infoStep stage (diagonal F) G := by
  obtain ⟨-, h2⟩ := orderProd_storeStep_rows stage F G π hπ
  generalize orderProd (storeStep F G) π = Y at h2 ⊢
  rw [eq_infoStep_iff]
  ext a b
  have hs := sum_mul_sample stage G (fun j => Y j b) (fun j => (1 : Matrix ι ι ℝ) j b) a
  have h : Y a b = F a * (1 : Matrix ι ι ℝ) a b +
      ((infoNew stage G *ᵥ fun j => Y j b) a +
        (infoOld stage G *ᵥ fun j => (1 : Matrix ι ι ℝ) j b) a) := by
    rw [← hs, h2 a (hall a) b]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : stage j < stage a
    · have hc' : j ∈ π ∧ stage j < stage a := ⟨hall j, hc⟩
      rw [ite_eq_left hc', ite_eq_left hc]
    · have hc' : ¬ (j ∈ π ∧ stage j < stage a) := fun h => hc h.2
      rw [ite_eq_right hc', ite_eq_right hc]
  have e1 : (infoNew stage G *ᵥ fun j => Y j b) a = (infoNew stage G * Y) a b := rfl
  have e2 : (infoOld stage G *ᵥ fun j => (1 : Matrix ι ι ℝ) j b) a = infoOld stage G a b := by
    have e : (infoOld stage G *ᵥ fun j => (1 : Matrix ι ι ℝ) j b) a =
        (infoOld stage G * (1 : Matrix ι ι ℝ)) a b := rfl
    rw [e, Matrix.mul_one]
  have e3 : diagonal F a b = F a * (1 : Matrix ι ι ℝ) a b := by
    by_cases hab : a = b
    · rw [hab, diagonal_apply_eq, one_apply_eq, mul_one]
    · rw [diagonal_apply_ne _ hab, one_apply_ne hab, mul_zero]
  rw [e1, e2] at h
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.add_apply, e3]
  linarith

/-- Every injective assignment of stages is realised by a list of all stores ordered by the
stages. -/
theorem exists_list_pairwise_stage (stage : ι → ℕ) (hinj : Function.Injective stage) :
    ∃ π : List ι, π.Pairwise (fun i j => stage i < stage j) ∧ ∀ i, i ∈ π := by
  let _ : LinearOrder ι := LinearOrder.lift' stage hinj
  refine ⟨(Finset.univ : Finset ι).sort, ?_, fun i => by simp⟩
  exact (Finset.sortedLT_sort _).pairwise.imp fun h => h

/-- **Sequential orders on a tree, scalar stores** (the paper, Proposition 5.10). Let the coupling
graph `Gr` be acyclic (a tree or a forest), let the sample coefficients `G` vanish between stores
that are not partners, and let all local coefficients `F i` be nonzero. Then the one-step maps of
the Gauss–Seidel schemes for any two orders of execution (injective stages `s₁`, `s₂`) are
similar: `c X₁ c⁻¹ = X₂` with an invertible matrix `c`. -/
theorem exists_units_conj_infoStep {Gr : SimpleGraph ι} (hGr : Gr.IsAcyclic) (F : ι → ℝ)
    (hF : ∀ i, F i ≠ 0) (G : Matrix ι ι ℝ) (hG : ∀ i j, ¬ Gr.Adj i j → G i j = 0)
    {s₁ s₂ : ι → ℕ} (h₁ : Function.Injective s₁) (h₂ : Function.Injective s₂) :
    ∃ c : (Matrix ι ι ℝ)ˣ, (c : Matrix ι ι ℝ) * infoStep s₁ (diagonal F) G *
      ((c⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) = infoStep s₂ (diagonal F) G := by
  obtain ⟨π, hπ, hπall⟩ := exists_list_pairwise_stage s₁ h₁
  obtain ⟨ρ, hρ, hρall⟩ := exists_list_pairwise_stage s₂ h₂
  rw [← orderProd_storeStep_eq_infoStep s₁ F G hπ hπall,
    ← orderProd_storeStep_eq_infoStep s₂ F G hρ hρall]
  have hG0 : ∀ i, G i i = 0 := fun i => hG i i (Gr.irrefl)
  have hπnd : π.Nodup := hπ.imp fun h => by
    rintro rfl
    exact lt_irrefl _ h
  have hρnd : ρ.Nodup := hρ.imp fun h => by
    rintro rfl
    exact lt_irrefl _ h
  refine exists_units_conj_orderProd hGr (storeStep F G)
    (fun i => isUnit_storeStep F G (hF i) (hG0 i)) (fun i j hij => ?_) hπnd hρnd
    fun i => ⟨fun _ => hρall i, fun _ => hπall i⟩
  by_cases h : i = j
  · rw [h]
    exact Commute.refl _
  · exact commute_storeStep F G h (hG i j hij) (hG j i fun h' => hij h'.symm)

/-- **Sequential orders on a tree have the same eigenvalues** (the paper, Proposition 5.10): under
the hypotheses of `exists_units_conj_infoStep` the one-step maps for any two orders of execution
have the same characteristic polynomial. -/
theorem charpoly_infoStep_eq {Gr : SimpleGraph ι} (hGr : Gr.IsAcyclic) (F : ι → ℝ)
    (hF : ∀ i, F i ≠ 0) (G : Matrix ι ι ℝ) (hG : ∀ i j, ¬ Gr.Adj i j → G i j = 0)
    {s₁ s₂ : ι → ℕ} (h₁ : Function.Injective s₁) (h₂ : Function.Injective s₂) :
    (infoStep s₂ (diagonal F) G).charpoly = (infoStep s₁ (diagonal F) G).charpoly := by
  obtain ⟨c, hc⟩ := exists_units_conj_infoStep hGr F hF G hG h₁ h₂
  rw [← hc, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end CoSimFoundations
