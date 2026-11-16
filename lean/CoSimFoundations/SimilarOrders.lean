/-
Sequential orders on a tree (the paper, Proposition 5.10): the one-step maps of all
Gauss–Seidel schemes are similar.

Setting. `E i` (`i : ι`) are elements of a monoid, in the paper the maps that replace the state of
subsystem `i` by its update, and `G` is a simple graph on `ι` (the coupling graph) such that `E i`
and `E j` commute whenever `i` and `j` are not adjacent. For a list `π` of indices,

  `orderProd E π = E π_N * ⋯ * E π_2 * E π_1`

is the map of the scheme that executes the subsystems in the order `π` (the first entry of the
list runs first and is the rightmost factor).

Statements.
(a) Exchanging two consecutive entries that commute does not change the product
    (`orderProd_swap`).
(b) Moving the first entry to the end conjugates the product by that entry:
    `E i * X_(i :: l) = X_(l ++ [i]) * E i` (`orderProd_rotate`, in a group
    `isConj_orderProd_rotate`).
(c) If `G` is acyclic (a forest; in particular a tree, or a chain, `isConj_orderProd_chain`) and
    the `E i` lie in a group, then `X_π` and `X_ρ` are conjugate for any two lists `π`, `ρ` without
    repetitions and with the same entries, in particular for any two orderings of all indices
    (`isConj_orderProd_of_isAcyclic`). For invertible elements of a monoid, for example invertible
    matrices: `c X_π c⁻¹ = X_ρ` with a unit `c` (`exists_units_conj_orderProd`), and for matrices
    the characteristic polynomials and the determinants agree (`charpoly_orderProd_eq`,
    `det_orderProd_eq`).

Proof of (c). The paper argues with orientations of the links and reversals at sources and sinks.
The proof here uses the same two moves (a) and (b) but is organised as Bourbaki's proof that the
Coxeter elements of a forest are conjugate (Lie groups and Lie algebras, Ch. V, §6, Lemma 1),
which needs no orientations. Induction on the number of entries. Every finite set of vertices of
an acyclic graph contains a vertex `a` with at most one neighbour in the set
(`exists_mem_adj_unique_of_isAcyclic`: the end of a longest path of the induced graph). Let `b` be
that neighbour, or any other entry if there is none. `E a` commutes with every entry except `b`.
If `a` runs after `b`, move it down next to `b` by exchanges (a). If it runs before `b`, move it
to the first place by exchanges, to the last place by (b), and down next to `b` by exchanges. In
both cases `X_π` is conjugate to the product for the order `π` without `a`, in which `E b` is
replaced by the element for "`b`, then `a`" (`isConj_prod_merge`). The new family again commutes
off the graph, because every entry other than `b` commutes with `E a`. The induction hypothesis
for the two shorter lists finishes the proof (`isConj_prod_map_of_perm`).

Not formalised here: the identification of the Gauss–Seidel one-step map of `InfoForm` for the
order `π` with `orderProd E π`, and that `E i` and `E j` commute for subsystems that are not
partners.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace CoSimFoundations

variable {ι : Type*}

section Monoid

variable {M : Type*} [Monoid M]

/-- The map of the scheme that executes the subsystems in the order of the list `π`:
`E π_N * ⋯ * E π_1`, the first entry of the list being the rightmost factor. -/
def orderProd (E : ι → M) (π : List ι) : M := (π.reverse.map E).prod

/-- The empty order. -/
theorem orderProd_nil (E : ι → M) : orderProd E [] = 1 := by simp [orderProd]

/-- The subsystem that runs first is the rightmost factor. -/
theorem orderProd_cons (E : ι → M) (i : ι) (l : List ι) :
    orderProd E (i :: l) = orderProd E l * E i := by
  simp [orderProd]

/-- Running `l₁` and then `l₂`. -/
theorem orderProd_append (E : ι → M) (l₁ l₂ : List ι) :
    orderProd E (l₁ ++ l₂) = orderProd E l₂ * orderProd E l₁ := by
  simp [orderProd]

/-- **(a) Exchanging two consecutive subsystems that commute does not change the scheme.** -/
theorem orderProd_swap (E : ι → M) {i j : ι} (h : Commute (E i) (E j)) (l₁ l₂ : List ι) :
    orderProd E (l₁ ++ i :: j :: l₂) = orderProd E (l₁ ++ j :: i :: l₂) := by
  simp only [orderProd_append, orderProd_cons, mul_assoc]
  rw [← mul_assoc (E j) (E i), ← mul_assoc (E i) (E j), h.eq]

/-- **(b) Moving the first subsystem to the end:** `E i * X_(i :: l) = X_(l ++ [i]) * E i`. -/
theorem orderProd_rotate (E : ι → M) (i : ι) (l : List ι) :
    E i * orderProd E (i :: l) = orderProd E (l ++ [i]) * E i := by
  simp [orderProd_append, orderProd_cons, orderProd_nil, mul_assoc]

end Monoid

section Group

variable {Γ : Type*} [Group Γ]

/-- **(b) Moving the first subsystem to the end gives a conjugate map.** -/
theorem isConj_orderProd_rotate (E : ι → Γ) (i : ι) (l : List ι) :
    IsConj (orderProd E (i :: l)) (orderProd E (l ++ [i])) :=
  isConj_iff.2 ⟨E i, by rw [mul_inv_eq_iff_eq_mul]; exact orderProd_rotate E i l⟩

/-- An element that commutes with every factor commutes with the product. -/
theorem commute_prod_map (x : Γ) (g : ι → Γ) (m : List ι) (h : ∀ c ∈ m, Commute x (g c)) :
    Commute x (m.map g).prod :=
  Commute.list_prod_right _ _ fun y hy => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact h c hc

/-- The algebra of the second case of `isConj_prod_merge`: `x` is moved to the front through `p`,
to the end by conjugation, and back through `r`. -/
theorem isConj_mul_aux {x y p q r : Γ} (hp : Commute x p) (hr : Commute x r) :
    IsConj (p * (x * (q * (y * r)))) (p * (q * (y * x * r))) := by
  refine isConj_iff.2 ⟨x⁻¹, ?_⟩
  have h1 : p * (x * (q * (y * r))) = x * (p * (q * (y * r))) := by
    rw [← mul_assoc, ← hp.eq, mul_assoc]
  have h2 : y * x * r = y * r * x := by rw [mul_assoc, hr.eq, ← mul_assoc]
  rw [h1, h2]
  group

variable [DecidableEq ι]

/-- A list that does not contain `b` does not see a change of the family at `b`. -/
theorem map_update_of_notMem (g : ι → Γ) (b : ι) (v : Γ) (m : List ι) (hb : b ∉ m) :
    m.map (Function.update g b v) = m.map g :=
  List.map_congr_left fun c hc => Function.update_of_ne (by
    rintro rfl
    exact hb hc) _ _

/-- **Merging an entry into its only neighbour.** Let `l` be a list without repetitions that
contains `a ≠ b`, and let `g a` commute with `g c` for every entry `c` other than `a` and `b`.
Then the product over `l` is conjugate to the product over `l` without `a` in which `g b` is
replaced by `g b * g a`. -/
theorem isConj_prod_merge (g : ι → Γ) {a b : ι} (hab : a ≠ b) (l : List ι) (hl : l.Nodup)
    (ha : a ∈ l) (hb : b ∈ l) (hcomm : ∀ c ∈ l, c ≠ a → c ≠ b → Commute (g a) (g c)) :
    IsConj (l.map g).prod ((l.erase a).map (Function.update g b (g b * g a))).prod := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  have hnd := List.nodup_cons.1 (List.nodup_middle.1 hl)
  have ha1 : a ∉ l₁ := fun h => hnd.1 (List.mem_append_left _ h)
  have ha2 : a ∉ l₂ := fun h => hnd.1 (List.mem_append_right _ h)
  have herase : (l₁ ++ a :: l₂).erase a = l₁ ++ l₂ := by
    rw [List.erase_append_right _ ha1, List.erase_cons_head]
  rw [herase]
  have hb' : b ∈ l₁ ∨ b ∈ l₂ := by
    rcases List.mem_append.1 hb with h | h
    · exact Or.inl h
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h.symm hab
      · exact Or.inr h
  rcases hb' with h | h
  · -- `b` runs before `a` in the list: `l = m₁ ++ b :: m₂ ++ a :: l₂`
    obtain ⟨m₁, m₂, rfl⟩ := List.append_of_mem h
    have hnd' : (m₁ ++ b :: (m₂ ++ l₂)).Nodup := by
      have h0 := hnd.2
      rwa [List.append_assoc, List.cons_append] at h0
    have hnd2 := List.nodup_cons.1 (List.nodup_middle.1 hnd')
    have hb1 : b ∉ m₁ := fun h => hnd2.1 (List.mem_append_left _ h)
    have hb2 : b ∉ m₂ := fun h => hnd2.1 (List.mem_append_right _ (List.mem_append_left _ h))
    have hb3 : b ∉ l₂ := fun h => hnd2.1 (List.mem_append_right _ (List.mem_append_right _ h))
    have hc2 : Commute (g a) (m₂.map g).prod := by
      refine commute_prod_map _ _ _ fun c hc => hcomm c (by simp [hc]) ?_ ?_
      · rintro rfl
        exact ha1 (by simp [hc])
      · rintro rfl
        exact hb2 hc
    have e1 : (((m₁ ++ b :: m₂) ++ a :: l₂).map g).prod =
        (m₁.map g).prod * (g b * (m₂.map g).prod) * (g a * (l₂.map g).prod) := by
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    have e2 : (((m₁ ++ b :: m₂) ++ l₂).map (Function.update g b (g b * g a))).prod =
        (m₁.map g).prod * (g b * g a * (m₂.map g).prod) * (l₂.map g).prod := by
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
        map_update_of_notMem g b _ _ hb1, map_update_of_notMem g b _ _ hb2,
        map_update_of_notMem g b _ _ hb3, Function.update_self]
    have e3 : (m₁.map g).prod * (g b * (m₂.map g).prod) * (g a * (l₂.map g).prod) =
        (m₁.map g).prod * (g b * g a * (m₂.map g).prod) * (l₂.map g).prod := by
      calc (m₁.map g).prod * (g b * (m₂.map g).prod) * (g a * (l₂.map g).prod)
          = (m₁.map g).prod * (g b * ((m₂.map g).prod * g a)) * (l₂.map g).prod := by
            simp only [mul_assoc]
        _ = (m₁.map g).prod * (g b * (g a * (m₂.map g).prod)) * (l₂.map g).prod := by
            rw [hc2.eq]
        _ = (m₁.map g).prod * (g b * g a * (m₂.map g).prod) * (l₂.map g).prod := by
            simp only [mul_assoc]
    rw [e1, e2, e3]
  · -- `a` runs before `b` in the list: `l = l₁ ++ a :: m₁ ++ b :: m₂`
    obtain ⟨m₁, m₂, rfl⟩ := List.append_of_mem h
    have hnd' : ((l₁ ++ m₁) ++ b :: m₂).Nodup := by
      have h0 := hnd.2
      rwa [← List.append_assoc] at h0
    have hnd2 := List.nodup_cons.1 (List.nodup_middle.1 hnd')
    have hb1 : b ∉ l₁ := fun h => hnd2.1 (List.mem_append_left _ (List.mem_append_left _ h))
    have hb2 : b ∉ m₁ := fun h => hnd2.1 (List.mem_append_left _ (List.mem_append_right _ h))
    have hb3 : b ∉ m₂ := fun h => hnd2.1 (List.mem_append_right _ h)
    have hc1 : Commute (g a) (l₁.map g).prod := by
      refine commute_prod_map _ _ _ fun c hc => hcomm c (by simp [hc]) ?_ ?_
      · rintro rfl
        exact ha1 hc
      · rintro rfl
        exact hb1 hc
    have hc3 : Commute (g a) (m₂.map g).prod := by
      refine commute_prod_map _ _ _ fun c hc => hcomm c (by simp [hc]) ?_ ?_
      · rintro rfl
        exact ha2 (by simp [hc])
      · rintro rfl
        exact hb3 hc
    have e1 : ((l₁ ++ a :: (m₁ ++ b :: m₂)).map g).prod =
        (l₁.map g).prod * (g a * ((m₁.map g).prod * (g b * (m₂.map g).prod))) := by
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    have e2 : ((l₁ ++ (m₁ ++ b :: m₂)).map (Function.update g b (g b * g a))).prod =
        (l₁.map g).prod * ((m₁.map g).prod * (g b * g a * (m₂.map g).prod)) := by
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
        map_update_of_notMem g b _ _ hb1, map_update_of_notMem g b _ _ hb2,
        map_update_of_notMem g b _ _ hb3, Function.update_self]
    rw [e1, e2]
    exact isConj_mul_aux hc1 hc3

/-- **Induction over the entries.** Let every finite set of vertices of `G` contain a vertex with
at most one neighbour in the set, and let `g i`, `g j` commute for distinct entries `i`, `j` of
`π` that are not adjacent. Then the products over `π` and over every rearrangement `ρ` of `π` are
conjugate. -/
theorem isConj_prod_map_of_perm (G : SimpleGraph ι)
    (hG : ∀ t : Finset ι, t.Nonempty →
      ∃ a ∈ t, ∀ b ∈ t, ∀ c ∈ t, G.Adj a b → G.Adj a c → b = c) :
    ∀ (n : ℕ) (g : ι → Γ) (π ρ : List ι), π.length = n → π.Nodup → π.Perm ρ →
      (∀ i ∈ π, ∀ j ∈ π, i ≠ j → ¬ G.Adj i j → Commute (g i) (g j)) →
      IsConj (π.map g).prod (ρ.map g).prod := by
  intro n
  induction n with
  | zero =>
    intro g π ρ hlen _ hperm _
    have hπ : π = [] := List.eq_nil_of_length_eq_zero hlen
    subst hπ
    rw [← hperm.nil_eq]
  | succ n ih =>
    intro g π ρ hlen hnd hperm hcomm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hlen
      rw [List.perm_singleton.1 hperm.symm]
    · have hπne : π ≠ [] := fun h => by
        rw [h] at hlen
        simp at hlen
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil π hπne
      obtain ⟨a, ha, hauniq⟩ := hG π.toFinset ⟨x, List.mem_toFinset.2 hx⟩
      rw [List.mem_toFinset] at ha
      have hρnd : ρ.Nodup := hperm.nodup hnd
      have hlen' : (π.erase a).length = n := by
        rw [List.length_erase_of_mem ha, hlen]
        rfl
      have hb : ∃ b ∈ π, b ≠ a ∧ ∀ c ∈ π, G.Adj a c → c = b := by
        by_cases h : ∃ c ∈ π, G.Adj a c
        · obtain ⟨b, hb, hab⟩ := h
          exact ⟨b, hb, (G.ne_of_adj hab).symm, fun c hc hac =>
            hauniq c (List.mem_toFinset.2 hc) b (List.mem_toFinset.2 hb) hac hab⟩
        · have hne' : π.erase a ≠ [] := fun h0 => by
            rw [h0] at hlen'
            simp at hlen'
            omega
          obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hne'
          have hb' := hnd.mem_erase_iff.1 hb
          exact ⟨b, hb'.2, hb'.1, fun c hc hac => absurd ⟨c, hc, hac⟩ h⟩
      obtain ⟨b, hbπ, hba, hbuniq⟩ := hb
      have hca : ∀ c ∈ π, c ≠ a → c ≠ b → Commute (g a) (g c) := fun c hc hca hcb =>
        hcomm a ha c hc (Ne.symm hca) fun hac => hcb (hbuniq c hc hac)
      have h1 := isConj_prod_merge g (Ne.symm hba) π hnd ha hbπ hca
      have h2 := isConj_prod_merge g (Ne.symm hba) ρ hρnd (hperm.mem_iff.1 ha)
        (hperm.mem_iff.1 hbπ) fun c hc => hca c (hperm.mem_iff.2 hc)
      have h3 : IsConj ((π.erase a).map (Function.update g b (g b * g a))).prod
          ((ρ.erase a).map (Function.update g b (g b * g a))).prod := by
        refine ih (Function.update g b (g b * g a)) (π.erase a) (ρ.erase a) hlen' (hnd.erase a)
          (hperm.erase a) ?_
        intro i hi j hj hij hadj
        have hi' := hnd.mem_erase_iff.1 hi
        have hj' := hnd.mem_erase_iff.1 hj
        by_cases hib : i = b
        · have hjb : j ≠ b := fun h => hij (hib.trans h.symm)
          have hbj : ¬ G.Adj b j := by
            rw [← hib]
            exact hadj
          rw [hib, Function.update_self, Function.update_of_ne hjb]
          exact (hcomm b hbπ j hj'.2 (Ne.symm hjb) hbj).mul_left (hca j hj'.2 hj'.1 hjb)
        · by_cases hjb : j = b
          · have hib' : ¬ G.Adj i b := by
              rw [← hjb]
              exact hadj
            rw [hjb, Function.update_self, Function.update_of_ne hib]
            exact (hcomm i hi'.2 b hbπ hib hib').mul_right (hca i hi'.2 hi'.1 hib).symm
          · rw [Function.update_of_ne hib, Function.update_of_ne hjb]
            exact hcomm i hi'.2 j hj'.2 hij hadj
      exact h1.trans (h3.trans h2.symm)

end Group

section Graph

/-- **Every finite set of vertices of an acyclic graph contains a vertex with at most one
neighbour in the set:** the end of a longest path of the induced graph. -/
theorem exists_mem_adj_unique_of_isAcyclic {G : SimpleGraph ι} (hG : G.IsAcyclic) (t : Finset ι)
    (ht : t.Nonempty) : ∃ a ∈ t, ∀ b ∈ t, ∀ c ∈ t, G.Adj a b → G.Adj a c → b = c := by
  classical
  have hH : (G.comap (Function.Embedding.subtype fun x => x ∈ t)).IsAcyclic := hG.of_comap _
  have hne : Nonempty {x // x ∈ t} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length
    (G.comap (Function.Embedding.subtype fun x => x ∈ t))
  have key : ∀ x, (G.comap (Function.Embedding.subtype fun x => x ∈ t)).Adj v x →
      x = p.penultimate := by
    intro x hx
    refine hH.eq_penultimate_of_adj_end hp hx ?_
    by_contra hns
    have h1 := hmax _ _ (p.concat hx) (hp.concat hns hx)
    rw [SimpleGraph.Walk.length_concat] at h1
    omega
  refine ⟨v.1, v.2, fun b hb c hc hab hac => ?_⟩
  have e1 := key ⟨b, hb⟩ hab
  have e2 := key ⟨c, hc⟩ hac
  exact congrArg Subtype.val (e1.trans e2.symm)

variable {Γ : Type*} [Group Γ]

/-- **(c) Sequential orders on a forest give conjugate maps** (the paper, Proposition 5.10). Let `G`
be an acyclic graph (a tree or a forest) and let `E i`, `E j` commute whenever `i` and `j` are not
adjacent. Then for any two lists `π`, `ρ` without repetitions and with the same entries, in
particular for any two orderings of all indices, `X_π` and `X_ρ` are conjugate. -/
theorem isConj_orderProd_of_isAcyclic {G : SimpleGraph ι} (hG : G.IsAcyclic) (E : ι → Γ)
    (hE : ∀ i j, ¬ G.Adj i j → Commute (E i) (E j)) {π ρ : List ι} (hπ : π.Nodup)
    (hρ : ρ.Nodup) (hmem : ∀ i, i ∈ π ↔ i ∈ ρ) : IsConj (orderProd E π) (orderProd E ρ) := by
  classical
  refine isConj_prod_map_of_perm G (exists_mem_adj_unique_of_isAcyclic hG) π.reverse.length E
    π.reverse ρ.reverse rfl (List.nodup_reverse.2 hπ) ?_ fun i _ j _ _ h => hE i j h
  refine (List.perm_ext_iff_of_nodup (List.nodup_reverse.2 hπ) (List.nodup_reverse.2 hρ)).2
    fun i => ?_
  rw [List.mem_reverse, List.mem_reverse]
  exact hmem i

/-- **(c) for orderings of all subsystems of a tree:** if every index occurs exactly once in `π`
and in `ρ`, the maps `X_π` and `X_ρ` are conjugate. -/
theorem isConj_orderProd_of_isTree {G : SimpleGraph ι} (hG : G.IsTree) (E : ι → Γ)
    (hE : ∀ i j, ¬ G.Adj i j → Commute (E i) (E j)) {π ρ : List ι} (hπ : π.Nodup)
    (hρ : ρ.Nodup) (hπall : ∀ i, i ∈ π) (hρall : ∀ i, i ∈ ρ) :
    IsConj (orderProd E π) (orderProd E ρ) :=
  isConj_orderProd_of_isAcyclic hG.isAcyclic E hE hπ hρ fun i =>
    ⟨fun _ => hρall i, fun _ => hπall i⟩

/-- **(c) for a chain of `n` subsystems:** if `E i` and `E j` commute whenever `i` and `j` are
not neighbours on the chain, all orders of execution give conjugate maps. -/
theorem isConj_orderProd_chain {n : ℕ} (E : Fin n → Γ)
    (hE : ∀ i j : Fin n, (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i → Commute (E i) (E j))
    {π ρ : List (Fin n)} (hπ : π.Nodup) (hρ : ρ.Nodup) (hmem : ∀ i, i ∈ π ↔ i ∈ ρ) :
    IsConj (orderProd E π) (orderProd E ρ) := by
  refine isConj_orderProd_of_isAcyclic (SimpleGraph.isAcyclic_pathGraph n) E (fun i j h => ?_)
    hπ hρ hmem
  rw [SimpleGraph.pathGraph_adj, not_or] at h
  exact hE i j h.1 h.2

end Graph

section Units

variable {M : Type*} [Monoid M]

/-- **(c) for invertible elements of a monoid,** for example invertible matrices: on an acyclic
graph, `c X_π c⁻¹ = X_ρ` with a unit `c`. -/
theorem exists_units_conj_orderProd {G : SimpleGraph ι} (hG : G.IsAcyclic) (E : ι → M)
    (hunit : ∀ i, IsUnit (E i)) (hE : ∀ i j, ¬ G.Adj i j → Commute (E i) (E j)) {π ρ : List ι}
    (hπ : π.Nodup) (hρ : ρ.Nodup) (hmem : ∀ i, i ∈ π ↔ i ∈ ρ) :
    ∃ c : Mˣ, (c : M) * orderProd E π * ((c⁻¹ : Mˣ) : M) = orderProd E ρ := by
  choose u hu using hunit
  have hcu : ∀ i j, ¬ G.Adj i j → Commute (u i) (u j) := fun i j h => by
    have h0 := hE i j h
    rw [← hu i, ← hu j] at h0
    exact h0.units_of_val
  have hval : ∀ l : List ι, ((orderProd u l : Mˣ) : M) = orderProd E l := by
    intro l
    induction l with
    | nil => rw [orderProd_nil, orderProd_nil, Units.val_one]
    | cons i l ih => rw [orderProd_cons, orderProd_cons, Units.val_mul, ih, hu]
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_orderProd_of_isAcyclic hG u hcu hπ hρ hmem)
  refine ⟨c, ?_⟩
  rw [← hval π, ← hval ρ, ← hc, Units.val_mul, Units.val_mul]

end Units

section Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] {R : Type*} [CommRing R]

/-- **Sequential orders on a forest have the same characteristic polynomial** (the paper,
Proposition 5.10: the same eigenvalues), for invertible matrices `E i` that commute off the
graph. -/
theorem charpoly_orderProd_eq {G : SimpleGraph ι} (hG : G.IsAcyclic) (E : ι → Matrix m m R)
    (hunit : ∀ i, IsUnit (E i)) (hE : ∀ i j, ¬ G.Adj i j → Commute (E i) (E j)) {π ρ : List ι}
    (hπ : π.Nodup) (hρ : ρ.Nodup) (hmem : ∀ i, i ∈ π ↔ i ∈ ρ) :
    (orderProd E ρ).charpoly = (orderProd E π).charpoly := by
  obtain ⟨c, hc⟩ := exists_units_conj_orderProd hG E hunit hE hπ hρ hmem
  rw [← hc, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

/-- **Sequential orders on a forest have the same determinant** (the paper, Proposition 5.10: the
same total numerical damping). -/
theorem det_orderProd_eq {G : SimpleGraph ι} (hG : G.IsAcyclic) (E : ι → Matrix m m R)
    (hunit : ∀ i, IsUnit (E i)) (hE : ∀ i j, ¬ G.Adj i j → Commute (E i) (E j)) {π ρ : List ι}
    (hπ : π.Nodup) (hρ : ρ.Nodup) (hmem : ∀ i, i ∈ π ↔ i ∈ ρ) :
    (orderProd E ρ).det = (orderProd E π).det := by
  obtain ⟨c, hc⟩ := exists_units_conj_orderProd hG E hunit hE hπ hρ hmem
  have h1 : (c : Matrix m m R).det * ((c⁻¹ : (Matrix m m R)ˣ) : Matrix m m R).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [← hc, Matrix.det_mul, Matrix.det_mul, mul_right_comm, h1, one_mul]

end Matrix

end CoSimFoundations
