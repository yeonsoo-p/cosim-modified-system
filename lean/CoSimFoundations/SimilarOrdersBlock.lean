/-
Sequential orders on a coupling graph without a cycle give similar one-step maps, for subsystems
with any number of states (the paper, Section "Energy stored and energy created", the
sentence on sequential orders on a tree).

**Setting.** States `ι` grouped into subsystems by `sub : ι → α`, own-state coefficients `K`
(block diagonal, the paper's `F`), sample coefficients `G` (the paper's `G C`), stages
`stage : α → ℕ`. `D_c` is the `0/1` diagonal matrix of the states of subsystem `c` (`subMask`),
and the map that executes subsystem `c` alone is
  `E_c = 1 + D_c (K + G - 1)`   (`blockStep`):
the rows of `c` are those of `K + G`, the other rows those of the identity.

**The stage maps** (`commute_blockStep`, `isUnit_blockStep`). `D_c² = D_c`, `D_c D_d = 0`,
`D_c K = K D_c`. If `G` has no block between `c ≠ d` in either direction,
`D_c (K + G - 1) D_d = 0` and `E_c`, `E_d` commute. If `K_i K = 1` and `G` has no block inside
`c`, then `E_c (1 - K_i D_c (K + G - 1)) = 1`: with `Z = K + G - 1`, `D_c Z D_c = K D_c - D_c`
and `D_c Z K_i D_c = D_c - K_i D_c`.

**The one-step map is the ordered product** (`orderProd_blockStep_rows`,
`orderProd_blockStep_eq_infoStep`). Let `G i j = 0` whenever the subsystems of `i` and `j` run
at the same stage (no link within a stage, no block inside a subsystem), and let the list `π`
contain every subsystem once, ordered by the stages (subsystems of one stage in any order).
Then `E_{π_N} ⋯ E_{π_1} = infoStep (stage ∘ sub) K G = (1 - N)⁻¹ (K + M)`. Proof by induction
over the subsystems executed so far: the rows of the subsystems not yet executed are those of
the identity, and a row `a` of an executed subsystem obeys
`Y_a = K_a + Σ_j G_aj (Y_j if j is executed and at an earlier stage, else e_j)`.

**Similar one-step maps** (`exists_units_conj_infoStep_block`,
`exists_units_conj_infoStep_of_isAcyclic`, `HeldScheme.X_eq_infoStep`,
`HeldScheme.exists_units_conj_X`, `HeldScheme.exists_units_conj_zoh_restage`). On an acyclic
graph `Gr` of the subsystems, with `G` zero unless the two subsystems are linked and `K`
invertible, the one-step maps of any two assignments of stages without a link within a stage are
similar: `c X₁ c⁻¹ = X₂` with an invertible `c` (`exists_units_conj_orderProd` of
`SimilarOrders`). The same for two schemes with one held sample (`HeldScheme`) that have the
subsystems, `F` and `N + M` in common, and for the zero-order hold in the stages of `S` and in
any other stages `st` (`restage`): there `F = e^{H A₀}` is invertible for every `H`.
-/
import CoSimFoundations.SimilarOrders
import CoSimFoundations.InfoForm
import CoSimFoundations.ReversedOrder
import CoSimFoundations.MidpointEnergy
import Mathlib.Data.List.Sort

open Matrix

namespace CoSimFoundations

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [DecidableEq α]

/-! ### The mask of a subsystem and the map that executes it -/

/-- The diagonal `0/1` matrix of the states of subsystem `c`. -/
def subMask (sub : ι → α) (c : α) : Matrix ι ι ℝ := diagonal fun r => if sub r = c then 1 else 0

/-- The map `E_c = 1 + D_c (K + G - 1)` that executes subsystem `c` alone: the rows of `c` are
those of `K + G`, the other rows those of the identity. -/
def blockStep (sub : ι → α) (K G : Matrix ι ι ℝ) (c : α) : Matrix ι ι ℝ :=
  1 + subMask sub c * (K + G - 1)

/-- `D_c² = D_c`. -/
theorem subMask_mul_self (sub : ι → α) (c : α) : subMask sub c * subMask sub c = subMask sub c := by
  rw [subMask, Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  by_cases h : sub r = c
  · rw [ite_eq_left h, mul_one]
  · rw [ite_eq_right h, mul_zero]

/-- `D_c D_d = 0` for `c ≠ d`. -/
theorem subMask_mul_of_ne (sub : ι → α) {c d : α} (h : c ≠ d) :
    subMask sub c * subMask sub d = 0 := by
  rw [subMask, subMask, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext r
  by_cases h1 : sub r = c
  · have h2 : sub r ≠ d := fun e => h (h1.symm.trans e)
    rw [ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]

/-- A block-diagonal matrix commutes with the masks: `D_c K = K D_c`. -/
theorem subMask_mul_comm (sub : ι → α) {K : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0) (c : α) : subMask sub c * K = K * subMask sub c := by
  ext a b
  rw [subMask, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : sub a = sub b
  · rw [hab, mul_comm]
  · rw [hK a b hab, mul_zero, zero_mul]

/-- `D_c G D_d = 0` if `G` has no block from `d` to `c`. -/
theorem subMask_mul_mul (sub : ι → α) {G : Matrix ι ι ℝ} {c d : α}
    (hG : ∀ a b, sub a = c → sub b = d → G a b = 0) :
    subMask sub c * G * subMask sub d = 0 := by
  ext a b
  rw [subMask, subMask, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases ha : sub a = c
  · by_cases hb : sub b = d
    · rw [hG a b ha hb, mul_zero, zero_mul]
    · rw [ite_eq_right hb, mul_zero]
  · rw [ite_eq_right ha, zero_mul, zero_mul]

/-- Executing `c` leaves the rows of the other subsystems unchanged. -/
theorem blockStep_mul_apply_of_ne (sub : ι → α) (K G : Matrix ι ι ℝ) {c : α} {a : ι}
    (h : sub a ≠ c) (Y : Matrix ι ι ℝ) (b : ι) : (blockStep sub K G c * Y) a b = Y a b := by
  rw [blockStep, add_mul, one_mul, Matrix.add_apply, Matrix.mul_assoc, subMask,
    Matrix.diagonal_mul, ite_eq_right h, zero_mul, add_zero]

/-- Executing `c` replaces the rows of `c` by the update. -/
theorem blockStep_mul_apply_self (sub : ι → α) (K G : Matrix ι ι ℝ) {c : α} {a : ι}
    (h : sub a = c) (Y : Matrix ι ι ℝ) (b : ι) :
    (blockStep sub K G c * Y) a b = (K * Y) a b + (G * Y) a b := by
  rw [blockStep, add_mul, one_mul, Matrix.add_apply, Matrix.mul_assoc, subMask,
    Matrix.diagonal_mul, ite_eq_left h, one_mul, sub_mul, one_mul, add_mul, Matrix.sub_apply,
    Matrix.add_apply]
  ring

/-- **Subsystems that are not linked commute:** if `K` is block diagonal and `G` has no block
between `c ≠ d` in either direction, `E_c` and `E_d` commute. -/
theorem commute_blockStep (sub : ι → α) {K G : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0) {c d : α} (hcd : c ≠ d)
    (h1 : ∀ a b, sub a = c → sub b = d → G a b = 0)
    (h2 : ∀ a b, sub a = d → sub b = c → G a b = 0) :
    Commute (blockStep sub K G c) (blockStep sub K G d) := by
  have z : ∀ {c d : α}, c ≠ d → (∀ a b, sub a = c → sub b = d → G a b = 0) →
      subMask sub c * (K + G - 1) * subMask sub d = 0 := by
    intro c d hcd h
    rw [mul_sub, mul_add, mul_one, sub_mul, add_mul, subMask_mul_comm sub hK c, mul_assoc K,
      subMask_mul_of_ne sub hcd, mul_zero, subMask_mul_mul sub h, add_zero, sub_self]
  have e : ∀ c d : α, blockStep sub K G c * blockStep sub K G d =
      1 + subMask sub c * (K + G - 1) + subMask sub d * (K + G - 1) +
        subMask sub c * (K + G - 1) * subMask sub d * (K + G - 1) := by
    intro c d
    rw [blockStep, blockStep]
    noncomm_ring
  show blockStep sub K G c * blockStep sub K G d = blockStep sub K G d * blockStep sub K G c
  rw [e c d, e d c, z hcd h1, z hcd.symm h2, zero_mul]
  abel

/-- **`E_c` is invertible** if `K` is block diagonal with a left inverse `K_i` and `G` has no
block inside `c`: `E_c (1 - K_i D_c (K + G - 1)) = 1`. -/
theorem isUnit_blockStep (sub : ι → α) {K G Ki : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0) (hKi : Ki * K = 1) {c : α}
    (hG : ∀ a b, sub a = c → sub b = c → G a b = 0) : IsUnit (blockStep sub K G c) := by
  have hKKi : K * Ki = 1 := mul_eq_one_comm.1 hKi
  have hPK := subMask_mul_comm sub hK c
  have hPP := subMask_mul_self sub c
  have hPGP := subMask_mul_mul sub hG
  have hKiP : Ki * subMask sub c = subMask sub c * Ki := by
    calc Ki * subMask sub c = Ki * subMask sub c * (K * Ki) := by rw [hKKi, mul_one]
      _ = Ki * (subMask sub c * K) * Ki := by noncomm_ring
      _ = Ki * K * subMask sub c * Ki := by rw [hPK]; noncomm_ring
      _ = subMask sub c * Ki := by rw [hKi, one_mul]
  have hPZP : subMask sub c * (K + G - 1) * subMask sub c = K * subMask sub c - subMask sub c := by
    rw [mul_sub, mul_add, mul_one, sub_mul, add_mul, hPK, mul_assoc K, hPP, hPGP, add_zero]
  have h3 : subMask sub c * (K + G - 1) * (Ki * subMask sub c) =
      subMask sub c - Ki * subMask sub c := by
    rw [hKiP, ← mul_assoc, hPZP, sub_mul, mul_assoc, ← hKiP, ← mul_assoc, hKKi, one_mul]
  have key : blockStep sub K G c * (1 - Ki * subMask sub c * (K + G - 1)) =
      1 + subMask sub c * (K + G - 1) - Ki * subMask sub c * (K + G - 1) -
        subMask sub c * (K + G - 1) * (Ki * subMask sub c) * (K + G - 1) := by
    rw [blockStep]
    noncomm_ring
  have hinv : blockStep sub K G c * (1 - Ki * subMask sub c * (K + G - 1)) = 1 := by
    rw [key, h3]
    noncomm_ring
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hinv)

/-! ### The one-step map as the ordered product -/

/-- **The rows of a partial execution.** Let `K` be block diagonal and `G i j = 0` whenever the
subsystems of `i` and `j` run at the same stage. For a list `l` of different subsystems ordered
by the stages, the product `E l_k * ⋯ * E l_1` has the rows of the identity at the subsystems
not in `l`, and a row `a` of a subsystem of `l` satisfies the update with the rows of the
subsystems of `l` at an earlier stage. -/
theorem orderProd_blockStep_rows (sub : ι → α) (stage : α → ℕ) {K G : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0)
    (hG0 : ∀ i j, stage (sub i) = stage (sub j) → G i j = 0) (l : List α) :
    l.Pairwise (fun c d => stage c ≤ stage d) → l.Nodup →
      (∀ a, sub a ∉ l → ∀ b, orderProd (blockStep sub K G) l a b = (1 : Matrix ι ι ℝ) a b) ∧
      ∀ a, sub a ∈ l → ∀ b, orderProd (blockStep sub K G) l a b = K a b +
        ∑ j, G a j * (if sub j ∈ l ∧ stage (sub j) < stage (sub a) then
          orderProd (blockStep sub K G) l j b else (1 : Matrix ι ι ℝ) j b) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro _ _
    refine ⟨fun a _ b => by rw [orderProd_nil], fun a ha => ?_⟩
    simp at ha
  | append_singleton l c ih =>
    intro hp hnd
    rw [List.pairwise_append] at hp
    obtain ⟨hl, -, hlc⟩ := hp
    obtain ⟨hndl, -, hdis⟩ := List.nodup_append.1 hnd
    have hle : ∀ d ∈ l, stage d ≤ stage c := fun d hd => hlc d hd c (List.mem_singleton.2 rfl)
    have hc : c ∉ l := fun h => hdis c h c (List.mem_singleton.2 rfl) rfl
    obtain ⟨ih1, ih2⟩ := ih hl hndl
    have hY : orderProd (blockStep sub K G) (l ++ [c]) =
        blockStep sub K G c * orderProd (blockStep sub K G) l := by
      rw [orderProd_append, orderProd_cons, orderProd_nil, one_mul]
    rw [hY]
    generalize orderProd (blockStep sub K G) l = Y at ih1 ih2 ⊢
    have hne : ∀ a, sub a ≠ c → ∀ b, (blockStep sub K G c * Y) a b = Y a b := fun a ha b =>
      blockStep_mul_apply_of_ne sub K G ha Y b
    refine ⟨fun a ha b => ?_, fun a ha b => ?_⟩
    · have ha1 : sub a ∉ l := fun h => ha (List.mem_append_left _ h)
      have ha2 : sub a ≠ c := fun h => ha (List.mem_append_right _ (List.mem_singleton.2 h))
      rw [hne a ha2, ih1 a ha1]
    · by_cases hac : sub a = c
      · have hKY : (K * Y) a b = K a b := by
          have e : ∀ j, K a j * Y j b = K a j * (1 : Matrix ι ι ℝ) j b := fun j => by
            by_cases hj : sub a = sub j
            · rw [ih1 j (by rw [← hj, hac]; exact hc)]
            · rw [hK a j hj, zero_mul, zero_mul]
          rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ => e j, ← Matrix.mul_apply,
            Matrix.mul_one]
        rw [blockStep_mul_apply_self sub K G hac, hKY, Matrix.mul_apply]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hGz : G a j = 0
        · rw [hGz, zero_mul, zero_mul]
        · have hst : stage (sub a) ≠ stage (sub j) := fun h => hGz (hG0 a j h)
          by_cases hj : sub j ∈ l
          · have hjc : sub j ≠ c := fun h => hc (h ▸ hj)
            have h1 := hle _ hj
            rw [← hac] at h1
            have hcnd : sub j ∈ l ++ [c] ∧ stage (sub j) < stage (sub a) :=
              ⟨List.mem_append_left _ hj, lt_of_le_of_ne h1 hst.symm⟩
            rw [ite_eq_left hcnd, hne j hjc]
          · have hcnd : ¬ (sub j ∈ l ++ [c] ∧ stage (sub j) < stage (sub a)) := by
              rintro ⟨h1, h2⟩
              rcases List.mem_append.1 h1 with h | h
              · exact hj h
              · rw [List.mem_singleton.1 h, hac] at h2
                exact lt_irrefl _ h2
            rw [ite_eq_right hcnd, ih1 j hj]
      · have hal : sub a ∈ l := by
          rcases List.mem_append.1 ha with h | h
          · exact h
          · exact absurd (List.mem_singleton.1 h) hac
        rw [hne a hac, ih2 a hal]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : sub j ∈ l
        · have hjc : sub j ≠ c := fun h => hc (h ▸ hj)
          by_cases hs : stage (sub j) < stage (sub a)
          · have hc1 : sub j ∈ l ∧ stage (sub j) < stage (sub a) := ⟨hj, hs⟩
            have hc2 : sub j ∈ l ++ [c] ∧ stage (sub j) < stage (sub a) :=
              ⟨List.mem_append_left _ hj, hs⟩
            rw [ite_eq_left hc1, ite_eq_left hc2, hne j hjc]
          · have hc1 : ¬ (sub j ∈ l ∧ stage (sub j) < stage (sub a)) := fun h => hs h.2
            have hc2 : ¬ (sub j ∈ l ++ [c] ∧ stage (sub j) < stage (sub a)) := fun h => hs h.2
            rw [ite_eq_right hc1, ite_eq_right hc2]
        · have hc1 : ¬ (sub j ∈ l ∧ stage (sub j) < stage (sub a)) := fun h => hj h.1
          have hc2 : ¬ (sub j ∈ l ++ [c] ∧ stage (sub j) < stage (sub a)) := by
            rintro ⟨h1, h2⟩
            rcases List.mem_append.1 h1 with h | h
            · exact hj h
            · rw [List.mem_singleton.1 h] at h2
              exact absurd (hle _ hal) (not_le.2 h2)
          rw [ite_eq_right hc1, ite_eq_right hc2]

/-- **The one-step map of a sequential scheme is the product of the maps of the subsystems.**
Let `K` be block diagonal, `G i j = 0` whenever the subsystems of `i` and `j` run at the same
stage, and let the list `π` contain every subsystem once, ordered by the stages. Then
`E π_N * ⋯ * E π_1 = (1 - N)⁻¹ (K + M)`, the one-step map `infoStep (stage ∘ sub) K G`. -/
theorem orderProd_blockStep_eq_infoStep (sub : ι → α) (stage : α → ℕ) {K G : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0)
    (hG0 : ∀ i j, stage (sub i) = stage (sub j) → G i j = 0) {π : List α}
    (hπ : π.Pairwise (fun c d => stage c ≤ stage d)) (hnd : π.Nodup) (hall : ∀ c, c ∈ π) :
    orderProd (blockStep sub K G) π = infoStep (stage ∘ sub) K G := by
  obtain ⟨-, h2⟩ := orderProd_blockStep_rows sub stage hK hG0 π hπ hnd
  generalize orderProd (blockStep sub K G) π = Y at h2 ⊢
  rw [eq_infoStep_iff]
  ext a b
  have hs := sum_mul_sample (stage ∘ sub) G (fun j => Y j b) (fun j => (1 : Matrix ι ι ℝ) j b) a
  have h : Y a b = K a b +
      ((infoNew (stage ∘ sub) G *ᵥ fun j => Y j b) a +
        (infoOld (stage ∘ sub) G *ᵥ fun j => (1 : Matrix ι ι ℝ) j b) a) := by
    rw [← hs, h2 a (hall (sub a)) b]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : (stage ∘ sub) j < (stage ∘ sub) a
    · have hc' : sub j ∈ π ∧ stage (sub j) < stage (sub a) := ⟨hall (sub j), hc⟩
      rw [ite_eq_left hc', ite_eq_left hc]
    · have hc' : ¬ (sub j ∈ π ∧ stage (sub j) < stage (sub a)) := fun h => hc h.2
      rw [ite_eq_right hc', ite_eq_right hc]
  have e1 : (infoNew (stage ∘ sub) G *ᵥ fun j => Y j b) a = (infoNew (stage ∘ sub) G * Y) a b :=
    rfl
  have e2 : (infoOld (stage ∘ sub) G *ᵥ fun j => (1 : Matrix ι ι ℝ) j b) a =
      infoOld (stage ∘ sub) G a b := by
    have e : (infoOld (stage ∘ sub) G *ᵥ fun j => (1 : Matrix ι ι ℝ) j b) a =
        (infoOld (stage ∘ sub) G * (1 : Matrix ι ι ℝ)) a b := rfl
    rw [e, Matrix.mul_one]
  rw [e1, e2] at h
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.add_apply]
  linarith

/-- Every assignment of stages to finitely many subsystems is realised by a list of all
subsystems, each once, ordered by the stages. -/
theorem exists_list_pairwise_stage_le [Fintype α] (stage : α → ℕ) :
    ∃ π : List α, π.Pairwise (fun c d => stage c ≤ stage d) ∧ π.Nodup ∧ ∀ c, c ∈ π := by
  refine ⟨Finset.univ.toList.insertionSort (fun c d => stage c ≤ stage d), ?_, ?_, ?_⟩
  · have : Std.Total (fun c d : α => stage c ≤ stage d) := ⟨fun c d => le_total _ _⟩
    have : IsTrans α (fun c d : α => stage c ≤ stage d) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
    exact List.pairwise_insertionSort _ _
  · exact (List.perm_insertionSort _ _).nodup_iff.2 (Finset.nodup_toList _)
  · intro c
    exact (List.perm_insertionSort _ _).mem_iff.2 (Finset.mem_toList.2 (Finset.mem_univ c))

/-! ### Similar one-step maps -/

/-- **Sequential orders on a coupling graph without a cycle give similar one-step maps, block
subsystems.** Let the graph `Gr` of the subsystems be acyclic, `K` block diagonal and invertible,
`G` zero unless the two subsystems are linked, and let `G i j = 0` whenever the subsystems of
`i` and `j` share a stage, in both assignments of stages `st₁`, `st₂`. Then the two one-step
maps are similar: `c X₁ c⁻¹ = X₂` with an invertible matrix `c`. -/
theorem exists_units_conj_infoStep_block [Fintype α] {Gr : SimpleGraph α} (hGr : Gr.IsAcyclic)
    (sub : ι → α) {K G : Matrix ι ι ℝ} (hK : ∀ i j, sub i ≠ sub j → K i j = 0)
    (hKu : IsUnit K.det) (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0) {st₁ st₂ : α → ℕ}
    (h₁ : ∀ i j, st₁ (sub i) = st₁ (sub j) → G i j = 0)
    (h₂ : ∀ i j, st₂ (sub i) = st₂ (sub j) → G i j = 0) :
    ∃ c : (Matrix ι ι ℝ)ˣ, (c : Matrix ι ι ℝ) * infoStep (st₁ ∘ sub) K G *
      ((c⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) = infoStep (st₂ ∘ sub) K G := by
  obtain ⟨π, hπ, hπnd, hπall⟩ := exists_list_pairwise_stage_le st₁
  obtain ⟨ρ, hρ, hρnd, hρall⟩ := exists_list_pairwise_stage_le st₂
  rw [← orderProd_blockStep_eq_infoStep sub st₁ hK h₁ hπ hπnd hπall,
    ← orderProd_blockStep_eq_infoStep sub st₂ hK h₂ hρ hρnd hρall]
  refine exists_units_conj_orderProd hGr (blockStep sub K G)
    (fun c => isUnit_blockStep sub hK (Matrix.nonsing_inv_mul K hKu) fun a b ha hb =>
      hG a b (by rw [ha, hb]; exact Gr.irrefl))
    (fun c d hcd => ?_) hπnd hρnd fun c => ⟨fun _ => hρall c, fun _ => hπall c⟩
  by_cases h : c = d
  · rw [h]
    exact Commute.refl _
  · exact commute_blockStep sub hK h (fun a b ha hb => hG a b (by rw [ha, hb]; exact hcd))
      (fun a b ha hb => hG a b (by rw [ha, hb]; exact fun h' => hcd h'.symm))

/-- **Sequential orders on a tree give similar one-step maps** (the paper, Section "Energy stored
and energy created"; block subsystems, invertible own-state coefficients). Acyclic graph `Gr`,
`K` block diagonal and invertible, `G` zero unless the two subsystems are linked, and two
assignments of stages without a link within a stage: `c X₁ c⁻¹ = X₂` with an invertible `c`. -/
theorem exists_units_conj_infoStep_of_isAcyclic [Fintype α] {Gr : SimpleGraph α}
    (hGr : Gr.IsAcyclic) (sub : ι → α) {K G : Matrix ι ι ℝ}
    (hK : ∀ i j, sub i ≠ sub j → K i j = 0) (hKu : IsUnit K.det)
    (hG : ∀ i j, ¬ Gr.Adj (sub i) (sub j) → G i j = 0) {st₁ st₂ : α → ℕ}
    (h₁ : ∀ a b, Gr.Adj a b → st₁ a ≠ st₁ b) (h₂ : ∀ a b, Gr.Adj a b → st₂ a ≠ st₂ b) :
    ∃ c : (Matrix ι ι ℝ)ˣ, (c : Matrix ι ι ℝ) * infoStep (st₁ ∘ sub) K G *
      ((c⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) = infoStep (st₂ ∘ sub) K G :=
  exists_units_conj_infoStep_block hGr sub hK hKu hG
    (fun i j h => hG i j fun hadj => h₁ _ _ hadj h)
    (fun i j h => hG i j fun hadj => h₂ _ _ hadj h)

end Block

namespace HeldScheme

variable {n : ℕ} {κ : Type*}

/-- **The one-step map of a scheme with one held sample in the form of `InfoForm`:**
`X = (1 - N)⁻¹ (F + M)` is `infoStep (stage ∘ sub) F (N + M)`. -/
theorem X_eq_infoStep (S : HeldScheme n κ) :
    S.X = infoStep (S.stage ∘ S.sub) S.F (S.N + S.M) := by
  have hN : infoNew (S.stage ∘ S.sub) (S.N + S.M) = S.N := by
    ext p q
    rw [infoNew_apply, Matrix.add_apply]
    by_cases h : (S.stage ∘ S.sub) q < (S.stage ∘ S.sub) p
    · rw [ite_eq_left h, S.hM p q fun hc => hc.2 h, add_zero]
    · rw [ite_eq_right h]
      exact (S.hN p q fun hc => h hc.2).symm
  rw [eq_infoStep_iff, infoOld, hN, add_sub_cancel_left, sub_mul, one_mul, sub_eq_iff_eq_add]
  exact S.hX

/-- **Sequential orders on a coupling graph without a cycle give similar one-step maps, for
schemes with one held sample.** Let `S` and `S'` have the subsystems, the own-state coefficients
`F` and the sample coefficients `N + M` in common (the coefficients do not depend on the order).
Let `F` be invertible, the partners of `S` be linked in an acyclic graph on finitely many
subsystems, and no two partners share a stage, in `S` and in `S'`. Then `c X c⁻¹ = X'` with an
invertible matrix `c`. -/
theorem exists_units_conj_X [Fintype κ] [DecidableEq κ] {Gr : SimpleGraph κ}
    (hGr : Gr.IsAcyclic) (S S' : HeldScheme n κ) (hsub : S'.sub = S.sub) (hF : S'.F = S.F)
    (hNM : S'.N + S'.M = S.N + S.M) (hFu : IsUnit S.F.det)
    (hpart : ∀ s t, S.partner s t → Gr.Adj s t)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    (hns' : ∀ s t, s ≠ t → S'.partner s t → S'.stage s ≠ S'.stage t) :
    ∃ c : (Matrix (Fin n) (Fin n) ℝ)ˣ, (c : Matrix (Fin n) (Fin n) ℝ) * S.X *
      ((c⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) = S'.X := by
  have hG : ∀ i j, ¬ Gr.Adj (S.sub i) (S.sub j) → (S.N + S.M) i j = 0 := fun i j h => by
    rw [Matrix.add_apply, S.hN i j fun hc => h (hpart _ _ hc.1),
      S.hM i j fun hc => h (hpart _ _ hc.1), add_zero]
  have h₁ : ∀ i j, S.stage (S.sub i) = S.stage (S.sub j) → (S.N + S.M) i j = 0 := fun i j h => by
    by_cases hadj : Gr.Adj (S.sub i) (S.sub j)
    · rw [Matrix.add_apply, S.hN i j fun hc => hns _ _ (Gr.ne_of_adj hadj) hc.1 h,
        S.hM i j fun hc => hns _ _ (Gr.ne_of_adj hadj) hc.1 h, add_zero]
    · exact hG i j hadj
  have h₂ : ∀ i j, S'.stage (S.sub i) = S'.stage (S.sub j) → (S.N + S.M) i j = 0 :=
    fun i j h => by
      by_cases hadj : Gr.Adj (S.sub i) (S.sub j)
      · have hne : S'.sub i ≠ S'.sub j := by
          rw [hsub]
          exact Gr.ne_of_adj hadj
        have h' : S'.stage (S'.sub i) = S'.stage (S'.sub j) := by
          rw [hsub]
          exact h
        rw [← hNM, Matrix.add_apply, S'.hN i j fun hc => hns' _ _ hne hc.1 h',
          S'.hM i j fun hc => hns' _ _ hne hc.1 h', add_zero]
      · exact hG i j hadj
  rw [S.X_eq_infoStep, S'.X_eq_infoStep, hsub, hF, hNM]
  exact exists_units_conj_infoStep_block hGr S.sub S.hF hFu hG h₁ h₂

/-- **Sequential orders on a tree give similar one-step maps of the zero-order hold** (the paper,
Section "Energy stored and energy created"). Let the partners be linked in an acyclic graph on
finitely many subsystems. For two assignments of stages, `S.stage` and `st`, in each of which no
two partners share a stage, the one-step maps of the zero-order hold are similar, for every
macro step `H` and subsystems with any number of states: `c X c⁻¹ = X_st` with an invertible
matrix `c`. -/
theorem exists_units_conj_zoh_restage [Fintype κ] [DecidableEq κ] (S : HeldScheme n κ)
    {Gr : SimpleGraph κ} (hGr : Gr.IsAcyclic) (hpart : ∀ s t, S.partner s t → Gr.Adj s t)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t) {st : κ → ℕ}
    (hns' : ∀ s t, s ≠ t → S.partner s t → st s ≠ st t) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    ∃ c : (Matrix (Fin n) (Fin n) ℝ)ˣ, (c : Matrix (Fin n) (Fin n) ℝ) * (S.zoh A hA H).X *
      ((c⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) =
        ((S.restage st).zoh A hA H).X := by
  have hNM : ((S.restage st).zoh A hA H).N + ((S.restage st).zoh A hA H).M =
      (S.zoh A hA H).N + (S.zoh A hA H).M := by
    show (S.restage st).zohNew A H + (S.restage st).zohOld A H =
      S.zohNew A H + S.zohOld A H
    rw [add_comm, (S.restage st).zohOld_add_zohNew, add_comm (S.zohNew A H),
      S.zohOld_add_zohNew]
    rfl
  have hFu : IsUnit (S.zoh A hA H).F.det :=
    Matrix.isUnit_det_of_right_inverse (MidpointEnergy.exp_mul_exp_neg (H • S.blockDiag A))
  exact exists_units_conj_X hGr (S.zoh A hA H) ((S.restage st).zoh A hA H) rfl rfl hNM hFu
    hpart hns hns'

end HeldScheme

end CoSimFoundations
