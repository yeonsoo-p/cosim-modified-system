/-
The converse of the visibility theorem for `l` held samples (the paper, Theorem
`thm:visibility`, last sentence, and the last three sentences of its proof).

**Paper.** "If `f_i = 0` for every `i`, coefficients `F_i` and `G_ij^r` exist with which the
scheme, started on samples of the monolithic system, reproduces the monolithic system at every
communication point."

**Setting.** `E` is the state space, `Pr i : E → Es i` the projection onto subsystem `i`; the
projections are jointly injective (a state is the collection of the states of the subsystems).
`c j : Es j → Yo j` is the output map of subsystem `j` (`B_jᵀ`), so that the output of `j` as a
map on the whole state is `C_j = c j ∘ Pr j`. `U` is the monolithic step with left inverse `Ui`.
`stage i` is the stage at which `i` runs; `σ_ij = 1` if `j` runs at an earlier stage than `i` and
`0` otherwise (`newSample`). A scheme with `l` held samples and coefficients `F i`, `G i j r`
produces the runs `x : ℕ → E` with (the paper, eq. `eq:memory`; `IsMemoryRun`)

  `Pr i x^{k+1} = F i (Pr i x^k) + Σ_j Σ_{r<l} G i j r (C_j x^{k + σ_ij - r})`,   `k ≥ l - 1`.

The monolithic samples shown to `i` are `C_j U^{σ_ij - r}`, `j` a partner of `i`, `r < l`
(`shownSample`, with `U^{σ - r} = U^σ Ui^r`); the states not shown and the visibility bound are
those of `VisibilityExact` (`notShown`, `visBound`) for this family, which is Definition
`def:visibility` of the paper (`mem_notShown_shownSample`).

**Statements.**
* `visBound_shownSample_eq_zero_iff`: `f_i = 0` iff `Pr i (U v) = 0` for every `v` with
  `Pr i v = 0` whose samples shown to `i` vanish.
* `exists_rule_of_visBound_eq_zero`: if `f_i = 0`, the block row of `U` is a rule of the form of
  the scheme on the monolithic samples, with coefficients only on the partners. (The linear
  algebra behind it, a map that vanishes on the common kernel of `Pr` and of the samples is a
  combination of them, is `exists_rule_iff_ker_le` of `VisibilityExact`.)
* `isMemoryRun_pow`: with such rules for every `i`, every monolithic trajectory `k ↦ U^k x_0` is
  a run of the scheme.
* `IsMemoryRun.eq_of_start`: a run of a scheme is determined by its first `l` states (induction
  over the steps and, within a step, over the stages).
* `exists_exact_memory_scheme` (**the converse**): if `f_i = 0` for every `i`, there are
  coefficients `F i`, `G i j r` (zero unless `j` is a partner of `i`) such that every monolithic
  trajectory is a run of the scheme and every run with `x^k = U^k x_0` for `k ≤ l - 1` (started on
  samples of the monolithic system) satisfies `x^k = U^k x_0` for all `k`.
* `exists_exact_hold`: for one held sample every run of that scheme is `x^k = U^k x^0`, that is,
  the one-step map is `U`.

**What is proved of the paper's sentence.** Every number `l` of held samples, every order of
execution, subsystems of any finite dimension. "Started on samples of the monolithic system" is
read as: the first `l` states of the run, from which the stored samples of the first step are
taken, are those of a monolithic trajectory. The statement is about the runs; it does not use the
modified system of the scheme or the step map on states and stored samples.
-/
import CoSimFoundations.VisibilityExact

open Finset

namespace CoSimFoundations

section MemoryScheme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  {Yo : ι → Type*} [∀ j, NormedAddCommGroup (Yo j)] [∀ j, NormedSpace ℝ (Yo j)]

/-- `σ_ij`: `1` if subsystem `j` runs at an earlier stage than `i` (then `i` can use the new
sample of `j`), `0` otherwise. -/
def newSample (stage : ι → ℕ) (i j : ι) : ℕ :=
  if stage j < stage i then 1 else 0

/-- The monolithic samples shown to subsystem `i` (the paper, Definition `def:visibility`): for a
partner `j` and an age `r < l` the map `C_j U^{σ_ij - r} = c j ∘ Pr j ∘ U^{σ_ij} ∘ Ui^r`; zero if
`j` is not a partner of `i`. -/
def shownSample (Pr : ∀ i, E →L[ℝ] Es i) (c : ∀ j, Es j →L[ℝ] Yo j) (U Ui : E →L[ℝ] E)
    (stage : ι → ℕ) (partner : ι → ι → Prop) [DecidableRel partner] (l : ℕ) (i : ι)
    (k : ι × Fin l) : E →L[ℝ] Yo k.1 :=
  if partner i k.1 then
    (c k.1 ∘L Pr k.1) ∘L (U ^ newSample stage i k.1 * Ui ^ (k.2 : ℕ))
  else 0

/-- **A run of a scheme with `l` held samples** (the paper, eq. `eq:memory`): from the step `l - 1`
on, every subsystem advances by its coefficient `F i` on its own state and the coefficients
`G i j r` on the samples of the ages `r < l` of the outputs of the subsystems `j`, the newest
being that of the new state if `j` runs at an earlier stage. -/
def IsMemoryRun (Pr : ∀ i, E →L[ℝ] Es i) (c : ∀ j, Es j →L[ℝ] Yo j) (stage : ι → ℕ) (l : ℕ)
    (F : ∀ i, Es i →L[ℝ] Es i) (G : ∀ i j, Fin l → Yo j →L[ℝ] Es i) (x : ℕ → E) : Prop :=
  ∀ k, l - 1 ≤ k → ∀ i, Pr i (x (k + 1)) = F i (Pr i (x k)) +
    ∑ j, ∑ r : Fin l, G i j r (c j (Pr j (x (k + newSample stage i j - (r : ℕ)))))

variable {Pr : ∀ i, E →L[ℝ] Es i} {c : ∀ j, Es j →L[ℝ] Yo j} {U Ui : E →L[ℝ] E}
  {stage : ι → ℕ} {partner : ι → ι → Prop} [DecidableRel partner] {l : ℕ}

/-- **The states not shown to subsystem `i`** are those of Definition `def:visibility`: the own
state vanishes and so does every sample `C_j U^{σ_ij - r} v` of a partner `j`, `r < l`. -/
theorem mem_notShown_shownSample {i : ι} {v : E} :
    v ∈ notShown (Pr i) (shownSample Pr c U Ui stage partner l i) ↔
      Pr i v = 0 ∧ ∀ j, partner i j → ∀ r : Fin l,
        c j (Pr j ((U ^ newSample stage i j) ((Ui ^ (r : ℕ)) v))) = 0 := by
  rw [mem_notShown]
  refine and_congr Iff.rfl ⟨fun h j hp r => ?_, fun h k => ?_⟩
  · have h1 := h (j, r)
    simpa [shownSample, hp] using h1
  · by_cases hp : partner i k.1
    · have h1 := h k.1 hp k.2
      simpa [shownSample, hp] using h1
    · simp [shownSample, hp]

/-- **The visibility bound of subsystem `i` vanishes** iff the subsystem does not respond, in one
step of the monolithic system, to any state that it is not shown. -/
theorem visBound_shownSample_eq_zero_iff {i : ι} :
    visBound (Pr i) U (shownSample Pr c U Ui stage partner l i) = 0 ↔
      ∀ v : E, Pr i v = 0 →
        (∀ j, partner i j → ∀ r : Fin l,
          c j (Pr j ((U ^ newSample stage i j) ((Ui ^ (r : ℕ)) v))) = 0) →
        Pr i (U v) = 0 := by
  rw [visBound_eq_zero_iff]
  constructor
  · intro h v h1 h2
    exact h v (mem_notShown_shownSample.2 ⟨h1, h2⟩)
  · intro h v hv
    obtain ⟨h1, h2⟩ := mem_notShown_shownSample.1 hv
    exact h v h1 h2

/-- **The rule of subsystem `i`** (the paper, proof of Theorem `thm:visibility`: "the block row
`Π_i U` vanishes on the common kernel of `Π_i` and of the monolithic samples and is therefore a
linear combination of them"). If the visibility bound of `i` vanishes, there are a local
coefficient `F` and coefficients `G j r` on the samples, zero unless `j` is a partner of `i`, with
`Pr i (U v) = F (Pr i v) + Σ_j Σ_{r<l} G j r (C_j U^{σ_ij - r} v)` for every state `v`. -/
theorem exists_rule_of_visBound_eq_zero [∀ i, FiniteDimensional ℝ (Es i)]
    [∀ j, FiniteDimensional ℝ (Yo j)] {i : ι}
    (hf : visBound (Pr i) U (shownSample Pr c U Ui stage partner l i) = 0) :
    ∃ (F : Es i →L[ℝ] Es i) (G : ∀ j, Fin l → Yo j →L[ℝ] Es i),
      (∀ j, ¬ partner i j → G j = 0) ∧
      ∀ v : E, Pr i (U v) = F (Pr i v) +
        ∑ j, ∑ r : Fin l, G j r (c j (Pr j ((U ^ newSample stage i j) ((Ui ^ (r : ℕ)) v)))) := by
  obtain ⟨F, Gk, hrule⟩ := (visBound_eq_zero_iff_exists_rule (Pr i) U
    (shownSample Pr c U Ui stage partner l i)).1 hf
  refine ⟨F, fun j r => if partner i j then Gk (j, r) else 0, fun j hp => ?_, fun v => ?_⟩
  · funext r
    simp [hp]
  · have h := congrArg (fun T : E →L[ℝ] Es i => T v) hrule
    simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.sum_apply] at h
    rw [h, Fintype.sum_prod_type]
    congr 1
    refine sum_congr rfl fun j _ => sum_congr rfl fun r _ => ?_
    by_cases hp : partner i j
    · simp [shownSample, hp]
    · simp [shownSample, hp]

/-- On a monolithic trajectory the sample `C_j U^{σ - r}` of the state `U^k x_0` is taken from
the state `U^{k + σ - r} x_0`, for `r ≤ k`. -/
theorem pow_mul_inv_pow_apply_pow (hU : Ui * U = 1) (s : ℕ) {r k : ℕ} (hr : r ≤ k) (x0 : E) :
    (U ^ s) ((Ui ^ r) ((U ^ k) x0)) = (U ^ (k + s - r)) x0 := by
  have h : ∀ r : ℕ, Ui ^ r * U ^ r = 1 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc Ui, hU, one_mul, ih]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h1 : U ^ s * (Ui ^ r * U ^ (r + j)) = U ^ (r + j + s - r) := by
    rw [pow_add U r j, ← mul_assoc (Ui ^ r), h r, one_mul, ← pow_add]
    congr 1
    omega
  rw [← h1]
  rfl

/-- **The monolithic trajectories are runs of the scheme** whose rules reproduce the block rows
of the monolithic step on the monolithic samples. -/
theorem isMemoryRun_pow (hU : Ui * U = 1) {F : ∀ i, Es i →L[ℝ] Es i}
    {G : ∀ i j, Fin l → Yo j →L[ℝ] Es i}
    (hrule : ∀ i (v : E), Pr i (U v) = F i (Pr i v) +
      ∑ j, ∑ r : Fin l, G i j r (c j (Pr j ((U ^ newSample stage i j) ((Ui ^ (r : ℕ)) v)))))
    (x0 : E) : IsMemoryRun Pr c stage l F G fun k => (U ^ k) x0 := by
  intro k hk i
  have h1 : (U ^ (k + 1)) x0 = U ((U ^ k) x0) := by
    rw [pow_succ']
    rfl
  change Pr i ((U ^ (k + 1)) x0) = F i (Pr i ((U ^ k) x0)) +
    ∑ j, ∑ r : Fin l, G i j r (c j (Pr j ((U ^ (k + newSample stage i j - (r : ℕ))) x0)))
  rw [h1, hrule i]
  congr 1
  refine sum_congr rfl fun j _ => sum_congr rfl fun r _ => ?_
  rw [pow_mul_inv_pow_apply_pow hU _ (by have := r.2; omega) x0]

/-- **A run is determined by its first `l` states**: two runs of the same scheme that agree up
to the step `l - 1` agree at every step. Induction over the steps; within a step, over the
stages, since a subsystem uses new samples of subsystems at earlier stages only. -/
theorem IsMemoryRun.eq_of_start (hPr : ∀ v : E, (∀ i, Pr i v = 0) → v = 0)
    {F : ∀ i, Es i →L[ℝ] Es i} {G : ∀ i j, Fin l → Yo j →L[ℝ] Es i} {x y : ℕ → E}
    (hx : IsMemoryRun Pr c stage l F G x) (hy : IsMemoryRun Pr c stage l F G y)
    (h0 : ∀ k ≤ l - 1, x k = y k) : ∀ k, x k = y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge (l - 1) k with hk | hk
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hk))
      have hm : l - 1 ≤ m := Nat.lt_succ_iff.1 hk
      have key : ∀ s i, stage i = s → Pr i (x (m + 1)) = Pr i (y (m + 1)) := by
        intro s
        induction s using Nat.strong_induction_on with
        | _ s ihs =>
          intro i hi
          rw [hx m hm i, hy m hm i, ih m (Nat.lt_succ_self m)]
          congr 1
          refine sum_congr rfl fun j _ => sum_congr rfl fun r _ => ?_
          by_cases hji : stage j < stage i
          · by_cases hr : (r : ℕ) = 0
            · have he : m + newSample stage i j - (r : ℕ) = m + 1 := by
                simp [newSample, hji, hr]
              rw [he, ihs (stage j) (hi ▸ hji) j rfl]
            · have hlt : m + newSample stage i j - (r : ℕ) < m + 1 := by
                simp only [newSample, ite_eq_left hji]
                omega
              rw [ih _ hlt]
          · have hlt : m + newSample stage i j - (r : ℕ) < m + 1 := by
              simp only [newSample, ite_eq_right hji]
              omega
            rw [ih _ hlt]
      have hz := hPr (x (m + 1) - y (m + 1)) fun i => by
        rw [map_sub, key (stage i) i rfl, sub_self]
      exact sub_eq_zero.1 hz
    · exact h0 k hk

variable [∀ i, FiniteDimensional ℝ (Es i)] [∀ j, FiniteDimensional ℝ (Yo j)]

/-- **The converse of the visibility theorem, `l` held samples, any order of execution** (the paper,
Theorem `thm:visibility`). Let the projections `Pr i` onto the subsystems be jointly injective,
let the outputs be `C_j = c j ∘ Pr j`, and let `Ui` be a left inverse of the monolithic step `U`.
If the visibility bound `f_i` of every subsystem vanishes, there are coefficients `F i` and
`G i j r`, zero unless `j` is a partner of `i`, such that
* every monolithic trajectory `k ↦ U^k x_0` is a run of the scheme with these coefficients, and
* every run of the scheme that starts on samples of the monolithic system, `x^k = U^k x_0` for
  `k ≤ l - 1`, reproduces it at every communication point: `x^k = U^k x_0` for all `k`. -/
theorem exists_exact_memory_scheme (hPr : ∀ v : E, (∀ i, Pr i v = 0) → v = 0)
    (hU : Ui * U = 1)
    (hf : ∀ i, visBound (Pr i) U (shownSample Pr c U Ui stage partner l i) = 0) :
    ∃ (F : ∀ i, Es i →L[ℝ] Es i) (G : ∀ i j, Fin l → Yo j →L[ℝ] Es i),
      (∀ i j, ¬ partner i j → G i j = 0) ∧
      (∀ x0 : E, IsMemoryRun Pr c stage l F G fun k => (U ^ k) x0) ∧
      ∀ (x : ℕ → E) (x0 : E), (∀ k ≤ l - 1, x k = (U ^ k) x0) →
        IsMemoryRun Pr c stage l F G x → ∀ k, x k = (U ^ k) x0 := by
  choose F G hG hrule using fun i => exists_rule_of_visBound_eq_zero (hf i)
  refine ⟨F, G, hG, fun x0 => isMemoryRun_pow hU hrule x0, fun x x0 h0 hx => ?_⟩
  exact hx.eq_of_start hPr (isMemoryRun_pow hU hrule x0) h0

/-- **The converse of the visibility theorem for one held sample** (paper: "For one held sample
this is `X = U`"), subsystems of any dimension, any order of execution: if every visibility bound
vanishes, a hold exists all of whose runs are monolithic trajectories, `x^k = U^k x^0`. -/
theorem exists_exact_hold (hPr : ∀ v : E, (∀ i, Pr i v = 0) → v = 0) (hU : Ui * U = 1)
    (hf : ∀ i, visBound (Pr i) U (shownSample Pr c U Ui stage partner 1 i) = 0) :
    ∃ (F : ∀ i, Es i →L[ℝ] Es i) (G : ∀ i j, Fin 1 → Yo j →L[ℝ] Es i),
      (∀ i j, ¬ partner i j → G i j = 0) ∧
      ∀ x : ℕ → E, IsMemoryRun Pr c stage 1 F G x → ∀ k, x k = (U ^ k) (x 0) := by
  obtain ⟨F, G, hG, -, h⟩ := exists_exact_memory_scheme hPr hU hf
  refine ⟨F, G, hG, fun x hx => h x (x 0) (fun k hk => ?_) hx⟩
  have hk0 : k = 0 := by omega
  rw [hk0, pow_zero]
  rfl

end MemoryScheme

end CoSimFoundations
