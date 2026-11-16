/-
The eigenvalue equation of a sequential scheme on a tree, for a scheme with one held sample
(`HeldScheme`) and for the zero-order hold (the paper, Section "Energy stored and energy
created", equation `eq:tree` and the sentence before it: on a tree the order of execution of a
sequential scheme changes no decay rate and no frequency if the coefficients do not depend on
the order).

`TreeDeterminant` proves `det(s² - X) = det(s² - F - s (N + M))` for matrices with a potential.
Here the matrices are those of a `HeldScheme` `S` (`X = F + M + N X`, `F` block diagonal, `N`
from partners at an earlier stage, `M` from partners that do not run at an earlier stage).

* `det_sq_sub_X_of_potential`: if `p` is a potential of the subsystems, that is, every pair of
  partners `s`, `t` runs at different stages and `p` is larger by one at the one that runs
  later, then over every field `𝕜 ⊇ ℝ` and for every `s : 𝕜`,
  `det(s² - X) = det(s² - F - s (N + M))`.
* `det_sq_sub_X_of_isAcyclic`: the same if the partners are linked in an acyclic graph on
  finitely many subsystems and no two partners share a stage (the potential exists,
  `exists_stagePotential`).
* `det_sq_sub_zoh_X`: for the zero-order hold `S.zoh A hA H`,
  `det(s² - X) = det(s² - e^{H A₀} - s (∫₀ᴴ e^{τ A₀} dτ) A_c)`; the right side does not contain
  the stages.
* `charpoly_zoh_restage_eq`: the zero-order holds in any two assignments of stages without two
  partners at the same stage have the same characteristic polynomial, hence the same
  eigenvalues with the same multiplicities.
-/
import CoSimFoundations.TreeDeterminant
import CoSimFoundations.ReversedOrder

open Matrix

namespace CoSimFoundations

namespace HeldScheme

variable {n : ℕ} {κ : Type*} (S : HeldScheme n κ) {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜]

/-- **The eigenvalue equation of a scheme with one held sample, with a potential.** Let every
pair of partners `s`, `t` run at different stages and let `p` be larger by one at the one that
runs later. Then over every field `𝕜 ⊇ ℝ` and for every `s : 𝕜`,
`det(s² - X) = det(s² - F - s (N + M))`. -/
theorem det_sq_sub_X_of_potential (p : κ → ℤ)
    (hp : ∀ s t, S.partner s t → (S.stage t < S.stage s ∧ p s = p t + 1) ∨
      (S.stage s < S.stage t ∧ p t = p s + 1)) (s : 𝕜) :
    (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.X.map (algebraMap ℝ 𝕜)).det =
      (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.F.map (algebraMap ℝ 𝕜) -
        s • (S.N + S.M).map (algebraMap ℝ 𝕜)).det := by
  have hX0 : (1 - S.N) * S.X = S.F + S.M := by
    rw [sub_mul, one_mul, sub_eq_iff_eq_add]
    exact S.hX
  have hX := congrArg (algebraMap ℝ 𝕜).mapMatrix hX0
  simp only [map_mul, map_sub, map_add, map_one, RingHom.mapMatrix_apply] at hX
  have hsum : S.N.map (algebraMap ℝ 𝕜) + S.M.map (algebraMap ℝ 𝕜) =
      (S.N + S.M).map (algebraMap ℝ 𝕜) := by
    ext i j
    rw [Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, ← map_add,
      Matrix.add_apply]
  have hF' : ∀ i j, p (S.sub i) ≠ p (S.sub j) → (S.F.map (algebraMap ℝ 𝕜)) i j = 0 :=
    fun i j h => by
      rw [Matrix.map_apply, S.hF i j fun e => h (by rw [e]), map_zero]
  have hN' : ∀ i j, p (S.sub i) ≠ p (S.sub j) + 1 → (S.N.map (algebraMap ℝ 𝕜)) i j = 0 :=
    fun i j h => by
      have h0 : S.N i j = 0 := S.hN i j fun hc => by
        rcases hp _ _ hc.1 with h1 | h1
        · exact h h1.2
        · exact lt_asymm hc.2 h1.1
      rw [Matrix.map_apply, h0, map_zero]
  have hM' : ∀ i j, p (S.sub j) ≠ p (S.sub i) + 1 → (S.M.map (algebraMap ℝ 𝕜)) i j = 0 :=
    fun i j h => by
      have h0 : S.M i j = 0 := S.hM i j fun hc => by
        rcases hp _ _ hc.1 with h1 | h1
        · exact hc.2 h1.1
        · exact h h1.2
      rw [Matrix.map_apply, h0, map_zero]
  rw [det_sq_sub_eq_of_potential (fun i => p (S.sub i)) hF' hN' hM' hX s, hsum]

/-- **The eigenvalue equation of a sequential scheme on a tree** (the paper, equation `eq:tree`).
Let the partners be linked in an acyclic graph `Gr` on finitely many subsystems and let no two
partners share a stage. Then over every field `𝕜 ⊇ ℝ` and for every `s : 𝕜`,
`det(s² - X) = det(s² - F - s (N + M))`. -/
theorem det_sq_sub_X_of_isAcyclic [Fintype κ] {Gr : SimpleGraph κ} (hGr : Gr.IsAcyclic)
    (hpart : ∀ s t, S.partner s t → Gr.Adj s t)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t) (s : 𝕜) :
    (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.X.map (algebraMap ℝ 𝕜)).det =
      (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.F.map (algebraMap ℝ 𝕜) -
        s • (S.N + S.M).map (algebraMap ℝ 𝕜)).det := by
  obtain ⟨p, hp⟩ := exists_stagePotential hGr S.stage
  refine S.det_sq_sub_X_of_potential p (fun a b hab => ?_) s
  have hadj := hpart a b hab
  have hne := hns a b (Gr.ne_of_adj hadj) hab
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr ⟨h, hp b a hadj.symm h⟩
  · exact Or.inl ⟨h, hp a b hadj h⟩

variable [DecidableEq κ]

/-- **The eigenvalue equation of the zero-order hold on a tree** (the paper, equation `eq:tree`).
Let the partners be linked in an acyclic graph on finitely many subsystems and let no two
partners share a stage. The one-step map `X` of the zero-order hold obeys, over every field
`𝕜 ⊇ ℝ` and for every `s : 𝕜`, `det(s² - X) = det(s² - e^{H A₀} - s G° C)`,
`G° C = (∫₀ᴴ e^{τ A₀} dτ) A_c` (`zohCoupling`). -/
theorem det_sq_sub_zoh_X [Fintype κ] {Gr : SimpleGraph κ} (hGr : Gr.IsAcyclic)
    (hpart : ∀ s t, S.partner s t → Gr.Adj s t)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (s : 𝕜) :
    (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - (S.zoh A hA H).X.map (algebraMap ℝ 𝕜)).det =
      (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) -
        (NormedSpace.exp (H • S.blockDiag A)).map (algebraMap ℝ 𝕜) -
        s • (S.zohCoupling A H).map (algebraMap ℝ 𝕜)).det := by
  have h := (S.zoh A hA H).det_sq_sub_X_of_isAcyclic (𝕜 := 𝕜) hGr hpart hns s
  rw [add_comm, S.zoh_M_add_N] at h
  exact h

/-- **On a tree the order of execution of a sequential zero-order hold changes no eigenvalue**
(the paper, Section "Energy stored and energy created"). Let the partners be linked in an acyclic
graph on finitely many subsystems. For two assignments of stages, `S.stage` and `st`, in each of
which no two partners share a stage, the one-step maps of the zero-order hold have the same
characteristic polynomial, for every macro step `H`. -/
theorem charpoly_zoh_restage_eq [Fintype κ] {Gr : SimpleGraph κ} (hGr : Gr.IsAcyclic)
    (hpart : ∀ s t, S.partner s t → Gr.Adj s t)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t) {st : κ → ℕ}
    (hns' : ∀ s t, s ≠ t → S.partner s t → st s ≠ st t) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    ((S.restage st).zoh A hA H).X.charpoly = (S.zoh A hA H).X.charpoly :=
  charpoly_eq_of_det_sq_sub_eq fun s => by
    rw [(S.restage st).det_sq_sub_zoh_X hGr hpart hns' hA H s,
      S.det_sq_sub_zoh_X hGr hpart hns hA H s]
    rfl

end HeldScheme

end CoSimFoundations
