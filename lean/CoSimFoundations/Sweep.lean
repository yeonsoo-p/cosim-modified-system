/-
The energy-conserving sweep on a chain of any length (the paper, Proposition 5.5).

On `n = m + 2` stores (index `Fin (m + 2)`), let `R k` be the plane rotation by the angle `φ k` in
the coordinates `k`, `k + 1` (`planeRot (φ k) k`: `cos φ k` on the two diagonal places, `-sin φ k`
at `(k, k+1)`, `sin φ k` at `(k+1, k)`, the identity elsewhere), and

  `X = R m * ⋯ * R 1 * R 0`   (`sweep φ m`; the rotation of the first link is applied first).

The angles are a function `φ : ℕ → ℝ` of which only `φ 0, …, φ m` enter. Statements:

* `Xᵀ X = 1` (`sweep_transpose_mul_self`): every factor is orthogonal.
* If `cos (φ k) ≠ 0` for `k ≤ m`, then `X` satisfies the relation of a Gauss–Seidel scheme with one
  held sample that executes the stores in the order `0, 1, …, n-1` (`InfoForm`):
  `(1 - N) X = diagonal F + M` with the coefficients of the paper,
    `F 0 = cos φ 0`, `F k = cos φ k / cos φ (k-1)` (`0 < k < n-1`), `F (n-1) = 1 / cos φ (n-2)`,
    `N k (k-1) = cos φ k · tan φ (k-1)` (`k < n-1`), `N (n-1) (n-2) = tan φ (n-2)`,
    `M k (k+1) = -sin φ k`,
  all other entries zero (`one_sub_infoNew_mul_sweep`, with `sweepF`, `sweepG`,
  `infoNew_sweepG_apply`, `infoOld_sweepG_apply`). Hence `X` is the one-step map of that scheme
  (`sweep_eq_infoStep`), all `F k` are positive if all `cos (φ k)` are (`sweepF_pos`), and for
  every network of scalar stores, output feedback and weights on the links of the chain realise it
  (`ScalarNet.exists_gsStep_eq_sweep`).

Proof of the relation (the recursion of the paper). Let `X_j = R j * ⋯ * R 0`. By induction on `j`:
the rows `> j + 1` of `X_j` are those of the identity; the row `j + 1` (the intermediate value of
store `j + 1`) is `tan φ j · (row j) + e_{j+1} / cos φ j`; row `0` is
`cos φ 0 · e_0 - sin φ 0 · e_1`;
and every row `1 ≤ i ≤ j` is final,
`row i = (cos φ i / cos φ (i-1)) e_i + cos φ i · tan φ (i-1) · (row (i-1)) - sin φ i · e_{i+1}`.
The step multiplies by `R (j+1)`, which changes the rows `j + 1` and `j + 2` only. At `j = m` these
are the rows of the relation.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import CoSimFoundations.InfoForm
import CoSimFoundations.SpectrumEnergyJacobi

open Matrix Real

namespace CoSimFoundations

variable {n : ℕ}

/-- The plane rotation by `θ` in the coordinates `k`, `k + 1` of `ℝⁿ` (it is a rotation if
`k + 1 < n`). -/
noncomputable def planeRot (θ : ℝ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = k then
      if (j : ℕ) = k then cos θ else if (j : ℕ) = k + 1 then -sin θ else 0
    else if (i : ℕ) = k + 1 then
      if (j : ℕ) = k then sin θ else if (j : ℕ) = k + 1 then cos θ else 0
    else if i = j then 1 else 0

/-- Row `k` of the rotation. -/
theorem planeRot_apply_fst (θ : ℝ) {k : ℕ} {i : Fin n} (hi : (i : ℕ) = k) (l : Fin n) :
    planeRot θ k i l =
      if (l : ℕ) = k then cos θ else if (l : ℕ) = k + 1 then -sin θ else 0 := by
  simp only [planeRot, of_apply, ite_eq_left hi]

/-- Row `k + 1` of the rotation. -/
theorem planeRot_apply_snd (θ : ℝ) {k : ℕ} {i : Fin n} (hi : (i : ℕ) = k + 1) (l : Fin n) :
    planeRot θ k i l =
      if (l : ℕ) = k then sin θ else if (l : ℕ) = k + 1 then cos θ else 0 := by
  have h : (i : ℕ) ≠ k := by omega
  simp only [planeRot, of_apply, ite_eq_right h, ite_eq_left hi]

/-- The other rows of the rotation are those of the identity. -/
theorem planeRot_apply_of_ne (θ : ℝ) {k : ℕ} {i : Fin n} (h1 : (i : ℕ) ≠ k)
    (h2 : (i : ℕ) ≠ k + 1) (l : Fin n) :
    planeRot θ k i l = if i = l then 1 else 0 := by
  simp only [planeRot, of_apply, ite_eq_right h1, ite_eq_right h2]

/-- Row `k` of a product with the rotation on the left. -/
theorem planeRot_mul_apply_fst (θ : ℝ) {k : ℕ} {i i' : Fin n} (hi : (i : ℕ) = k)
    (hi' : (i' : ℕ) = k + 1) (A : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) :
    (planeRot θ k * A : Matrix (Fin n) (Fin n) ℝ) i l = cos θ * A i l - sin θ * A i' l := by
  have hne : i ≠ i' := fun h => by
    rw [h] at hi
    omega
  have e1 : planeRot θ k i i = cos θ := by rw [planeRot_apply_fst θ hi, ite_eq_left hi]
  have e2 : planeRot θ k i i' = -sin θ := by
    rw [planeRot_apply_fst θ hi, ite_eq_right (by omega), ite_eq_left hi']
  rw [Matrix.mul_apply, Fintype.sum_eq_add i i' hne, e1, e2]
  · ring
  · rintro x ⟨hx, hx'⟩
    have h1 : (x : ℕ) ≠ k := fun h => hx (Fin.ext (h.trans hi.symm))
    have h2 : (x : ℕ) ≠ k + 1 := fun h => hx' (Fin.ext (h.trans hi'.symm))
    rw [planeRot_apply_fst θ hi, ite_eq_right h1, ite_eq_right h2, zero_mul]

/-- Row `k + 1` of a product with the rotation on the left. -/
theorem planeRot_mul_apply_snd (θ : ℝ) {k : ℕ} {i i' : Fin n} (hi : (i : ℕ) = k)
    (hi' : (i' : ℕ) = k + 1) (A : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) :
    (planeRot θ k * A : Matrix (Fin n) (Fin n) ℝ) i' l = sin θ * A i l + cos θ * A i' l := by
  have hne : i ≠ i' := fun h => by
    rw [h] at hi
    omega
  have e1 : planeRot θ k i' i = sin θ := by rw [planeRot_apply_snd θ hi', ite_eq_left hi]
  have e2 : planeRot θ k i' i' = cos θ := by
    rw [planeRot_apply_snd θ hi', ite_eq_right (by omega), ite_eq_left hi']
  rw [Matrix.mul_apply, Fintype.sum_eq_add i i' hne, e1, e2]
  rintro x ⟨hx, hx'⟩
  have h1 : (x : ℕ) ≠ k := fun h => hx (Fin.ext (h.trans hi.symm))
  have h2 : (x : ℕ) ≠ k + 1 := fun h => hx' (Fin.ext (h.trans hi'.symm))
  rw [planeRot_apply_snd θ hi', ite_eq_right h1, ite_eq_right h2, zero_mul]

/-- The other rows of a product with the rotation on the left are unchanged. -/
theorem planeRot_mul_apply_of_ne (θ : ℝ) {k : ℕ} {i : Fin n} (h1 : (i : ℕ) ≠ k)
    (h2 : (i : ℕ) ≠ k + 1) (A : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) :
    (planeRot θ k * A : Matrix (Fin n) (Fin n) ℝ) i l = A i l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [planeRot_apply_of_ne θ h1 h2, ite_eq_left rfl, one_mul]
  · intro x _ hx
    rw [planeRot_apply_of_ne θ h1 h2, ite_eq_right (Ne.symm hx), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The transpose of a plane rotation is the rotation by the opposite angle. -/
theorem planeRot_transpose (θ : ℝ) (k : ℕ) :
    (planeRot θ k : Matrix (Fin n) (Fin n) ℝ)ᵀ = planeRot (-θ) k := by
  ext i j
  rw [transpose_apply]
  by_cases hi : (i : ℕ) = k
  · rw [planeRot_apply_fst _ hi]
    by_cases hj : (j : ℕ) = k
    · rw [planeRot_apply_fst _ hj, ite_eq_left hi, ite_eq_left hj, cos_neg]
    · by_cases hj' : (j : ℕ) = k + 1
      · rw [planeRot_apply_snd _ hj', ite_eq_left hi, ite_eq_right hj, ite_eq_left hj', sin_neg,
          neg_neg]
      · have hne : j ≠ i := fun h => hj (by rw [h]; exact hi)
        rw [planeRot_apply_of_ne _ hj hj', ite_eq_right hne, ite_eq_right hj, ite_eq_right hj']
  · by_cases hi' : (i : ℕ) = k + 1
    · rw [planeRot_apply_snd _ hi']
      by_cases hj : (j : ℕ) = k
      · rw [planeRot_apply_fst _ hj, ite_eq_right hi, ite_eq_left hi', ite_eq_left hj, sin_neg]
      · by_cases hj' : (j : ℕ) = k + 1
        · rw [planeRot_apply_snd _ hj', ite_eq_right hi, ite_eq_left hi', ite_eq_right hj,
            ite_eq_left hj', cos_neg]
        · have hne : j ≠ i := fun h => hj' (by rw [h]; exact hi')
          rw [planeRot_apply_of_ne _ hj hj', ite_eq_right hne, ite_eq_right hj, ite_eq_right hj']
    · rw [planeRot_apply_of_ne _ hi hi']
      by_cases hj : (j : ℕ) = k
      · have hne : i ≠ j := fun h => hi (by rw [h]; exact hj)
        rw [planeRot_apply_fst _ hj, ite_eq_right hi, ite_eq_right hi', ite_eq_right hne]
      · by_cases hj' : (j : ℕ) = k + 1
        · have hne : i ≠ j := fun h => hi' (by rw [h]; exact hj')
          rw [planeRot_apply_snd _ hj', ite_eq_right hi, ite_eq_right hi', ite_eq_right hne]
        · rw [planeRot_apply_of_ne _ hj hj']
          by_cases hij : i = j
          · rw [ite_eq_left hij, ite_eq_left hij.symm]
          · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]

/-- **A plane rotation is orthogonal.** -/
theorem planeRot_transpose_mul_self (θ : ℝ) {k : ℕ} (hk : k + 1 < n) :
    (planeRot θ k : Matrix (Fin n) (Fin n) ℝ)ᵀ * planeRot θ k = 1 := by
  have hk0 : k < n := by omega
  have h0 : ((⟨k, hk0⟩ : Fin n) : ℕ) = k := rfl
  have h1 : ((⟨k + 1, hk⟩ : Fin n) : ℕ) = k + 1 := rfl
  have hsc := sin_sq_add_cos_sq θ
  rw [planeRot_transpose]
  ext i l
  rw [Matrix.one_apply]
  by_cases hi : (i : ℕ) = k
  · rw [planeRot_mul_apply_fst _ hi h1, planeRot_apply_fst _ hi, planeRot_apply_snd _ h1, cos_neg,
      sin_neg]
    by_cases hl : (l : ℕ) = k
    · have hil : i = l := Fin.ext (hi.trans hl.symm)
      rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left hil]
      linear_combination hsc
    · have hil : i ≠ l := fun h => hl (by rw [← h]; exact hi)
      by_cases hl' : (l : ℕ) = k + 1
      · rw [ite_eq_right hl, ite_eq_left hl', ite_eq_right hl, ite_eq_left hl', ite_eq_right hil]
        ring
      · rw [ite_eq_right hl, ite_eq_right hl', ite_eq_right hl, ite_eq_right hl', ite_eq_right hil]
        ring
  · by_cases hi' : (i : ℕ) = k + 1
    · rw [planeRot_mul_apply_snd _ h0 hi', planeRot_apply_fst _ h0, planeRot_apply_snd _ hi',
        cos_neg, sin_neg]
      by_cases hl : (l : ℕ) = k
      · have hil : i ≠ l := fun h => hi (by rw [h]; exact hl)
        rw [ite_eq_left hl, ite_eq_left hl, ite_eq_right hil]
        ring
      · by_cases hl' : (l : ℕ) = k + 1
        · have hil : i = l := Fin.ext (hi'.trans hl'.symm)
          rw [ite_eq_right hl, ite_eq_left hl', ite_eq_right hl, ite_eq_left hl', ite_eq_left hil]
          linear_combination hsc
        · have hil : i ≠ l := fun h => hl' (by rw [← h]; exact hi')
          rw [ite_eq_right hl, ite_eq_right hl', ite_eq_right hl, ite_eq_right hl',
            ite_eq_right hil]
          ring
    · rw [planeRot_mul_apply_of_ne _ hi hi', planeRot_apply_of_ne _ hi hi']

/-- The partial products of the sweep: `sweepPart φ j = R (j-1) * ⋯ * R 0`. -/
noncomputable def sweepPart (φ : ℕ → ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | j + 1 => planeRot (φ j) j * sweepPart φ j

/-- **The sweep** on `m + 2` stores: `X = R m * ⋯ * R 1 * R 0` (the paper, equation (29)). -/
noncomputable def sweep (φ : ℕ → ℝ) (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  sweepPart φ (m + 1)

/-- The partial product as a product of the list of rotations, the last rotation on the left. -/
theorem sweepPart_eq_prod (φ : ℕ → ℝ) (j : ℕ) :
    (sweepPart φ j : Matrix (Fin n) (Fin n) ℝ) =
      (((List.range j).map fun k => planeRot (φ k) k).reverse).prod := by
  induction j with
  | zero => simp [sweepPart]
  | succ j ih => simp [sweepPart, ih, List.range_succ]

/-- The sweep on two stores is one rotation. -/
theorem sweep_zero (φ : ℕ → ℝ) : sweep φ 0 = planeRot (φ 0) 0 := by
  simp [sweep, sweepPart]

/-- The sweep on three stores is the product of two rotations. -/
theorem sweep_one (φ : ℕ → ℝ) : sweep φ 1 = planeRot (φ 1) 1 * planeRot (φ 0) 0 := by
  simp [sweep, sweepPart]

/-- The partial products are orthogonal. -/
theorem sweepPart_transpose_mul_self (φ : ℕ → ℝ) {j : ℕ} (hj : j < n) :
    (sweepPart φ j : Matrix (Fin n) (Fin n) ℝ)ᵀ * sweepPart φ j = 1 := by
  induction j with
  | zero => simp [sweepPart]
  | succ j ih =>
    rw [sweepPart, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (planeRot (φ j) j)ᵀ, planeRot_transpose_mul_self _ hj, Matrix.one_mul]
    exact ih (by omega)

/-- **The sweep is orthogonal** (the paper, Proposition 5.5): `Xᵀ X = 1`, for all angles. -/
theorem sweep_transpose_mul_self (φ : ℕ → ℝ) (m : ℕ) : (sweep φ m)ᵀ * sweep φ m = 1 :=
  sweepPart_transpose_mul_self φ (by omega)

/-- The invariant of the recursion over the stores, for `X = R j * ⋯ * R 0`: the rows above
`j + 1` are untouched, the row `j + 1` is the intermediate value, the rows up to `j` are final. -/
private def SweepInv (φ : ℕ → ℝ) (j : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i l : Fin n, j + 1 < (i : ℕ) → X i l = if i = l then 1 else 0) ∧
  (∀ i i' l : Fin n, (i : ℕ) = j → (i' : ℕ) = j + 1 →
    X i' l = tan (φ j) * X i l + (if i' = l then 1 else 0) / cos (φ j)) ∧
  (∀ i l : Fin n, (i : ℕ) = 0 →
    X i l = cos (φ 0) * (if i = l then 1 else 0) - sin (φ 0) * (if (l : ℕ) = 1 then 1 else 0)) ∧
  ∀ i₀ i l : Fin n, (i₀ : ℕ) + 1 = i → (i : ℕ) ≤ j →
    X i l = cos (φ i) / cos (φ i₀) * (if i = l then 1 else 0) + cos (φ i) * tan (φ i₀) * X i₀ l -
      sin (φ i) * (if (l : ℕ) = (i : ℕ) + 1 then 1 else 0)

/-- The invariant holds after the first rotation. -/
private theorem sweepInv_zero (φ : ℕ → ℝ) (hc : cos (φ 0) ≠ 0) :
    SweepInv φ 0 (sweepPart φ 1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hX : (sweepPart φ 1 : Matrix (Fin n) (Fin n) ℝ) = planeRot (φ 0) 0 := by
    simp [sweepPart]
  rw [hX]
  refine ⟨fun i l hi => ?_, fun i i' l hi hi' => ?_, fun i l hi => ?_, fun i₀ i l h hi => ?_⟩
  · exact planeRot_apply_of_ne _ (by omega) (by omega) l
  · rw [planeRot_apply_snd _ hi', planeRot_apply_fst _ hi, tan_eq_sin_div_cos]
    have hsc := sin_sq_add_cos_sq (φ 0)
    by_cases hl : (l : ℕ) = 0
    · have hil : i' ≠ l := fun h => by
        rw [h] at hi'
        omega
      rw [ite_eq_left hl, ite_eq_left hl, ite_eq_right hil]
      field_simp
      ring
    · by_cases hl' : (l : ℕ) = 0 + 1
      · have hil : i' = l := Fin.ext (hi'.trans hl'.symm)
        rw [ite_eq_right hl, ite_eq_left hl', ite_eq_right hl, ite_eq_left hl', ite_eq_left hil]
        field_simp
        linear_combination hsc
      · have hil : i' ≠ l := fun h => hl' (by rw [← h]; exact hi')
        rw [ite_eq_right hl, ite_eq_right hl', ite_eq_right hl, ite_eq_right hl', ite_eq_right hil]
        simp
  · rw [planeRot_apply_fst _ hi]
    by_cases hl : (l : ℕ) = 0
    · have hil : i = l := Fin.ext (hi.trans hl.symm)
      have hl1 : (l : ℕ) ≠ 1 := by omega
      rw [ite_eq_left hl, ite_eq_left hil, ite_eq_right hl1]
      ring
    · have hil : i ≠ l := fun h => hl (by rw [← h]; exact hi)
      by_cases hl' : (l : ℕ) = 0 + 1
      · have hl1 : (l : ℕ) = 1 := hl'
        rw [ite_eq_right hl, ite_eq_left hl', ite_eq_right hil, ite_eq_left hl1]
        ring
      · have hl1 : (l : ℕ) ≠ 1 := hl'
        rw [ite_eq_right hl, ite_eq_right hl', ite_eq_right hil, ite_eq_right hl1]
        ring
  · omega

/-- The next rotation preserves the invariant: it changes the rows `j + 1` and `j + 2` only. -/
private theorem sweepInv_succ (φ : ℕ → ℝ) {j : ℕ} (hc : cos (φ (j + 1)) ≠ 0) (hn : j + 2 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : SweepInv φ j X) :
    SweepInv φ (j + 1) (planeRot (φ (j + 1)) (j + 1) * X) := by
  obtain ⟨ha, hb, hc0, hfin⟩ := hX
  have hsc := sin_sq_add_cos_sq (φ (j + 1))
  have hq : ((⟨j + 2, hn⟩ : Fin n) : ℕ) = j + 1 + 1 := rfl
  refine ⟨fun i l hi => ?_, fun i i' l hi hi' => ?_, fun i l hi => ?_, fun i₀ i l h hi => ?_⟩
  · rw [planeRot_mul_apply_of_ne _ (by omega) (by omega)]
    exact ha i l (by omega)
  · rw [planeRot_mul_apply_snd _ hi hi', planeRot_mul_apply_fst _ hi hi', ha i' l (by omega),
      tan_eq_sin_div_cos]
    field_simp
    linear_combination (if i' = l then (1 : ℝ) else 0) * hsc
  · rw [planeRot_mul_apply_of_ne _ (by omega) (by omega)]
    exact hc0 i l hi
  · have h0 : (planeRot (φ (j + 1)) (j + 1) * X : Matrix (Fin n) (Fin n) ℝ) i₀ l = X i₀ l :=
      planeRot_mul_apply_of_ne _ (by omega) (by omega) X l
    rw [h0]
    by_cases hij : (i : ℕ) ≤ j
    · rw [planeRot_mul_apply_of_ne _ (by omega) (by omega)]
      exact hfin i₀ i l h hij
    · have hi1 : (i : ℕ) = j + 1 := by omega
      have hi0 : (i₀ : ℕ) = j := by omega
      have hq' : (if (⟨j + 2, hn⟩ : Fin n) = l then (1 : ℝ) else 0) =
          if (l : ℕ) = (i : ℕ) + 1 then 1 else 0 := by
        by_cases hl : (l : ℕ) = (i : ℕ) + 1
        · have : (⟨j + 2, hn⟩ : Fin n) = l := Fin.ext (by rw [hl, hi1])
          rw [ite_eq_left hl, ite_eq_left this]
        · have : (⟨j + 2, hn⟩ : Fin n) ≠ l := fun h' => hl (by rw [← h', hi1])
          rw [ite_eq_right hl, ite_eq_right this]
      rw [planeRot_mul_apply_fst _ hi1 hq, ha ⟨j + 2, hn⟩ l (show j + 1 < j + 2 by omega), hq',
        hb i₀ i l hi0 hi1, hi1, hi0]
      ring

/-- The invariant holds for every partial product of the sweep. -/
private theorem sweepInv (φ : ℕ → ℝ) {j : ℕ} (hc : ∀ k ≤ j, cos (φ k) ≠ 0) (hn : j + 1 < n) :
    SweepInv φ j (sweepPart φ (j + 1) : Matrix (Fin n) (Fin n) ℝ) := by
  induction j with
  | zero => exact sweepInv_zero φ (hc 0 le_rfl)
  | succ j ih =>
    exact sweepInv_succ φ (hc (j + 1) le_rfl) hn
      (ih (fun k hk => hc k (by omega)) (by omega))

/-- The local coefficients of the sweep (the paper, Proposition 5.5): `F 0 = cos φ 0`,
`F k = cos φ k / cos φ (k-1)` for `0 < k < m + 1`, `F (m+1) = 1 / cos φ m`. -/
noncomputable def sweepF (φ : ℕ → ℝ) (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  if (i : ℕ) = 0 then cos (φ 0)
  else if (i : ℕ) = m + 1 then 1 / cos (φ m)
  else cos (φ i) / cos (φ ((i : ℕ) - 1))

/-- The sample coefficients of the sweep: store `k` uses the sample of store `k - 1` with the
coefficient `cos φ k · tan φ (k-1)` (`tan φ m` for the last store) and the sample of store `k + 1`
with the coefficient `-sin φ k`. -/
noncomputable def sweepG (φ : ℕ → ℝ) (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  Matrix.of fun i j =>
    if (j : ℕ) + 1 = i then (if (i : ℕ) = m + 1 then tan (φ j) else cos (φ i) * tan (φ j))
    else if (j : ℕ) = (i : ℕ) + 1 then -sin (φ i) else 0

/-- The sample coefficients vanish on the diagonal. -/
theorem sweepG_diag (φ : ℕ → ℝ) (m : ℕ) (i : Fin (m + 2)) : sweepG φ m i i = 0 := by
  simp [sweepG]

/-- In the order `0, 1, …, n-1` the new samples of the sweep are those of the store before:
`N k (k-1) = cos φ k · tan φ (k-1)`, and `N (n-1) (n-2) = tan φ (n-2)`. -/
theorem infoNew_sweepG_apply (φ : ℕ → ℝ) (m : ℕ) (i j : Fin (m + 2)) :
    infoNew (fun i : Fin (m + 2) => (i : ℕ)) (sweepG φ m) i j =
      if (j : ℕ) + 1 = i then (if (i : ℕ) = m + 1 then tan (φ j) else cos (φ i) * tan (φ j))
      else 0 := by
  rw [infoNew_apply]
  by_cases h : (j : ℕ) + 1 = i
  · have hlt : (j : ℕ) < i := by omega
    simp only [sweepG, of_apply, ite_eq_left h, ite_eq_left hlt]
  · by_cases hlt : (j : ℕ) < i
    · have h' : (j : ℕ) ≠ (i : ℕ) + 1 := by omega
      simp only [sweepG, of_apply, ite_eq_right h, ite_eq_left hlt, ite_eq_right h']
    · simp only [ite_eq_right hlt, ite_eq_right h]

/-- In the order `0, 1, …, n-1` the old samples of the sweep are those of the store after:
`M k (k+1) = -sin φ k`. -/
theorem infoOld_sweepG_apply (φ : ℕ → ℝ) (m : ℕ) (i j : Fin (m + 2)) :
    infoOld (fun i : Fin (m + 2) => (i : ℕ)) (sweepG φ m) i j =
      if (j : ℕ) = (i : ℕ) + 1 then -sin (φ i) else 0 := by
  rw [infoOld_apply]
  by_cases h : (j : ℕ) = (i : ℕ) + 1
  · have hlt : ¬ (j : ℕ) < i := by omega
    have h' : (j : ℕ) + 1 ≠ i := by omega
    simp only [sweepG, of_apply, ite_eq_right hlt, ite_eq_right h', ite_eq_left h]
  · by_cases hlt : (j : ℕ) < i
    · simp only [ite_eq_left hlt, ite_eq_right h]
    · have h' : (j : ℕ) + 1 ≠ i := by omega
      simp only [sweepG, of_apply, ite_eq_right hlt, ite_eq_right h', ite_eq_right h]

/-- **The sweep satisfies the relation of a Gauss–Seidel scheme with one held sample** (the paper,
Proposition 5.5): if `cos (φ k) ≠ 0` for `k ≤ m`, then `(1 - N) X = diagonal F + M` for the order
`0, 1, …, m + 1`, with the coefficients `sweepF`, `infoNew_sweepG_apply`, `infoOld_sweepG_apply`. -/
theorem one_sub_infoNew_mul_sweep (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, cos (φ k) ≠ 0) :
    (1 - infoNew (fun i : Fin (m + 2) => (i : ℕ)) (sweepG φ m)) * sweep φ m =
      diagonal (sweepF φ m) + infoOld (fun i : Fin (m + 2) => (i : ℕ)) (sweepG φ m) := by
  obtain ⟨-, hb, hc0, hfin⟩ := sweepInv (n := m + 2) φ hc (by omega)
  ext i l
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    infoOld_sweepG_apply, diagonal_apply]
  by_cases hi : (i : ℕ) = 0
  · have hsum : ∑ k, infoNew (fun i : Fin (m + 2) => (i : ℕ)) (sweepG φ m) i k * sweep φ m k l =
        0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [infoNew_sweepG_apply, ite_eq_right (by omega), zero_mul]
    rw [hsum, sub_zero, sweep, hc0 i l hi, sweepF, ite_eq_left hi, hi]
    split_ifs <;> ring
  · have hi0 : (i : ℕ) - 1 < m + 2 := by omega
    have hi0' : ((⟨(i : ℕ) - 1, hi0⟩ : Fin (m + 2)) : ℕ) + 1 = i := by
      change (i : ℕ) - 1 + 1 = i
      omega
    have hsum : ∑ k, infoNew (fun i : Fin (m + 2) => (i : ℕ)) (sweepG φ m) i k * sweep φ m k l =
        infoNew (fun i : Fin (m + 2) => (i : ℕ)) (sweepG φ m) i ⟨(i : ℕ) - 1, hi0⟩ *
          sweep φ m ⟨(i : ℕ) - 1, hi0⟩ l := by
      refine Finset.sum_eq_single _ (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ _) h)
      have hk' : ¬ (k : ℕ) + 1 = i := fun h => hk (Fin.ext (by
        change (k : ℕ) = (i : ℕ) - 1
        omega))
      rw [infoNew_sweepG_apply, ite_eq_right hk', zero_mul]
    rw [hsum, infoNew_sweepG_apply, ite_eq_left hi0', sweepF, ite_eq_right hi]
    by_cases him : (i : ℕ) = m + 1
    · have hl : ¬ (l : ℕ) = (i : ℕ) + 1 := by omega
      have h := hb ⟨(i : ℕ) - 1, hi0⟩ i l (by change (i : ℕ) - 1 = m; omega) him
      have hm : ((⟨(i : ℕ) - 1, hi0⟩ : Fin (m + 2)) : ℕ) = m := by
        change (i : ℕ) - 1 = m
        omega
      rw [ite_eq_left him, ite_eq_left him, ite_eq_right hl, sweep, h, hm]
      split_ifs <;> ring
    · have h := hfin ⟨(i : ℕ) - 1, hi0⟩ i l hi0' (by omega)
      have hm : ((⟨(i : ℕ) - 1, hi0⟩ : Fin (m + 2)) : ℕ) = (i : ℕ) - 1 := rfl
      rw [ite_eq_right him, ite_eq_right him, sweep, h, hm]
      split_ifs <;> ring

/-- **The sweep is the one-step map of a Gauss–Seidel scheme with one held sample** (the paper,
Proposition 5.5) that executes the stores in the order `0, 1, …, m + 1`, with the local
coefficients `sweepF` and the sample coefficients `sweepG`. -/
theorem sweep_eq_infoStep (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, cos (φ k) ≠ 0) :
    sweep φ m =
      infoStep (fun i : Fin (m + 2) => (i : ℕ)) (diagonal (sweepF φ m)) (sweepG φ m) :=
  (eq_infoStep_iff _ _ _ _).2 (one_sub_infoNew_mul_sweep φ m hc)

/-- **The local coefficients of the sweep are positive** if all `cos (φ k)` are (angles in
`(-π/2, π/2)`); they are then realised by output feedback. -/
theorem sweepF_pos (φ : ℕ → ℝ) (m : ℕ) (hc : ∀ k ≤ m, 0 < cos (φ k)) (i : Fin (m + 2)) :
    0 < sweepF φ m i := by
  unfold sweepF
  split_ifs with h1 h2
  · exact hc 0 (Nat.zero_le m)
  · exact one_div_pos.2 (hc m le_rfl)
  · exact div_pos (hc _ (by omega)) (hc _ (by omega))

/-- **The sweep is the step of a Gauss–Seidel scheme with output feedback** (the paper,
Proposition 5.5), for every network of `m + 2` scalar stores and every macro step `H > 0`: if
`cos (φ k) > 0` for `k ≤ m`, there are gains `k` and weights `w`, the weights supported on the
links of the chain, such that the Gauss–Seidel step matrix of `GaussSeidel` (order `0, …, m + 1`)
is the sweep. -/
theorem ScalarNet.exists_gsStep_eq_sweep {m : ℕ} (N : ScalarNet (m + 2)) {H : ℝ} (hH : 0 < H)
    (φ : ℕ → ℝ) (hc : ∀ k ≤ m, 0 < cos (φ k)) :
    ∃ k w, (∀ i j : Fin (m + 2), (j : ℕ) + 1 ≠ i → (i : ℕ) + 1 ≠ j → w i j = 0) ∧
      N.gsStep H k w = sweep φ m := by
  obtain ⟨k, w, hw, h⟩ := N.exists_gsStep_eq_infoStep hH (sweepF φ m) (sweepF_pos φ m hc)
    (sweepG φ m) (sweepG_diag φ m)
  refine ⟨k, w, fun i j h1 h2 => hw i j ?_, ?_⟩
  · have h2' : ¬ (j : ℕ) = (i : ℕ) + 1 := fun h => h2 h.symm
    simp only [sweepG, of_apply, ite_eq_right h1, ite_eq_right h2']
  · rw [h, sweep_eq_infoStep φ m fun k hk => (hc k hk).ne']

/-- For three stores and equal angles the sweep is the matrix `gsRot` of
`SpectrumEnergyJacobi`. -/
theorem sweep_one_eq_gsRot (φ : ℕ → ℝ) (h : φ 1 = φ 0) :
    sweep φ 1 = gsRot (cos (φ 0)) (sin (φ 0)) := by
  rw [sweep_one, h]
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, planeRot, gsRot] <;> ring

end CoSimFoundations
