/-
The least one-step error (the paper, Proposition "least one-step error", `prop:leastalpha`).

**Paper.** `e_σ = min_{Z ∈ 𝒵} ‖½ A_ς A + Z‖`. Every scheme with one held sample has
`α ≥ H² e_σ - O(H³)`, and some scheme has `α = H² e_σ + O(H³)`. Moreover `e_σ` is at least the
response `a_i = ‖Π_i (½ A_ς A)|_{𝒱_i^0}‖` of each subsystem to the states `𝒱_i^0` that it is not
shown (`H² a_i = f_i + O(H³)` by eq. `eq:vbound`), with equality if these responses act on mutually
orthogonal states.

**What is formalised.** Setting of `Reach`: `P = halfStepTerm A = ½ A_ς A`, `reach Θ` the reach
of the coefficients for the kernels `Θ` of the outputs, `α = ‖(X - U) e^{-HA}‖` (the paper's
`‖(X - U) U⁻¹‖`) and the absolute one-step error `‖X - U‖`.

* **The least value exists** (`exists_isLeast_reach`): `e = min_{Z ∈ reach Θ} ‖P + Z‖` is
  attained.
* **Every scheme** (`Consistent.least_one_step_le`, `Consistent.least_one_step_rel_le`): for a
  consistent scheme whose coupling and coefficients act through the outputs, `H > 0`, and every
  `e` with `e ≤ ‖P + Z‖` on the reach:
    `‖X - U‖ ≥ H² e - √(card κ) C₃ H³`,  `α ≥ H² e - (√(card κ) C₃ + c ‖A‖ e^{H‖A‖}) H³`.
* **Some scheme** (`least_one_step_attained`): the scheme `reachScheme` of a minimiser `Z₀` has
  `‖X - U‖ ≤ H² e + reachK σ β H³` and `α ≤ H² e + (reachK σ β + (6 + 27σ) β³ e^{Hβ}) H³`
  (`‖A‖ ≤ β`, `‖Z₀‖ ≤ β²`, `H β ≤ 1/4`, `σ H β ≤ 1/6`).
* **The rows** (`hidden`, `opE_hidden_apply`, `opE_hidden_eq_self_iff`, `mul_hidden_apply_eq_zero`,
  `abs_inner_le_of_hidden`): `hidden Θ s` acts as `0` on the states of `s`, as `Θ` on those of the
  partners of `s` and as the identity on the others; its fixed vectors are `𝒱_s^0`. A matrix of the
  reach does not act on them from the rows of `s`, so `|⟪x, P v⟫| ≤ e ‖x‖ ‖v‖` for `x` supported on
  `s` and `v ∈ 𝒱_s^0`: `e ≥ a_s`.
* **Equality for orthogonal responses** (`isLeast_reach_of_orthogonal`): for `Θ` symmetric and
  idempotent (the orthogonal projections onto the kernels of the outputs), `N_s = mask_s P hidden_s`
  has `‖N_s‖ = a_s` (`abs_inner_le_rowResp`, `norm_rowResp_le`), and if `N_s N_tᵀ = 0` for `s ≠ t`
  then `e = max_s ‖N_s‖`, attained by `Z₀ = Σ_s N_s - P ∈ reach Θ`.

The passage from `a_s` to the paper's `f_i` (eq. `eq:vbound`) is not repeated here.
-/
import CoSimFoundations.Reach

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-- **The least norm over a coset of a subspace is a least element:** for every matrix `M` and
subspace `𝓡`, `{‖M + Z‖ : Z ∈ 𝓡}` has a least element. -/
theorem exists_isLeast_reach (M : Matrix (Fin n) (Fin n) ℝ)
    (𝓡 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    ∃ e, IsLeast {r | ∃ Z ∈ 𝓡, r = ‖opE (M + Z)‖} e := by
  obtain ⟨Z₀, hZ₀, hmin⟩ := exists_forall_norm_opE_add_le M 𝓡
  refine ⟨_, ⟨Z₀, hZ₀, rfl⟩, ?_⟩
  rintro _ ⟨Z, hZ, rfl⟩
  exact hmin Z hZ

/-- **The relative and the absolute one-step error.** If `‖X - e^{HA}‖ ≤ c H²` and `H ≥ 0`, then
`|‖(X - e^{HA}) e^{-HA}‖ - ‖X - e^{HA}‖| ≤ c ‖A‖ e^{H‖A‖} H³`. -/
theorem abs_norm_rel_sub_le {X A : Matrix (Fin n) (Fin n) ℝ} {H c : ℝ} (hH : 0 ≤ H)
    (hc : ‖opE (X - NormedSpace.exp (H • A))‖ ≤ c * H ^ 2) :
    |‖opE ((X - NormedSpace.exp (H • A)) * NormedSpace.exp (-(H • A)))‖ -
        ‖opE (X - NormedSpace.exp (H • A))‖| ≤
      c * ‖opE A‖ * Real.exp (H * ‖opE A‖) * H ^ 3 := by
  have e : (X - NormedSpace.exp (H • A)) * NormedSpace.exp (-(H • A)) -
      (X - NormedSpace.exp (H • A)) =
      (X - NormedSpace.exp (H • A)) * (NormedSpace.exp (H • -A) - 1) := by
    rw [smul_neg, Matrix.mul_sub, Matrix.mul_one]
  have h1 : ‖opE (NormedSpace.exp (H • -A) - 1)‖ ≤ ‖opE A‖ * Real.exp (H * ‖opE A‖) * H := by
    have h := norm_opE_exp_sub_one_le (-A) hH
    have hn : ‖opE (-A)‖ = ‖opE A‖ := by
      rw [show -A = (-1 : ℝ) • A by rw [neg_one_smul], opE_smul, norm_smul]
      simp
    rwa [hn] at h
  have h2 := abs_norm_sub_norm_le (opE ((X - NormedSpace.exp (H • A)) *
    NormedSpace.exp (-(H • A)))) (opE (X - NormedSpace.exp (H • A)))
  rw [← opE_sub, e] at h2
  refine h2.trans ?_
  rw [opE_mul]
  refine (norm_mul_le _ _).trans ?_
  have hc0 : 0 ≤ c * H ^ 2 := (norm_nonneg _).trans hc
  calc ‖opE (X - NormedSpace.exp (H • A))‖ * ‖opE (NormedSpace.exp (H • -A) - 1)‖
      ≤ c * H ^ 2 * (‖opE A‖ * Real.exp (H * ‖opE A‖) * H) :=
        mul_le_mul hc h1 (norm_nonneg _) hc0
    _ = c * ‖opE A‖ * Real.exp (H * ‖opE A‖) * H ^ 3 := by ring

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

/-! ### Every scheme -/

/-- **The least one-step error, every scheme** (the paper, `prop:leastalpha`: `α ≥ H² e_σ - O(H³)`,
here for the absolute error). For a consistent scheme whose coupling and coefficients of the
samples act through the outputs, `H > 0`, and every `e` with `e ≤ ‖½ A_ς A + Z‖` for all `Z` in
the reach: `‖X - U‖ ≥ H² e - √(card κ) C₃ H³`, `C₃ = reactionC a b c ‖A‖ H`. -/
theorem Consistent.least_one_step_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) (hH : 0 < H) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) {e : ℝ}
    (he : ∀ Z ∈ S.reach Θ, e ≤ ‖opE (S.halfStepTerm A + Z)‖) :
    H ^ 2 * e - Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 3 ≤
      ‖opE (S.X - U)‖ := by
  obtain ⟨Z, hZ, h1, -⟩ := h.exists_reach hH hΘ hAΘ hGΘ
  have h2 := norm_sub_le (opE (S.X - U)) (opE (S.X - U - H ^ 2 • (S.halfStepTerm A + Z)))
  rw [← opE_sub, sub_sub_cancel, opE_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at h2
  have h3 := mul_le_mul_of_nonneg_left (he Z hZ) (sq_nonneg H)
  linarith

/-- **The least one-step error, every scheme, relative form** (the paper, `prop:leastalpha` with
`α = ‖(X - U) U⁻¹‖`): under the hypotheses of `Consistent.least_one_step_le`,
`α ≥ H² e - (√(card κ) C₃ + c ‖A‖ e^{H‖A‖}) H³`. -/
theorem Consistent.least_one_step_rel_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) (hH : 0 < H) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) {e : ℝ}
    (he : ∀ Z ∈ S.reach Θ, e ≤ ‖opE (S.halfStepTerm A + Z)‖) :
    H ^ 2 * e - (Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
        c * ‖opE A‖ * Real.exp (H * ‖opE A‖)) * H ^ 3 ≤
      ‖opE ((S.X - U) * NormedSpace.exp (-(H • A)))‖ := by
  have h1 := h.least_one_step_le hH hΘ hAΘ hGΘ he
  have hc := h.hc
  rw [h.hU] at hc ⊢
  have h2 := abs_le.1 (abs_norm_rel_sub_le h.hH hc)
  rw [h.hU] at h1
  linarith [h2.1]

/-! ### Some scheme -/

/-- **The least one-step error is attained** (the paper, `prop:leastalpha`: "some scheme has
`α = H² e_σ + O(H³)`"). For `A` without blocks between subsystems that are not partners, with
`A_c Θ = 0`, and the least value `e` of `‖½ A_ς A + Z‖` over the reach, there is a minimiser
`Z₀ ∈ reach Θ` such that, for `‖A‖ ≤ β`, `‖Z₀‖ ≤ β²`, `0 ≤ H`, `H β ≤ 1/4`, `σ H β ≤ 1/6`, the
scheme `reachScheme` of `Z₀` (consistent, `reachScheme_consistent`; its coefficients act through
the outputs) has `‖X - U‖ ≤ H² e + reachK σ β H³` and
`α ≤ H² e + (reachK σ β + (6 + 27σ) β³ e^{Hβ}) H³`. -/
theorem least_one_step_attained [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hAΘ : S.coupling A * Θ = 0) {e : ℝ}
    (he : IsLeast {r | ∃ Z ∈ S.reach Θ, r = ‖opE (S.halfStepTerm A + Z)‖} e) :
    ∃ Z₀, ∃ hZ₀ : Z₀ ∈ S.reach Θ, ‖opE (S.halfStepTerm A + Z₀)‖ = e ∧
      ∀ {H β : ℝ}, 0 ≤ H → ‖opE A‖ ≤ β → ‖opE Z₀‖ ≤ β ^ 2 → H * β ≤ 1 / 4 →
        Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6 →
        ((S.reachScheme A hA Z₀ hZ₀.1 H).M + (S.reachScheme A hA Z₀ hZ₀.1 H).N) * Θ = 0 ∧
        ‖opE ((S.reachScheme A hA Z₀ hZ₀.1 H).X - NormedSpace.exp (H • A))‖ ≤
          H ^ 2 * e + reachK (Real.sqrt (Fintype.card κ)) β * H ^ 3 ∧
        ‖opE (((S.reachScheme A hA Z₀ hZ₀.1 H).X - NormedSpace.exp (H • A)) *
            NormedSpace.exp (-(H • A)))‖ ≤
          H ^ 2 * e + (reachK (Real.sqrt (Fintype.card κ)) β +
            (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 3 * Real.exp (H * β)) * H ^ 3 := by
  obtain ⟨⟨Z₀, hZ₀, he₀⟩, -⟩ := he
  refine ⟨Z₀, hZ₀, he₀.symm, fun {H β} hH hAβ hZβ hβH hσ => ?_⟩
  have h1 := norm_reachScheme_sub_le (hA := hA) (hZ := hZ₀.1) hH hAβ hZβ hβH hσ
  have h2 := norm_sub_norm_le (opE ((S.reachScheme A hA Z₀ hZ₀.1 H).X - NormedSpace.exp (H • A)))
    (opE ((S.reachScheme A hA Z₀ hZ₀.1 H).X - NormedSpace.exp (H • A) -
      H ^ 2 • (S.halfStepTerm A + Z₀)))
  rw [← opE_sub, sub_sub_cancel, opE_smul, norm_smul, Real.norm_of_nonneg (by positivity),
    ← he₀] at h2
  have habs : ‖opE ((S.reachScheme A hA Z₀ hZ₀.1 H).X - NormedSpace.exp (H • A))‖ ≤
      H ^ 2 * e + reachK (Real.sqrt (Fintype.card κ)) β * H ^ 3 := by linarith
  refine ⟨reachScheme_samples_mul_eq_zero hAΘ hZ₀.2, habs, ?_⟩
  have hc := (reachScheme_consistent (hA := hA) (hZ := hZ₀.1) hH hAβ hZβ hβH hσ).hc
  have h3 := abs_le.1 (abs_norm_rel_sub_le hH hc)
  have hα : 0 ≤ ‖opE A‖ := norm_nonneg _
  have hβ : 0 ≤ β := hα.trans hAβ
  have hσ0 : 0 ≤ Real.sqrt (Fintype.card κ) := Real.sqrt_nonneg _
  have hk : (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2 * ‖opE A‖ * Real.exp (H * ‖opE A‖) ≤
      (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 3 * Real.exp (H * β) := by
    have e1 : Real.exp (H * ‖opE A‖) ≤ Real.exp (H * β) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hAβ hH)
    have e2 : ‖opE A‖ * Real.exp (H * ‖opE A‖) ≤ β * Real.exp (H * β) :=
      mul_le_mul hAβ e1 (Real.exp_nonneg _) hβ
    have e3 := mul_le_mul_of_nonneg_left e2
      (by positivity : 0 ≤ (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2)
    calc (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2 * ‖opE A‖ * Real.exp (H * ‖opE A‖)
        = (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2 * (‖opE A‖ * Real.exp (H * ‖opE A‖)) := by
          ring
      _ ≤ (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2 * (β * Real.exp (H * β)) := e3
      _ = (6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 3 * Real.exp (H * β) := by ring
  have hk3 := mul_le_mul_of_nonneg_right hk (pow_nonneg hH 3)
  nlinarith [h3.2]

/-! ### The rows: what a subsystem is not shown -/

section Rows

open Classical

variable (S)

/-- The diagonal `0/1` matrix of the states of the subsystems other than `s` that are not partners
of `s`. -/
noncomputable def hideN (s : κ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun r => if S.sub r ≠ s ∧ ¬ S.partner s (S.sub r) then 1 else 0

/-- The diagonal `0/1` matrix of the states of the subsystems other than `s` that are partners
of `s`. -/
noncomputable def hideP (s : κ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun r => if S.sub r ≠ s ∧ S.partner s (S.sub r) then 1 else 0

/-- **The states not shown to `s`** (the paper, eq. `eq:vbound`: `𝒱_s^0 = {v : Π_s v = 0, C_j v = 0
for j ∈ 𝒫(s)}`): `hidden Θ s` is `0` on the states of `s`, `Θ` (the projection onto the kernel of
the output) on those of the partners of `s`, and the identity on the others. -/
noncomputable def hidden (Θ : Matrix (Fin n) (Fin n) ℝ) (s : κ) : Matrix (Fin n) (Fin n) ℝ :=
  S.hideN s + S.hideP s * Θ

/-- A diagonal matrix that is constant on each subsystem commutes with a block-diagonal matrix. -/
theorem diagonal_comp_sub_mul_comm (f : κ → ℝ) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) :
    diagonal (fun r => f (S.sub r)) * Θ = Θ * diagonal (fun r => f (S.sub r)) := by
  ext p q
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : S.sub p = S.sub q
  · rw [h, mul_comm]
  · rw [hΘ p q h, mul_zero, zero_mul]

/-- The three masks of `s` add up to the identity. -/
theorem mask_add_hideN_add_hideP (s : κ) : S.mask s + S.hideN s + S.hideP s = 1 := by
  rw [mask, hideN, hideP, diagonal_add, diagonal_add, ← diagonal_one]
  congr 1
  funext r
  by_cases h1 : S.sub r = s
  · simp [h1]
  · by_cases h2 : S.partner s (S.sub r) <;> simp [h1, h2]

theorem hideN_mul_hideN (s : κ) : S.hideN s * S.hideN s = S.hideN s := by
  rw [hideN, diagonal_mul_diagonal]
  congr 1
  funext r
  split_ifs <;> simp

theorem hideP_mul_hideP (s : κ) : S.hideP s * S.hideP s = S.hideP s := by
  rw [hideP, diagonal_mul_diagonal]
  congr 1
  funext r
  split_ifs <;> simp

theorem hideN_mul_hideP (s : κ) : S.hideN s * S.hideP s = 0 := by
  rw [hideN, hideP, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext r
  by_cases h : S.partner s (S.sub r) <;> simp [h]

theorem hideP_mul_hideN (s : κ) : S.hideP s * S.hideN s = 0 := by
  rw [hideN, hideP, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext r
  by_cases h : S.partner s (S.sub r) <;> simp [h]

theorem hideN_mul_comm (s : κ) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) : S.hideN s * Θ = Θ * S.hideN s :=
  S.diagonal_comp_sub_mul_comm (fun k => if k ≠ s ∧ ¬ S.partner s k then 1 else 0) hΘ

theorem hideP_mul_comm (s : κ) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) : S.hideP s * Θ = Θ * S.hideP s :=
  S.diagonal_comp_sub_mul_comm (fun k => if k ≠ s ∧ S.partner s k then 1 else 0) hΘ

/-- **The action of `hidden`:** `(hidden v)_p` is `0` on the states of `s`, `(Θ v)_p` on those of
the partners of `s` and `v_p` on the others. -/
theorem opE_hidden_apply (Θ : Matrix (Fin n) (Fin n) ℝ) (s : κ) (v : EuclideanSpace ℝ (Fin n))
    (p : Fin n) :
    (opE (S.hidden Θ s) v) p =
      (if S.sub p ≠ s ∧ ¬ S.partner s (S.sub p) then 1 else 0) * v p +
        (if S.sub p ≠ s ∧ S.partner s (S.sub p) then 1 else 0) * (opE Θ v) p := by
  rw [hidden, opE_add, _root_.add_apply, opE_mul_apply, PiLp.add_apply, hideN, hideP,
    opE_diagonal_apply, opE_diagonal_apply]

/-- **The fixed vectors of `hidden` are the states not shown to `s`:** `hidden v = v` if and only
if `v` vanishes on `s` and `Θ v = v` on the partners of `s` (`C_j v = 0`). -/
theorem opE_hidden_eq_self_iff (Θ : Matrix (Fin n) (Fin n) ℝ) (s : κ)
    (v : EuclideanSpace ℝ (Fin n)) :
    opE (S.hidden Θ s) v = v ↔
      (∀ p, S.sub p = s → v p = 0) ∧
        ∀ p, S.sub p ≠ s → S.partner s (S.sub p) → (opE Θ v) p = v p := by
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hp hpp => ?_⟩
    · have h1 := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w p) h
      simp only [S.opE_hidden_apply] at h1
      rw [← h1]
      simp [hp]
    · have h1 := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w p) h
      simp only [S.opE_hidden_apply] at h1
      rw [← h1]
      simp [hp, hpp]
  · rintro ⟨h1, h2⟩
    ext p
    rw [S.opE_hidden_apply]
    by_cases hp : S.sub p = s
    · simp [hp, h1 p hp]
    · by_cases hpp : S.partner s (S.sub p)
      · simp [hp, hpp, h2 p hp hpp]
      · simp [hp, hpp]

/-- `(T hideP Θ)_{pq} = [q partner of s] (T Θ)_{pq}` for block-diagonal `Θ`. -/
theorem mul_hideP_mul_apply (T : Matrix (Fin n) (Fin n) ℝ) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (s : κ) (p q : Fin n) :
    (T * S.hideP s * Θ) p q =
      (if S.sub q ≠ s ∧ S.partner s (S.sub q) then 1 else 0) * (T * Θ) p q := by
  rw [Matrix.mul_assoc, S.hideP_mul_comm s hΘ, ← Matrix.mul_assoc, hideP, Matrix.mul_diagonal,
    mul_comm]

/-- **A matrix of the reach does not act on the states not shown to `s` from the rows of `s`:**
`(Z hidden_s)_{pq} = 0` for `p` a state of `s` (`Θ` block diagonal). -/
theorem mul_hidden_apply_eq_zero {Θ Z : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hZ : Z ∈ S.reach Θ) {s : κ} {p : Fin n}
    (hp : S.sub p = s) (q : Fin n) : (Z * S.hidden Θ s) p q = 0 := by
  rw [hidden, Matrix.mul_add, Matrix.add_apply, ← Matrix.mul_assoc, S.mul_hideP_mul_apply Z hΘ,
    hideN, Matrix.mul_diagonal]
  have hZΘ : S.sub p ≠ S.sub q → (Z * Θ) p q = (S.coupling Z * Θ) p q := by
    intro hpq
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : S.sub r = S.sub q
    · rw [S.coupling_apply, ite_eq_right fun e => hpq (e.trans hr)]
    · rw [hΘ r q hr, mul_zero, mul_zero]
  by_cases hq : S.sub q = s
  · simp [hq]
  · have hpq' : S.sub p ≠ S.sub q := by rw [hp]; exact fun e => hq e.symm
    by_cases hpq : S.partner s (S.sub q)
    · rw [hZΘ hpq', hZ.2]
      simp [hq, hpq]
    · rw [hZ.1 p q hpq' (by rw [hp]; exact hpq)]
      simp [hq, hpq]

/-- **The rows of `s` on the states not shown to `s` are those of `P`:** for `x` supported on `s`,
`v` with `hidden v = v` and `Z ∈ reach Θ`: `⟪x, (P + Z) v⟫ = ⟪x, P v⟫`. -/
theorem inner_add_reach_hidden {Θ Z : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hZ : Z ∈ S.reach Θ) {s : κ}
    {x v : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hv : opE (S.hidden Θ s) v = v) (P : Matrix (Fin n) (Fin n) ℝ) :
    ⟪x, opE (P + Z) v⟫ = ⟪x, opE P v⟫ := by
  have h0 : ⟪x, opE Z v⟫ = 0 := by
    rw [← hv, ← opE_mul_apply]
    rw [inner_opE_congr_row hx v (T' := 0) fun p q hp =>
      (S.mul_hidden_apply_eq_zero hΘ hZ hp q).trans (Matrix.zero_apply p q).symm]
    simp
  rw [inner_opE_add, h0, add_zero]

/-- **The least value is at least the response to the states not shown** (the paper,
`prop:leastalpha`: `e_σ ≥ a_i`). For `Θ` block diagonal, `x` supported on `s`, `v ∈ 𝒱_s^0`
(`hidden v = v`) and every `Z` in the reach: `|⟪x, ½ A_ς A v⟫| ≤ ‖½ A_ς A + Z‖ ‖x‖ ‖v‖`. -/
theorem abs_inner_le_of_hidden (A : Matrix (Fin n) (Fin n) ℝ) {Θ Z : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hZ : Z ∈ S.reach Θ) {s : κ}
    {x v : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hv : opE (S.hidden Θ s) v = v) :
    |⟪x, opE (S.halfStepTerm A) v⟫| ≤ ‖opE (S.halfStepTerm A + Z)‖ * (‖x‖ * ‖v‖) := by
  rw [← S.inner_add_reach_hidden hΘ hZ hx hv]
  exact abs_inner_opE_le _ x v

/-- **The least value bounds every response to the states not shown:** if `e` is the least value
of `‖½ A_ς A + Z‖` over the reach, then `|⟪x, ½ A_ς A v⟫| ≤ e ‖x‖ ‖v‖` for `x` supported on `s`
and `v ∈ 𝒱_s^0`. -/
theorem abs_inner_le_least (A : Matrix (Fin n) (Fin n) ℝ) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) {e : ℝ}
    (he : IsLeast {r | ∃ Z ∈ S.reach Θ, r = ‖opE (S.halfStepTerm A + Z)‖} e) {s : κ}
    {x v : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hv : opE (S.hidden Θ s) v = v) :
    |⟪x, opE (S.halfStepTerm A) v⟫| ≤ e * (‖x‖ * ‖v‖) := by
  obtain ⟨⟨Z₀, hZ₀, rfl⟩, -⟩ := he
  exact S.abs_inner_le_of_hidden A hΘ hZ₀ hx hv

/-! ### Equality for orthogonal responses -/

/-- `hidden` is idempotent if `Θ` is (and block diagonal). -/
theorem hidden_mul_self {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hΘ2 : Θ * Θ = Θ) (s : κ) :
    S.hidden Θ s * S.hidden Θ s = S.hidden Θ s := by
  have hN := S.hideN_mul_comm s hΘ
  have hP := S.hideP_mul_comm s hΘ
  have e1 : S.hideP s * Θ * S.hideN s = 0 := by
    rw [Matrix.mul_assoc, ← hN, ← Matrix.mul_assoc, S.hideP_mul_hideN, Matrix.zero_mul]
  have e2 : S.hideP s * Θ * (S.hideP s * Θ) = S.hideP s * Θ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Θ, ← hP, Matrix.mul_assoc, hΘ2, ← Matrix.mul_assoc,
      S.hideP_mul_hideP]
  rw [hidden, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, S.hideN_mul_hideN, ← Matrix.mul_assoc,
    S.hideN_mul_hideP, Matrix.zero_mul, add_zero, e1, zero_add, e2]

/-- `hidden` is symmetric if `Θ` is (and block diagonal). -/
theorem hidden_transpose {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hΘt : Θᵀ = Θ) (s : κ) :
    (S.hidden Θ s)ᵀ = S.hidden Θ s := by
  rw [hidden, transpose_add, transpose_mul, hΘt, hideN, hideP, diagonal_transpose,
    diagonal_transpose]
  congr 1
  exact (S.hideP_mul_comm s hΘ).symm

/-- An orthogonal projection does not lengthen a vector: `‖Q v‖ ≤ ‖v‖` for `Qᵀ = Q`, `Q Q = Q`. -/
theorem _root_.CoSimFoundations.norm_opE_apply_le_of_proj {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQt : Qᵀ = Q) (hQ2 : Q * Q = Q) (v : EuclideanSpace ℝ (Fin n)) : ‖opE Q v‖ ≤ ‖v‖ := by
  have h1 : ‖opE Q v‖ ^ 2 = ⟪v, opE Q v⟫ := by
    rw [← real_inner_self_eq_norm_sq, OneStep.inner_opE_transpose Q v (opE Q v), hQt,
      ← opE_mul_apply, hQ2]
  have h2 : ⟪v, opE Q v⟫ ≤ ‖v‖ * ‖opE Q v‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (opE Q v)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact norm_nonneg _
  · nlinarith

/-- **The response of the rows of `s` to the states not shown:** `N_s = mask_s P hidden_s`. -/
noncomputable def rowResp (P Θ : Matrix (Fin n) (Fin n) ℝ) (s : κ) : Matrix (Fin n) (Fin n) ℝ :=
  S.mask s * P * S.hidden Θ s

/-- A vector supported on `s` is fixed by the mask of `s`. -/
theorem opE_mask_eq_self {s : κ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) : opE (S.mask s) x = x := by
  ext p
  rw [S.opE_mask_apply]
  by_cases hp : S.sub p = s
  · rw [ite_eq_left hp, one_mul]
  · rw [ite_eq_right hp, zero_mul, hx p hp]

/-- The matrix element of `N_s`: `⟪x, N_s y⟫ = ⟪mask_s x, P (hidden_s y)⟫`. -/
theorem inner_rowResp (P Θ : Matrix (Fin n) (Fin n) ℝ) (s : κ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.rowResp P Θ s) y⟫ = ⟪opE (S.mask s) x, opE P (opE (S.hidden Θ s) y)⟫ := by
  have hmt : (S.mask s)ᵀ = S.mask s := by rw [mask, diagonal_transpose]
  rw [rowResp, opE_mul_apply, opE_mul_apply, OneStep.inner_opE_transpose, hmt, real_inner_comm]

/-- **`N_s` is the response to the states not shown** (one side): for `x` supported on `s` and
`v ∈ 𝒱_s^0`, `⟪x, P v⟫ = ⟪x, N_s v⟫`, so `|⟪x, P v⟫| ≤ ‖N_s‖ ‖x‖ ‖v‖`. -/
theorem abs_inner_le_rowResp (P Θ : Matrix (Fin n) (Fin n) ℝ) {s : κ}
    {x v : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hv : opE (S.hidden Θ s) v = v) :
    |⟪x, opE P v⟫| ≤ ‖opE (S.rowResp P Θ s)‖ * (‖x‖ * ‖v‖) := by
  have e : ⟪x, opE P v⟫ = ⟪x, opE (S.rowResp P Θ s) v⟫ := by
    rw [S.inner_rowResp, S.opE_mask_eq_self hx, hv]
  rw [e]
  exact abs_inner_opE_le _ x v

/-- **`N_s` is the response to the states not shown** (other side): for `Θ` symmetric, idempotent
and block diagonal, every bound `r ≥ 0` of `|⟪x, P v⟫| / (‖x‖ ‖v‖)` over `x` supported on `s` and
`v ∈ 𝒱_s^0` bounds `‖N_s‖`. So `‖N_s‖ = a_s = ‖Π_s P|_{𝒱_s^0}‖`. -/
theorem norm_rowResp_le (P : Matrix (Fin n) (Fin n) ℝ) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hΘt : Θᵀ = Θ) (hΘ2 : Θ * Θ = Θ) (s : κ)
    {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀ x v : EuclideanSpace ℝ (Fin n), (∀ p, S.sub p ≠ s → x p = 0) →
      opE (S.hidden Θ s) v = v → |⟪x, opE P v⟫| ≤ r * (‖x‖ * ‖v‖)) :
    ‖opE (S.rowResp P Θ s)‖ ≤ r := by
  refine norm_opE_le_of_abs_inner_le hr fun x y => ?_
  rw [S.inner_rowResp]
  have hQ2 := S.hidden_mul_self hΘ hΘ2 s
  have hQt := S.hidden_transpose hΘ hΘt s
  have hfix : opE (S.hidden Θ s) (opE (S.hidden Θ s) y) = opE (S.hidden Θ s) y := by
    rw [← opE_mul_apply, hQ2]
  refine (hrow _ _ (S.opE_mask_support s x) hfix).trans ?_
  have h1 := S.norm_opE_mask_apply_le s x
  have h2 := norm_opE_apply_le_of_proj hQt hQ2 y
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)) hr

/-- The masks of the subsystems add up to the identity. -/
theorem sum_mask [Fintype κ] : ∑ s, S.mask s = 1 := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [mask, Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    simp
  · simp [hpq]

/-- **The responses sum to `P` plus an element of the reach:** for `Θ` idempotent and block
diagonal, `Σ_s N_s - P ∈ reach Θ`. -/
theorem sum_rowResp_sub_mem_reach [Fintype κ] (P : Matrix (Fin n) (Fin n) ℝ)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0)
    (hΘ2 : Θ * Θ = Θ) : ∑ s, S.rowResp P Θ s - P ∈ S.reach Θ := by
  have hP : P = ∑ s, S.mask s * P := by rw [← Finset.sum_mul, S.sum_mask, Matrix.one_mul]
  have e : ∑ s, S.rowResp P Θ s - P = ∑ s, S.mask s * P * (S.hidden Θ s - 1) := by
    have e0 : ∑ s, S.rowResp P Θ s - P = ∑ s, S.rowResp P Θ s - ∑ s, S.mask s * P := by
      rw [← hP]
    rw [e0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [rowResp, Matrix.mul_sub, Matrix.mul_one]
  have hrow : ∀ (T : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n),
      (∑ s, S.mask s * T * (S.hidden Θ s - 1)) p q = (T * (S.hidden Θ (S.sub p) - 1)) p q := by
    intro T p q
    rw [Matrix.sum_apply, Finset.sum_eq_single (S.sub p)]
    · rw [Matrix.mul_assoc, mask, Matrix.diagonal_mul, ite_eq_left rfl, one_mul]
    · intro s _ hs
      rw [Matrix.mul_assoc, mask, Matrix.diagonal_mul, ite_eq_right fun e => hs e.symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [e]
  refine ⟨fun p q hne hnp => ?_, ?_⟩
  · rw [hrow, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, hidden, Matrix.mul_add,
      Matrix.add_apply, ← Matrix.mul_assoc, S.mul_hideP_mul_apply P hΘ, hideN, Matrix.mul_diagonal,
      ite_eq_left (⟨fun e => hne e.symm, hnp⟩ :
        S.sub q ≠ S.sub p ∧ ¬ S.partner (S.sub p) (S.sub q)),
      ite_eq_right (fun h => hnp h.2 : ¬ (S.sub q ≠ S.sub p ∧ S.partner (S.sub p) (S.sub q)))]
    ring
  · -- `(hidden_s - 1) Θ = -mask_s Θ`
    have hQΘ : ∀ s, (S.hidden Θ s - 1) * Θ = -(S.mask s * Θ) := by
      intro s
      have h1 := S.mask_add_hideN_add_hideP s
      rw [hidden, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hΘ2, Matrix.one_mul,
        ← Matrix.add_mul]
      have h2 : S.hideN s + S.hideP s = 1 - S.mask s := by rw [← h1]; abel
      rw [h2, Matrix.sub_mul, Matrix.one_mul]
      abel
    have hsum : (∑ s, S.mask s * P * (S.hidden Θ s - 1)) * Θ =
        -∑ s, S.mask s * P * (S.mask s * Θ) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.mul_assoc, hQΘ, Matrix.mul_neg]
    rw [S.coupling_mul_of_block hΘ, hsum]
    refine S.coupling_eq_zero_of_block fun p q hne => ?_
    rw [Matrix.neg_apply, Matrix.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Matrix.mul_assoc, mask, Matrix.diagonal_mul, ← Matrix.mul_assoc, ← mask,
      Matrix.mul_apply]
    by_cases hp : S.sub p = s
    · rw [ite_eq_left hp, one_mul]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [mask, Matrix.mul_diagonal]
      by_cases hr : S.sub r = s
      · rw [hΘ r q (by rw [hr, ← hp]; exact hne), mul_zero]
      · rw [ite_eq_right hr, mul_zero, zero_mul]
    · rw [ite_eq_right hp, zero_mul]

/-- **The least one-step value for orthogonal responses** (the paper, `prop:leastalpha`, "with
equality if the responses act on mutually orthogonal states"). For `Θ` symmetric, idempotent and
block diagonal (orthogonal projections onto the kernels of the outputs) and responses
`N_s = mask_s P hidden_s` with `N_s N_tᵀ = 0` for `s ≠ t`: the least value of `‖P + Z‖` over the
reach is `max_s ‖N_s‖`, attained by `Z₀ = Σ_s N_s - P`. With `norm_rowResp_le` and
`abs_inner_le_rowResp`, `‖N_s‖ = a_s`, so `e_σ = max_s a_s`. -/
theorem isLeast_reach_of_orthogonal [Fintype κ] (P : Matrix (Fin n) (Fin n) ℝ)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hΘt : Θᵀ = Θ)
    (hΘ2 : Θ * Θ = Θ)
    (horth : ∀ s t, s ≠ t → S.rowResp P Θ s * (S.rowResp P Θ t)ᵀ = 0) :
    IsLeast {r | ∃ Z ∈ S.reach Θ, r = ‖opE (P + Z)‖} (⨆ s, ‖opE (S.rowResp P Θ s)‖) := by
  have hsum : ‖opE (∑ s, S.rowResp P Θ s)‖ = ⨆ s, ‖opE (S.rowResp P Θ s)‖ := by
    refine norm_opE_sum_eq_iSup S.sub (fun s => S.rowResp P Θ s) (fun s p q hp => ?_) horth
    rw [rowResp, Matrix.mul_assoc, mask, Matrix.diagonal_mul, ite_eq_right hp, zero_mul]
  refine ⟨⟨_, S.sum_rowResp_sub_mem_reach P hΘ hΘ2, ?_⟩, ?_⟩
  · rw [add_sub_cancel, hsum]
  · rintro _ ⟨Z, hZ, rfl⟩
    refine Real.iSup_le (fun s => S.norm_rowResp_le P hΘ hΘt hΘ2 s (norm_nonneg _)
      fun x v hx hv => ?_) (norm_nonneg _)
    rw [← S.inner_add_reach_hidden hΘ hZ hx hv]
    exact abs_inner_opE_le _ x v

end Rows

end HeldScheme

end CoSimFoundations
