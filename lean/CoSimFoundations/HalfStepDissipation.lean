/-
The numerical dissipation of the half step (the paper, Proposition "the numerical dissipation
of the half step" `prop:parts`, equation `eq:dissipation`, and the first formula of
`eq:negdamping`).

**Setting** (`HalfStep.lean`): states grouped by `S.sub` into subsystems with stages `S.stage`;
`A = A₀ + A_c` with `A₀ = S.blockDiag A`, `A_c = S.coupling A`; `A_ς = S.signedCoupling A` with
the blocks `ς_{ik} A_{ik}`, `ς_{ik} = S.sg i k = +1` if `k` runs at an earlier stage than `i`,
else `-1`. Power-conjugate ports are `hskew : A q p = -A p q` between states of different
subsystems (`A_{ik} = -A_{ki}ᵀ`).

**The two rates.** For a subsystem `k`, as matrices on all states with rows in `k` only:
* `S.driveAfter A k = a_k⁺`: the entries `A p q` with `p` in `k` and `q` in a subsystem that
  runs after `k` (`ς_{ik} = +1`);
* `S.driveOther A k = a_k⁻`: the entries `A p q` with `p` in `k` and `q` in another subsystem
  that does not run after `k` (`ς_{ik} = -1`).
The paper sums over the partners of `k`; for a matrix without blocks between subsystems that are
not partners (the hypothesis `hA` of the library) this is the same sum.

**The identity** (`inner_signedCoupling_mul_coupling_self`), exact, for every `x`:
  `xᵀ A_ς A_c x = -Σ_k (|a_k⁺ x|² - |a_k⁻ x|²)`.
Proof (the paper's): in the rows of `k`, `A_c x = (a_k⁺ + a_k⁻) x`
(`opE_driveAfter_add_driveOther_apply`) and, by `hskew`, `A_ςᵀ x = -(a_k⁺ - a_k⁻) x`
(`opE_driveAfter_sub_driveOther_apply`); `xᵀ A_ς A_c x = ⟪A_ςᵀ x, A_c x⟫` is the sum over `k` of
`-⟪(a_k⁺ - a_k⁻) x, (a_k⁺ + a_k⁻) x⟫ = -(|a_k⁺ x|² - |a_k⁻ x|²)`.
Hence (`inner_sym_signedCoupling_mul_self`, `inner_halfStepDissipation_self`), with
`D = S.halfStepDissipation A H = -(H/2) sym (A_ς A)`:
  `xᵀ sym (A_ς A) x = -Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) + xᵀ A_ς A₀ x`,
  `xᵀ D x = (H/2) Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) - (H/2) xᵀ A_ς A₀ x`.

**The zero-order hold** (`abs_numDissipation_zoh_sub_le`, equation `eq:dissipation` with an
explicit remainder). With `Δ_R = numDissipation A Ã`, `Ã` the modified system of the zero-order
hold, for `0 < H`, `H ‖A‖ ≤ 1/24`, `σ H ‖A‖ ≤ 1/6`, `σ = √(card κ)`, in every order of execution:
  `|xᵀ Δ_R x - (H/2) Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) + (H/2) xᵀ A_ς A₀ x|`
      `≤ (37 + 220σ + 53σ² + 54σ³) ‖A‖³ H² ‖x‖²`.
It follows from `norm_zoh_difference_sub_half_le` (`‖Δ - (H/2) A_ς A‖ ≤ zohDiffK · H²`) and the
passage to the symmetric part (`abs_inner_numDissipation_sub_le`,
`norm_numDissipation_zoh_sub_le`: `‖Δ_R - D‖ ≤ zohDiffK · H²`).

**The diagonal block** (first formula of `eq:negdamping`). For `x`, `y` supported on a subsystem
`s`, exactly (`inner_sym_signedCoupling_mul_diag`, `inner_signedCoupling_mul_blockDiag_diag`):
  `⟪x, sym (A_ς A) y⟫ = -⟪A x, osgn_s (A y)⟫ = -Σ_{k ≠ s} ς_{sk} ⟪A_{ks} x, A_{ks} y⟫`,
  `⟪x, A_ς A₀ y⟫ = 0`,
and `Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) = Σ_{k ≠ s} ς_{sk} |A_{ks} x|²` (`sum_drive_eq_of_support`: the
diagonal block collects `ς_{sk} A_{ks}ᵀ A_{ks}` from the square of each `k`). With the remainder:
* zero-order hold (`abs_numDissipation_zoh_diag_le`):
  `|⟪x, Δ_R y⟫ - (H/2) Σ_k ς_{sk} ⟪A_{ks} x, A_{ks} y⟫| ≤ zohDiffK · H² ‖x‖ ‖y‖`;
* every consistent scheme with partner weights only for `s` (`F_s = e^{H A_s}`) and `s` not its
  own partner (`Consistent.numDissipation_diag`): the same with the constant
  `K + C₃ + ‖A_s‖³/6 · e^{H‖A_s‖}`, from `Consistent.reaction_partner_weights` and the passage
  `abs_inner_difference_sub_le`.

**What a scheme changes** (second statement of the proposition). For every consistent scheme
(`Consistent.norm_numDissipation_add_sym_sub_le`, from `Consistent.norm_difference_half_step_le`)
  `‖Δ_R + sym G - D‖ ≤ (K + √(card κ) C₃) H²`,
with `G = S.schemeChange A H` the two brackets of the half-step normal form divided by `H`, and
`sym G` has no block between different subsystems that are not partners
(`Consistent.inner_sym_schemeChange_eq_zero`).

Not in this file: `eq:parts` between subsystems that are not partners
(`Consistent.numDissipation_block`) and the trace in `eq:negdamping`
(`Consistent.abs_numDamping_add_links_le`), which the library has.
-/
import CoSimFoundations.ZeroOrderHold
import CoSimFoundations.Setting

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-- The matrix element of the symmetric part: `⟪x, sym M y⟫ = ½ (⟪x, M y⟫ + ⟪y, M x⟫)`. -/
theorem inner_opE_sym_eq (M : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (sym M) y⟫ = 1 / 2 * (⟪x, opE M y⟫ + ⟪y, opE M x⟫) := by
  rw [sym, inner_opE_smul, inner_opE_add, ← inner_opE_transpose M x y]

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The two rates at which a subsystem is driven -/

/-- `a_k⁺` of the paper, as a matrix on all states: the entries of the coupling in the rows of
the subsystem `k` and the columns of the subsystems that run after `k` (`ς_{ik} = +1`). `a_k⁺ x`
is the rate at which `k` is driven by the partners that run after it. -/
noncomputable def driveAfter (A : Matrix (Fin n) (Fin n) ℝ) (k : κ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    if S.sub p = k then (if S.stage k < S.stage (S.sub q) then S.coupling A p q else 0) else 0

/-- `a_k⁻` of the paper, as a matrix on all states: the entries of the coupling in the rows of
the subsystem `k` and the columns of the other subsystems that do not run after `k`
(`ς_{ik} = -1`). `a_k⁻ x` is the rate at which `k` is driven by these. -/
noncomputable def driveOther (A : Matrix (Fin n) (Fin n) ℝ) (k : κ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    if S.sub p = k then (if S.stage k < S.stage (S.sub q) then 0 else S.coupling A p q) else 0

/-- The entries of `a_k⁺`. -/
theorem driveAfter_apply (A : Matrix (Fin n) (Fin n) ℝ) (k : κ) (p q : Fin n) :
    S.driveAfter A k p q =
      if S.sub p = k then (if S.stage k < S.stage (S.sub q) then S.coupling A p q else 0)
      else 0 := rfl

/-- The entries of `a_k⁻`. -/
theorem driveOther_apply (A : Matrix (Fin n) (Fin n) ℝ) (k : κ) (p q : Fin n) :
    S.driveOther A k p q =
      if S.sub p = k then (if S.stage k < S.stage (S.sub q) then 0 else S.coupling A p q)
      else 0 := rfl

/-- `a_k⁺` has the entries of `A` itself: `p` in `k`, `q` in a subsystem that runs after `k`. -/
theorem driveAfter_apply_of_lt (A : Matrix (Fin n) (Fin n) ℝ) {k : κ} {p q : Fin n}
    (hp : S.sub p = k) (hq : S.stage k < S.stage (S.sub q)) : S.driveAfter A k p q = A p q := by
  have hne : S.sub p ≠ S.sub q := fun e => by
    rw [← e, hp] at hq
    exact lt_irrefl _ hq
  rw [S.driveAfter_apply, ite_eq_left hp, ite_eq_left hq, S.coupling_apply, ite_eq_right hne]

/-- `a_k⁻` has the entries of `A` itself: `p` in `k`, `q` in another subsystem that does not run
after `k`. -/
theorem driveOther_apply_of_not_lt (A : Matrix (Fin n) (Fin n) ℝ) {k : κ} {p q : Fin n}
    (hp : S.sub p = k) (hqk : S.sub q ≠ k) (hq : ¬ S.stage k < S.stage (S.sub q)) :
    S.driveOther A k p q = A p q := by
  have hne : S.sub p ≠ S.sub q := fun e => hqk (e.symm.trans hp)
  rw [S.driveOther_apply, ite_eq_left hp, ite_eq_right hq, S.coupling_apply, ite_eq_right hne]

/-- With power-conjugate ports the transposed signed coupling is the coupling with the signs of
the columns: `A_ς q p = -ς(sub q, sub p) A_c p q`. -/
theorem signedCoupling_apply_of_skew {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (p q : Fin n) :
    S.signedCoupling A q p = -(S.sg (S.sub q) (S.sub p) * S.coupling A p q) := by
  rw [S.signedCoupling_apply, S.coupling_apply]
  by_cases h : S.sub p = S.sub q
  · rw [ite_eq_left h.symm, ite_eq_left h, mul_zero, neg_zero]
  · rw [ite_eq_right fun e => h e.symm, ite_eq_right h, hskew p q h]
    ring

/-- In the rows of `k`, `A_c x = (a_k⁺ + a_k⁻) x`; the two rates vanish in the other rows. -/
theorem opE_driveAfter_add_driveOther_apply (A : Matrix (Fin n) (Fin n) ℝ) (k : κ)
    (x : EuclideanSpace ℝ (Fin n)) (r : Fin n) :
    (opE (S.driveAfter A k) x) r + (opE (S.driveOther A k) x) r =
      if S.sub r = k then (opE (S.coupling A) x) r else 0 := by
  rw [opE_apply, opE_apply, ← Finset.sum_add_distrib]
  by_cases hr : S.sub r = k
  · rw [ite_eq_left hr, opE_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [S.driveAfter_apply, S.driveOther_apply, ite_eq_left hr, ite_eq_left hr]
    by_cases h : S.stage k < S.stage (S.sub q)
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      ring
  · rw [ite_eq_right hr]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [S.driveAfter_apply, S.driveOther_apply, ite_eq_right hr, ite_eq_right hr]
    ring

/-- With power-conjugate ports, in the rows of `k`, `A_ςᵀ x = -(a_k⁺ - a_k⁻) x`. -/
theorem opE_driveAfter_sub_driveOther_apply {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (k : κ)
    (x : EuclideanSpace ℝ (Fin n)) (r : Fin n) :
    (opE (S.driveAfter A k) x) r - (opE (S.driveOther A k) x) r =
      if S.sub r = k then -(opE (S.signedCoupling A)ᵀ x) r else 0 := by
  rw [opE_apply, opE_apply, ← Finset.sum_sub_distrib]
  by_cases hr : S.sub r = k
  · rw [ite_eq_left hr, opE_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e : S.sg (S.sub q) (S.sub r) = if S.stage k < S.stage (S.sub q) then 1 else -1 := by
      rw [hr]
      rfl
    rw [S.driveAfter_apply, S.driveOther_apply, ite_eq_left hr, ite_eq_left hr,
      Matrix.transpose_apply, S.signedCoupling_apply_of_skew hskew r q, e]
    by_cases h : S.stage k < S.stage (S.sub q)
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      ring
  · rw [ite_eq_right hr]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [S.driveAfter_apply, S.driveOther_apply, ite_eq_right hr, ite_eq_right hr]
    ring

/-! ### The identity -/

/-- **The numerical dissipation of the half step, the identity behind `eq:dissipation`** (the paper,
Proposition `prop:parts`, proof). With power-conjugate ports (`A_{ik} = -A_{ki}ᵀ`), for every
`x` and every assignment of stages:
`xᵀ A_ς A_c x = -Σ_k (|a_k⁺ x|² - |a_k⁻ x|²)`. -/
theorem inner_signedCoupling_mul_coupling_self [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.signedCoupling A * S.coupling A) x⟫ =
      -∑ k, (‖opE (S.driveAfter A k) x‖ ^ 2 - ‖opE (S.driveOther A k) x‖ ^ 2) := by
  have hn : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ 2 = ∑ r, w r * w r := fun w => by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  have hk : ∀ k, ‖opE (S.driveAfter A k) x‖ ^ 2 - ‖opE (S.driveOther A k) x‖ ^ 2 =
      ∑ r, if S.sub r = k then
        -((opE (S.signedCoupling A)ᵀ x) r * (opE (S.coupling A) x) r) else 0 := by
    intro k
    rw [hn, hn, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 := S.opE_driveAfter_add_driveOther_apply A k x r
    have h2 := S.opE_driveAfter_sub_driveOther_apply hskew k x r
    have e : (opE (S.driveAfter A k) x) r * (opE (S.driveAfter A k) x) r -
        (opE (S.driveOther A k) x) r * (opE (S.driveOther A k) x) r =
        ((opE (S.driveAfter A k) x) r - (opE (S.driveOther A k) x) r) *
          ((opE (S.driveAfter A k) x) r + (opE (S.driveOther A k) x) r) := by ring
    rw [e, h1, h2]
    by_cases hr : S.sub r = k
    · rw [ite_eq_left hr, ite_eq_left hr, ite_eq_left hr]
      ring
    · rw [ite_eq_right hr, ite_eq_right hr, ite_eq_right hr, mul_zero]
  have hs : ∀ r, (∑ k, if S.sub r = k then
      -((opE (S.signedCoupling A)ᵀ x) r * (opE (S.coupling A) x) r) else 0) =
      -((opE (S.signedCoupling A)ᵀ x) r * (opE (S.coupling A) x) r) := fun r => by
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm, Finset.sum_congr rfl fun r _ => hs r,
    Finset.sum_neg_distrib, neg_neg, opE_mul_apply,
    inner_opE_transpose (S.signedCoupling A) (opE (S.coupling A) x) x, inner_eq_sum]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- **The symmetric part of `A_ς A`** (the paper, `eq:dissipation` without the factor `-H/2`):
`xᵀ sym (A_ς A) x = -Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) + xᵀ A_ς A₀ x`. -/
theorem inner_sym_signedCoupling_mul_self [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (sym (S.signedCoupling A * A)) x⟫ =
      -∑ k, (‖opE (S.driveAfter A k) x‖ ^ 2 - ‖opE (S.driveOther A k) x‖ ^ 2) +
        ⟪x, opE (S.signedCoupling A * S.blockDiag A) x⟫ := by
  have e : S.signedCoupling A * A =
      S.signedCoupling A * S.blockDiag A + S.signedCoupling A * S.coupling A := by
    rw [← Matrix.mul_add, S.blockDiag_add_coupling]
  rw [inner_opE_sym_eq, e, inner_opE_add, S.inner_signedCoupling_mul_coupling_self hskew]
  ring

/-- **The leading term of the numerical dissipation of the zero-order hold:**
`D = -(H/2) sym (A_ς A)` (the paper, proof of Proposition `prop:parts`). -/
noncomputable def halfStepDissipation (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (-(H / 2)) • sym (S.signedCoupling A * A)

/-- **The numerical dissipation of the half step** (the paper, Proposition `prop:parts`, the leading
term of `eq:dissipation`), exactly: for `D = -(H/2) sym (A_ς A)` and power-conjugate ports,
`xᵀ D x = (H/2) Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) - (H/2) xᵀ A_ς A₀ x`. -/
theorem inner_halfStepDissipation_self [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (H : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.halfStepDissipation A H) x⟫ =
      H / 2 * ∑ k, (‖opE (S.driveAfter A k) x‖ ^ 2 - ‖opE (S.driveOther A k) x‖ ^ 2) -
        H / 2 * ⟪x, opE (S.signedCoupling A * S.blockDiag A) x⟫ := by
  rw [halfStepDissipation, inner_opE_smul, S.inner_sym_signedCoupling_mul_self hskew]
  ring

/-! ### The passage to the numerical dissipation of a modified system -/

/-- **From the difference to the numerical dissipation.** If the difference `Δ = Ã - A` is within
`C` of `(H/2) A_ς A`, the numerical dissipation `Δ_R = -sym Δ` is within `C` of
`D = -(H/2) sym (A_ς A)`: `|⟪x, Δ_R y⟫ - ⟪x, D y⟫| ≤ C ‖x‖ ‖y‖`. -/
theorem abs_inner_numDissipation_sub_le {A At : Matrix (Fin n) (Fin n) ℝ} {H C : ℝ}
    (hC : ‖opE (At - A - (H / 2) • (S.signedCoupling A * A))‖ ≤ C)
    (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (numDissipation A At) y⟫ - ⟪x, opE (S.halfStepDissipation A H) y⟫| ≤
      C * (‖x‖ * ‖y‖) := by
  have hxy : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  have h1 := abs_le.1 ((abs_inner_opE_le (At - A - (H / 2) • (S.signedCoupling A * A)) x y).trans
    (mul_le_mul_of_nonneg_right hC hxy))
  have h2 := abs_le.1 ((abs_inner_opE_le (At - A - (H / 2) • (S.signedCoupling A * A)) y x).trans
    (mul_le_mul_of_nonneg_right hC (by positivity)))
  rw [mul_comm ‖y‖ ‖x‖] at h2
  rw [inner_opE_sub, inner_opE_smul] at h1 h2
  rw [inner_numDissipation, halfStepDissipation, inner_opE_smul, inner_opE_sym_eq, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `‖Δ_R - D‖ ≤ C` if `‖Δ - (H/2) A_ς A‖ ≤ C`, for `D = -(H/2) sym (A_ς A)`. -/
theorem norm_numDissipation_sub_le {A At : Matrix (Fin n) (Fin n) ℝ} {H C : ℝ}
    (hC : ‖opE (At - A - (H / 2) • (S.signedCoupling A * A))‖ ≤ C) :
    ‖opE (numDissipation A At - S.halfStepDissipation A H)‖ ≤ C := by
  refine norm_opE_le_of_abs_inner_le ((norm_nonneg _).trans hC) fun x y => ?_
  rw [inner_opE_sub]
  exact S.abs_inner_numDissipation_sub_le hC x y

/-! ### The zero-order hold: equation `eq:dissipation` -/

/-- **The numerical dissipation of the zero-order hold is `-(H/2) sym (A_ς A)` to leading
order:** for `0 < H`, `H ‖A‖ ≤ 1/24` and `√(card κ) · H ‖A‖ ≤ 1/6`, in every order of execution,
`‖Δ_R + (H/2) sym (A_ς A)‖ ≤ (37 + 220σ + 53σ² + 54σ³) ‖A‖³ · H²`, `σ = √(card κ)`. -/
theorem norm_numDissipation_zoh_sub_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    ‖opE (numDissipation A (modifiedSystem H (S.zoh A hA H).X) - S.halfStepDissipation A H)‖ ≤
      zohDiffK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 2 :=
  S.norm_numDissipation_sub_le (S.norm_zoh_difference_sub_half_le hA hH hAH hσ)

/-- **Proposition `prop:parts`, equation `eq:dissipation`, with an explicit remainder.** The
zero-order hold on a system with power-conjugate ports (`A_{ik} = -A_{ki}ᵀ`), in every order of
execution, for `0 < H`, `H ‖A‖ ≤ 1/24` and `√(card κ) · H ‖A‖ ≤ 1/6`: the numerical dissipation
`Δ_R` of its modified system satisfies, for every `x`,
`|xᵀ Δ_R x - ((H/2) Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) - (H/2) xᵀ A_ς A₀ x)|`
`≤ (37 + 220σ + 53σ² + 54σ³) ‖A‖³ · H² ‖x‖²`, `σ = √(card κ)`. -/
theorem abs_numDissipation_zoh_sub_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) (x : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (numDissipation A (modifiedSystem H (S.zoh A hA H).X)) x⟫ -
        (H / 2 * ∑ k, (‖opE (S.driveAfter A k) x‖ ^ 2 - ‖opE (S.driveOther A k) x‖ ^ 2) -
          H / 2 * ⟪x, opE (S.signedCoupling A * S.blockDiag A) x⟫)| ≤
      zohDiffK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 2 * ‖x‖ ^ 2 := by
  have h := S.abs_inner_numDissipation_sub_le
    (S.norm_zoh_difference_sub_half_le hA hH hAH hσ) x x
  rwa [S.inner_halfStepDissipation_self hskew, ← sq] at h

/-! ### The diagonal block: the first formula of `eq:negdamping` -/

/-- The diagonal blocks of `A_ς A₀` vanish: `⟪x, A_ς A₀ y⟫ = 0` for `x`, `y` supported on one
subsystem (`A_ς` has no diagonal blocks and `A₀` is block diagonal). -/
theorem inner_signedCoupling_mul_blockDiag_diag (A : Matrix (Fin n) (Fin n) ℝ) {s : κ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    ⟪x, opE (S.signedCoupling A * S.blockDiag A) y⟫ = 0 := by
  refine inner_opE_eq_zero hx hy fun p q hp hq => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [S.signedCoupling_apply, S.blockDiag_apply]
  by_cases hr : S.sub p = S.sub r
  · rw [ite_eq_left hr, zero_mul]
  · rw [ite_eq_right hr, ite_eq_right fun e => hr (hp.trans (hq.symm.trans e.symm)), mul_zero]

/-- **The diagonal block of `sym (A_ς A)`** (the paper, `eq:negdamping`, first formula, without the
factor `-H/2`), exactly: with power-conjugate ports, for `x`, `y` supported on a subsystem `s`,
`⟪x, sym (A_ς A) y⟫ = -⟪A x, osgn_s (A y)⟫ = -Σ_{k ≠ s} ς_{sk} ⟪A_{ks} x, A_{ks} y⟫`
(`inner_osgn`), that is `[sym (A_ς A)]_{ss} = -Σ_{k ≠ s} ς_{sk} A_{ks}ᵀ A_{ks}`. -/
theorem inner_sym_signedCoupling_mul_diag {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s : κ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    ⟪x, opE (sym (S.signedCoupling A * A)) y⟫ = -⟪opE A x, opE (S.osgn s) (opE A y)⟫ := by
  have e : ⟪opE A y, opE (S.osgn s) (opE A x)⟫ = ⟪opE A x, opE (S.osgn s) (opE A y)⟫ := by
    rw [S.inner_osgn, S.inner_osgn]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [inner_opE_sym_eq, S.inner_signedCoupling_row A hx y, S.inner_signedCoupling_row A hy x,
    S.inner_osgn_skew hskew hx y, S.inner_osgn_skew hskew hy x, e]
  ring

/-- **The diagonal block of the leading numerical dissipation:** for `x`, `y` supported on `s`,
`⟪x, D y⟫ = (H/2) Σ_{k ≠ s} ς_{sk} ⟪A_{ks} x, A_{ks} y⟫`, `D = -(H/2) sym (A_ς A)`. -/
theorem inner_halfStepDissipation_diag {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (H : ℝ) {s : κ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    ⟪x, opE (S.halfStepDissipation A H) y⟫ =
      H / 2 * ⟪opE A x, opE (S.osgn s) (opE A y)⟫ := by
  rw [halfStepDissipation, inner_opE_smul, S.inner_sym_signedCoupling_mul_diag hskew hx hy]
  ring

/-- **The squares of the two rates on one subsystem** (the paper, proof of Proposition `prop:parts`:
"the diagonal block collects `ς_{ik} A_{ki}ᵀ A_{ki}` from the square of each partner `k`"). For
`x` supported on `s`: `Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) = Σ_{k ≠ s} ς_{sk} |A_{ks} x|²`. -/
theorem sum_drive_eq_of_support [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s : κ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0) :
    ∑ k, (‖opE (S.driveAfter A k) x‖ ^ 2 - ‖opE (S.driveOther A k) x‖ ^ 2) =
      ⟪opE A x, opE (S.osgn s) (opE A x)⟫ := by
  have h1 := S.inner_sym_signedCoupling_mul_self hskew x
  rw [S.inner_sym_signedCoupling_mul_diag hskew hx hx,
    S.inner_signedCoupling_mul_blockDiag_diag A hx hx] at h1
  linarith

/-- **Equation `eq:negdamping`, first formula, for the zero-order hold, with an explicit
remainder.** Power-conjugate ports, every order of execution, `0 < H`, `H ‖A‖ ≤ 1/24`,
`√(card κ) · H ‖A‖ ≤ 1/6`, `x` and `y` supported on a subsystem `s`:
`|⟪x, Δ_R y⟫ - (H/2) Σ_{k ≠ s} ς_{sk} ⟪A_{ks} x, A_{ks} y⟫|`
`≤ (37 + 220σ + 53σ² + 54σ³) ‖A‖³ · H² ‖x‖ ‖y‖`, that is
`[Δ_R]_{ss} = (H/2) Σ_k ς_{sk} A_{ks}ᵀ A_{ks} + O(H²)`. -/
theorem abs_numDissipation_zoh_diag_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) {s : κ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    |⟪x, opE (numDissipation A (modifiedSystem H (S.zoh A hA H).X)) y⟫ -
        H / 2 * ⟪opE A x, opE (S.osgn s) (opE A y)⟫| ≤
      zohDiffK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 2 * (‖x‖ * ‖y‖) := by
  have h := S.abs_inner_numDissipation_sub_le
    (S.norm_zoh_difference_sub_half_le hA hH hAH hσ) x y
  rwa [S.inner_halfStepDissipation_diag hskew H hx hy] at h

/-! ### What a scheme changes -/

/-- **What a scheme adds to the difference, to leading order:** the two brackets of the
half-step normal form divided by the macro step,
`G = H⁻¹ [(F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c)]` (the local maps and the
coefficients of the samples against those of the zero-order hold to second order). -/
noncomputable def schemeChange (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  H⁻¹ • ((S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
    (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)))

/-- **From the difference to the numerical dissipation, with the change of a scheme.** If
`‖Δ - G - (H/2) A_ς A‖ ≤ C`, then `|⟪x, Δ_R y⟫ + ⟪x, sym G y⟫ - ⟪x, D y⟫| ≤ C ‖x‖ ‖y‖` with
`D = -(H/2) sym (A_ς A)`. -/
theorem abs_inner_numDissipation_add_sub_le {A At G : Matrix (Fin n) (Fin n) ℝ} {H C : ℝ}
    (hC : ‖opE (At - A - G - (H / 2) • (S.signedCoupling A * A))‖ ≤ C)
    (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (numDissipation A At) y⟫ + ⟪x, opE (sym G) y⟫ -
        ⟪x, opE (S.halfStepDissipation A H) y⟫| ≤ C * (‖x‖ * ‖y‖) := by
  have hxy : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  have h1 := abs_le.1
    ((abs_inner_opE_le (At - A - G - (H / 2) • (S.signedCoupling A * A)) x y).trans
      (mul_le_mul_of_nonneg_right hC hxy))
  have h2 := abs_le.1
    ((abs_inner_opE_le (At - A - G - (H / 2) • (S.signedCoupling A * A)) y x).trans
      (mul_le_mul_of_nonneg_right hC (by positivity)))
  rw [mul_comm ‖y‖ ‖x‖] at h2
  rw [inner_opE_sub, inner_opE_sub, inner_opE_smul] at h1 h2
  rw [inner_numDissipation, halfStepDissipation, inner_opE_smul, inner_opE_sym_eq,
    inner_opE_sym_eq, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

variable {S}

/-- What a scheme adds has no block between different subsystems that are not partners: it
consists of blocks within the subsystems and between partners. -/
theorem Consistent.inner_schemeChange_eq_zero {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) : ⟪x, opE (S.schemeChange A H) y⟫ = 0 := by
  rw [schemeChange, inner_opE_smul, inner_opE_add, S.inner_local_bracket_eq_zero A H hst hx hy,
    h.inner_sample_bracket_eq_zero hnp hx hy, add_zero, mul_zero]

/-- **A scheme changes the numerical dissipation by a symmetric matrix with blocks within the
subsystems and between partners only** (the paper, Proposition `prop:parts`, second statement, the
structure): `⟪x, sym G y⟫ = 0` for `x`, `y` supported on different subsystems that are not
partners. -/
theorem Consistent.inner_sym_schemeChange_eq_zero {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    ⟪x, opE (sym (S.schemeChange A H)) y⟫ = 0 := by
  rw [inner_opE_sym_eq, h.inner_schemeChange_eq_zero hst hnp hx hy,
    h.inner_schemeChange_eq_zero hst.symm hnp' hy hx, add_zero, mul_zero]

/-- **The numerical dissipation of every consistent scheme** (the paper, Proposition `prop:parts`,
second statement, with an explicit remainder). For `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, in any
order of execution: `‖Δ_R + sym G + (H/2) sym (A_ς A)‖ ≤ (K + √(card κ) C₃) H²`, with `G` the
change of the scheme (`schemeChange`), `K = diffLeadC b c ‖A‖`, `C₃ = reactionC a b c ‖A‖ H`.
The numerical dissipation is that of the half step, `-(H/2) sym (A_ς A)`, minus `sym G`. -/
theorem Consistent.norm_numDissipation_add_sym_sub_le [Fintype κ]
    {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ} (h : S.Consistent A U H a b c)
    (hH : 0 < H) (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    ‖opE (numDissipation A (modifiedSystem H S.X) + sym (S.schemeChange A H) -
        S.halfStepDissipation A H)‖ ≤
      (diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H) *
        H ^ 2 := by
  have hC := h.norm_difference_half_step_le hH hbH hAH
  refine norm_opE_le_of_abs_inner_le ((norm_nonneg _).trans hC) fun x y => ?_
  rw [inner_opE_sub, inner_opE_add]
  exact S.abs_inner_numDissipation_add_sub_le hC x y

/-- **Equation `eq:negdamping`, first formula, for every scheme with partner weights only, with
an explicit remainder.** A consistent scheme with one held sample, in any order of execution,
power-conjugate ports, `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`; a subsystem `s` that is not its own
partner and whose local map is `e^{H A_s}` (partner weights only); `x`, `y` supported on `s`:
`|⟪x, Δ_R y⟫ - (H/2) Σ_{k ≠ s} ς_{sk} ⟪A_{ks} x, A_{ks} y⟫|`
`≤ (K + C₃ + ‖A_s‖³/6 · e^{H‖A_s‖}) H² ‖x‖ ‖y‖`, `K = diffLeadC b c ‖A‖`,
`C₃ = reactionC a b c ‖A‖ H`, whatever the coefficients of the partner samples. -/
theorem Consistent.numDissipation_diag {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hH : 0 < H) (hbH : b * H ≤ 1 / 3) (hAH : H * ‖opE A‖ ≤ 1 / 4) {s : κ}
    (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    |⟪x, opE (numDissipation A (modifiedSystem H S.X)) y⟫ -
        H / 2 * ⟪opE A x, opE (S.osgn s) (opE A y)⟫| ≤
      (diffLeadC b c ‖opE A‖ + (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖))) * H ^ 2 *
          (‖x‖ * ‖y‖) := by
  have e : ⟪opE A y, opE (S.osgn s) (opE A x)⟫ = ⟪opE A x, opE (S.osgn s) (opE A y)⟫ := by
    rw [S.inner_osgn, S.inner_osgn]
    exact Finset.sum_congr rfl fun r _ => by ring
  have h1 := abs_le.1 (abs_inner_difference_sub_le hH h.hU h.hb h.hc hbH hAH x y)
  have h2 := abs_le.1 (abs_inner_difference_sub_le hH h.hU h.hb h.hc hbH hAH y x)
  rw [mul_comm ‖y‖ ‖x‖] at h2
  have key : ∀ {u v : EuclideanSpace ℝ (Fin n)}, (∀ p, S.sub p ≠ s → u p = 0) →
      (∀ q, S.sub q ≠ s → v q = 0) →
      |H⁻¹ * ⟪u, opE (S.X - U) v⟫ + H / 2 * ⟪opE A u, opE (S.osgn s) (opE A v)⟫| ≤
        (reactionC a b c ‖opE A‖ H +
          ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖)) * H ^ 2 *
            (‖u‖ * ‖v‖) := by
    intro u v hu hv
    have h3 : |H⁻¹ * (⟪u, opE (S.X - U) v⟫ +
        H ^ 2 / 2 * ⟪opE A u, opE (S.osgn s) (opE A v)⟫)| ≤
        (reactionC a b c ‖opE A‖ H +
          ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖)) * H ^ 2 *
            (‖u‖ * ‖v‖) := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hH), inv_mul_le_iff₀ hH]
      exact (h.reaction_partner_weights hskew hnp hFs hu hv).trans_eq (by ring)
    rwa [mul_add, ← mul_assoc, inv_mul_sq_half hH.ne'] at h3
  have h3 := abs_le.1 (key hx hy)
  have h4 := abs_le.1 (key hy hx)
  rw [mul_comm ‖y‖ ‖x‖, e] at h4
  rw [inner_numDissipation, abs_le]
  change -((diffLeadC b c ‖opE A‖ + (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖))) * H ^ 2 *
          (‖x‖ * ‖y‖)) ≤
      -(1 / 2) * (⟪x, opE (difference A H S.X) y⟫ + ⟪y, opE (difference A H S.X) x⟫) -
        H / 2 * ⟪opE A x, opE (S.osgn s) (opE A y)⟫ ∧
    -(1 / 2) * (⟪x, opE (difference A H S.X) y⟫ + ⟪y, opE (difference A H S.X) x⟫) -
        H / 2 * ⟪opE A x, opE (S.osgn s) (opE A y)⟫ ≤
      (diffLeadC b c ‖opE A‖ + (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖))) * H ^ 2 *
          (‖x‖ * ‖y‖)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

end HeldScheme

end CoSimFoundations
