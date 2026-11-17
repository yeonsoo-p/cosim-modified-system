/-
The half-step normal form of the one-step difference `X - U`, for the whole matrix (the paper:
"a held sample is half a macro step old, a new sample half a macro step ahead").

Setting of `ForcedBlock`, `Reaction`, `ReactionDiag`: a `HeldScheme` (`X = F + M + N * X`, states
grouped by `sub`), `U = exp (H • A)`, spectral norms `‖opE ·‖`, `S.Consistent A U H a b c`.
`Reaction.lean` gives the rows of `X - U` subsystem by subsystem, with the signs
`ς_s = sgn s` of the subsystem `s` of the row (`Consistent.reaction_row`). Here the same fact is
stated once, with matrices that do not depend on the row:

* `blockDiag A = A₀`  the block-diagonal part of `A`: `A₀ p q = A p q` if `sub p = sub q`, else `0`;
* `coupling A = A_c = A - A₀`  the coupling part;
* `signedCoupling A = A_ς`  the coupling signed by the stage of its source:
  `A_ς p q = ς(sub p, sub q) A p q` for `sub p ≠ sub q`, else `0`, with `ς_{sk} = S.sg s k`
  (`+1` if `k` runs at an earlier stage than `s`, so that `s` uses a new sample of `k`; `-1` if
  not, so that `s` uses a held sample of `k`).

**The normal form** (`halfStepLead`, `Consistent.half_step_row`, `Consistent.half_step`,
`Consistent.norm_half_step_le`):
  `X - U = (F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c) + ½H² A_ς A + r`,
* in the rows of one subsystem (`x` supported on `s`, every `y`):
  `|⟪x, r y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`, `C₃ = reactionC a b c ‖A‖ H`, the constant of `reaction_row`;
* for all `x`, `y`: `|⟪x, r y⟫| ≤ √(card κ) C₃ H³ ‖x‖ ‖y‖`, that is `‖r‖ ≤ √(card κ) C₃ H³`
  (`κ` the type of the subsystems: `x` is cut into its parts on the subsystems, the row bounds are
  added, and `Σ_s ‖x_s‖ ≤ √(card κ) ‖x‖`).
The first bracket is the error of the local maps against `e^{H A₀}` to second order. The second
is the error of the coefficients of the samples against `H A_c + ½H² A₀ A_c`, the zero-order hold
to second order. The third is `H A_ς · (H/2) A`. The monolithic step couples, to this order,
through the state in the middle of the macro step: `H A_c + ½H² A_c A = H A_c (1 + (H/2) A)`. A new
sample is the state half a macro step later, `+ (H/2) A x`, a held sample the state half a macro
step earlier, `- (H/2) A x`; with the sign of each coupling entry this is `H A_ς (H/2) A x`.

Proof of the row form: `reaction_row`, the matrix identity `half_step_brackets`
(`F - 1 - H A = (F - 1 - H A₀) - H A_c`, `A₀ A = A₀² + A₀ A_c`), and, in the rows of `s`,
`A ς_s A = A_ς A - A₀ A` (`sgn_row`: `ς_{ss} = -1`).

**The three readings** of the row form, `x` supported on `s`, `y` on `t`:
* `s ≠ t`, not partners (`Consistent.half_step_forced`): both brackets vanish,
  `|⟪x, (X - U) y⟫ - ½H² ⟪x, A_ς A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`. This is `Consistent.forced_block'` with
  `A_ς A` in place of `A ς_s A` (the two have the same block there).
* `s ≠ t` (`Consistent.half_step_offdiag`): the first bracket vanishes; for partners the second
  stays.
* `s = t`, `s` not its own partner (`Consistent.half_step_diag`): the second bracket vanishes,
  `|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A₀ - ½H² A₀²) y⟫ - ½H² ⟪x, A_ς A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`.
  In the rows of `s`, `A_ς A = A osgn_s A` (`inner_signedCoupling_row`), so this is
  `Consistent.reaction_diag` with `1 + H A₀ + ½H² A₀²` in place of `e^{H A_s}` and without the
  Taylor remainder of `e^{H A_s}` in the constant.

**Exact local maps** (`norm_local_bracket_le`): if `F = exp (H • A₀)`, the first bracket is at most
`‖A₀‖³/6 · e^{H‖A₀‖} H³`. The second bracket for the zero-order hold
(`M + N = H φ₁(H A₀) A_c`) is not formalized: the library has no coefficients of a hold (`Phi`
defines `φ_b` in a Banach algebra, without bounds and without the bridge to `opE`).
-/
import CoSimFoundations.ReactionDiag
import Mathlib.Algebra.Order.Chebyshev

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-- From the matrix elements to the spectral norm: if `|⟪x, W y⟫| ≤ K ‖x‖ ‖y‖` for all `x`, `y`,
then `‖W‖ ≤ K`. -/
theorem norm_opE_le_of_abs_inner_le {W : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x y : EuclideanSpace ℝ (Fin n), |⟪x, opE W y⟫| ≤ K * (‖x‖ * ‖y‖)) :
    ‖opE W‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le hK fun u v hu hv => ?_
  have h1 := h v u
  rw [hu, hv, mul_one, mul_one] at h1
  rw [RCLike.re_to_real, real_inner_comm]
  exact (le_abs_self _).trans h1

/-- The spectral norm is submultiplicative: `‖A B‖ ≤ ‖A‖ ‖B‖`. -/
theorem norm_opE_mul_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (A * B)‖ ≤ ‖opE A‖ * ‖opE B‖ := by
  rw [opE_mul]
  exact norm_mul_le _ _

/-- A factor of spectral norm at most one on the right does not increase the spectral norm:
`‖A D‖ ≤ ‖A‖` if `‖D‖ ≤ 1`. -/
theorem norm_opE_mul_le_of_norm_le_one (A : Matrix (Fin n) (Fin n) ℝ)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : ‖opE D‖ ≤ 1) : ‖opE (A * D)‖ ≤ ‖opE A‖ :=
  (norm_opE_mul_le A D).trans (mul_le_of_le_one_right (norm_nonneg _) hD)

namespace HeldScheme

section Bound

variable {κ : Type*} {S : HeldScheme n κ}

/-- The bound of the reaction is not negative: `0 ≤ C₃ H³` (for `H > 0` the constants `a`, `b`,
`c` of a consistent scheme bound norms, for `H = 0` the product vanishes). -/
theorem Consistent.reaction_bound_nonneg {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) : 0 ≤ reactionC a b c ‖opE A‖ H * H ^ 3 := by
  rcases h.hH.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · have ha : 0 ≤ a := (mul_nonneg_iff_of_pos_right hpos).1 (le_trans (norm_nonneg _) h.ha)
    have hb : 0 ≤ b := (mul_nonneg_iff_of_pos_right hpos).1 (le_trans (norm_nonneg _) h.hb)
    have hc : 0 ≤ c :=
      (mul_nonneg_iff_of_pos_right (pow_pos hpos 2)).1 (le_trans (norm_nonneg _) h.hc)
    have hC : 0 ≤ reactionC a b c ‖opE A‖ H := by
      unfold reactionC reactionConst couplingConst
      positivity
    exact mul_nonneg hC (pow_nonneg h.hH 3)

end Bound

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The three parts of `A` -/

/-- The block-diagonal part `A₀` of a matrix: the entries inside the subsystems. -/
def blockDiag (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if S.sub p = S.sub q then A p q else 0

/-- The coupling part `A_c = A - A₀` of a matrix: the entries between different subsystems. -/
noncomputable def coupling (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A - S.blockDiag A

/-- The coupling signed by the stage of its source, `A_ς`: between different subsystems
`A_ς p q = ς(sub p, sub q) A p q`, with `+1` if the subsystem of `q` runs at an earlier stage than
the subsystem of `p` (a new sample) and `-1` if not (a held sample); `0` inside a subsystem. -/
noncomputable def signedCoupling (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if S.sub p = S.sub q then 0 else S.sg (S.sub p) (S.sub q) * A p q

/-- The entries of the block-diagonal part. -/
theorem blockDiag_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    S.blockDiag A p q = if S.sub p = S.sub q then A p q else 0 := rfl

/-- The entries of the coupling part. -/
theorem coupling_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    S.coupling A p q = if S.sub p = S.sub q then 0 else A p q := by
  rw [coupling, Matrix.sub_apply, S.blockDiag_apply]
  by_cases hpq : S.sub p = S.sub q
  · rw [ite_eq_left hpq, ite_eq_left hpq, sub_self]
  · rw [ite_eq_right hpq, ite_eq_right hpq, sub_zero]

/-- The entries of the signed coupling. -/
theorem signedCoupling_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    S.signedCoupling A p q =
      if S.sub p = S.sub q then 0 else S.sg (S.sub p) (S.sub q) * A p q := rfl

/-- `A = A₀ + A_c`. -/
theorem blockDiag_add_coupling (A : Matrix (Fin n) (Fin n) ℝ) :
    S.blockDiag A + S.coupling A = A := by
  rw [coupling]
  abel

/-! ### The signs of the other subsystems -/

/-- The signs of the other subsystems form a diagonal matrix of spectral norm at most one. -/
theorem norm_opE_osgn_le (s : κ) : ‖opE (S.osgn s)‖ ≤ 1 :=
  norm_opE_diagonal_le _ zero_le_one fun i => by
    by_cases h1 : S.sub i = s
    · simp [h1]
    · by_cases h2 : S.stage (S.sub i) < S.stage s <;> simp [sg, h1, h2]

/-- The entry of a product with the signs of the other subsystems in the middle:
`(A osgn_s B)_{pq} = Σ_{r ∉ s} A_{pr} ς_{s, sub r} B_{rq}`. -/
theorem mul_osgn_mul_apply (A B : Matrix (Fin n) (Fin n) ℝ) (s : κ) (p q : Fin n) :
    (A * S.osgn s * B) p q =
      ∑ r, A p r * (if S.sub r = s then 0 else S.sg s (S.sub r)) * B r q :=
  mul_diagonal_mul_apply A B _ p q

/-! ### The algebra of the normal form -/

/-- In the rows of a subsystem `s`, `A ς_s A = A_ς A - A₀ A`: the sign of `s` on itself is `-1`. -/
theorem sgn_row (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    (A * S.sgn (S.sub p) * A) p q = (S.signedCoupling A * A) p q - (S.blockDiag A * A) p q := by
  rw [S.sgn_entry, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [S.signedCoupling_apply, S.blockDiag_apply]
  by_cases hr : S.sub p = S.sub r
  · have e : S.sg (S.sub p) (S.sub r) = -1 := by
      rw [← hr]
      simp [sg]
    rw [ite_eq_left hr, ite_eq_left hr, e]
    ring
  · rw [ite_eq_right hr, ite_eq_right hr]
    ring

/-- Between different subsystems that are not partners the entries of `A_ς A` are those of
`A ς_s A`: the entry of `A₀ A` by which the two differ (`sgn_row`) vanishes, because `A` has no
block between the two subsystems. -/
theorem signedCoupling_mul_apply_eq_sgn {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {p q : Fin n}
    (hne : S.sub p ≠ S.sub q) (hnp : ¬ S.partner (S.sub p) (S.sub q)) :
    (S.signedCoupling A * A) p q = (A * S.sgn (S.sub p) * A) p q := by
  have h0 : (S.blockDiag A * A) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [S.blockDiag_apply]
    by_cases hr : S.sub p = S.sub r
    · rw [hA r q (by rw [← hr]; exact hne) (by rw [← hr]; exact hnp), mul_zero]
    · rw [ite_eq_right hr, zero_mul]
  rw [S.sgn_row, h0, sub_zero]

/-- `⟪x, A ς_s A y⟫ = ⟪x, A_ς A y⟫ - ⟪x, A₀ A y⟫` for `x` supported on the subsystem `s`. -/
theorem inner_sgn_row (A : Matrix (Fin n) (Fin n) ℝ) {s : κ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (A * S.sgn s * A) y⟫ =
      ⟪x, opE (S.signedCoupling A * A) y⟫ - ⟪x, opE (S.blockDiag A * A) y⟫ := by
  rw [← inner_opE_sub]
  refine inner_opE_congr_row hx y fun p q hp => ?_
  rw [Matrix.sub_apply, ← hp]
  exact S.sgn_row A p q

/-- In the rows of a subsystem `s`, `A_ς A = A osgn_s A`, that is `Σ_{k ≠ s} ς_{sk} A_{sk}` times
the rows of `k` of `A`: the third term of the normal form is the term of
`Consistent.reaction_diag`. -/
theorem inner_signedCoupling_row (A : Matrix (Fin n) (Fin n) ℝ) {s : κ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ = ⟪x, opE (A * S.osgn s * A) y⟫ := by
  refine inner_opE_congr_row hx y fun p q hp => ?_
  rw [S.mul_osgn_mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [S.signedCoupling_apply, hp]
  by_cases hr : S.sub r = s
  · rw [ite_eq_left hr.symm, ite_eq_left hr]
    ring
  · rw [ite_eq_right fun e' => hr e'.symm, ite_eq_right hr]
    ring

/-- **The two brackets of the normal form.**
`(F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c) = (F - 1 - H A) + (M + N) - ½H² A₀ A`. -/
theorem half_step_brackets (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    (S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
        (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) =
      (S.F - 1 - H • A) + (S.M + S.N) - (H ^ 2 / 2) • (S.blockDiag A * A) := by
  simp only [coupling, Matrix.mul_sub, smul_sub]
  abel

/-- **The leading term of `X - U` in the half-step normal form:**
`(F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c) + ½H² A_ς A`. -/
noncomputable def halfStepLead (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
    (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) +
    (H ^ 2 / 2) • (S.signedCoupling A * A)

/-- The matrix element of `X - U` minus its leading term, term by term. -/
theorem inner_halfStepLead (A U : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.X - U - S.halfStepLead A H) y⟫ =
      ⟪x, opE (S.X - U) y⟫ -
        ⟪x, opE (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) y⟫ -
        ⟪x, opE (S.M + S.N - H • S.coupling A -
          (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫ := by
  rw [halfStepLead, inner_opE_sub, inner_opE_add, inner_opE_add, inner_opE_smul]
  ring

/-- The first bracket has no block between different subsystems. -/
theorem inner_local_bracket_eq_zero (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) {s t : κ}
    (hst : s ≠ t) {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    ⟪x, opE (S.F - 1 - H • S.blockDiag A -
      (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) y⟫ = 0 := by
  refine inner_opE_eq_zero hx hy fun p q hp hq => ?_
  have hne : S.sub p ≠ S.sub q := by rw [hp, hq]; exact hst
  have hpq : p ≠ q := fun e => hne (e ▸ rfl)
  have h2 : (S.blockDiag A * S.blockDiag A) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [S.blockDiag_apply, S.blockDiag_apply]
    by_cases hr : S.sub p = S.sub r
    · rw [ite_eq_right fun e => hne (hr.trans e), mul_zero]
    · rw [ite_eq_right hr, zero_mul]
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.smul_apply, S.hF p q hne, Matrix.one_apply_ne hpq, S.blockDiag_apply, ite_eq_right hne, h2]
  simp

/-- **Exact local maps.** If `F = exp (H • A₀)`, the first bracket of the normal form is the Taylor
remainder of the exponential: `‖F - 1 - H A₀ - ½H² A₀²‖ ≤ ‖A₀‖³/6 · e^{H‖A₀‖} H³`. -/
theorem norm_local_bracket_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) :
    ‖opE (S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A))‖ ≤
      ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 := by
  have e : S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A) =
      NormedSpace.exp (H • S.blockDiag A) -
        (1 + H • S.blockDiag A + (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) := by
    rw [← hF]
    abel
  rw [e]
  exact norm_opE_exp_sub_quadratic_le _ hH

/-! ### From the rows to the whole matrix -/

/-- The part of a vector on a subsystem, in components. -/
theorem opE_mask_apply (s : κ) (x : EuclideanSpace ℝ (Fin n)) (p : Fin n) :
    (opE (S.mask s) x) p = (if S.sub p = s then 1 else 0) * x p :=
  opE_diagonal_apply _ x p

/-- The part of a vector on a subsystem is supported on the subsystem. -/
theorem opE_mask_support (s : κ) (x : EuclideanSpace ℝ (Fin n)) (p : Fin n)
    (hp : S.sub p ≠ s) : (opE (S.mask s) x) p = 0 := by
  rw [S.opE_mask_apply, ite_eq_right hp, zero_mul]

/-- An inner product is the sum over the parts of its first vector on the subsystems. -/
theorem inner_eq_sum_parts [Fintype κ] (x w : EuclideanSpace ℝ (Fin n)) :
    ⟪x, w⟫ = ∑ s, ⟪opE (S.mask s) x, w⟫ := by
  simp only [inner_eq_sum, S.opE_mask_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), one_mul]

/-- The parts of a vector on the subsystems are orthogonal: `Σ_s ‖x_s‖² = ‖x‖²`. -/
theorem sum_norm_sq_parts [Fintype κ] (x : EuclideanSpace ℝ (Fin n)) :
    ∑ s, ‖opE (S.mask s) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h : ∀ s, ‖opE (S.mask s) x‖ ^ 2 = ⟪opE (S.mask s) x, x⟫ := by
    intro s
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum, inner_eq_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [S.opE_mask_apply]
    by_cases hr : S.sub r = s
    · rw [ite_eq_left hr]
      ring
    · rw [ite_eq_right hr]
      ring
  rw [Finset.sum_congr rfl fun s _ => h s, ← S.inner_eq_sum_parts, real_inner_self_eq_norm_sq]

/-- `Σ_s ‖x_s‖ ≤ √(card κ) ‖x‖` for the parts `x_s` of a vector on the subsystems. -/
theorem sum_norm_parts_le [Fintype κ] (x : EuclideanSpace ℝ (Fin n)) :
    ∑ s, ‖opE (S.mask s) x‖ ≤ Real.sqrt (Fintype.card κ) * ‖x‖ := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ))
    (f := fun s => ‖opE (S.mask s) x‖)
  rw [Finset.card_univ, S.sum_norm_sq_parts] at h1
  have h2 : Real.sqrt (Fintype.card κ) * ‖x‖ = Real.sqrt ((Fintype.card κ : ℝ) * ‖x‖ ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [h2]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

/-- **From the rows to the whole matrix.** If `|⟪x, W y⟫| ≤ K ‖x‖ ‖y‖` for every `x` supported on
one subsystem and every `y`, then `|⟪x, W y⟫| ≤ √(card κ) K ‖x‖ ‖y‖` for all `x`, `y`. -/
theorem abs_inner_opE_le_of_rows [Fintype κ] {W : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hrow : ∀ (s : κ) (x : EuclideanSpace ℝ (Fin n)), (∀ p, S.sub p ≠ s → x p = 0) →
      ∀ y : EuclideanSpace ℝ (Fin n), |⟪x, opE W y⟫| ≤ K * (‖x‖ * ‖y‖))
    (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE W y⟫| ≤ Real.sqrt (Fintype.card κ) * K * (‖x‖ * ‖y‖) := by
  rw [S.inner_eq_sum_parts x (opE W y)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ s ∈ (Finset.univ : Finset κ),
      |⟪opE (S.mask s) x, opE W y⟫| ≤ K * (‖opE (S.mask s) x‖ * ‖y‖) :=
    fun s _ => hrow s _ (S.opE_mask_support s x) y
  refine (Finset.sum_le_sum h1).trans ?_
  have h2 : ∑ s, K * (‖opE (S.mask s) x‖ * ‖y‖) = K * ‖y‖ * ∑ s, ‖opE (S.mask s) x‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h2]
  exact (mul_le_mul_of_nonneg_left (S.sum_norm_parts_le x)
    (mul_nonneg hK (norm_nonneg y))).trans_eq (by ring)

/-- **From the rows to the spectral norm.** Under the hypothesis of `abs_inner_opE_le_of_rows`,
`‖W‖ ≤ √(card κ) K`. -/
theorem norm_opE_le_of_rows [Fintype κ] {W : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ (s : κ) (x : EuclideanSpace ℝ (Fin n)), (∀ p, S.sub p ≠ s → x p = 0) →
      ∀ y : EuclideanSpace ℝ (Fin n), |⟪x, opE W y⟫| ≤ K * (‖x‖ * ‖y‖)) :
    ‖opE W‖ ≤ Real.sqrt (Fintype.card κ) * K :=
  norm_opE_le_of_abs_inner_le (mul_nonneg (Real.sqrt_nonneg _) hK)
    (S.abs_inner_opE_le_of_rows hK hrow)

variable {S}

/-! ### The normal form -/

/-- **The half-step normal form, in the rows of a subsystem.** For a consistent scheme with one
held sample, in any order of execution, `x` supported on a subsystem `s` and every vector `y`:
`|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A₀ - ½H² A₀²) y⟫ - ⟪x, (M + N - H A_c - ½H² A₀ A_c) y⟫`
`- ½H² ⟪x, A_ς A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`, `C₃ = reactionC a b c ‖A‖ H`. This is
`Consistent.reaction_row`, rewritten with matrices that do not depend on `s`. -/
theorem Consistent.half_step_row {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (S.X - U) y⟫ -
        ⟪x, opE (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) y⟫ -
        ⟪x, opE (S.M + S.N - H • S.coupling A -
          (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have e1 := S.inner_sgn_row A hx y
  have e2 : ⟪x, opE (S.F - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) y⟫ +
      ⟪x, opE (S.M + S.N - H • S.coupling A -
        (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) y⟫ =
      ⟪x, opE (S.F - 1 - H • A) y⟫ + ⟪x, opE (S.M + S.N) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (S.blockDiag A * A) y⟫ := by
    rw [← inner_opE_add, S.half_step_brackets, inner_opE_sub, inner_opE_add, inner_opE_smul]
  refine le_of_eq_of_le (congrArg abs ?_) (h.reaction_row hx y)
  linear_combination (H ^ 2 / 2) * e1 - e2

/-- **The half-step normal form of `X - U`, for the whole matrix.** For a consistent scheme with
one held sample, in any order of execution, and all vectors `x`, `y`:
`|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A₀ - ½H² A₀²) y⟫ - ⟪x, (M + N - H A_c - ½H² A₀ A_c) y⟫`
`- ½H² ⟪x, A_ς A y⟫| ≤ √(card κ) C₃ H³ ‖x‖ ‖y‖`, `C₃ = reactionC a b c ‖A‖ H`, `κ` the type of the
subsystems. -/
theorem Consistent.half_step [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (S.X - U) y⟫ -
        ⟪x, opE (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) y⟫ -
        ⟪x, opE (S.M + S.N - H • S.coupling A -
          (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫| ≤
      Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := S.abs_inner_opE_le_of_rows (W := S.X - U - S.halfStepLead A H)
    h.reaction_bound_nonneg
    (fun s x' hx' y' => by
      rw [S.inner_halfStepLead]
      exact h.half_step_row hx' y') x y
  rw [S.inner_halfStepLead] at h1
  exact h1.trans_eq (by ring)

/-- **The half-step normal form, in the spectral norm:**
`‖X - U - [(F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c) + ½H² A_ς A]‖`
`≤ √(card κ) C₃ H³`, `C₃ = reactionC a b c ‖A‖ H`. -/
theorem Consistent.norm_half_step_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) :
    ‖opE (S.X - U - S.halfStepLead A H)‖ ≤
      Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := S.norm_opE_le_of_rows (W := S.X - U - S.halfStepLead A H)
    h.reaction_bound_nonneg
    (fun s x' hx' y' => by
      rw [S.inner_halfStepLead]
      exact h.half_step_row hx' y')
  exact h1.trans_eq (by ring)

/-! ### The three readings -/

/-- The second bracket has no block between subsystems that are not partners (the two may
coincide): there `M`, `N`, `A_c` and `A₀ A_c` vanish. -/
theorem Consistent.inner_sample_bracket_eq_zero {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    ⟪x, opE (S.M + S.N - H • S.coupling A -
      (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) y⟫ = 0 := by
  refine inner_opE_eq_zero hx hy fun p q hp hq => ?_
  have hnp' : ¬ S.partner (S.sub p) (S.sub q) := by rw [hp, hq]; exact hnp
  have hc : ∀ r, S.sub r = s → S.coupling A r q = 0 := by
    intro r hr
    rw [S.coupling_apply]
    by_cases e : S.sub r = S.sub q
    · rw [ite_eq_left e]
    · rw [ite_eq_right e]
      exact h.hA r q e (by rw [hr, hq]; exact hnp)
  have h2 : (S.blockDiag A * S.coupling A) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : S.sub p = S.sub r
    · rw [hc r (hr.symm.trans hp), mul_zero]
    · rw [S.blockDiag_apply, ite_eq_right hr, zero_mul]
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, S.hM p q (fun h' => hnp' h'.1), S.hN p q (fun h' => hnp' h'.1),
    hc p hp, h2]
  simp

/-- **Different subsystems that are not partners:** only the half-step term remains. For `x`
supported on `s` and `y` on `t ≠ s`, not a partner of `s`:
`|⟪x, (X - U) y⟫ - ½H² ⟪x, A_ς A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`. This is `Consistent.forced_block'` with
`A_ς A` in place of `A ς_s A`. -/
theorem Consistent.half_step_forced {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - H ^ 2 / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := h.half_step_row hx y
  rwa [S.inner_local_bracket_eq_zero A H hst hx hy, sub_zero,
    h.inner_sample_bracket_eq_zero hnp hx hy, sub_zero] at h1

/-- **Different subsystems:** the local bracket is absent. For `x` supported on `s` and `y` on
`t ≠ s`: `|⟪x, (X - U) y⟫ - ⟪x, (M + N - H A_c - ½H² A₀ A_c) y⟫ - ½H² ⟪x, A_ς A y⟫|`
`≤ C₃ H³ ‖x‖ ‖y‖`. -/
theorem Consistent.half_step_offdiag {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ -
        ⟪x, opE (S.M + S.N - H • S.coupling A -
          (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := h.half_step_row hx y
  rwa [S.inner_local_bracket_eq_zero A H hst hx hy, sub_zero] at h1

/-- **The diagonal block:** the bracket of the samples is absent. For `x`, `y` supported on a
subsystem `s` that is not its own partner:
`|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A₀ - ½H² A₀²) y⟫ - ½H² ⟪x, A_ς A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`.
Compare `Consistent.reaction_diag`, which has `F - e^{H A_s}` and a larger constant. -/
theorem Consistent.half_step_diag {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} (hnp : ¬ S.partner s s)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ -
        ⟪x, opE (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (S.signedCoupling A * A) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := h.half_step_row hx y
  rwa [h.inner_sample_bracket_eq_zero hnp hx hy, sub_zero] at h1

end HeldScheme

end CoSimFoundations
