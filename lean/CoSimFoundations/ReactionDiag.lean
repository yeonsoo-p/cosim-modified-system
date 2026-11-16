/-
The reaction, diagonal block (the paper, Proposition 6.1 `prop:reaction`, equation
`eq:reaction`, with an explicit remainder). Continues `Reaction.lean`.

Setting of `ForcedBlock` and `Reaction`. For a subsystem `s`:
* `mask s`  the diagonal `0/1` matrix of the states of `s`;
* `blk s A = mask s * A * mask s`  the block `A_s` of `A`, padded with zeros. It is block
  diagonal, so the block `s` of `exp (H • blk s A)` is `e^{H A_s}` (and the rest is the unit
  matrix), and `‖opE (blk s A)‖` is the spectral norm of `A_s`. "`F_s = e^{H A_s}`" is therefore
  stated as: `F` and `exp (H • blk s A)` have the same block `s` (`BlockExp.lean` proves that
  this block is the exponential of the matrix `A_s` on the states of `s`, and `‖A_s‖ ≤ ‖A‖`);
* `osgn s = sgn s + mask s`  the diagonal matrix of the signs `ς_{sk}` on the states of the other
  subsystems `k`, and `0` on `s`.

**The diagonal block** (`Consistent.reaction_diag`). For a consistent scheme, `s` not a partner
of itself, `x`, `y` supported on `s`:
  `|⟪x, (X - U) y⟫ - ⟪x, (F - e^{H A_s}) y⟫ - ½H² ⟪x, A osgn_s A y⟫|`
      `≤ (C₃ + ‖A_s‖³/6 · e^{H‖A_s‖}) H³ ‖x‖ ‖y‖`,
that is `Π_s (X - U) Π_sᵀ = F_s - e^{H A_s} + ½H² Σ_{k ≠ s} ς_{sk} A_{sk} A_{ks} + r_s`.
Proof: `Consistent.reaction_block` with `t = s`; on the block `s`,
`F - 1 - H A - ½H² A mask_s A = (F - e^{H A_s}) + (e^{H A_s} - 1 - H A_s - ½H² A_s²)`, and the
last bracket is at most `‖A_s‖³/6 · e^{H‖A_s‖} H³`; `sgn s` is `-1` on `s`, so `A sgn_s A` and
`A osgn_s A` differ by `-A mask_s A`.

**The form of the paper** (`Consistent.reaction_diag_skew`). If `A_{sk} = -A_{ks}ᵀ` (`hskew`:
`A q p = -A p q` for states of different subsystems), then
`⟪x, A osgn_s A y⟫ = -⟪A x, osgn_s A y⟫ = -Σ_{k ≠ s} ς_{sk} ⟪A_{ks} x, A_{ks} y⟫`, so
  `|⟪x, (X - U) y⟫ - ⟪x, (F - e^{H A_s}) y⟫ + ½H² Σ_k ς_{sk} ⟪A_{ks} x, A_{ks} y⟫| ≤ … H³ ‖x‖ ‖y‖`.

**Partner weights only** (`Consistent.reaction_partner_weights`): with `F_s = e^{H A_s}` the term
with `F` is absent, whatever the weights.

The paper's Proposition 6.1 is stated for "every consistent family of holds" with `O(H³)`; here
the family is replaced by one scheme at one macro step `H ≥ 0` with the constants `a`, `b`, `c` of
`HeldScheme.Consistent`, and that no subsystem is its own partner (`L_ii = 0` in the paper) is the
hypothesis `hnp`.
-/
import CoSimFoundations.Reaction

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- The diagonal `0/1` matrix of the states of the subsystem `s`. -/
def mask (s : κ) : Matrix (Fin n) (Fin n) ℝ := diagonal fun r => if S.sub r = s then 1 else 0

/-- The block `A_s` of a matrix `A`, padded with zeros: `mask_s A mask_s`. -/
def blk (s : κ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  S.mask s * A * S.mask s

/-- The diagonal matrix of the signs `ς_{s, sub r}` on the states of the other subsystems, and
`0` on the states of `s`. -/
def osgn (s : κ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun r => if S.sub r = s then 0 else S.sg s (S.sub r)

/-- On its own states the sign of a subsystem is `-1`: `osgn s = sgn s + mask s`. -/
theorem osgn_eq (s : κ) : S.osgn s = S.sgn s + S.mask s := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    by_cases h : S.sub p = s
    · simp [osgn, sgn, sg, mask, h]
    · simp [osgn, sgn, mask, h]
  · simp [osgn, sgn, mask, hpq]

/-- The entries of the padded block. -/
theorem blk_apply (s : κ) (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    S.blk s A p q =
      (if S.sub p = s then 1 else 0) * A p q * (if S.sub q = s then 1 else 0) := by
  simp [blk, mask, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- On the block `s`: `F - 1 - H A - ½H² A mask_s A = (F - e^{H A_s}) + (e^{H A_s} - 1 - H A_s -
½H² A_s²)`. -/
theorem local_block_eq (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) {s : κ} {p q : Fin n}
    (hp : S.sub p = s) (hq : S.sub q = s) :
    (S.F - 1 - H • A - (H ^ 2 / 2) • (A * S.mask s * A) : Matrix (Fin n) (Fin n) ℝ) p q =
      (S.F - NormedSpace.exp (H • S.blk s A) + (NormedSpace.exp (H • S.blk s A) -
        (1 + H • S.blk s A + (H ^ 2 / 2) • (S.blk s A * S.blk s A))) :
          Matrix (Fin n) (Fin n) ℝ) p q := by
  have hZ : S.blk s A p q = A p q := by
    rw [blk_apply, ite_eq_left hp, ite_eq_left hq, one_mul, mul_one]
  have e1 : (A * S.mask s * A) p q = ∑ r, A p r * (if S.sub r = s then 1 else 0) * A r q :=
    mul_diagonal_mul_apply A A _ p q
  have hZZ : (S.blk s A * S.blk s A) p q = (A * S.mask s * A) p q := by
    rw [e1, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [blk_apply, blk_apply, ite_eq_left hp, ite_eq_left hq]
    by_cases hr : S.sub r = s
    · rw [ite_eq_left hr]
      ring
    · rw [ite_eq_right hr]
      ring
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hZ, hZZ]
  ring

/-- The operator of `osgn s` multiplies the components by the signs. -/
theorem opE_osgn_apply (s : κ) (u : EuclideanSpace ℝ (Fin n)) (r : Fin n) :
    (opE (S.osgn s) u) r = (if S.sub r = s then 0 else S.sg s (S.sub r)) * u r :=
  opE_diagonal_apply _ u r

/-- The matrix element of `osgn s` is the sum over the states of the other subsystems, with the
signs: `⟪u, osgn_s w⟫ = Σ_{r ∉ s} ς_{s, sub r} u_r w_r`. -/
theorem inner_osgn (s : κ) (u w : EuclideanSpace ℝ (Fin n)) :
    ⟪u, opE (S.osgn s) w⟫ =
      ∑ r, (if S.sub r = s then 0 else S.sg s (S.sub r)) * u r * w r :=
  inner_opE_diagonal _ u w

omit [DecidableEq κ] in
/-- If `A_{sk} = -A_{ks}ᵀ` between different subsystems, then `⟪x, A w⟫ = -⟪A x, w⟫` for `x`
supported on a subsystem `s` and `w` vanishing on `s`. -/
theorem inner_opE_skew {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s : κ}
    {x w : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hw : ∀ r, S.sub r = s → w r = 0) : ⟪x, opE A w⟫ = -⟪opE A x, w⟫ := by
  rw [real_inner_comm w (opE A x), inner_opE_eq_sum, inner_opE_eq_sum, Finset.sum_comm,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : S.sub p = s
  · by_cases hq : S.sub q = s
    · rw [hw q hq]
      ring
    · have e : A q p = -A p q := hskew p q (by rw [hp]; exact fun e => hq e.symm)
      rw [e]
      ring
  · rw [hx p hp]
    ring

/-- With `A_{sk} = -A_{ks}ᵀ`: `⟪x, A osgn_s A y⟫ = -⟪A x, osgn_s (A y)⟫` for `x` supported on
`s`, that is `Σ_k ς_{sk} A_{sk} A_{ks} = -Σ_k ς_{sk} A_{ks}ᵀ A_{ks}`. -/
theorem inner_osgn_skew {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s : κ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (A * S.osgn s * A) y⟫ = -⟪opE A x, opE (S.osgn s) (opE A y)⟫ := by
  rw [opE_mul_apply, opE_mul_apply]
  exact S.inner_opE_skew hskew hx fun r hr => by
    rw [opE_osgn_apply, ite_eq_left hr, zero_mul]

variable {S}

/-- **The diagonal block** (Proposition 6.1, with its remainder). For a consistent scheme with
one held sample, in any order of execution, a subsystem `s` that is not its own partner and `x`,
`y` supported on `s`:
`|⟪x, (X - U) y⟫ - ⟪x, (F - e^{H A_s}) y⟫ - ½H² ⟪x, A osgn_s A y⟫|`
`≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖}) H³ ‖x‖ ‖y‖`, `C₃ = reactionC a b c ‖A‖ H`. In the paper's notation:
`Π_s (X - U) Π_sᵀ = F_s - e^{H A_s} + ½H² Σ_{k ≠ s} ς_{sk} A_{sk} A_{ks} + r_s`. -/
theorem Consistent.reaction_diag {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} (hnp : ¬ S.partner s s)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - NormedSpace.exp (H • S.blk s A)) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (A * S.osgn s * A) y⟫| ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖)) * H ^ 3 *
          (‖x‖ * ‖y‖) := by
  have h1 := h.reaction_block hnp hx hy
  have k := inner_opE_congr hx hy (fun p q hp hq => S.local_block_eq A H hp hq)
  have e1 := inner_opE_sub (S.F - 1 - H • A) ((H ^ 2 / 2) • (A * S.mask s * A)) x y
  have e2 := inner_opE_smul (H ^ 2 / 2) (A * S.mask s * A) x y
  have e3 := inner_opE_add (S.F - NormedSpace.exp (H • S.blk s A))
    (NormedSpace.exp (H • S.blk s A) -
      (1 + H • S.blk s A + (H ^ 2 / 2) • (S.blk s A * S.blk s A))) x y
  have e4 : A * S.osgn s * A = A * S.sgn s * A + A * S.mask s * A := by
    rw [S.osgn_eq, Matrix.mul_add, Matrix.add_mul]
  have e5 := inner_opE_add (A * S.sgn s * A) (A * S.mask s * A) x y
  have hW : |⟪x, opE (NormedSpace.exp (H • S.blk s A) -
      (1 + H • S.blk s A + (H ^ 2 / 2) • (S.blk s A * S.blk s A))) y⟫| ≤
      ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) * H ^ 3 * (‖x‖ * ‖y‖) :=
    (abs_inner_opE_le _ x y).trans (mul_le_mul_of_nonneg_right
      (norm_opE_exp_sub_quadratic_le (S.blk s A) h.hH) (by positivity))
  rw [e1, e2, e3] at k
  have e6 : ⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - NormedSpace.exp (H • S.blk s A)) y⟫ -
      H ^ 2 / 2 * ⟪x, opE (A * S.osgn s * A) y⟫ =
      (⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - 1 - H • A) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫) +
      ⟪x, opE (NormedSpace.exp (H • S.blk s A) -
        (1 + H • S.blk s A + (H ^ 2 / 2) • (S.blk s A * S.blk s A))) y⟫ := by
    rw [e4, e5]
    linear_combination k
  rw [e6]
  refine (abs_add_le _ _).trans ?_
  have e7 : (reactionC a b c ‖opE A‖ H +
      ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖)) * H ^ 3 * (‖x‖ * ‖y‖) =
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) +
      ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖) * H ^ 3 * (‖x‖ * ‖y‖) := by
    ring
  rw [e7]
  exact add_le_add h1 hW

/-- **The reaction, in the form of the paper** (Proposition 6.1, `eq:reaction`, with its
remainder). If moreover `A_{sk} = -A_{ks}ᵀ` between different subsystems, then for `x`, `y`
supported on `s`:
`|⟪x, (X - U) y⟫ - ⟪x, (F - e^{H A_s}) y⟫ + ½H² ⟪A x, osgn_s (A y)⟫|`
`≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖}) H³ ‖x‖ ‖y‖`, where
`⟪A x, osgn_s (A y)⟫ = Σ_{k ≠ s} ς_{sk} ⟪A_{ks} x, A_{ks} y⟫` (`inner_osgn`): the block is
`F_s - e^{H A_s} - ½H² Σ_k ς_{sk} A_{ks}ᵀ A_{ks} + r_s`. -/
theorem Consistent.reaction_diag_skew {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - NormedSpace.exp (H • S.blk s A)) y⟫ +
        H ^ 2 / 2 * ⟪opE A x, opE (S.osgn s) (opE A y)⟫| ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖)) * H ^ 3 *
          (‖x‖ * ‖y‖) := by
  have h1 := h.reaction_diag hnp hx hy
  rwa [S.inner_osgn_skew hskew hx y, mul_neg, sub_neg_eq_add] at h1

/-- **The reaction with partner weights only** (Proposition 6.1, last sentence): if the block
`s` of `F` is `e^{H A_s}`, then for `x`, `y` supported on `s`
`|⟪x, (X - U) y⟫ + ½H² Σ_k ς_{sk} ⟪A_{ks} x, A_{ks} y⟫| ≤ (C₃ + ‖A_s‖³/6 e^{H‖A_s‖}) H³ ‖x‖ ‖y‖`,
whatever the coefficients of the partner samples. -/
theorem Consistent.reaction_partner_weights {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s : κ} (hnp : ¬ S.partner s s)
    (hFs : ∀ p q, S.sub p = s → S.sub q = s → S.F p q = NormedSpace.exp (H • S.blk s A) p q)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ s → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ + H ^ 2 / 2 * ⟪opE A x, opE (S.osgn s) (opE A y)⟫| ≤
      (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blk s A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blk s A)‖)) * H ^ 3 *
          (‖x‖ * ‖y‖) := by
  have h1 := h.reaction_diag_skew hskew hnp hx hy
  have h0 : ⟪x, opE (S.F - NormedSpace.exp (H • S.blk s A)) y⟫ = 0 := by
    rw [inner_opE_sub, inner_opE_congr hx hy hFs, sub_self]
  rwa [h0, sub_zero] at h1

end HeldScheme

end CoSimFoundations
