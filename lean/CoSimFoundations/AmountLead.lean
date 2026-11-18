/-
The amount, for the modified system and with a remainder in the constants of consistency alone
(the paper, Section 6: Corollary "the amount", `cor:amount`, eq. `eq:amount`, with Theorem
"injection or damping", `thm:triple`; Section 3, Definition `def:props`).

**Paper.** `Δ = Ã - A` is the difference of a co-simulation with the modified system
`Ã = (1/H) Log X`, `Δ_R = -sym Δ` its numerical dissipation, `ν = tr Δ_R` the total numerical
damping and `ι = -λ_min (Δ_R)` the injection rate. For subsystems `i ≠ j` that are not partners
and unit vectors `e`, `d` in their state spaces, every consistent family of holds satisfies
  `ν + n ι ≥ (H/2) |Σ_k (ς_ik + ς_jk) eᵀ A_ik A_kj d| - O(H²)`            (`eq:amount`).
In a Jacobi scheme the right-hand side is `H |eᵀ [A²]_ij d| - O(H²)`; for scalar stores that
interact through a single store `k` with `ς_ik = ς_jk` it is `H |A_ik A_kj|`.

**What is formalised.** Setting of `DifferenceLeadHalfStep`: a scheme with one held sample `S`,
consistent with the monolithic step `U = exp (H • A)` with the constants `a`, `b`, `c`
(`S.Consistent A U H a b c`: `‖N‖ ≤ a H`, `‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²`), in the range
`0 < H`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, where `Ã = modifiedSystem H X = H⁻¹ • log X` exists;
power-conserving coupling (`hskew`: `A q p = -A p q` between different subsystems); subsystems
`i ≠ j` that are not partners in either direction; unit vectors `x` supported on `i` and `y`
supported on `j`; `Δ_R = numDissipation A (modifiedSystem H S.X)`. The number `ι` is any real with
`-ι ‖v‖² ≤ ⟪v, Δ_R v⟫` for all `v` (the least one is `-λ_min (Δ_R)`; this is `⟪v, Δ v⟫ ≤ ι ‖v‖²`,
`inner_numDissipation_self`), and `μ` any real with `⟪v, Δ_R v⟫ ≤ μ ‖v‖²` for all `v` (the least
one is `λ_max (Δ_R)`). No eigenvalue is used. The remainder is `K H²` with
  `K = amountC a b c ‖A‖`
    `= 2 (3/2 · c · max b (4/3 ‖A‖) + a² b + (c + a b + 2/3 ‖A‖²) (a + ‖A‖) + 2/9 ‖A‖³)`,
which depends on the constants of consistency and on `‖A‖` only: neither on the macro step nor on
`‖Δ‖` or `‖Ã‖` of the scheme.

* `Consistent.amount_block`: the entry that the scheme cannot avoid,
    `(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ 2 |⟪x, Δ_R y⟫|`,
  where `⟪x, A (ς_i + ς_j) A y⟫ = Σ_k (ς_ik + ς_jk) xᵀ A_ik A_kj y`. Proof:
  `Consistent.numDissipation_block` (eq. `eq:parts` for `Δ_R`, remainder
  `(diffLeadC b c ‖A‖ + forcedC a b c ‖A‖ H) H²`) and `e^{H‖A‖} ≤ e^{1/4} ≤ 4/3` in `forcedC`
  (`forcedC_le`).
* **Trace form** (`Consistent.amount_trace`, eq. `eq:amount` as printed):
    `(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ tr Δ_R + n ι`,
  and with `ν = numDamping A H X = tr Δ_R` (`Consistent.amount_numDamping`). Proof: `Δ_R` is
  symmetric (`isSymm_numDissipation`), `x` and `y` are orthonormal, and `thm:triple` in the form
  `2 |⟪x, Δ_R y⟫| ≤ tr Δ_R + n ι` (`two_mul_abs_inner_opE_le_trace_add`, from
  `abs_inner_add_inner_le_trace_sub`, both of `TripleLawGeneral`).
* **Spread form** (`Consistent.amount_spread`):
    `(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ μ + ι`
  (`two_mul_abs_inner_opE_le_spread`, from `abs_inner_add_inner_le_spread` of `SpreadLaw`). There
  is no factor `n`; with `μ = tr Δ_R + (n - 1) ι` it is the trace form.
* **Jacobi** (all subsystems at the same stage; `Consistent.amount_trace_jacobi`,
  `Consistent.amount_spread_jacobi`): the left-hand side is `H |⟪x, A² y⟫| - K H²`.
* **A single common partner that does not run between the two** (`i` and `j` are joined only
  through `k`, `A p r * A r q = 0` unless `r` is a state of `k`, and `ς_ik = ς_jk`;
  `Consistent.amount_trace_partner`, `Consistent.amount_spread_partner`): the left-hand side is
  `H |⟪x, A mask_k A y⟫| - K H²`, `⟪x, A mask_k A y⟫ = xᵀ A_ik A_kj y`. For scalar stores
  (`Consistent.amount_trace_entry`): `H |A p r A r q| - K H² ≤ tr Δ_R + n ι`, the last statement
  of `cor:amount` with its remainder.
* **The two readings** of `thm:triple` for a co-simulation: a scheme that never injects (`ι ≤ 0`)
  has `tr Δ_R ≥ (H/2) |…| - K H²` and a largest dissipation rate `μ ≥ (H/2) |…| - K H²`
  (`Consistent.amount_damping_of_injection_nonpos`,
  `Consistent.amount_rate_of_injection_nonpos`); a scheme with `tr Δ_R ≤ 0` injects at a rate
  `ι ≥ ((H/2) |…| - K H²) / n` (`Consistent.amount_injection_of_damping_nonpos`).

**Differences from the paper.** The corollary is stated for one macro step in the range above with
an explicit remainder, in place of "a consistent family" and `O(H²)`. The power-conserving
coupling, which the paper assumes throughout, is the hypothesis `hskew`. `ι` and `μ` are bounds of
the form of `Δ_R` and not its extreme eigenvalues. `Ã` is the logarithm series (see
`DifferenceLead` on the principal logarithm).
-/
import CoSimFoundations.DifferenceLeadHalfStep
import CoSimFoundations.SpreadLaw

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-! ### The numerical dissipation is symmetric; the spread form for the operator of a matrix -/

/-- **The numerical dissipation is symmetric:** `Δ_Rᵀ = Δ_R` for `Δ_R = -sym (Ã - A)`. -/
theorem isSymm_numDissipation (A At : Matrix (Fin n) (Fin n) ℝ) :
    (numDissipation A At).IsSymm := by
  unfold Matrix.IsSymm numDissipation
  rw [transpose_neg, transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- The form of the numerical dissipation is minus the form of the difference:
`⟪v, Δ_R v⟫ = -⟪v, Δ v⟫`. Hence `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫` says `⟪v, Δ v⟫ ≤ ι ‖v‖²`. -/
theorem inner_numDissipation_self (A At : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, opE (numDissipation A At) v⟫ = -⟪v, opE (At - A) v⟫ := by
  rw [inner_numDissipation]
  ring

/-- **The spread form for the operator of a symmetric matrix.** If `T` is symmetric and
`-ι ‖v‖² ≤ ⟪v, T v⟫ ≤ μ ‖v‖²` for all `v` (as `μ = λ_max (T)`, `ι = -λ_min (T)`), then for
orthonormal `e`, `f`: `2 |⟪e, T f⟫| ≤ μ + ι`. -/
theorem two_mul_abs_inner_opE_le_spread {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm)
    {μ ι : ℝ} (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE T v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE T v⟫ ≤ μ * ‖v‖ ^ 2)
    {e f : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    2 * |⟪e, opE T f⟫| ≤ μ + ι :=
  two_mul_abs_inner_le_spread _ (isSymmetric_opE hT) hlo hhi he hf hef

/-- A Euclidean space with a unit vector has a positive number of coordinates. -/
theorem natCast_pos_of_norm_eq_one {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    (0 : ℝ) < (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : x = 0 := PiLp.ext fun i => i.elim0
    rw [h0, norm_zero] at hx
    exact absurd hx zero_ne_one
  · exact_mod_cast hn

/-- **The constant of the amount:** `K = 2 (K₁ + K₂)` with `K₁ = diffLeadC b c α`
`= 3/2 · c · max b (4/3 α)` (the passage from the one-step error to the difference) and
`K₂ = a² b + (c + a b + 2/3 α²) (a + α) + 2/9 α³` (the forced block, `forcedC` with
`e^{Hα} ≤ 4/3`); `‖N‖ ≤ a H`, `‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²`, `α = ‖A‖`. -/
noncomputable def amountC (a b c α : ℝ) : ℝ :=
  2 * (diffLeadC b c α + (a ^ 2 * b + (c + a * b + 2 / 3 * α ^ 2) * (a + α) + 2 / 9 * α ^ 3))

namespace HeldScheme

/-- The constant of the forced block without the macro step: for `a ≥ 0`, `α ≥ 0` and
`H α ≤ 1/4`, `forcedC a b c α H ≤ a² b + (c + a b + 2/3 α²) (a + α) + 2/9 α³`
(`e^{Hα} ≤ e^{1/4} ≤ 4/3`). -/
theorem forcedC_le {a b c α H : ℝ} (ha : 0 ≤ a) (hα : 0 ≤ α) (hαH : H * α ≤ 1 / 4) :
    forcedC a b c α H ≤
      a ^ 2 * b + (c + a * b + 2 / 3 * α ^ 2) * (a + α) + 2 / 9 * α ^ 3 := by
  have he : Real.exp (H * α) ≤ 4 / 3 := (Real.exp_le_exp.2 hαH).trans exp_quarter_le
  have h1 := mul_nonneg (mul_nonneg (sq_nonneg α) (add_nonneg ha hα)) (sub_nonneg.2 he)
  have h2 := mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 he)
  rw [forcedC, forcedConst, couplingConst]
  nlinarith [h1, h2]

variable {κ : Type*}

/-! ### The leading term in the two special cases -/

/-- **The leading term in a Jacobi scheme.** If all subsystems run at the same stage, then
`|⟪x, A (ς_i + ς_j) A y⟫| = 2 |⟪x, A² y⟫|` (every sign is `-1`). -/
theorem abs_inner_sgn_add_jacobi (S : HeldScheme n κ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ k k' : κ, S.stage k = S.stage k') (i j : κ) (x y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| = 2 * |⟪x, opE (A * A) y⟫| := by
  rw [mul_sgn_add_mul_of_jacobi hJ, inner_opE_smul, abs_mul, abs_neg, abs_two]

/-- **The leading term through a single common partner that does not run between the two.** If
`i` and `j` are joined only through `k` (`A p r * A r q = 0` unless `r` is a state of `k`) and
`ς_ik = ς_jk`, then for `x` supported on `i` and `y` on `j`:
`|⟪x, A (ς_i + ς_j) A y⟫| = 2 |⟪x, A mask_k A y⟫|`, with `⟪x, A mask_k A y⟫ = xᵀ A_ik A_kj y`. -/
theorem abs_inner_sgn_add_partner [DecidableEq κ] (S : HeldScheme n κ)
    {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} (hs : S.sg i k = S.sg j k)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) :
    |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| = 2 * |⟪x, opE (A * S.mask k * A) y⟫| := by
  have e : ⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫ =
      ⟪x, opE ((2 * S.sg i k) • (A * S.mask k * A)) y⟫ := by
    refine inner_opE_congr hx hy fun p q hp hq => ?_
    rw [S.sgn_add_entry, Matrix.smul_apply, S.mul_mask_mul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : S.sub r = k
    · rw [ite_eq_left hr, hr]
      linear_combination -(A p r * A r q) * hs
    · rw [ite_eq_right hr]
      linear_combination (S.sg i (S.sub r) + S.sg j (S.sub r)) * hpq p q r hp hq hr
  rw [e, inner_opE_smul, abs_mul, abs_mul, abs_two, S.abs_sg i k, mul_one]

/-! ### The amount for the modified system -/

section Amount

variable {S : HeldScheme n κ} {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- **The entry of the numerical dissipation that a consistent scheme cannot avoid** (the paper,
eq. `eq:parts` for `Δ_R`, with a remainder in the constants of consistency alone). For a
consistent scheme with power-conserving coupling, `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, subsystems
`i ≠ j` that are not partners, unit vectors `x` supported on `i` and `y` on `j`, and
`Δ_R = numDissipation A (modifiedSystem H S.X)`:
`(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ 2 |⟪x, Δ_R y⟫|`, `K = amountC a b c ‖A‖`. -/
theorem Consistent.amount_block (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) :
    H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      2 * |⟪x, opE (numDissipation A (modifiedSystem H S.X)) y⟫| := by
  have h1 := h.numDissipation_block hskew hH hbH hAH hij hnp hnp' hx hy
  rw [hx1, hy1, mul_one, mul_one] at h1
  have ha0 : 0 ≤ a := (mul_nonneg_iff_of_pos_right hH).1 ((norm_nonneg _).trans h.ha)
  have h2 := mul_le_mul_of_nonneg_right
    (forcedC_le (b := b) (c := c) ha0 (norm_nonneg (opE A)) hAH) (sq_nonneg H)
  have h3 := abs_le.1 h1
  have h4 := le_abs_self ⟪x, opE (numDissipation A (modifiedSystem H S.X)) y⟫
  have h5 := neg_le_abs ⟪x, opE (numDissipation A (modifiedSystem H S.X)) y⟫
  rw [amountC]
  rcases abs_cases ⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫ with ⟨hL, _⟩ | ⟨hL, _⟩ <;>
    rw [hL] <;> linarith [h3.1, h3.2]

/-- **The amount, trace form** (the paper, Corollary `cor:amount`, eq. `eq:amount`, for the modified
system). For a consistent scheme with power-conserving coupling, `H > 0`, `b H ≤ 1/3`,
`H ‖A‖ ≤ 1/4`, subsystems `i ≠ j` that are not partners, unit vectors `x` supported on `i` and
`y` on `j`, `Δ_R = numDissipation A (modifiedSystem H S.X)` and a real `ι` with
`-ι ‖v‖² ≤ ⟪v, Δ_R v⟫` for all `v` (as the injection rate `ι = -λ_min (Δ_R)`):
`(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ tr Δ_R + n ι`, `K = amountC a b c ‖A‖`, where
`⟪x, A (ς_i + ς_j) A y⟫ = Σ_k (ς_ik + ς_jk) xᵀ A_ik A_kj y`. -/
theorem Consistent.amount_trace (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      Matrix.trace (numDissipation A (modifiedSystem H S.X)) + (n : ℝ) * ι :=
  (h.amount_block hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1).trans
    (two_mul_abs_inner_opE_le_trace_add (isSymm_numDissipation A _) hlo hx1 hy1
      (inner_eq_zero_of_support hij hx hy))

/-- **The amount with the total numerical damping** (the paper, eq. `eq:amount` as printed,
`ν + n ι ≥ …`). In the setting of `Consistent.amount_trace`, with `ν = numDamping A H S.X`
`= -tr Δ = tr Δ_R`: `(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ ν + n ι`. -/
theorem Consistent.amount_numDamping (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      numDamping A H S.X + (n : ℝ) * ι := by
  rw [numDamping_eq_trace_numDissipation]
  exact h.amount_trace hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo

/-- **The amount, spread form** (`cor:amount` with the spread `λ_max (Δ_R) - λ_min (Δ_R)` in
place of `ν + n ι`). In the setting of `Consistent.amount_trace`, if in addition
`⟪v, Δ_R v⟫ ≤ μ ‖v‖²` for all `v` (as the largest dissipation rate `μ = λ_max (Δ_R)`):
`(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ μ + ι`. There is no factor `n`. -/
theorem Consistent.amount_spread (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      μ + ι :=
  (h.amount_block hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1).trans
    (two_mul_abs_inner_opE_le_spread (isSymm_numDissipation A _) hlo hhi hx1 hy1
      (inner_eq_zero_of_support hij hx hy))

/-! ### The two special cases of the paper -/

/-- **The amount in a Jacobi scheme, trace form** (the paper, `cor:amount`, second statement). If
all subsystems run at the same stage, then in the setting of `Consistent.amount_trace`:
`H |⟪x, A² y⟫| - K H² ≤ tr Δ_R + n ι`, with `⟪x, A² y⟫ = xᵀ [A²]_ij y`. -/
theorem Consistent.amount_trace_jacobi (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hJ : ∀ k k' : κ, S.stage k = S.stage k') (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H * |⟪x, opE (A * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      Matrix.trace (numDissipation A (modifiedSystem H S.X)) + (n : ℝ) * ι := by
  have h1 := h.amount_trace hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo
  rw [S.abs_inner_sgn_add_jacobi A hJ] at h1
  linarith

/-- **The amount in a Jacobi scheme, spread form.** If all subsystems run at the same stage, then
in the setting of `Consistent.amount_spread`: `H |⟪x, A² y⟫| - K H² ≤ μ + ι`. -/
theorem Consistent.amount_spread_jacobi (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hJ : ∀ k k' : κ, S.stage k = S.stage k') (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H * |⟪x, opE (A * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤ μ + ι := by
  have h1 := h.amount_spread hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo hhi
  rw [S.abs_inner_sgn_add_jacobi A hJ] at h1
  linarith

/-- **The amount through a single common partner that does not run between the two, trace form**
(the paper, `cor:amount`, last statement, for blocks). In the setting of `Consistent.amount_trace`,
if `i` and `j` are joined only through `k` (`A p r * A r q = 0` unless `r` is a state of `k`) and
`ς_ik = ς_jk` (`k` runs before both or before neither):
`H |⟪x, A mask_k A y⟫| - K H² ≤ tr Δ_R + n ι`, with `⟪x, A mask_k A y⟫ = xᵀ A_ik A_kj y`. -/
theorem Consistent.amount_trace_partner [DecidableEq κ] (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j k : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) (hs : S.sg i k = S.sg j k)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H * |⟪x, opE (A * S.mask k * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      Matrix.trace (numDissipation A (modifiedSystem H S.X)) + (n : ℝ) * ι := by
  have h1 := h.amount_trace hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo
  rw [S.abs_inner_sgn_add_partner hs hpq hx hy] at h1
  linarith

/-- **The amount through a single common partner that does not run between the two, spread
form.** In the setting of `Consistent.amount_spread`, if `i` and `j` are joined only through `k`
and `ς_ik = ς_jk`: `H |⟪x, A mask_k A y⟫| - K H² ≤ μ + ι`. -/
theorem Consistent.amount_spread_partner [DecidableEq κ] (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j k : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) (hs : S.sg i k = S.sg j k)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H * |⟪x, opE (A * S.mask k * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤ μ + ι := by
  have h1 := h.amount_spread hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo hhi
  rw [S.abs_inner_sgn_add_partner hs hpq hx hy] at h1
  linarith

/-- **The amount for scalar stores that interact through a single store** (the paper, `cor:amount`,
last statement, with its remainder). For a consistent scheme with power-conserving coupling,
`H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, states `p`, `q` of different subsystems that are not
partners and are joined only through the state `r` (`A p r' * A r' q = 0` for `r' ≠ r`), whose
subsystem runs before both or before neither (`ς` equal), and `ι` with `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫`:
`H |A p r · A r q| - K H² ≤ tr Δ_R + n ι`: the macro step times the product of the two coupling
rates. -/
theorem Consistent.amount_trace_entry (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {p q r : Fin n} (hne : S.sub p ≠ S.sub q)
    (hnp : ¬ S.partner (S.sub p) (S.sub q)) (hnp' : ¬ S.partner (S.sub q) (S.sub p))
    (honly : ∀ r', r' ≠ r → A p r' * A r' q = 0)
    (hs : S.sg (S.sub p) (S.sub r) = S.sg (S.sub q) (S.sub r)) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H * |A p r * A r q| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      Matrix.trace (numDissipation A (modifiedSystem H S.X)) + (n : ℝ) * ι := by
  have h1 := h.amount_trace hskew hH hbH hAH hne hnp hnp' (S.unitE_support p)
    (S.unitE_support q) (norm_unitE p) (norm_unitE q) hlo
  have hσ : |S.sg (S.sub p) (S.sub r)| = 1 := by
    unfold sg
    by_cases hlt : S.stage (S.sub r) < S.stage (S.sub p)
    · rw [ite_eq_left hlt, abs_one]
    · rw [ite_eq_right hlt, abs_neg, abs_one]
  have e : (S.sg (S.sub p) (S.sub r) + S.sg (S.sub p) (S.sub r)) * A p r * A r q =
      2 * S.sg (S.sub p) (S.sub r) * (A p r * A r q) := by ring
  rw [inner_unitE_opE, S.sgn_add_entry,
    Finset.sum_eq_single r (fun r' _ hr => by rw [mul_assoc, honly r' hr, mul_zero])
      (fun hk => absurd (Finset.mem_univ r) hk), ← hs, e, abs_mul, abs_mul, abs_two, hσ,
    mul_one] at h1
  linarith

/-! ### The two readings: never injecting costs damping, adding no damping costs injection -/

/-- **A scheme that never injects is damped** (the paper, the first reading of `eq:amount`). In the
setting of `Consistent.amount_trace`, if `ι ≤ 0` (the form of `Δ_R` is nonnegative):
`(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ tr Δ_R = ν`. -/
theorem Consistent.amount_damping_of_injection_nonpos (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) (hι : ι ≤ 0) :
    H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤
      Matrix.trace (numDissipation A (modifiedSystem H S.X)) := by
  have h1 := h.amount_trace hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo
  have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (neg_nonneg.2 hι)
  linarith

/-- **A scheme that never injects has a largest dissipation rate of first order.** In the setting
of `Consistent.amount_spread`, if `ι ≤ 0`: `(H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H² ≤ μ`. -/
theorem Consistent.amount_rate_of_injection_nonpos (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫ ≤ μ * ‖v‖ ^ 2) (hι : ι ≤ 0) :
    H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 ≤ μ := by
  have h1 := h.amount_spread hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo hhi
  linarith

/-- **A scheme that adds no damping injects** (the paper, the second reading of `eq:amount`). In the
setting of `Consistent.amount_trace`, if `tr Δ_R ≤ 0` (`ν ≤ 0`):
`((H/2) |⟪x, A (ς_i + ς_j) A y⟫| - K H²) / n ≤ ι`. -/
theorem Consistent.amount_injection_of_damping_nonpos (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫)
    (hν : Matrix.trace (numDissipation A (modifiedSystem H S.X)) ≤ 0) :
    (H / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2) /
      (n : ℝ) ≤ ι := by
  have h1 := h.amount_trace hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1 hlo
  rw [div_le_iff₀ (natCast_pos_of_norm_eq_one hx1)]
  linarith

end Amount

end HeldScheme

end CoSimFoundations
