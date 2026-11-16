/-
The reaction: the block of `X - U` between subsystems that are not partners, the diagonal block
included, with an explicit remainder (the paper, Proposition 6.1 `prop:reaction`; the paper
states it "+ O(H³)").

Setting of `ForcedBlock`: a `HeldScheme` (`X = F + M + N * X`, states grouped by `sub`),
`U = exp (H • A)`, spectral norms `‖opE ·‖`. `early s` is the `0/1` mask of the states whose
subsystem runs before `s`, `ς_s = sgn s = 2 early s - 1` (`-1` on `s` itself).

1. **A row of the scheme, exactly** (`row_expand`). If `M + N = H A + E` between different
   subsystems (`coupling_eq`: true with `E = X - 1 - H A - N (X - 1)`), then for all states `p`,
   `q`, with `s = sub p`,
     `X p q = F p q + M p q + N p q + H² (A early_s A) p q + H (E early_s A) p q`
              `+ (N (X - 1 - H A)) p q`.
   Proof: `X = F + M + N X`, `N X = N + H N A + N (X - 1 - H A)`, and the row `p` of `N` is
   `early_s` times the row of `H A + E` (a new sample is used exactly for the partners that run
   before `s`). No hypothesis on `p`, `q`: this is wider than `ForcedBlock.entry_expand`, which
   needs `sub p ≠ sub q` and uses `F p q = 0`, `(N F) p q = 0`.

2. **The rows of `X - U`** (`row_identity`, `reaction_row`). Subtracting
   `U = 1 + H A + ½H² A² + R`: for `x` supported on a subsystem `s` and every vector `y`,
     `|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A) y⟫ - ⟪x, (M + N) y⟫ - ½H² ⟪x, A ς_s A y⟫|`
         `≤ C₃ H³ ‖x‖ ‖y‖`,
     `C₃ = d ‖A‖ + a (c + ‖A‖²/2 · e^{H‖A‖}) + ‖A‖³/6 · e^{H‖A‖}`
   for `‖N‖ ≤ a H`, `‖X - U‖ ≤ c H²`, `‖E‖ ≤ d H²`; for a `Consistent` scheme
   `d = c + a b + ‖A‖²/2 · e^{H‖A‖}` (`reactionC`).

3. **Blocks of non-partners, `s = t` allowed** (`Consistent.reaction_block`). If `s` and `t` are
   not partners, `M + N` has no block `(s, t)`, so for `x` on `s` and `y` on `t`
     `|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A) y⟫ - ½H² ⟪x, A ς_s A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`.
   For `s ≠ t` the term with `F` vanishes and this is `forced_block` with the constant `C₃`
   (`Consistent.forced_block'`). `forced_block` itself is false for `s = t`.

4. **The diagonal block** (`Consistent.reaction_diag`, `reaction_diag_skew`,
   `reaction_partner_weights`). `blk s A` is the block `A_s` of `A`, padded with zeros, so that
   the block `s` of `exp (H • blk s A)` is `e^{H A_s}`; `osgn s = ς_s + mask_s` carries the signs
   `ς_{sk}` of the other subsystems and `0` on `s`. For `x`, `y` supported on `s`, `s` not a
   partner of itself:
     `|⟪x, (X - U) y⟫ - ⟪x, (F - e^{H A_s}) y⟫ - ½H² ⟪x, A osgn_s A y⟫|`
         `≤ (C₃ + ‖A_s‖³/6 · e^{H‖A_s‖}) H³ ‖x‖ ‖y‖`,
   that is `Π_s (X - U) Π_sᵀ = F_s - e^{H A_s} + ½H² Σ_{k ≠ s} ς_{sk} A_{sk} A_{ks} + r_s`. With
   `A_{sk} = -A_{ks}ᵀ` (`hskew`) the last term is `-½H² Σ_k ς_{sk} ⟪A_{ks} x, A_{ks} y⟫`, the
   form printed in the paper, and with `F_s = e^{H A_s}` (partner weights only) the term with `F`
   is absent.
-/
import CoSimFoundations.ForcedParts

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

variable {n : ℕ}

/-- The matrix element of a scalar multiple of a matrix. -/
theorem inner_opE_smul (c : ℝ) (T : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (c • T) y⟫ = c * ⟪x, opE T y⟫ := by
  rw [inner_opE_eq_sum, inner_opE_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- A matrix element with the first vector supported on a subsystem depends only on the rows of
the matrix that belong to the subsystem. -/
theorem inner_opE_congr_row {κ : Type*} {sub : Fin n → κ} {s : κ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, sub p ≠ s → x p = 0)
    (y : EuclideanSpace ℝ (Fin n)) {T T' : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ p q, sub p = s → T p q = T' p q) : ⟪x, opE T y⟫ = ⟪x, opE T' y⟫ := by
  rw [inner_opE_eq_sum, inner_opE_eq_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hp : sub p = s
  · rw [h p q hp]
  · rw [hx p hp, zero_mul, zero_mul, zero_mul, zero_mul]

/-- A matrix element vanishes if the block of the matrix between the supports vanishes. -/
theorem inner_opE_eq_zero {κ : Type*} {sub : Fin n → κ} {s t : κ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, sub p ≠ s → x p = 0)
    (hy : ∀ q, sub q ≠ t → y q = 0) {T : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ p q, sub p = s → sub q = t → T p q = 0) : ⟪x, opE T y⟫ = 0 := by
  rw [inner_opE_eq_sum]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  by_cases hp : sub p = s
  · by_cases hq : sub q = t
    · rw [h p q hp hq, mul_zero, zero_mul]
    · rw [hy q hq, mul_zero]
  · rw [hx p hp, zero_mul, zero_mul]

/-- The component of the image of a vector under the operator of a matrix. -/
theorem opE_apply (T : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) (p : Fin n) :
    (opE T y) p = ∑ q, T p q * y q := by
  simp [opE, ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]

/-- The operator of a diagonal matrix multiplies the components. -/
theorem opE_diagonal_apply (v : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) (p : Fin n) :
    (opE (diagonal v) y) p = v p * y p := by
  rw [opE_apply, Finset.sum_eq_single p]
  · rw [diagonal_apply_eq]
  · intro q _ hq
    rw [diagonal_apply_ne _ hq.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- The inner product of Euclidean space as a sum. -/
theorem inner_eq_sum (u w : EuclideanSpace ℝ (Fin n)) : ⟪u, w⟫ = ∑ r, u r * w r := by
  simp [PiLp.inner_apply, mul_comm]

/-- The matrix element of a diagonal matrix. -/
theorem inner_opE_diagonal (v : Fin n → ℝ) (u w : EuclideanSpace ℝ (Fin n)) :
    ⟪u, opE (diagonal v) w⟫ = ∑ r, v r * u r * w r := by
  rw [inner_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [opE_diagonal_apply]
  ring

end OneStep

open OneStep

variable {n : ℕ}

namespace HeldScheme

variable {κ : Type*} (S : HeldScheme n κ)

/-- **A row of the scheme, exactly.** If `M + N = H A + E` between different subsystems, then for
all states `p`, `q`:
`X p q = F p q + M p q + N p q + H² (A early A) p q + H (E early A) p q + (N (X - 1 - H A)) p q`,
with the mask `early` of the subsystems that run before the subsystem of `p`. -/
theorem row_expand {A E : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hE : ∀ p q, S.sub p ≠ S.sub q → S.M p q + S.N p q = H * A p q + E p q) (p q : Fin n) :
    S.X p q = S.F p q + S.M p q + S.N p q + H ^ 2 * (A * S.early (S.sub p) * A) p q +
      H * (E * S.early (S.sub p) * A) p q + (S.N * (S.X - 1 - H • A)) p q := by
  have hrow : ∀ r, S.N p r =
      (if S.stage (S.sub r) < S.stage (S.sub p) then 1 else 0) * (H * A p r + E p r) := by
    intro r
    by_cases hr : S.stage (S.sub r) < S.stage (S.sub p)
    · have hpr : S.sub p ≠ S.sub r := fun h => by
        rw [h] at hr
        exact lt_irrefl _ hr
      have hM0 : S.M p r = 0 := S.hM p r (fun h => h.2 hr)
      simp only [hr, ↓reduceIte, one_mul]
      rw [← hE p r hpr, hM0, zero_add]
    · simp only [hr, ↓reduceIte, zero_mul]
      exact S.hN p r (fun h => hr h.2)
  have hNA : (S.N * A) p q =
      H * (A * S.early (S.sub p) * A) p q + (E * S.early (S.sub p) * A) p q := by
    rw [Matrix.mul_apply]
    simp only [early, mul_diagonal_mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hrow r]
    ring
  have hNX : S.N * S.X = S.N + H • (S.N * A) + S.N * (S.X - 1 - H • A) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    abel
  have h : S.X p q = S.F p q + S.M p q + (S.N * S.X) p q := by
    have h0 := congrFun (congrFun S.hX p) q
    rwa [Matrix.add_apply, Matrix.add_apply] at h0
  rw [h, hNX, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hNA]
  ring

/-- The remainder of a row of `X - U`:
`H E early_s A + N (X - 1 - H A) - (U - 1 - H A - ½H² A²)`. -/
noncomputable def rem (A E U : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) (s : κ) :
    Matrix (Fin n) (Fin n) ℝ :=
  H • (E * S.early s * A) + S.N * (S.X - 1 - H • A) - (U - (1 + H • A + (H ^ 2 / 2) • (A * A)))

/-- **The rows of `X - U`, exactly.** If `M + N = H A + E` between different subsystems, the rows
of a subsystem `s` obey
`X - U = (F - 1 - H A) + ½H² A ς_s A + (M + N) + rem`. -/
theorem row_identity {A E : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hE : ∀ p q, S.sub p ≠ S.sub q → S.M p q + S.N p q = H * A p q + E p q)
    (U : Matrix (Fin n) (Fin n) ℝ) {s : κ} {p : Fin n} (hp : S.sub p = s) (q : Fin n) :
    (S.X - U - (S.F - 1 - H • A) - (H ^ 2 / 2) • (A * S.sgn s * A) :
        Matrix (Fin n) (Fin n) ℝ) p q =
      (S.M + S.N + S.rem A E U H s) p q := by
  subst hp
  have hX := S.row_expand hE p q
  have hsg : (A * S.sgn (S.sub p) * A) p q =
      2 * (A * S.early (S.sub p) * A) p q - (A * A) p q := by
    rw [S.sgn_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [rem, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hX, hsg]
  ring

/-- The constant of the reaction: `d α + a (c + α²/2 · e^{Hα}) + α³/6 · e^{Hα}`, with
`‖N‖ ≤ a H`, `‖X - U‖ ≤ c H²`, `‖E‖ ≤ d H²`, `α = ‖A‖` (the report's `C₃`). -/
noncomputable def reactionConst (a c d α H : ℝ) : ℝ :=
  d * α + a * (c + α ^ 2 / 2 * Real.exp (H * α)) + α ^ 3 / 6 * Real.exp (H * α)

/-- The remainder of a row is of third order: `‖rem‖ ≤ C₃ H³`. -/
theorem norm_rem_le {A U E : Matrix (Fin n) (Fin n) ℝ} {H a c d : ℝ} (hH : 0 ≤ H)
    (hU : U = NormedSpace.exp (H • A)) (ha : ‖opE S.N‖ ≤ a * H)
    (hc : ‖opE (S.X - U)‖ ≤ c * H ^ 2) (hd : ‖opE E‖ ≤ d * H ^ 2) (s : κ) :
    ‖opE (S.rem A E U H s)‖ ≤ reactionConst a c d ‖opE A‖ H * H ^ 3 := by
  have haH : 0 ≤ a * H := le_trans (norm_nonneg _) ha
  have hdH : 0 ≤ d * H ^ 2 := le_trans (norm_nonneg _) hd
  have hR : ‖opE (U - (1 + H • A + (H ^ 2 / 2) • (A * A)))‖ ≤
      ‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖) * H ^ 3 := by
    rw [hU]
    exact norm_opE_exp_sub_quadratic_le A hH
  have h1 : ‖opE (H • (E * S.early s * A))‖ ≤ H * (d * H ^ 2 * 1 * ‖opE A‖) := by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg hH, opE_mul, opE_mul]
    refine mul_le_mul_of_nonneg_left ?_ hH
    refine (norm_mul_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul hd (S.norm_opE_early_le s) (norm_nonneg _) hdH
  have hXA : ‖opE (S.X - 1 - H • A)‖ ≤
      c * H ^ 2 + ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2 := by
    have e : S.X - 1 - H • A = (S.X - U) + (U - (1 + H • A)) := by abel
    have h2 : ‖opE (U - (1 + H • A))‖ ≤ ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2 := by
      rw [hU]
      exact norm_opE_exp_sub_linear_le A hH
    rw [e, opE_add]
    exact (norm_add_le _ _).trans (add_le_add hc h2)
  have h2 : ‖opE (S.N * (S.X - 1 - H • A))‖ ≤
      a * H * (c * H ^ 2 + ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2) := by
    rw [opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul ha hXA (norm_nonneg _) haH)
  have h4 : ‖opE (S.rem A E U H s)‖ ≤ ‖opE (H • (E * S.early s * A))‖ +
      ‖opE (S.N * (S.X - 1 - H • A))‖ + ‖opE (U - (1 + H • A + (H ^ 2 / 2) • (A * A)))‖ := by
    unfold rem
    rw [opE_sub, opE_add]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h5 : reactionConst a c d ‖opE A‖ H * H ^ 3 = H * (d * H ^ 2 * 1 * ‖opE A‖) +
      a * H * (c * H ^ 2 + ‖opE A‖ ^ 2 / 2 * Real.exp (H * ‖opE A‖) * H ^ 2) +
      ‖opE A‖ ^ 3 / 6 * Real.exp (H * ‖opE A‖) * H ^ 3 := by
    simp only [reactionConst]
    ring
  rw [h5]
  linarith

/-- **The rows of `X - U`, from the coupling coefficients.** `U = exp (H • A)`, `M + N = H A + E`
between different subsystems, `‖N‖ ≤ a H`, `‖X - U‖ ≤ c H²`, `‖E‖ ≤ d H²`. For `x` supported on a
subsystem `s` and every vector `y`:
`|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A) y⟫ - ⟪x, (M + N) y⟫ - ½H² ⟪x, A ς_s A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`,
`C₃ = d ‖A‖ + a (c + ‖A‖²/2 e^{H‖A‖}) + ‖A‖³/6 e^{H‖A‖}`. Nothing is assumed about partners. -/
theorem reaction_row_of_coupling {A U E : Matrix (Fin n) (Fin n) ℝ} {H a c d : ℝ} (hH : 0 ≤ H)
    (hU : U = NormedSpace.exp (H • A))
    (hE : ∀ p q, S.sub p ≠ S.sub q → S.M p q + S.N p q = H * A p q + E p q)
    (ha : ‖opE S.N‖ ≤ a * H) (hc : ‖opE (S.X - U)‖ ≤ c * H ^ 2) (hd : ‖opE E‖ ≤ d * H ^ 2)
    {s : κ} {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - 1 - H • A) y⟫ - ⟪x, opE (S.M + S.N) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫| ≤
      reactionConst a c d ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have key := inner_opE_congr_row hx y (fun p q hp => S.row_identity hE U hp q)
  have e1 := inner_opE_sub (S.X - U - (S.F - 1 - H • A)) ((H ^ 2 / 2) • (A * S.sgn s * A)) x y
  have e2 := inner_opE_sub (S.X - U) (S.F - 1 - H • A) x y
  have e3 := inner_opE_smul (H ^ 2 / 2) (A * S.sgn s * A) x y
  have e4 := inner_opE_add (S.M + S.N) (S.rem A E U H s) x y
  have e5 : ⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - 1 - H • A) y⟫ - ⟪x, opE (S.M + S.N) y⟫ -
      H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫ = ⟪x, opE (S.rem A E U H s) y⟫ := by
    rw [e1, e2, e3, e4] at key
    linarith
  rw [e5]
  exact (abs_inner_opE_le _ x y).trans
    (mul_le_mul_of_nonneg_right (S.norm_rem_le hH hU ha hc hd s) (by positivity))

/-- The coefficients of the samples have no block between subsystems that are not partners
(the two may coincide). -/
theorem inner_coupling_eq_zero {s t : κ} (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) : ⟪x, opE (S.M + S.N) y⟫ = 0 := by
  refine inner_opE_eq_zero hx hy fun p q hp hq => ?_
  have hnp' : ¬ S.partner (S.sub p) (S.sub q) := by rw [hp, hq]; exact hnp
  rw [Matrix.add_apply, S.hM p q (fun h => hnp' h.1), S.hN p q (fun h => hnp' h.1), add_zero]

/-- The constant of the reaction for a consistent scheme, in terms of `‖N‖ ≤ a H`,
`‖X - 1‖ ≤ b H`, `‖X - U‖ ≤ c H²` and `α = ‖A‖`:
`(c + a b + α²/2 · e^{Hα}) α + a (c + α²/2 · e^{Hα}) + α³/6 · e^{Hα}`. -/
noncomputable def reactionC (a b c α H : ℝ) : ℝ :=
  reactionConst a c (couplingConst a b c α H) α H

variable {S}

/-- **The rows of `X - U` for a consistent scheme.** For `x` supported on a subsystem `s` and
every vector `y`:
`|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A) y⟫ - ⟪x, (M + N) y⟫ - ½H² ⟪x, A ς_s A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`
with `C₃ = reactionC a b c ‖A‖ H`. -/
theorem Consistent.reaction_row {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - 1 - H • A) y⟫ - ⟪x, opE (S.M + S.N) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) :=
  S.reaction_row_of_coupling h.hH h.hU (fun _ _ hne => S.coupling_eq A H hne) h.ha h.hc
    h.norm_coupling_le hx y

/-- **Blocks of non-partners, the diagonal block included** (Proposition 6.1 with its remainder;
the report's `eq:reactionbound`). For a consistent scheme with one held sample, in any order of
execution, `x` supported on a subsystem `s` and `y` on a subsystem `t` that is not a partner of
`s`, where `s = t` is allowed:
`|⟪x, (X - U) y⟫ - ⟪x, (F - 1 - H A) y⟫ - ½H² ⟪x, A ς_s A y⟫| ≤ C₃ H³ ‖x‖ ‖y‖`,
`C₃ = (c + a b + ‖A‖²/2 e^{H‖A‖}) ‖A‖ + a (c + ‖A‖²/2 e^{H‖A‖}) + ‖A‖³/6 e^{H‖A‖}`. -/
theorem Consistent.reaction_block {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - ⟪x, opE (S.F - 1 - H • A) y⟫ -
        H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := h.reaction_row hx y
  rwa [S.inner_coupling_eq_zero hnp hx hy, sub_zero] at h1

/-- **The forced block with the constant of the reaction** (the case `s ≠ t` of
`reaction_block`: `F`, `1` and `A` have no block between different subsystems that are not
partners). This is `Consistent.forced_block` with `reactionC` in place of `forcedC`. -/
theorem Consistent.forced_block' {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) (hnp : ¬ S.partner s t)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ - H ^ 2 / 2 * ⟪x, opE (A * S.sgn s * A) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := h.reaction_block hnp hx hy
  have h0 : ⟪x, opE (S.F - 1 - H • A) y⟫ = 0 := by
    refine inner_opE_eq_zero hx hy fun p q hp hq => ?_
    have hne : S.sub p ≠ S.sub q := by rw [hp, hq]; exact hst
    have hnp' : ¬ S.partner (S.sub p) (S.sub q) := by rw [hp, hq]; exact hnp
    have hpq : p ≠ q := fun e => hne (e ▸ rfl)
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, S.hF p q hne,
      Matrix.one_apply_ne hpq, h.hA p q hne hnp', smul_zero, sub_zero, sub_zero]
  rwa [h0, sub_zero] at h1

end HeldScheme

end CoSimFoundations
