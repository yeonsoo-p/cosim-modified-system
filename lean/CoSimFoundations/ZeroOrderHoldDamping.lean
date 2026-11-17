/-
The total numerical damping as a sum over links, and the staggered readout, for the zero-order
hold without a hypothesis of consistency (the paper, Proposition `prop:lent` (ii) with eq.
`eq:negdamping`; the paragraph on the bipartite coupling graph with eq. `eq:staggered`).

`ZeroOrderHold` proves that the zero-order hold `S.zoh A hA H` is consistent, with the constants
`a = 3σα`, `b = 8α`, `c = 3 (1 + 6σ) α²` (`α = ‖A‖`, `σ = √(card κ)`, `κ` the type of the
subsystems) for `0 ≤ H`, `H α ≤ 1/4`, `σ H α ≤ 1/6`. Here `n` is the number of states,
`K = diffLeadC b c α`, `C₃ = reactionC a b c α H`, `α₀ = ‖A₀‖`, spectral norms `‖opE ·‖`.

1. **The total numerical damping as a sum over links** (eq. `eq:negdamping`). For a consistent
   scheme with exact local maps `F = e^{H A₀}` (partner weights only), no subsystem its own
   partner, and a lossless coupling (`hskew`), for `H > 0`, `b H ≤ 1/3`, `H α ≤ 1/4`
   (`Consistent.abs_numDamping_add_links_le`):
     `|ν + (H/2) Σ_p Σ_q (A_par p q)²| ≤ n (K + C₃ + α₀³/6 · e^{H α₀}) H²`,
   `A_par` the coupling between different subsystems at the same stage; the double sum counts
   each link twice, so this is `ν = -H Σ_{links within a stage} ‖A_ik‖_F² + O(H²)`. It is
   `Consistent.abs_numDamping_partner_weights_le` with `tr (A_ς A) = Σ_p Σ_q (A_par p q)²`
   (`trace_signedCoupling_mul`). Corollaries: different subsystems never share a stage,
   `|ν| ≤ …` (`Consistent.abs_numDamping_le_of_stage_ne`); all stages equal, the sum runs over all
   links, `Σ_p Σ_q (A_c p q)²` (`Consistent.abs_numDamping_add_links_le_of_stage_eq`); links with
   a kind `ε` and no `hskew` (`Consistent.abs_numDamping_add_kind_le`, from
   `trace_signedCoupling_mul_kind`).
   For the zero-order hold (`abs_numDamping_zoh_add_links_le`,
   `abs_numDamping_zoh_add_links_le_of_stage_eq`), for `0 < H`, `H α ≤ 1/24`, `σ H α ≤ 1/6`: the
   same with the bound `n (41 + 269σ + 54σ²) α³ H²` (`zohDampK`).

2. **Exactly zero in a sequential order** (`det_X_eq_det_F`, `numDamping_eq_zero_of_sequential`,
   `numDamping_zoh_eq_zero_of_sequential`). If different subsystems never share a stage and no
   subsystem is its own partner, `1 - N` is unipotent (`det_one_sub_N`) and `F + M` is block
   triangular for the stages with the diagonal blocks of `F`, so `det X = det F` for every scheme
   with one held sample and every coupling. With `F = e^{H A₀}`, `H ≠ 0` and `‖X - 1‖ < 1` (the
   modified system `Ã = H⁻¹ log X` exists): `e^{H tr Ã} = det X = det F = e^{H tr A}`
   (`det_exp`), so `ν = -tr (Ã - A) = 0`. Neither `hskew` nor consistency is needed.

3. **Staggered readout for the scheme** (`zoh_staggered_conj`, `zoh_staggered_conj_pow`,
   `norm_zoh_staggered_pow_sub_le`, `norm_zoh_staggered_pow_sub_le'`). On a bipartite stage
   pattern (`hbip`: of two partners exactly one runs at stage `0`), with `P = firstMask`,
   `A_a = P A`, `A_b = (1 - P) A` and `W = e^{(H/2) A_a}`, from `zoh_X_staggered`
   (`X = e^{H A_b} e^{H A_a}`) and `Staggered`:
     `W X W⁻¹ = e^{(H/2) A_a} e^{H A_b} e^{(H/2) A_a}`,  `W X^k W⁻¹ = (…)^k`,
   and for `H ≥ 0`, `k H ≤ T`, `μ = ‖A_a‖ + ‖A_b‖ ≤ 2α`:
     `‖W X^k W⁻¹ - (e^{HA})^k‖ ≤ μ³/3 · T e^{μ T} · H² ≤ 8/3 · α³ T e^{2 α T} · H²`.
   No range of `H` is needed here (the consistency of the hold is not used).
-/
import CoSimFoundations.ZeroOrderHold
import CoSimFoundations.Staggered

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

namespace HeldScheme

section General

variable {κ : Type*} (S : HeldScheme n κ)

/-- **In a sequential order the determinant of the one-step map is that of the local maps**
(the paper, Proposition `prop:lent` (ii): "in a sequential scheme `det X = ∏ det F_i` for every
hold"). If different subsystems never share a stage and no subsystem is its own partner, then
`det X = det F`: `det (1 - N) = 1`, and `F + M` is block triangular for the stages with the
diagonal blocks of `F`. -/
theorem det_X_eq_det_F (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hstage : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) ≠ S.stage (S.sub q)) :
    S.X.det = S.F.det := by
  have hsub : ∀ i j, S.stage (S.sub i) = S.stage (S.sub j) → S.sub i = S.sub j := fun i j h => by
    by_contra hne
    exact hstage i j hne h
  have hM0 : ∀ i j, S.stage (S.sub i) = S.stage (S.sub j) → S.M i j = 0 := fun i j h =>
    S.hM i j fun h' => hself i (by
      have h1 := h'.1
      rwa [← hsub i j h] at h1)
  have hT1 : (S.F + S.M).BlockTriangular fun p => S.stage (S.sub p) := by
    intro i j hij
    have hij' : S.stage (S.sub j) < S.stage (S.sub i) := hij
    have hne : S.sub i ≠ S.sub j := fun e => by
      rw [e] at hij'
      exact lt_irrefl _ hij'
    rw [Matrix.add_apply, S.hF i j hne, S.hM i j fun h' => h'.2 hij', add_zero]
  have hT2 : S.F.BlockTriangular fun p => S.stage (S.sub p) := by
    intro i j hij
    have hij' : S.stage (S.sub j) < S.stage (S.sub i) := hij
    exact S.hF i j fun e => by
      rw [e] at hij'
      exact lt_irrefl _ hij'
  have h1 : (S.F + S.M).det = S.F.det := by
    rw [hT1.det, hT2.det]
    refine Finset.prod_congr rfl fun a _ => ?_
    congr 1
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : S.stage (S.sub i) = a := hi
    have hj' : S.stage (S.sub j) = a := hj
    simp [toSquareBlock_def, hM0 i j (hi'.trans hj'.symm)]
  have h2 := congrArg Matrix.det S.one_sub_N_mul_X
  rw [Matrix.det_mul, S.det_one_sub_N, one_mul] at h2
  rw [h2, h1]

/-- The mask of the first class is a coordinate projection: its spectral norm is at most one. -/
theorem norm_opE_firstMask_le : ‖opE S.firstMask‖ ≤ 1 :=
  norm_opE_diagonal_le _ zero_le_one fun i => by
    by_cases h : S.stage (S.sub i) = 0 <;> simp [h]

/-- The mask of the later class is a coordinate projection: its spectral norm is at most one. -/
theorem norm_opE_one_sub_firstMask_le : ‖opE (1 - S.firstMask)‖ ≤ 1 := by
  rw [S.one_sub_firstMask]
  exact norm_opE_diagonal_le _ zero_le_one fun i => by
    by_cases h : S.stage (S.sub i) = 0 <;> simp [h]

end General

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- The trace of the block-diagonal part is the trace of the matrix. -/
theorem trace_blockDiag (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (S.blockDiag A) = Matrix.trace A := by
  rw [Matrix.trace, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, S.blockDiag_apply, ite_eq_left rfl]

/-! ### The total numerical damping as a sum over links -/

section Damping

variable {S} {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- **The total numerical damping as a sum over the links within a stage** (the paper, Proposition
`prop:lent` (ii), eq. `eq:negdamping`, "for every consistent family of holds with partner weights
only"). For a consistent scheme with exact local maps `F = e^{H A₀}`, no subsystem its own
partner, a lossless coupling, `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, in any order of execution:
`|ν + (H/2) Σ_p Σ_q (A_par p q)²| ≤ n (K + C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H²`, `A_par` the coupling
between different subsystems at the same stage. The double sum counts each link twice:
`ν = -H Σ_{links within a stage} ‖A_ik‖_F² + O(H²)`. -/
theorem Consistent.abs_numDamping_add_links_le (h : S.Consistent A U H a b c)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    |numDamping A H S.X + H / 2 * ∑ p, ∑ q, (S.parCoupling A p q) ^ 2| ≤
      (n : ℝ) * (diffLeadC b c ‖opE A‖ + reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 := by
  rw [← S.trace_signedCoupling_mul hskew]
  exact h.abs_numDamping_partner_weights_le hself hF hH hbH hAH

/-- **A sequential order loses no damping to first order:** under the hypotheses of
`Consistent.abs_numDamping_add_links_le`, if different subsystems never share a stage,
`|ν| ≤ n (K + C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H²`. (In fact `ν = 0`:
`numDamping_eq_zero_of_sequential`.) -/
theorem Consistent.abs_numDamping_le_of_stage_ne (h : S.Consistent A U H a b c)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hstage : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) ≠ S.stage (S.sub q))
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    |numDamping A H S.X| ≤
      (n : ℝ) * (diffLeadC b c ‖opE A‖ + reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 := by
  have h1 := h.abs_numDamping_add_links_le hself hskew hF hH hbH hAH
  rw [S.parCoupling_eq_zero hstage] at h1
  simpa using h1

/-- **A Jacobi order loses damping on every link:** under the hypotheses of
`Consistent.abs_numDamping_add_links_le`, if all stages are equal,
`|ν + (H/2) Σ_p Σ_q (A_c p q)²| ≤ n (K + C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H²`: the sum runs over all
links (each twice), `ν = -H Σ_{links} ‖A_ik‖_F² + O(H²)`. -/
theorem Consistent.abs_numDamping_add_links_le_of_stage_eq (h : S.Consistent A U H a b c)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hstage : ∀ p q, S.stage (S.sub p) = S.stage (S.sub q))
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    |numDamping A H S.X + H / 2 * ∑ p, ∑ q, (S.coupling A p q) ^ 2| ≤
      (n : ℝ) * (diffLeadC b c ‖opE A‖ + reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 := by
  have h1 := h.abs_numDamping_add_links_le hself hskew hF hH hbH hAH
  rwa [S.parCoupling_eq_coupling hstage] at h1

/-- **The total numerical damping for links with a kind.** For a consistent scheme with exact
local maps, no subsystem its own partner, `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, and links
`s`-`k` of the kinds `ε s k` (`-1` conservative, `+1` dissipative):
`|ν + (H/2) Σ_p Σ_{r ∉ sub p} ε ς (A p r)²| ≤ n (K + C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H²`. -/
theorem Consistent.abs_numDamping_add_kind_le (h : S.Consistent A U H a b c)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p)) (ε : κ → κ → ℝ)
    (hkind : ∀ s k, s ≠ k → S.LinkKind A s k (ε s k))
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) :
    |numDamping A H S.X + H / 2 * ∑ p, ∑ r, (if S.sub r = S.sub p then 0 else
        ε (S.sub p) (S.sub r) * S.sg (S.sub p) (S.sub r) * (A p r) ^ 2)| ≤
      (n : ℝ) * (diffLeadC b c ‖opE A‖ + reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 := by
  rw [← S.trace_signedCoupling_mul_kind ε hkind]
  exact h.abs_numDamping_partner_weights_le hself hF hH hbH hAH

end Damping

/-- **In a sequential order with partner weights only the total numerical damping is zero,
exactly** (the paper, Proposition `prop:lent` (ii): "`ν = 0` exactly with partner weights only").
For every scheme with one held sample, exact local maps `F = e^{H A₀}`, no subsystem its own
partner, different subsystems never at the same stage, `H ≠ 0` and `‖X - 1‖ < 1` (so that the
modified system exists), and every coupling: `ν = -tr Δ = 0`, because
`e^{H tr Ã} = det X = det F = e^{H tr A}`. -/
theorem numDamping_eq_zero_of_sequential {A : Matrix (Fin n) (Fin n) ℝ} {H : ℝ} (hH : H ≠ 0)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hstage : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) ≠ S.stage (S.sub q))
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hX : ‖opE (S.X - 1)‖ < 1) :
    numDamping A H S.X = 0 := by
  have h1 : S.X.det = Real.exp (H * A.trace) := by
    rw [S.det_X_eq_det_F hself hstage, hF, det_exp, Matrix.trace_smul, smul_eq_mul,
      S.trace_blockDiag]
  have h2 : S.X.det = Real.exp (H * (modifiedSystem H S.X).trace) := by
    have h := congrArg Matrix.det (CoSimFoundations.exp_smul_modifiedSystem hH hX)
    rw [det_exp, Matrix.trace_smul, smul_eq_mul] at h
    exact h.symm
  have h3 : H * (modifiedSystem H S.X).trace = H * A.trace :=
    Real.exp_injective (h2.symm.trans h1)
  have h4 : (modifiedSystem H S.X).trace = A.trace := mul_left_cancel₀ hH h3
  rw [numDamping, difference, Matrix.trace_sub, h4, sub_self, neg_zero]

/-- **The total numerical damping of the zero-order hold** (the paper, Proposition `prop:lent` (ii),
eq. `eq:negdamping`). For a lossless coupling, no subsystem its own partner, `0 < H`,
`H ‖A‖ ≤ 1/24` and `√(card κ) · H ‖A‖ ≤ 1/6`, in any order of execution:
`|ν + (H/2) Σ_p Σ_q (A_par p q)²| ≤ n (41 + 269σ + 54σ²) ‖A‖³ · H²`, `σ = √(card κ)`, that is
`ν = -H Σ_{links within a stage} ‖A_ik‖_F² + O(H²)`. -/
theorem abs_numDamping_zoh_add_links_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    |numDamping A H (S.zoh A hA H).X + H / 2 * ∑ p, ∑ q, (S.parCoupling A p q) ^ 2| ≤
      (n : ℝ) * zohDampK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 2 := by
  obtain ⟨hAH4, hbH⟩ := zohConsB_mul_le hAH
  have hc := S.zoh_consistent hA hH.le hAH4 hσ
  have h := hc.abs_numDamping_add_links_le hself hskew (S.zoh_F A hA H) hH hbH hAH4
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
    (by positivity))
  exact (S.zoh_constants_le A hH.le hAH4 (Real.sqrt_nonneg _)).2.2

/-- **The zero-order hold in a Jacobi order:** under the hypotheses of
`abs_numDamping_zoh_add_links_le`, if all stages are equal,
`|ν + (H/2) Σ_p Σ_q (A_c p q)²| ≤ n (41 + 269σ + 54σ²) ‖A‖³ · H²`: every link counts. -/
theorem abs_numDamping_zoh_add_links_le_of_stage_eq [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hstage : ∀ p q, S.stage (S.sub p) = S.stage (S.sub q)) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    |numDamping A H (S.zoh A hA H).X + H / 2 * ∑ p, ∑ q, (S.coupling A p q) ^ 2| ≤
      (n : ℝ) * zohDampK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 2 := by
  have h1 := S.abs_numDamping_zoh_add_links_le hA hself hskew hH hAH hσ
  rwa [S.parCoupling_eq_coupling hstage] at h1

/-- **The zero-order hold in a sequential order has no total numerical damping, exactly**
(the paper, Proposition `prop:lent` (ii)). If different subsystems never share a stage and no
subsystem is its own partner, then for `0 < H`, `H ‖A‖ ≤ 1/24`, `√(card κ) · H ‖A‖ ≤ 1/6` and
every coupling, `ν = 0`. -/
theorem numDamping_zoh_eq_zero_of_sequential [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hstage : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) ≠ S.stage (S.sub q)) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    numDamping A H (S.zoh A hA H).X = 0 := by
  have hc := S.zoh_consistent hA hH.le (hAH.trans (by norm_num)) hσ
  have hb := hc.hb
  have hX : ‖opE ((S.zoh A hA H).X - 1)‖ < 1 := by
    unfold zohConsB at hb
    linarith
  exact (S.zoh A hA H).numDamping_eq_zero_of_sequential hH.ne' hself hstage (S.zoh_F A hA H) hX

/-! ### Staggered readout for the zero-order hold -/

/-- **Staggered readout for the zero-order hold** (the paper, eq. `eq:staggered`). On a bipartite
stage pattern (of two partners exactly one runs at stage `0`), with `P = firstMask`, `A_a = P A`,
`A_b = (1 - P) A` and `W = e^{(H/2) A_a}`, the one-step map of the zero-order hold is conjugate
to the Strang splitting: `W X W⁻¹ = e^{(H/2) A_a} e^{H A_b} e^{(H/2) A_a}`. -/
theorem zoh_staggered_conj {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) :
    NormedSpace.exp ((H / 2) • (S.firstMask * A)) * (S.zoh A hA H).X *
        (NormedSpace.exp ((H / 2) • (S.firstMask * A)))⁻¹ =
      NormedSpace.exp ((H / 2) • (S.firstMask * A)) *
        NormedSpace.exp (H • ((1 - S.firstMask) * A)) *
        NormedSpace.exp ((H / 2) • (S.firstMask * A)) := by
  rw [S.zoh_X_staggered hA H hbip]
  exact staggered_conj_matrix _ _ H

open scoped Matrix.Norms.Operator in
/-- **Staggered readout for the zero-order hold, over a run:** under the hypotheses of
`zoh_staggered_conj`, `W X^k W⁻¹ = (e^{(H/2) A_a} e^{H A_b} e^{(H/2) A_a})^k`. -/
theorem zoh_staggered_conj_pow {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) (k : ℕ) :
    NormedSpace.exp ((H / 2) • (S.firstMask * A)) * (S.zoh A hA H).X ^ k *
        (NormedSpace.exp ((H / 2) • (S.firstMask * A)))⁻¹ =
      (NormedSpace.exp ((H / 2) • (S.firstMask * A)) *
        NormedSpace.exp (H • ((1 - S.firstMask) * A)) *
        NormedSpace.exp ((H / 2) • (S.firstMask * A))) ^ k := by
  rw [S.zoh_X_staggered hA H hbip, ← Matrix.exp_neg]
  exact staggered_conj_pow _ _ H k

open scoped Matrix.Norms.Operator in
/-- **Staggered readout for the zero-order hold, second order over a run** (the paper, the paragraph
after eq. `eq:staggered`: "a sequential zero-order hold on a bipartite graph is of second order
if the states of class `a` are read as values at `t_k - H/2`"). Under the hypotheses of
`zoh_staggered_conj`, for `H ≥ 0` and `k H ≤ T`, with `μ = ‖A_a‖ + ‖A_b‖`:
`‖W X^k W⁻¹ - e^{HA k}‖ ≤ μ³/3 · T · e^{μ T} · H²`. -/
theorem norm_zoh_staggered_pow_sub_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) {H T : ℝ} (hH : 0 ≤ H)
    (k : ℕ) (hk : (k : ℝ) * H ≤ T) :
    ‖opE (NormedSpace.exp ((H / 2) • (S.firstMask * A)) * (S.zoh A hA H).X ^ k *
        (NormedSpace.exp ((H / 2) • (S.firstMask * A)))⁻¹ - NormedSpace.exp (H • A) ^ k)‖ ≤
      (‖opE (S.firstMask * A)‖ + ‖opE ((1 - S.firstMask) * A)‖) ^ 3 / 3 * T *
        Real.exp ((‖opE (S.firstMask * A)‖ + ‖opE ((1 - S.firstMask) * A)‖) * T) * H ^ 2 := by
  have hT : 0 ≤ T := le_trans (by positivity) hk
  rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin n)) with hs | hnt
  · have h0 : opE (NormedSpace.exp ((H / 2) • (S.firstMask * A)) * (S.zoh A hA H).X ^ k *
        (NormedSpace.exp ((H / 2) • (S.firstMask * A)))⁻¹ - NormedSpace.exp (H • A) ^ k) = 0 :=
      Subsingleton.elim _ _
    rw [h0, norm_zero]
    positivity
  · have h := norm_staggered_pow_sub_exp_pow_le (opE (S.firstMask * A))
      (opE ((1 - S.firstMask) * A)) hH k hk
    have eab : opE (S.firstMask * A) + opE ((1 - S.firstMask) * A) = opE A := by
      rw [← opE_add, sub_mul, one_mul, add_sub_cancel]
    rw [eab] at h
    refine le_of_eq_of_le (congrArg norm ?_) h
    rw [S.zoh_X_staggered hA H hbip, ← Matrix.exp_neg]
    simp only [opE_sub, opE_mul, map_pow, opE_exp, opE_smul, map_neg]

/-- **Staggered readout for the zero-order hold, second order over a run, in `‖A‖` alone:**
under the hypotheses of `zoh_staggered_conj`, for `H ≥ 0` and `k H ≤ T`,
`‖W X^k W⁻¹ - e^{HA k}‖ ≤ 8/3 · ‖A‖³ · T · e^{2‖A‖T} · H²`. -/
theorem norm_zoh_staggered_pow_sub_le' {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) {H T : ℝ} (hH : 0 ≤ H)
    (k : ℕ) (hk : (k : ℝ) * H ≤ T) :
    ‖opE (NormedSpace.exp ((H / 2) • (S.firstMask * A)) * (S.zoh A hA H).X ^ k *
        (NormedSpace.exp ((H / 2) • (S.firstMask * A)))⁻¹ - NormedSpace.exp (H • A) ^ k)‖ ≤
      8 / 3 * ‖opE A‖ ^ 3 * T * Real.exp (2 * ‖opE A‖ * T) * H ^ 2 := by
  have hT : 0 ≤ T := le_trans (by positivity) hk
  have hP : ‖opE (S.firstMask * A)‖ ≤ ‖opE A‖ := by
    rw [opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) S.norm_opE_firstMask_le)
  have hQ : ‖opE ((1 - S.firstMask) * A)‖ ≤ ‖opE A‖ := by
    rw [opE_mul]
    exact (norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) S.norm_opE_one_sub_firstMask_le)
  have hμ : ‖opE (S.firstMask * A)‖ + ‖opE ((1 - S.firstMask) * A)‖ ≤ 2 * ‖opE A‖ := by
    linarith
  refine (S.norm_zoh_staggered_pow_sub_le hA hbip hH k hk).trans ?_
  calc (‖opE (S.firstMask * A)‖ + ‖opE ((1 - S.firstMask) * A)‖) ^ 3 / 3 * T *
        Real.exp ((‖opE (S.firstMask * A)‖ + ‖opE ((1 - S.firstMask) * A)‖) * T) * H ^ 2
      ≤ (2 * ‖opE A‖) ^ 3 / 3 * T * Real.exp (2 * ‖opE A‖ * T) * H ^ 2 := by gcongr
    _ = 8 / 3 * ‖opE A‖ ^ 3 * T * Real.exp (2 * ‖opE A‖ * T) * H ^ 2 := by ring

end HeldScheme

end CoSimFoundations
