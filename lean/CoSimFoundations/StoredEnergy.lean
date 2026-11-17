/-
The half-step term `½H² A_ς A` for a lossless coupling, and an exact invariant of a sequential
order of lossless scalar stores.

Setting of `HalfStep`: a `HeldScheme` (`X = F + M + N * X`, states grouped by `sub`, stages
`stage`), the signed coupling `A_ς = signedCoupling A` (`ς_{sk} = S.sg s k`: `+1` if `k` runs at an
earlier stage than `s`, `-1` if not), and the leading term `½H² A_ς A` of `X - U`
(`Consistent.half_step`). Operators `opE ·` and spectral norms `‖opE ·‖` on Euclidean space.
"Lossless coupling" is the hypothesis
  `hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q`
(`A_{ki} = -A_{ik}ᵀ` between different subsystems; nothing is assumed inside a subsystem).

1. **The split of the signed coupling by the stages of the two ends**
   (`signedCoupling_eq`, `seqCoupling_transpose`, `parCoupling_transpose`).
   * `seqCoupling A = A_seq`: the entries `ς A p q` between subsystems at different stages;
   * `parCoupling A = A_par`: the entries `A p q` between different subsystems at the same stage.
   `A_ς = A_seq - A_par` for every `A` (at equal stages `ς = -1`). For a lossless coupling
   `A_seqᵀ = A_seq` (the sign and the entry both change sign) and `A_parᵀ = -A_par`.

2. **Traces** (`trace_seqCoupling_mul`, `trace_parCoupling_mul`, `trace_signedCoupling_mul`). For a
   lossless coupling
     `tr (A_seq A) = 0`,  `tr (A_par A) = -Σ_p Σ_q (A_par p q)²`,
     `tr (A_ς A) = Σ_p Σ_q (A_par p q)²`.
   The double sum counts each link twice: `tr (½H² A_ς A) = H² Σ ‖A_ik‖_F²` over the links whose
   two ends run in the same stage. If coupled subsystems never share a stage, `A_par = 0` and the
   trace vanishes (`parCoupling_eq_zero`, `trace_signedCoupling_mul_of_stage_ne`); if all stages
   are equal (Jacobi), `A_ς = -A_c` and the trace is `Σ_p Σ_q (A_c p q)²`
   (`signedCoupling_eq_neg_coupling`, `trace_signedCoupling_mul_of_stage_eq`).

3. **The quadratic form** (`inner_signedCoupling_mul`, `inner_signedCoupling_mul_self`). For a
   lossless coupling and all vectors `x`, `y`:
     `⟪x, A_ς A y⟫ = ⟪A_seq x, A y⟫ + ⟪A_par x, A y⟫`
   (`⟪x, A_seq B y⟫ = ⟪A_seq x, B y⟫`, `⟪x, A_par B y⟫ = -⟪A_par x, B y⟫` for every `B`).

4. **An exact invariant** (`stored_invariant`, `stored_invariant_pow`, `stored_norm_pow_le`,
   `HeldScheme.stored_invariant`, `HeldScheme.stored_norm_pow_le`). For a real square matrix `Λ`
   and a matrix `X` with `(1 - Λ) X = 1 - Λᵀ` (if `1 - Λ` is invertible: `X = (1 - Λ)⁻¹ (1 - Λᵀ)`),
   and `Q = 1 - ½ (Λ + Λᵀ)`:
     `Xᵀ Q X = Q`,  `(X^k)ᵀ Q X^k = Q` for all `k`,
   and if `‖Λ + Λᵀ‖ ≤ 2ρ`, then `(1 - ρ) ‖X^k x‖² ≤ (1 + ρ) ‖x‖²` for all `k` and `x`.
   Proof: with `P = 1 - Λ`, `P X = Pᵀ` gives `Xᵀ P X = Xᵀ Pᵀ = (P X)ᵀ = P` and
   `Xᵀ Pᵀ X = (P X)ᵀ X = P X = Pᵀ`, and `Q = ½ (P + Pᵀ)`; no inverse is needed. The bound follows
   from `(1 - ρ) ‖y‖² ≤ ⟪y, Q y⟫ ≤ (1 + ρ) ‖y‖²`.
   A `HeldScheme` with `F = 1` and `M = -Nᵀ` (lossless scalar stores in a sequential order: the
   coefficients of the old samples are minus the transpose of those of the new samples) has
   `(1 - N) X = 1 - Nᵀ`, so `Λ = N`. For every `HeldScheme`, `det (1 - N) = 1` (`det_one_sub_N`:
   the transpose of `1 - N` is block triangular for the stages, with identity diagonal blocks),
   hence `X = (1 - N)⁻¹ (F + M)` (`X_eq_inv_mul`).
-/
import CoSimFoundations.HalfStep
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

namespace HeldScheme

section Signs

variable {κ : Type*} (S : HeldScheme n κ)

/-- Between two subsystems at different stages the sign changes with the direction:
`ς_{ks} = -ς_{sk}`. -/
theorem sg_swap {s k : κ} (h : S.stage s ≠ S.stage k) : S.sg k s = -S.sg s k := by
  unfold sg
  rcases lt_or_gt_of_ne h with h1 | h1
  · rw [ite_eq_left h1, ite_eq_right (lt_asymm h1), neg_neg]
  · rw [ite_eq_right (lt_asymm h1), ite_eq_left h1]

end Signs

section Split

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The split of the signed coupling by the stages of the two ends -/

/-- The sequential part `A_seq` of the signed coupling: the entries `ς(sub p, sub q) A p q`
between different subsystems that run at different stages. -/
noncomputable def seqCoupling (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    if S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q) then
      S.sg (S.sub p) (S.sub q) * A p q
    else 0

/-- The parallel part `A_par` of the coupling: the entries `A p q` between different subsystems
that run at the same stage. -/
def parCoupling (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    if S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q) then A p q else 0

/-- The entries of the sequential part. -/
theorem seqCoupling_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    S.seqCoupling A p q =
      if S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q) then
        S.sg (S.sub p) (S.sub q) * A p q
      else 0 := rfl

/-- The entries of the parallel part. -/
theorem parCoupling_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    S.parCoupling A p q =
      if S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q) then A p q else 0 := rfl

/-- **The split of the signed coupling:** `A_ς = A_seq - A_par`, for every matrix `A` (between
subsystems at the same stage the sign is `-1`). -/
theorem signedCoupling_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    S.signedCoupling A = S.seqCoupling A - S.parCoupling A := by
  ext p q
  rw [Matrix.sub_apply, S.signedCoupling_apply, S.seqCoupling_apply, S.parCoupling_apply]
  by_cases hpq : S.sub p = S.sub q
  · have h1 : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q)) := fun h => h.1 hpq
    have h2 : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)) := fun h => h.1 hpq
    rw [ite_eq_left hpq, ite_eq_right h1, ite_eq_right h2, sub_zero]
  · by_cases hst : S.stage (S.sub p) = S.stage (S.sub q)
    · have h1 : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q)) :=
        fun h => h.2 hst
      have h2 : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q) := ⟨hpq, hst⟩
      rw [ite_eq_right hpq, ite_eq_right h1, ite_eq_left h2, S.sg_of_stage_eq hst]
      ring
    · have h1 : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q) := ⟨hpq, hst⟩
      have h2 : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)) :=
        fun h => hst h.2
      rw [ite_eq_right hpq, ite_eq_left h1, ite_eq_right h2, sub_zero]

/-- **For a lossless coupling the sequential part is symmetric:** `A_seqᵀ = A_seq` (the sign and
the entry both change sign with the direction of the link). -/
theorem seqCoupling_transpose {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    (S.seqCoupling A)ᵀ = S.seqCoupling A := by
  ext p q
  rw [Matrix.transpose_apply, S.seqCoupling_apply, S.seqCoupling_apply]
  by_cases h : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q)
  · have h' : S.sub q ≠ S.sub p ∧ S.stage (S.sub q) ≠ S.stage (S.sub p) :=
      ⟨h.1.symm, h.2.symm⟩
    rw [ite_eq_left h, ite_eq_left h', hskew p q h.1, S.sg_swap h.2]
    ring
  · have h' : ¬ (S.sub q ≠ S.sub p ∧ S.stage (S.sub q) ≠ S.stage (S.sub p)) :=
      fun e => h ⟨e.1.symm, e.2.symm⟩
    rw [ite_eq_right h, ite_eq_right h']

/-- **For a lossless coupling the parallel part is skew:** `A_parᵀ = -A_par`. -/
theorem parCoupling_transpose {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    (S.parCoupling A)ᵀ = -S.parCoupling A := by
  ext p q
  rw [Matrix.transpose_apply, Matrix.neg_apply, S.parCoupling_apply, S.parCoupling_apply]
  by_cases h : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)
  · have h' : S.sub q ≠ S.sub p ∧ S.stage (S.sub q) = S.stage (S.sub p) :=
      ⟨h.1.symm, h.2.symm⟩
    rw [ite_eq_left h, ite_eq_left h', hskew p q h.1]
  · have h' : ¬ (S.sub q ≠ S.sub p ∧ S.stage (S.sub q) = S.stage (S.sub p)) :=
      fun e => h ⟨e.1.symm, e.2.symm⟩
    rw [ite_eq_right h, ite_eq_right h', neg_zero]

/-! ### Traces -/

/-- **The sequential part does not contribute to the trace:** `tr (A_seq A) = 0` for a lossless
coupling (`A_seq` is symmetric, and `A` is skew where `A_seq` does not vanish). -/
theorem trace_seqCoupling_mul {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    Matrix.trace (S.seqCoupling A * A) = 0 := by
  have hterm : ∀ p q, S.seqCoupling A p q * A q p = -(S.seqCoupling A q p * A p q) := by
    intro p q
    have hsym : S.seqCoupling A q p = S.seqCoupling A p q := by
      have h := congrFun (congrFun (S.seqCoupling_transpose hskew) p) q
      rwa [Matrix.transpose_apply] at h
    by_cases hpq : S.sub p = S.sub q
    · have hn : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q)) :=
        fun h => h.1 hpq
      have h0 : S.seqCoupling A p q = 0 := by
        rw [S.seqCoupling_apply]
        exact ite_eq_right hn
      rw [hsym, h0, zero_mul, zero_mul, neg_zero]
    · rw [hsym, hskew p q hpq]
      ring
  have h1 : Matrix.trace (S.seqCoupling A * A) = ∑ p, ∑ q, S.seqCoupling A p q * A q p := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
  have h2 : ∑ p, ∑ q, S.seqCoupling A p q * A q p =
      -∑ p, ∑ q, S.seqCoupling A p q * A q p := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => hterm p q
  rw [h1]
  linarith

/-- **The trace of the parallel part:** `tr (A_par A) = -Σ_p Σ_q (A_par p q)²` for a lossless
coupling. -/
theorem trace_parCoupling_mul {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    Matrix.trace (S.parCoupling A * A) = -∑ p, ∑ q, (S.parCoupling A p q) ^ 2 := by
  rw [Matrix.trace, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [S.parCoupling_apply]
  by_cases h : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)
  · rw [ite_eq_left h, hskew p q h.1]
    ring
  · rw [ite_eq_right h]
    ring

/-- **The trace of the half-step term:** `tr (A_ς A) = Σ_p Σ_q (A_par p q)²` for a lossless
coupling. Only the links whose two ends run in the same stage count (each twice in the double
sum). -/
theorem trace_signedCoupling_mul {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    Matrix.trace (S.signedCoupling A * A) = ∑ p, ∑ q, (S.parCoupling A p q) ^ 2 := by
  rw [S.signedCoupling_eq, Matrix.sub_mul, Matrix.trace_sub, S.trace_seqCoupling_mul hskew,
    S.trace_parCoupling_mul hskew, zero_sub, neg_neg]

/-- The trace of the half-step term of a lossless coupling is not negative. -/
theorem trace_signedCoupling_mul_nonneg {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) :
    0 ≤ Matrix.trace (S.signedCoupling A * A) := by
  rw [S.trace_signedCoupling_mul hskew]
  exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg _

/-! ### Two extreme orders -/

/-- If different subsystems never share a stage, there is no parallel part. -/
theorem parCoupling_eq_zero
    (hstage : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) ≠ S.stage (S.sub q))
    (A : Matrix (Fin n) (Fin n) ℝ) : S.parCoupling A = 0 := by
  ext p q
  have hn : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)) :=
    fun h => hstage p q h.1 h.2
  rw [S.parCoupling_apply, Matrix.zero_apply]
  exact ite_eq_right hn

/-- If no two partners share a stage and `A` has no block between subsystems that are not
partners, the coupling within a stage vanishes: `A_par = 0`. -/
theorem parCoupling_eq_zero_of_partner {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t) : S.parCoupling A = 0 := by
  ext p q
  rw [S.parCoupling_apply, Matrix.zero_apply]
  by_cases h : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)
  · rw [ite_eq_left h]
    exact hA p q h.1 fun hp => hns _ _ h.1 hp h.2
  · rw [ite_eq_right h]

/-- If different subsystems never share a stage, the signed coupling is its sequential part. -/
theorem signedCoupling_eq_seqCoupling
    (hstage : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) ≠ S.stage (S.sub q))
    (A : Matrix (Fin n) (Fin n) ℝ) : S.signedCoupling A = S.seqCoupling A := by
  rw [S.signedCoupling_eq, S.parCoupling_eq_zero hstage, sub_zero]

/-- **A sequential order of a lossless coupling:** if different subsystems never share a stage,
`tr (A_ς A) = 0`. -/
theorem trace_signedCoupling_mul_of_stage_ne {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hstage : ∀ p q, S.sub p ≠ S.sub q → S.stage (S.sub p) ≠ S.stage (S.sub q)) :
    Matrix.trace (S.signedCoupling A * A) = 0 := by
  rw [S.signedCoupling_eq_seqCoupling hstage]
  exact S.trace_seqCoupling_mul hskew

/-- If all stages are equal, there is no sequential part. -/
theorem seqCoupling_eq_zero (hstage : ∀ p q, S.stage (S.sub p) = S.stage (S.sub q))
    (A : Matrix (Fin n) (Fin n) ℝ) : S.seqCoupling A = 0 := by
  ext p q
  have hn : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) ≠ S.stage (S.sub q)) :=
    fun h => h.2 (hstage p q)
  rw [S.seqCoupling_apply, Matrix.zero_apply]
  exact ite_eq_right hn

/-- If all stages are equal, the parallel part is the whole coupling. -/
theorem parCoupling_eq_coupling (hstage : ∀ p q, S.stage (S.sub p) = S.stage (S.sub q))
    (A : Matrix (Fin n) (Fin n) ℝ) : S.parCoupling A = S.coupling A := by
  ext p q
  rw [S.parCoupling_apply, S.coupling_apply]
  by_cases hpq : S.sub p = S.sub q
  · have hn : ¬ (S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q)) :=
      fun h => h.1 hpq
    rw [ite_eq_right hn, ite_eq_left hpq]
  · have h : S.sub p ≠ S.sub q ∧ S.stage (S.sub p) = S.stage (S.sub q) := ⟨hpq, hstage p q⟩
    rw [ite_eq_left h, ite_eq_right hpq]

/-- **Jacobi:** if all stages are equal, the signed coupling is minus the coupling,
`A_ς = -A_c`. -/
theorem signedCoupling_eq_neg_coupling (hstage : ∀ p q, S.stage (S.sub p) = S.stage (S.sub q))
    (A : Matrix (Fin n) (Fin n) ℝ) : S.signedCoupling A = -S.coupling A := by
  rw [S.signedCoupling_eq, S.seqCoupling_eq_zero hstage, S.parCoupling_eq_coupling hstage,
    zero_sub]

/-- **Jacobi with a lossless coupling:** if all stages are equal,
`tr (A_ς A) = Σ_p Σ_q (A_c p q)²`. -/
theorem trace_signedCoupling_mul_of_stage_eq {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    (hstage : ∀ p q, S.stage (S.sub p) = S.stage (S.sub q)) :
    Matrix.trace (S.signedCoupling A * A) = ∑ p, ∑ q, (S.coupling A p q) ^ 2 := by
  rw [S.trace_signedCoupling_mul hskew, S.parCoupling_eq_coupling hstage]

/-! ### The quadratic form -/

/-- The sequential part of a lossless coupling moves to the other side of the inner product:
`⟪x, A_seq B y⟫ = ⟪A_seq x, B y⟫`. -/
theorem inner_seqCoupling_mul {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (B : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.seqCoupling A * B) y⟫ = ⟪opE (S.seqCoupling A) x, opE B y⟫ := by
  rw [opE_mul_apply, OneStep.inner_opE_transpose (S.seqCoupling A) (opE B y) x,
    S.seqCoupling_transpose hskew]
  exact real_inner_comm _ _

/-- The parallel part of a lossless coupling moves to the other side of the inner product with
the opposite sign: `⟪x, A_par B y⟫ = -⟪A_par x, B y⟫`. -/
theorem inner_parCoupling_mul {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (B : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.parCoupling A * B) y⟫ = -⟪opE (S.parCoupling A) x, opE B y⟫ := by
  have hneg : opE (-S.parCoupling A) = -opE (S.parCoupling A) := map_neg _ _
  rw [opE_mul_apply, OneStep.inner_opE_transpose (S.parCoupling A) (opE B y) x,
    S.parCoupling_transpose hskew, hneg, _root_.neg_apply, inner_neg_right]
  exact neg_inj.2 (real_inner_comm _ _)

/-- **The bilinear form of the half-step term of a lossless coupling:**
`⟪x, A_ς A y⟫ = ⟪A_seq x, A y⟫ + ⟪A_par x, A y⟫`. -/
theorem inner_signedCoupling_mul {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ =
      ⟪opE (S.seqCoupling A) x, opE A y⟫ + ⟪opE (S.parCoupling A) x, opE A y⟫ := by
  rw [S.signedCoupling_eq, Matrix.sub_mul, inner_opE_sub, S.inner_seqCoupling_mul hskew,
    S.inner_parCoupling_mul hskew, sub_neg_eq_add]

/-- **The quadratic form of the half-step term of a lossless coupling:**
`⟪x, A_ς A x⟫ = ⟪A_seq x, A x⟫ + ⟪A_par x, A x⟫`. -/
theorem inner_signedCoupling_mul_self {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.signedCoupling A * A) x⟫ =
      ⟪opE (S.seqCoupling A) x, opE A x⟫ + ⟪opE (S.parCoupling A) x, opE A x⟫ :=
  S.inner_signedCoupling_mul hskew x x

end Split

end HeldScheme

/-! ### An exact invariant: matrices -/

namespace OneStep

/-- If `P X = Pᵀ`, then `Xᵀ P X = P`. -/
theorem transpose_mul_mul_of_mul_eq_transpose {P X : Matrix (Fin n) (Fin n) ℝ}
    (h : P * X = Pᵀ) : Xᵀ * P * X = P := by
  rw [Matrix.mul_assoc, h, ← Matrix.transpose_mul, h, Matrix.transpose_transpose]

/-- If `P X = Pᵀ`, then `Xᵀ Pᵀ X = Pᵀ`. -/
theorem transpose_mul_transpose_mul_of_mul_eq_transpose {P X : Matrix (Fin n) (Fin n) ℝ}
    (h : P * X = Pᵀ) : Xᵀ * Pᵀ * X = Pᵀ := by
  rw [← Matrix.transpose_mul, h, Matrix.transpose_transpose, h]

/-- An invariant form of a matrix is an invariant form of its powers. -/
theorem transpose_pow_mul_mul_pow {X Q : Matrix (Fin n) (Fin n) ℝ} (h : Xᵀ * Q * X = Q)
    (k : ℕ) : (X ^ k)ᵀ * Q * X ^ k = Q := by
  induction k with
  | zero => rw [pow_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  | succ k ih =>
    have e : (X ^ (k + 1))ᵀ * Q * X ^ (k + 1) = Xᵀ * ((X ^ k)ᵀ * Q * X ^ k) * X := by
      rw [pow_succ, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e, ih, h]

/-- `⟪x, Yᵀ Q Y x⟫ = ⟪Y x, Q Y x⟫`. -/
theorem inner_opE_transpose_mul_mul (Y Q : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (Yᵀ * Q * Y) x⟫ = ⟪opE Y x, opE Q (opE Y x)⟫ := by
  rw [Matrix.mul_assoc, opE_mul_apply, opE_mul_apply,
    OneStep.inner_opE_transpose Yᵀ (opE Q (opE Y x)) x, Matrix.transpose_transpose]
  exact real_inner_comm _ _

/-- `1 - Λᵀ` is invertible if `1 - Λ` is. -/
theorem isUnit_det_one_sub_transpose {Λ : Matrix (Fin n) (Fin n) ℝ}
    (hΛ : IsUnit (1 - Λ).det) : IsUnit (1 - Λᵀ).det := by
  have e : 1 - Λᵀ = (1 - Λ)ᵀ := by rw [Matrix.transpose_sub, Matrix.transpose_one]
  rw [e, Matrix.det_transpose]
  exact hΛ

/-- `X = (1 - Λ)⁻¹ (1 - Λᵀ)` satisfies `(1 - Λ) X = 1 - Λᵀ`. -/
theorem stored_rel_inv {Λ : Matrix (Fin n) (Fin n) ℝ} (hΛ : IsUnit (1 - Λ).det) :
    (1 - Λ) * ((1 - Λ)⁻¹ * (1 - Λᵀ)) = 1 - Λᵀ := by
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hΛ, Matrix.one_mul]

/-- If `1 - Λ` is invertible, `X = (1 - Λ)⁻¹ (1 - Λᵀ)` is the only matrix with
`(1 - Λ) X = 1 - Λᵀ`. -/
theorem eq_inv_mul_of_stored_rel {Λ X : Matrix (Fin n) (Fin n) ℝ} (hΛ : IsUnit (1 - Λ).det)
    (hX : (1 - Λ) * X = 1 - Λᵀ) : X = (1 - Λ)⁻¹ * (1 - Λᵀ) := by
  rw [← hX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hΛ, Matrix.one_mul]

/-- **The invariant, from the relation.** If `(1 - Λ) X = 1 - Λᵀ`, then `Xᵀ Q X = Q` with
`Q = 1 - ½ (Λ + Λᵀ)`. No inverse is needed. -/
theorem stored_invariant_of_rel {Λ X : Matrix (Fin n) (Fin n) ℝ}
    (hX : (1 - Λ) * X = 1 - Λᵀ) :
    Xᵀ * (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) * X = 1 - (1 / 2 : ℝ) • (Λ + Λᵀ) := by
  have hT : (1 - Λ)ᵀ = 1 - Λᵀ := by rw [Matrix.transpose_sub, Matrix.transpose_one]
  have h' : (1 - Λ) * X = (1 - Λ)ᵀ := hX.trans hT.symm
  have hQ : 1 - (1 / 2 : ℝ) • (Λ + Λᵀ) = (1 / 2 : ℝ) • ((1 - Λ) + (1 - Λ)ᵀ) := by
    rw [hT]
    module
  rw [hQ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    transpose_mul_mul_of_mul_eq_transpose h',
    transpose_mul_transpose_mul_of_mul_eq_transpose h']

/-- **The invariant.** If `1 - Λ` is invertible, `X = (1 - Λ)⁻¹ (1 - Λᵀ)` and
`Q = 1 - ½ (Λ + Λᵀ)`, then `Xᵀ Q X = Q`. -/
theorem stored_invariant {Λ : Matrix (Fin n) (Fin n) ℝ} (hΛ : IsUnit (1 - Λ).det) :
    ((1 - Λ)⁻¹ * (1 - Λᵀ))ᵀ * (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) * ((1 - Λ)⁻¹ * (1 - Λᵀ)) =
      1 - (1 / 2 : ℝ) • (Λ + Λᵀ) :=
  stored_invariant_of_rel (stored_rel_inv hΛ)

/-- **The invariant along the trajectory, from the relation.** If `(1 - Λ) X = 1 - Λᵀ`, then
`(X^k)ᵀ Q X^k = Q` for all `k`, `Q = 1 - ½ (Λ + Λᵀ)`. -/
theorem stored_invariant_pow_of_rel {Λ X : Matrix (Fin n) (Fin n) ℝ}
    (hX : (1 - Λ) * X = 1 - Λᵀ) (k : ℕ) :
    (X ^ k)ᵀ * (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) * X ^ k = 1 - (1 / 2 : ℝ) • (Λ + Λᵀ) :=
  transpose_pow_mul_mul_pow (stored_invariant_of_rel hX) k

/-- **The invariant along the trajectory.** If `1 - Λ` is invertible,
`X = (1 - Λ)⁻¹ (1 - Λᵀ)` and `Q = 1 - ½ (Λ + Λᵀ)`, then `(X^k)ᵀ Q X^k = Q` for all `k`. -/
theorem stored_invariant_pow {Λ : Matrix (Fin n) (Fin n) ℝ} (hΛ : IsUnit (1 - Λ).det) (k : ℕ) :
    (((1 - Λ)⁻¹ * (1 - Λᵀ)) ^ k)ᵀ * (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) *
        ((1 - Λ)⁻¹ * (1 - Λᵀ)) ^ k =
      1 - (1 / 2 : ℝ) • (Λ + Λᵀ) :=
  stored_invariant_pow_of_rel (stored_rel_inv hΛ) k

/-! ### An exact invariant: the bound -/

/-- The form `Q = 1 - ½ (Λ + Λᵀ)` is between `(1 - ρ)` and `(1 + ρ)` times the Euclidean one if
`‖Λ + Λᵀ‖ ≤ 2ρ`: `(1 - ρ) ‖y‖² ≤ ⟪y, Q y⟫ ≤ (1 + ρ) ‖y‖²`. -/
theorem stored_form_bounds {Λ : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    (hρ : ‖opE (Λ + Λᵀ)‖ ≤ 2 * ρ) (y : EuclideanSpace ℝ (Fin n)) :
    (1 - ρ) * ‖y‖ ^ 2 ≤ ⟪y, opE (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) y⟫ ∧
      ⟪y, opE (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) y⟫ ≤ (1 + ρ) * ‖y‖ ^ 2 := by
  have e : ⟪y, opE (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) y⟫ =
      ‖y‖ ^ 2 - 1 / 2 * ⟪y, opE (Λ + Λᵀ) y⟫ := by
    rw [inner_opE_sub, inner_opE_smul, opE_one, one_apply_eq_self,
      real_inner_self_eq_norm_sq]
  have h1 := abs_inner_opE_le (Λ + Λᵀ) y y
  have h2 : ‖opE (Λ + Λᵀ)‖ * (‖y‖ * ‖y‖) ≤ 2 * ρ * (‖y‖ * ‖y‖) :=
    mul_le_mul_of_nonneg_right hρ (mul_nonneg (norm_nonneg y) (norm_nonneg y))
  have h3 := abs_le.1 (h1.trans h2)
  rw [e]
  constructor
  · linarith [h3.2]
  · linarith [h3.1]

/-- A matrix `Y` with `Yᵀ Q Y = Q`, `Q = 1 - ½ (Λ + Λᵀ)`, `‖Λ + Λᵀ‖ ≤ 2ρ`, stretches no vector
by more than `(1 + ρ)/(1 - ρ)` in the square of the norm: `(1 - ρ) ‖Y x‖² ≤ (1 + ρ) ‖x‖²`. -/
theorem stored_norm_le_of_invariant {Λ Y : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    (hY : Yᵀ * (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) * Y = 1 - (1 / 2 : ℝ) • (Λ + Λᵀ))
    (hρ : ‖opE (Λ + Λᵀ)‖ ≤ 2 * ρ) (x : EuclideanSpace ℝ (Fin n)) :
    (1 - ρ) * ‖opE Y x‖ ^ 2 ≤ (1 + ρ) * ‖x‖ ^ 2 := by
  have h1 := (stored_form_bounds hρ (opE Y x)).1
  have h2 := (stored_form_bounds hρ x).2
  have e := inner_opE_transpose_mul_mul Y (1 - (1 / 2 : ℝ) • (Λ + Λᵀ)) x
  rw [hY] at e
  linarith

/-- **The bound along the trajectory, from the relation.** If `(1 - Λ) X = 1 - Λᵀ` and
`‖Λ + Λᵀ‖ ≤ 2ρ`, then `(1 - ρ) ‖X^k x‖² ≤ (1 + ρ) ‖x‖²` for all `k` and `x`. The inequality holds
for every `ρ`; it bounds the trajectory if `ρ < 1` (`stored_norm_pow_sq_le_of_rel`). -/
theorem stored_norm_pow_le_of_rel {Λ X : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    (hX : (1 - Λ) * X = 1 - Λᵀ) (hρ : ‖opE (Λ + Λᵀ)‖ ≤ 2 * ρ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (1 - ρ) * ‖opE (X ^ k) x‖ ^ 2 ≤ (1 + ρ) * ‖x‖ ^ 2 :=
  stored_norm_le_of_invariant (stored_invariant_pow_of_rel hX k) hρ x

/-- **The trajectory is bounded for all times, from the relation.** If `(1 - Λ) X = 1 - Λᵀ`,
`ρ < 1` and `‖Λ + Λᵀ‖ ≤ 2ρ`, then `‖X^k x‖² ≤ (1 + ρ)/(1 - ρ) ‖x‖²` for all `k` and `x`. -/
theorem stored_norm_pow_sq_le_of_rel {Λ X : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    (hX : (1 - Λ) * X = 1 - Λᵀ) (hρ1 : ρ < 1) (hρ : ‖opE (Λ + Λᵀ)‖ ≤ 2 * ρ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖opE (X ^ k) x‖ ^ 2 ≤ (1 + ρ) / (1 - ρ) * ‖x‖ ^ 2 := by
  have h := stored_norm_pow_le_of_rel hX hρ k x
  have hpos : 0 < 1 - ρ := sub_pos.2 hρ1
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-- **The bound along the trajectory.** If `1 - Λ` is invertible, `X = (1 - Λ)⁻¹ (1 - Λᵀ)` and
`‖Λ + Λᵀ‖ ≤ 2ρ`, then `(1 - ρ) ‖X^k x‖² ≤ (1 + ρ) ‖x‖²` for all `k` and `x`. -/
theorem stored_norm_pow_le {Λ : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (hΛ : IsUnit (1 - Λ).det)
    (hρ : ‖opE (Λ + Λᵀ)‖ ≤ 2 * ρ) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (1 - ρ) * ‖opE (((1 - Λ)⁻¹ * (1 - Λᵀ)) ^ k) x‖ ^ 2 ≤ (1 + ρ) * ‖x‖ ^ 2 :=
  stored_norm_pow_le_of_rel (stored_rel_inv hΛ) hρ k x

/-- **The trajectory is bounded for all times.** If `1 - Λ` is invertible,
`X = (1 - Λ)⁻¹ (1 - Λᵀ)`, `ρ < 1` and `‖Λ + Λᵀ‖ ≤ 2ρ`, then
`‖X^k x‖² ≤ (1 + ρ)/(1 - ρ) ‖x‖²` for all `k` and `x`. -/
theorem stored_norm_pow_sq_le {Λ : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (hΛ : IsUnit (1 - Λ).det)
    (hρ1 : ρ < 1) (hρ : ‖opE (Λ + Λᵀ)‖ ≤ 2 * ρ) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖opE (((1 - Λ)⁻¹ * (1 - Λᵀ)) ^ k) x‖ ^ 2 ≤ (1 + ρ) / (1 - ρ) * ‖x‖ ^ 2 :=
  stored_norm_pow_sq_le_of_rel (stored_rel_inv hΛ) hρ1 hρ k x

end OneStep

/-! ### An exact invariant: schemes with one held sample -/

namespace HeldScheme

section Stored

variable {κ : Type*} (S : HeldScheme n κ)

/-- **`1 - N` is unipotent:** `det (1 - N) = 1` for every scheme with one held sample (new samples
come only from earlier stages, so the transpose of `1 - N` is block triangular for the stages,
with identity diagonal blocks). -/
theorem det_one_sub_N : (1 - S.N).det = 1 := by
  have hT : (1 - S.N)ᵀ.BlockTriangular fun p => S.stage (S.sub p) := by
    intro i j hij
    have hij' : S.stage (S.sub j) < S.stage (S.sub i) := hij
    have hne : j ≠ i := fun h => by
      rw [h] at hij'
      exact lt_irrefl _ hij'
    have hN0 : S.N j i = 0 := S.hN j i fun h => lt_asymm hij' h.2
    rw [Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply_ne hne, hN0, sub_zero]
  rw [← det_transpose, hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have h1 : (1 - S.N)ᵀ.toSquareBlock (fun p => S.stage (S.sub p)) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : S.stage (S.sub i) = a := hi
    have hj' : S.stage (S.sub j) = a := hj
    have hN0 : S.N j i = 0 := S.hN j i fun h => by
      have h2 := h.2
      rw [hi', hj'] at h2
      exact lt_irrefl _ h2
    simp [toSquareBlock_def, Matrix.one_apply, hN0]
  rw [h1, det_one]

/-- **`1 - N` is invertible.** -/
theorem isUnit_det_one_sub_N : IsUnit (1 - S.N).det := by
  rw [S.det_one_sub_N]
  exact isUnit_one

/-- The relation of the scheme: `(1 - N) X = F + M`. -/
theorem one_sub_N_mul_X : (1 - S.N) * S.X = S.F + S.M := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  exact sub_eq_of_eq_add S.hX

/-- **The one-step map of a scheme with one held sample:** `X = (1 - N)⁻¹ (F + M)`. -/
theorem X_eq_inv_mul : S.X = (1 - S.N)⁻¹ * (S.F + S.M) := by
  rw [← S.one_sub_N_mul_X, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ S.isUnit_det_one_sub_N,
    Matrix.one_mul]

/-- Lossless scalar stores in a sequential order (`F = 1`, `M = -Nᵀ`): `(1 - N) X = 1 - Nᵀ`. -/
theorem stored_rel (hF : S.F = 1) (hM : S.M = -(S.N)ᵀ) : (1 - S.N) * S.X = 1 - (S.N)ᵀ := by
  rw [S.one_sub_N_mul_X, hF, hM, sub_eq_add_neg]

/-- Lossless scalar stores in a sequential order (`F = 1`, `M = -Nᵀ`):
`X = (1 - N)⁻¹ (1 - Nᵀ)`. -/
theorem X_eq_stored (hF : S.F = 1) (hM : S.M = -(S.N)ᵀ) :
    S.X = (1 - S.N)⁻¹ * (1 - (S.N)ᵀ) :=
  eq_inv_mul_of_stored_rel S.isUnit_det_one_sub_N (S.stored_rel hF hM)

/-- **The invariant of lossless scalar stores in a sequential order.** If `F = 1` and `M = -Nᵀ`,
then `Xᵀ Q X = Q` with `Q = 1 - ½ (N + Nᵀ)`. -/
theorem stored_invariant (hF : S.F = 1) (hM : S.M = -(S.N)ᵀ) :
    (S.X)ᵀ * (1 - (1 / 2 : ℝ) • (S.N + (S.N)ᵀ)) * S.X = 1 - (1 / 2 : ℝ) • (S.N + (S.N)ᵀ) :=
  stored_invariant_of_rel (S.stored_rel hF hM)

/-- **The invariant along the trajectory.** If `F = 1` and `M = -Nᵀ`, then `(X^k)ᵀ Q X^k = Q` for
all `k`, `Q = 1 - ½ (N + Nᵀ)`. -/
theorem stored_invariant_pow (hF : S.F = 1) (hM : S.M = -(S.N)ᵀ) (k : ℕ) :
    (S.X ^ k)ᵀ * (1 - (1 / 2 : ℝ) • (S.N + (S.N)ᵀ)) * S.X ^ k =
      1 - (1 / 2 : ℝ) • (S.N + (S.N)ᵀ) :=
  stored_invariant_pow_of_rel (S.stored_rel hF hM) k

/-- **The bound along the trajectory.** If `F = 1`, `M = -Nᵀ` and `‖N + Nᵀ‖ ≤ 2ρ`, then
`(1 - ρ) ‖X^k x‖² ≤ (1 + ρ) ‖x‖²` for all `k` and `x`. -/
theorem stored_norm_pow_le (hF : S.F = 1) (hM : S.M = -(S.N)ᵀ) {ρ : ℝ}
    (hρ : ‖opE (S.N + (S.N)ᵀ)‖ ≤ 2 * ρ) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (1 - ρ) * ‖opE (S.X ^ k) x‖ ^ 2 ≤ (1 + ρ) * ‖x‖ ^ 2 :=
  stored_norm_pow_le_of_rel (S.stored_rel hF hM) hρ k x

/-- **The trajectory is bounded for all times.** If `F = 1`, `M = -Nᵀ`, `ρ < 1` and
`‖N + Nᵀ‖ ≤ 2ρ`, then `‖X^k x‖² ≤ (1 + ρ)/(1 - ρ) ‖x‖²` for all `k` and `x`. -/
theorem stored_norm_pow_sq_le (hF : S.F = 1) (hM : S.M = -(S.N)ᵀ) {ρ : ℝ} (hρ1 : ρ < 1)
    (hρ : ‖opE (S.N + (S.N)ᵀ)‖ ≤ 2 * ρ) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖opE (S.X ^ k) x‖ ^ 2 ≤ (1 + ρ) / (1 - ρ) * ‖x‖ ^ 2 :=
  stored_norm_pow_sq_le_of_rel (S.stored_rel hF hM) hρ1 hρ k x

end Stored

end HeldScheme

end CoSimFoundations
