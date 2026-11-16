/-
The order of execution reversed in the next macro step (the paper, Section `sec:half`, after
Lemma `thm:half`: two macro steps of the zero-order hold, the second in the reversed order).

**Two steps** (`two_step_identity`, `two_step_split`). For one-step maps `X_a`, `X_b` and `U`,
  `X_b X_a - U² = (X_b - U) U + U (X_a - U) + (X_b - U)(X_a - U)`.
Let `U = e^{HA}`, `H ≥ 0`, `α = ‖A‖`, and
  `‖X_a - U - ½H² S_a A‖ ≤ c_a H³`,  `‖X_b - U - ½H² S_b A‖ ≤ c_b H³`,  `‖S_a‖, ‖S_b‖ ≤ s`.
Then (`norm_two_step_le`, for matrices `norm_opE_two_step_le`)
  `‖X_b X_a - e^{2HA} - ½H² (S_a + S_b) A‖ ≤ twoStepC s α c_a c_b H · H³`,
  `twoStepC = e^{Hα} (s α² + c_a + c_b) + H (sα/2 + c_a H)(sα/2 + c_b H)`.
Proof: with `P = ½H² S A` and `R = X - U - P`,
  `X_b X_a - U² - (P_a + P_b) = R_b U + P_b (U - 1) + U R_a + (U - 1) P_a + (X_b - U)(X_a - U)`,
`‖U‖ ≤ e^{Hα}`, `‖U - 1‖ ≤ α e^{Hα} H`, `‖X - U‖ ≤ ½H² s α + c H³`. If bounds `‖X_a - U‖ ≤ e_a`,
`‖X_b - U‖ ≤ e_b` are known, the last product is at most `e_b e_a`
(`norm_two_step_le_of_error`, `norm_opE_two_step_le_of_error`).

**The reversed assignment of stages.** `S.restage st` is the frame of `S` (subsystems,
partners) with the stages `st`; `S.Reversed st` says `st s < st t ↔ S.stage t < S.stage s` for
all subsystems `s`, `t`: every pair at different stages is in the opposite order, and a pair
shares a stage in `st` exactly if it shares one in `S` (`Reversed.eq_iff`). The assignment
`S.revStage m = fun s => m - S.stage s` is reversed if `m` bounds the stages
(`reversed_revStage`, `reversed_revStage_sup`). For a reversed assignment
(`signedCoupling_add_restage`)
  `A_ς^a + A_ς^b = -2 A_par`,
`A_par` the coupling between different subsystems at the same stage (`parCoupling` of
`StoredEnergy`): the sign of a link between two stages changes, that of a link within a stage
is `-1` in both. If no two partners share a stage, `A_par = 0`
(`parCoupling_eq_zero_of_partner`, `signedCoupling_add_restage_eq_zero`).

**The zero-order hold** (`norm_zoh_reversed_sub_le`, `norm_zoh_reversed_le`). For `0 ≤ H`,
`H ‖A‖ ≤ 1/4`, `σ H ‖A‖ ≤ 1/6`, `σ = √(card κ)` (the range of `norm_zoh_step_sub_le`), `X_a` the
one-step map of the zero-order hold in the stages of `S` and `X_b` that in a reversed assignment,
  `‖X_b X_a - e^{2HA} + H² A_par A‖ ≤ (5 + 39σ + 223σ² + 144σ³) ‖A‖³ · H³`   (`zohTwoStepK`),
and if no two partners share a stage, `‖X_b X_a - e^{2HA}‖` has this bound: the two macro steps
together are of third order, although each is of second order.
Proof: `norm_opE_two_step_le_of_error` with `norm_zoh_step_sub_le` (`c_a = c_b = zohStepK`),
`‖A_ς‖ ≤ σ ‖A‖` (`norm_opE_signedCoupling_le`: in the rows of a subsystem `A_ς` is `A` times a
diagonal matrix of signs) and `‖X - e^{HA}‖ ≤ zohConsC · H²` (`zoh_consistent`).
-/
import CoSimFoundations.ZeroOrderHold
import CoSimFoundations.StoredEnergy
import CoSimFoundations.BarrierConstants

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

/-! ### Two steps -/

/-- **Two steps against two steps of the reference:**
`X_b X_a - U² = (X_b - U) U + U (X_a - U) + (X_b - U)(X_a - U)`. -/
theorem two_step_identity {R : Type*} [Ring R] (Xa Xb U : R) :
    Xb * Xa - U * U = (Xb - U) * U + U * (Xa - U) + (Xb - U) * (Xa - U) := by
  noncomm_ring

/-- The two-step identity with the leading terms `P_a`, `P_b` of the two one-step differences
taken out. -/
theorem two_step_split {R : Type*} [Ring R] (Xa Xb U Pa Pb : R) :
    Xb * Xa - U * U - (Pa + Pb) =
      (Xb - U - Pb) * U + Pb * (U - 1) + U * (Xa - U - Pa) + (U - 1) * Pa +
        (Xb - U) * (Xa - U) := by
  noncomm_ring

/-- The constant of two steps: `e^{Hα} (s α² + c_a + c_b) + H (sα/2 + c_a H)(sα/2 + c_b H)`. -/
noncomputable def twoStepC (s α ca cb H : ℝ) : ℝ :=
  Real.exp (H * α) * (s * α ^ 2 + ca + cb) + H * (s * α / 2 + ca * H) * (s * α / 2 + cb * H)

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `e^{2HA} = e^{HA} e^{HA}`. -/
theorem exp_two_mul_smul (A : 𝔸) (H : ℝ) :
    NormedSpace.exp ((2 * H) • A) = NormedSpace.exp (H • A) * NormedSpace.exp (H • A) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← NormedSpace.exp_add_of_commute (Commute.refl (H • A)), two_mul, add_smul]

/-- `‖e^{HA}‖ ≤ e^{H‖A‖}` for `H ≥ 0`, in a Banach algebra with `‖1‖ ≤ 1`. -/
theorem norm_exp_smul_le_of_norm_one_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) (A : 𝔸) {H : ℝ} (hH : 0 ≤ H) :
    ‖NormedSpace.exp (H • A)‖ ≤ Real.exp (H * ‖A‖) := by
  have h := norm_exp_sub_one_le_exp_norm (H • A)
  rw [norm_smul, Real.norm_of_nonneg hH] at h
  have h2 : ‖NormedSpace.exp (H • A) - 1 + 1‖ ≤ ‖NormedSpace.exp (H • A) - 1‖ + ‖(1 : 𝔸)‖ :=
    norm_add_le _ _
  rw [sub_add_cancel] at h2
  linarith

/-- `‖½H² S A‖ ≤ ½H² s ‖A‖` if `‖S‖ ≤ s`. -/
theorem norm_half_sq_smul_mul_le {S' A : 𝔸} {s : ℝ} (hS : ‖S'‖ ≤ s) (H : ℝ) :
    ‖(H ^ 2 / 2) • (S' * A)‖ ≤ H ^ 2 / 2 * (s * ‖A‖) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))) (by positivity)

/-- **Two steps, with bounds of the two one-step differences.** In a Banach algebra with
`‖1‖ ≤ 1`, let `U = e^{HA}`, `H ≥ 0`, `‖S_a‖, ‖S_b‖ ≤ s`, `‖X_a - U - ½H² S_a A‖ ≤ c_a H³`,
`‖X_b - U - ½H² S_b A‖ ≤ c_b H³`, `‖X_a - U‖ ≤ e_a`, `‖X_b - U‖ ≤ e_b`. Then
`‖X_b X_a - e^{2HA} - ½H² (S_a + S_b) A‖ ≤ e^{H‖A‖} (s ‖A‖² + c_a + c_b) H³ + e_b e_a`. -/
theorem norm_two_step_le_of_error (h1 : ‖(1 : 𝔸)‖ ≤ 1) {Xa Xb Sa Sb A : 𝔸}
    {H s ca cb ea eb : ℝ} (hH : 0 ≤ H) (hSa : ‖Sa‖ ≤ s) (hSb : ‖Sb‖ ≤ s)
    (ha : ‖Xa - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sa * A)‖ ≤ ca * H ^ 3)
    (hb : ‖Xb - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sb * A)‖ ≤ cb * H ^ 3)
    (hea : ‖Xa - NormedSpace.exp (H • A)‖ ≤ ea) (heb : ‖Xb - NormedSpace.exp (H • A)‖ ≤ eb) :
    ‖Xb * Xa - NormedSpace.exp ((2 * H) • A) - (H ^ 2 / 2) • ((Sa + Sb) * A)‖ ≤
      Real.exp (H * ‖A‖) * (s * ‖A‖ ^ 2 + ca + cb) * H ^ 3 + eb * ea := by
  have hUn : ‖NormedSpace.exp (H • A)‖ ≤ Real.exp (H * ‖A‖) :=
    norm_exp_smul_le_of_norm_one_le h1 A hH
  have hU1 : ‖NormedSpace.exp (H • A) - 1‖ ≤ ‖A‖ * Real.exp (H * ‖A‖) * H :=
    OneStep.norm_exp_smul_sub_one_le A hH
  have hPa := norm_half_sq_smul_mul_le (A := A) hSa H
  have hPb := norm_half_sq_smul_mul_le (A := A) hSb H
  have t1 : ‖(Xb - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sb * A)) *
      NormedSpace.exp (H • A)‖ ≤ cb * H ^ 3 * Real.exp (H * ‖A‖) :=
    (norm_mul_le _ _).trans (mul_le_mul hb hUn (norm_nonneg _) ((norm_nonneg _).trans hb))
  have t2 : ‖(H ^ 2 / 2) • (Sb * A) * (NormedSpace.exp (H • A) - 1)‖ ≤
      H ^ 2 / 2 * (s * ‖A‖) * (‖A‖ * Real.exp (H * ‖A‖) * H) :=
    (norm_mul_le _ _).trans (mul_le_mul hPb hU1 (norm_nonneg _) ((norm_nonneg _).trans hPb))
  have t3 : ‖NormedSpace.exp (H • A) *
      (Xa - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sa * A))‖ ≤
      Real.exp (H * ‖A‖) * (ca * H ^ 3) :=
    (norm_mul_le _ _).trans (mul_le_mul hUn ha (norm_nonneg _) (Real.exp_nonneg _))
  have t4 : ‖(NormedSpace.exp (H • A) - 1) * (H ^ 2 / 2) • (Sa * A)‖ ≤
      ‖A‖ * Real.exp (H * ‖A‖) * H * (H ^ 2 / 2 * (s * ‖A‖)) :=
    (norm_mul_le _ _).trans (mul_le_mul hU1 hPa (norm_nonneg _) ((norm_nonneg _).trans hU1))
  have t5 : ‖(Xb - NormedSpace.exp (H • A)) * (Xa - NormedSpace.exp (H • A))‖ ≤ eb * ea :=
    (norm_mul_le _ _).trans (mul_le_mul heb hea (norm_nonneg _) ((norm_nonneg _).trans heb))
  rw [exp_two_mul_smul, add_mul, smul_add, two_step_split]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add t1 t2) t3) t4) t5).trans_eq ?_
  ring

/-- **Two steps** (the general statement). In a Banach algebra with `‖1‖ ≤ 1`, let `U = e^{HA}`,
`H ≥ 0`, `‖S_a‖, ‖S_b‖ ≤ s`, `‖X_a - U - ½H² S_a A‖ ≤ c_a H³` and
`‖X_b - U - ½H² S_b A‖ ≤ c_b H³`. Then
`‖X_b X_a - e^{2HA} - ½H² (S_a + S_b) A‖ ≤ twoStepC s ‖A‖ c_a c_b H · H³`. -/
theorem norm_two_step_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) {Xa Xb Sa Sb A : 𝔸} {H s ca cb : ℝ}
    (hH : 0 ≤ H) (hSa : ‖Sa‖ ≤ s) (hSb : ‖Sb‖ ≤ s)
    (ha : ‖Xa - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sa * A)‖ ≤ ca * H ^ 3)
    (hb : ‖Xb - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sb * A)‖ ≤ cb * H ^ 3) :
    ‖Xb * Xa - NormedSpace.exp ((2 * H) • A) - (H ^ 2 / 2) • ((Sa + Sb) * A)‖ ≤
      twoStepC s ‖A‖ ca cb H * H ^ 3 := by
  have hE : ∀ {X S' : 𝔸} {c : ℝ}, ‖S'‖ ≤ s →
      ‖X - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (S' * A)‖ ≤ c * H ^ 3 →
      ‖X - NormedSpace.exp (H • A)‖ ≤ H ^ 2 / 2 * (s * ‖A‖) + c * H ^ 3 := by
    intro X S' c hS h
    have h2 := norm_add_le (X - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (S' * A))
      ((H ^ 2 / 2) • (S' * A))
    rw [sub_add_cancel] at h2
    have h3 := norm_half_sq_smul_mul_le (A := A) hS H
    linarith
  refine (norm_two_step_le_of_error h1 hH hSa hSb ha hb (hE hSa ha) (hE hSb hb)).trans_eq ?_
  rw [twoStepC]
  ring

end Algebra

open OneStep

variable {n : ℕ}

/-! ### Two steps, for matrices in the spectral norm -/

/-- The operator of a one-step difference minus its leading term. -/
theorem opE_step_sub (X S' A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    opE (X - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (S' * A)) =
      opE X - NormedSpace.exp (H • opE A) - (H ^ 2 / 2) • (opE S' * opE A) := by
  rw [opE_sub, opE_sub, opE_exp, opE_smul, opE_smul, opE_mul]

/-- The operator of the two-step difference minus its leading term. -/
theorem opE_two_step_sub (Xa Xb Sa Sb A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    opE (Xb * Xa - NormedSpace.exp ((2 * H) • A) - (H ^ 2 / 2) • ((Sa + Sb) * A)) =
      opE Xb * opE Xa - NormedSpace.exp ((2 * H) • opE A) -
        (H ^ 2 / 2) • ((opE Sa + opE Sb) * opE A) := by
  rw [opE_sub, opE_sub, opE_mul, opE_exp, opE_smul, opE_smul, opE_mul, opE_add]

/-- **Two steps, for matrices, with bounds of the two one-step differences** (spectral norms):
under the hypotheses of `norm_two_step_le_of_error`,
`‖X_b X_a - e^{2HA} - ½H² (S_a + S_b) A‖ ≤ e^{H‖A‖} (s ‖A‖² + c_a + c_b) H³ + e_b e_a`. -/
theorem norm_opE_two_step_le_of_error {Xa Xb Sa Sb A : Matrix (Fin n) (Fin n) ℝ}
    {H s ca cb ea eb : ℝ} (hH : 0 ≤ H) (hSa : ‖opE Sa‖ ≤ s) (hSb : ‖opE Sb‖ ≤ s)
    (ha : ‖opE (Xa - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sa * A))‖ ≤ ca * H ^ 3)
    (hb : ‖opE (Xb - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sb * A))‖ ≤ cb * H ^ 3)
    (hea : ‖opE (Xa - NormedSpace.exp (H • A))‖ ≤ ea)
    (heb : ‖opE (Xb - NormedSpace.exp (H • A))‖ ≤ eb) :
    ‖opE (Xb * Xa - NormedSpace.exp ((2 * H) • A) - (H ^ 2 / 2) • ((Sa + Sb) * A))‖ ≤
      Real.exp (H * ‖opE A‖) * (s * ‖opE A‖ ^ 2 + ca + cb) * H ^ 3 + eb * ea := by
  rw [opE_step_sub] at ha hb
  rw [opE_sub, opE_exp, opE_smul] at hea heb
  rw [opE_two_step_sub]
  exact norm_two_step_le_of_error ContinuousLinearMap.norm_id_le hH hSa hSb ha hb hea heb

/-- **Two steps, for matrices** (spectral norms). Let `H ≥ 0`, `‖S_a‖, ‖S_b‖ ≤ s`,
`‖X_a - e^{HA} - ½H² S_a A‖ ≤ c_a H³` and `‖X_b - e^{HA} - ½H² S_b A‖ ≤ c_b H³`. Then
`‖X_b X_a - e^{2HA} - ½H² (S_a + S_b) A‖ ≤ twoStepC s ‖A‖ c_a c_b H · H³`,
`twoStepC = e^{H‖A‖} (s ‖A‖² + c_a + c_b) + H (s‖A‖/2 + c_a H)(s‖A‖/2 + c_b H)`. -/
theorem norm_opE_two_step_le {Xa Xb Sa Sb A : Matrix (Fin n) (Fin n) ℝ} {H s ca cb : ℝ}
    (hH : 0 ≤ H) (hSa : ‖opE Sa‖ ≤ s) (hSb : ‖opE Sb‖ ≤ s)
    (ha : ‖opE (Xa - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sa * A))‖ ≤ ca * H ^ 3)
    (hb : ‖opE (Xb - NormedSpace.exp (H • A) - (H ^ 2 / 2) • (Sb * A))‖ ≤ cb * H ^ 3) :
    ‖opE (Xb * Xa - NormedSpace.exp ((2 * H) • A) - (H ^ 2 / 2) • ((Sa + Sb) * A))‖ ≤
      twoStepC s ‖opE A‖ ca cb H * H ^ 3 := by
  rw [opE_step_sub] at ha hb
  rw [opE_two_step_sub]
  exact norm_two_step_le ContinuousLinearMap.norm_id_le hH hSa hSb ha hb

namespace HeldScheme

/-! ### The reversed assignment of stages -/

section Restage

variable {κ : Type*} (S : HeldScheme n κ)

/-- The frame of `S` (subsystems and partners) with another assignment of stages `st`; the
coefficient matrices are zero. It carries the signs, the parts of a matrix and the zero-order
hold `(S.restage st).zoh A hA H` of the new assignment. -/
def restage (st : κ → ℕ) : HeldScheme n κ where
  sub := S.sub
  partner := S.partner
  stage := st
  F := 0
  N := 0
  M := 0
  X := 0
  hF := fun _ _ _ => rfl
  hN := fun _ _ _ => rfl
  hM := fun _ _ _ => rfl
  hX := by simp

/-- **A reversed assignment of stages:** `st s < st t ↔ S.stage t < S.stage s` for all
subsystems. Every pair of subsystems at different stages of `S` is in the opposite order in
`st`, and pairs that share a stage of `S` share one in `st` (`Reversed.eq_iff`). -/
def Reversed (st : κ → ℕ) : Prop := ∀ s t, st s < st t ↔ S.stage t < S.stage s

variable {S}

/-- Two subsystems share a stage in a reversed assignment exactly if they share one in `S`. -/
theorem Reversed.eq_iff {st : κ → ℕ} (h : S.Reversed st) (s t : κ) :
    st s = st t ↔ S.stage s = S.stage t := by
  have h1 := h s t
  have h2 := h t s
  constructor <;> intro e <;> omega

variable (S)

/-- The stages counted from the end: `m - S.stage s`. -/
def revStage (m : ℕ) : κ → ℕ := fun s => m - S.stage s

/-- Counting the stages from the end reverses the assignment, if `m` bounds the stages. -/
theorem reversed_revStage {m : ℕ} (hm : ∀ s, S.stage s ≤ m) : S.Reversed (S.revStage m) := by
  intro s t
  have h1 := hm s
  have h2 := hm t
  unfold revStage
  omega

/-- For finitely many subsystems, counting the stages from the last one reverses the
assignment. -/
theorem reversed_revStage_sup [Fintype κ] :
    S.Reversed (S.revStage (Finset.univ.sup S.stage)) :=
  S.reversed_revStage fun s => Finset.le_sup (f := S.stage) (Finset.mem_univ s)

/-- The sign of a pair in a reversed assignment: `+1` if the first runs at an earlier stage of
`S` than the second, else `-1`. -/
theorem Reversed.sg_restage {st : κ → ℕ} (h : S.Reversed st) (s k : κ) :
    (S.restage st).sg s k = if S.stage s < S.stage k then 1 else -1 := by
  unfold sg
  exact if_congr (h k s) rfl rfl

end Restage

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- **The signed couplings of an assignment and of a reversed one add up to minus twice the
coupling within a stage:** `A_ς^a + A_ς^b = -2 A_par`. On a link between two stages the two
signs are opposite, on a link within a stage both are `-1`. -/
theorem signedCoupling_add_restage {st : κ → ℕ} (h : S.Reversed st)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S.signedCoupling A + (S.restage st).signedCoupling A = -((2 : ℝ) • S.parCoupling A) := by
  ext p q
  have e : (S.restage st).signedCoupling A p q =
      if S.sub p = S.sub q then 0 else (S.restage st).sg (S.sub p) (S.sub q) * A p q := rfl
  rw [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, S.signedCoupling_apply, e,
    S.parCoupling_apply, h.sg_restage, sg]
  by_cases hpq : S.sub p = S.sub q
  · simp [hpq]
  · rcases lt_trichotomy (S.stage (S.sub p)) (S.stage (S.sub q)) with h1 | h1 | h1
    · simp [hpq, h1, lt_asymm h1, h1.ne]
    · simp [hpq, h1]
      ring
    · simp [hpq, h1, lt_asymm h1, h1.ne']

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

/-- **No two partners at the same stage:** the signed couplings of an assignment and of a
reversed one cancel, `A_ς^a + A_ς^b = 0`. -/
theorem signedCoupling_add_restage_eq_zero {st : κ → ℕ} (h : S.Reversed st)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t) :
    S.signedCoupling A + (S.restage st).signedCoupling A = 0 := by
  rw [S.signedCoupling_add_restage h, S.parCoupling_eq_zero_of_partner hA hns, smul_zero,
    neg_zero]

/-- **The signed coupling is at most `√(card κ) ‖A‖`** in the spectral norm: in the rows of a
subsystem `s` it is `A` times the diagonal matrix of the signs `ς_{s·}` (zero on `s`). -/
theorem norm_opE_signedCoupling_le [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (S.signedCoupling A)‖ ≤ Real.sqrt (Fintype.card κ) * ‖opE A‖ := by
  refine S.norm_opE_le_of_rows (norm_nonneg _) fun s x hx y => ?_
  have e : ⟪x, opE (S.signedCoupling A) y⟫ = ⟪x, opE (A * S.osgn s) y⟫ := by
    refine inner_opE_congr_row hx y fun p q hp => ?_
    have e' : (A * S.osgn s) p q = A p q * (if S.sub q = s then 0 else S.sg s (S.sub q)) := by
      rw [osgn, Matrix.mul_diagonal]
    rw [e', S.signedCoupling_apply, hp]
    by_cases hq : S.sub q = s
    · rw [ite_eq_left hq.symm, ite_eq_left hq, mul_zero]
    · rw [ite_eq_right fun e'' => hq e''.symm, ite_eq_right hq, mul_comm]
  have hos : ‖opE (S.osgn s)‖ ≤ 1 := by
    refine norm_opE_diagonal_le _ zero_le_one fun r => ?_
    by_cases hr : S.sub r = s
    · simp [hr]
    · by_cases hst : S.stage (S.sub r) < S.stage s <;> simp [hr, sg, hst]
  rw [e]
  refine (abs_inner_opE_le _ x y).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [opE_mul]
  calc ‖opE A * opE (S.osgn s)‖ ≤ ‖opE A‖ * ‖opE (S.osgn s)‖ := norm_mul_le _ _
    _ ≤ ‖opE A‖ * 1 := mul_le_mul_of_nonneg_left hos (norm_nonneg _)
    _ = ‖opE A‖ := mul_one _

/-! ### The zero-order hold in an assignment and then in a reversed one -/

/-- The constant of two macro steps of the zero-order hold, the second in a reversed
assignment: `(5 + 39σ + 223σ² + 144σ³) α³`, `σ = √(card κ)`, `α = ‖A‖`. -/
noncomputable def zohTwoStepK (σ α : ℝ) : ℝ :=
  (5 + 39 * σ + 223 * σ ^ 2 + 144 * σ ^ 3) * α ^ 3

/-- The arithmetic of the constant: for `e^{Hα} ≤ 4/3` and `H α ≤ 1/4`,
`e^{Hα} (σα · α² + 2 zohStepK) H³ + (zohConsC H²)² ≤ zohTwoStepK · H³`. -/
theorem zohTwoStep_constants_le {σ α H : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hE : Real.exp (H * α) ≤ 4 / 3) (hAH : H * α ≤ 1 / 4) :
    Real.exp (H * α) * (σ * α * α ^ 2 + zohStepK σ α + zohStepK σ α) * H ^ 3 +
        zohConsC σ α * H ^ 2 * (zohConsC σ α * H ^ 2) ≤ zohTwoStepK σ α * H ^ 3 := by
  have hK : 0 ≤ zohStepK σ α := by
    unfold zohStepK
    positivity
  have p : 0 ≤ (σ * α * α ^ 2 + zohStepK σ α + zohStepK σ α) * H ^ 3 := by positivity
  have t1 := mul_le_mul_of_nonneg_right hE p
  have t2 : 9 * (1 + 6 * σ) ^ 2 * α ^ 3 * H ^ 3 * (H * α) ≤
      9 * (1 + 6 * σ) ^ 2 * α ^ 3 * H ^ 3 * (1 / 4) :=
    mul_le_mul_of_nonneg_left hAH (by positivity)
  have q0 : 0 ≤ α ^ 3 * H ^ 3 := by positivity
  have q2 : 0 ≤ σ ^ 2 * α ^ 3 * H ^ 3 := by positivity
  unfold zohStepK at t1
  unfold zohStepK zohConsC zohTwoStepK
  nlinarith [t1, t2, q0, q2]

/-- **Two macro steps of the zero-order hold, the second in a reversed assignment of stages.**
Let `X_a` be the one-step map of the zero-order hold in the stages of `S` and `X_b` that in a
reversed assignment `st` (`S.Reversed st`). For `0 ≤ H`, `H ‖A‖ ≤ 1/4` and
`√(card κ) · H ‖A‖ ≤ 1/6`:
`‖X_b X_a - e^{2HA} + H² A_par A‖ ≤ (5 + 39σ + 223σ² + 144σ³) ‖A‖³ · H³`, `σ = √(card κ)`,
`A_par` the coupling between different subsystems at the same stage. -/
theorem norm_zoh_reversed_sub_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {st : κ → ℕ} (hrev : S.Reversed st) {H : ℝ} (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    ‖opE (((S.restage st).zoh A hA H).X * (S.zoh A hA H).X - NormedSpace.exp ((2 * H) • A) +
        H ^ 2 • (S.parCoupling A * A))‖ ≤
      zohTwoStepK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 3 := by
  have ha := S.norm_zoh_step_sub_le hA hH hAH hσ
  have hb := (S.restage st).norm_zoh_step_sub_le hA hH hAH hσ
  have hea := (S.zoh_consistent hA hH hAH hσ).hc
  have heb := ((S.restage st).zoh_consistent hA hH hAH hσ).hc
  have hSa := S.norm_opE_signedCoupling_le A
  have hSb := (S.restage st).norm_opE_signedCoupling_le A
  have h := norm_opE_two_step_le_of_error hH hSa hSb ha hb hea heb
  have e : ((S.restage st).zoh A hA H).X * (S.zoh A hA H).X - NormedSpace.exp ((2 * H) • A) +
      H ^ 2 • (S.parCoupling A * A) =
      ((S.restage st).zoh A hA H).X * (S.zoh A hA H).X - NormedSpace.exp ((2 * H) • A) -
        (H ^ 2 / 2) • ((S.signedCoupling A + (S.restage st).signedCoupling A) * A) := by
    rw [S.signedCoupling_add_restage hrev, neg_mul, smul_mul_assoc]
    module
  rw [e]
  exact h.trans (zohTwoStep_constants_le (Real.sqrt_nonneg _) (norm_nonneg _) hH
    ((Real.exp_le_exp.2 hAH).trans exp_quarter_le) hAH)

/-- **The order of execution reversed in the next macro step.** If no two partners share a
stage, the zero-order hold in the stages of `S` (one-step map `X_a`) followed by the zero-order
hold in a reversed assignment (`X_b`) is of third order over the two macro steps: for `0 ≤ H`,
`H ‖A‖ ≤ 1/4` and `√(card κ) · H ‖A‖ ≤ 1/6`,
`‖X_b X_a - e^{2HA}‖ ≤ (5 + 39σ + 223σ² + 144σ³) ‖A‖³ · H³`, `σ = √(card κ)`. -/
theorem norm_zoh_reversed_le [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hns : ∀ s t, s ≠ t → S.partner s t → S.stage s ≠ S.stage t)
    {st : κ → ℕ} (hrev : S.Reversed st) {H : ℝ} (hH : 0 ≤ H) (hAH : H * ‖opE A‖ ≤ 1 / 4)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) :
    ‖opE (((S.restage st).zoh A hA H).X * (S.zoh A hA H).X - NormedSpace.exp ((2 * H) • A))‖ ≤
      zohTwoStepK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 3 := by
  have h := S.norm_zoh_reversed_sub_le hA hrev hH hAH hσ
  rwa [S.parCoupling_eq_zero_of_partner hA hns, zero_mul, smul_zero, add_zero] at h

end HeldScheme

end CoSimFoundations
