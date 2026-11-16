/-
One order per held sample (the paper, Theorem 4.10 `thm:memory`, inequality `eq:memorylead`).

**Setting.** `E` is the state space of the monolithic system `ẋ = A x`, `F` that of subsystem
`i`, `P = Π_i : E → F` the projection (`‖P‖ ≤ 1`), `C : E → G` the stack of the outputs `C_j` of
the partners of `i`. The subsystem is driven through its own state and these outputs only:

  `P ∘ A = Ai ∘ P + L ∘ C`        (`Π_i A = A_i Π_i + Σ_j B_i L_ij C_j`).

The subsystem runs before all of its partners with `l ≥ 1` held samples, of the ages
`0, …, l-1`; the coefficient of the samples of age `r` is `g r ∘ C` (`Σ_j G_ij^r C_j`), the local
coefficient is `Fi`, and the local defect of the rule is, with `U = exp (H • A)`,

  `𝒯 = P ∘ U - Fi ∘ P - Σ_{r<l} g r ∘ C ∘ U^{-r}`      (`localDefect`, eq. `eq:localdefect`).

The states not shown up to the order `m` are
`unseen P C A m = {v : P v = 0, C (A^q v) = 0 for q < m}`; the paper's `𝒱_i^0` is
`unseen P C A l` and `c_i = ‖P A^{l+1}`  restricted to it`‖`.

**Filtration** (`map_mem_unseen`, `pow_mem_unseen`, `proj_pow_eq_zero`): `A` maps
`unseen (m+1)` into `unseen m`, hence `P A^p v = 0` for `v ∈ unseen m`, `p ≤ m`.

**Step 1** (`memory_key_step`). With the moments `ν_p = Σ_r ((-r)^p / p!) g r ∘ C` (`moment`),
for `v ∈ unseen m`, the Taylor series of `U v` and of `U^{-r} v` give

  `𝒯 v = -(H^m ν_m A^m v - H^{m+1}/(m+1)! P A^{m+1} v) + ρ`,   `‖ρ‖ ≤ e_m ‖v‖`,
  `e_m = Σ_{p≥m+2} x^p/p! + w H Σ_{r<l} Σ_{p≥m+1} (r x)^p/p!`,   `x = H ‖A‖`   (`memE`),

if `‖g r ∘ C‖ ≤ w H` for `1 ≤ r < l`. Hence `‖H^m ν_m A^m v - H^{m+1}/(m+1)! P A^{m+1} v‖ ≤
(‖𝒯‖ + e_m) ‖v‖`. (The paper writes this with `η_m = ν_m - H/(m+1)! a_i`; on `unseen m`,
`a_i A^m v = P A^{m+1} v`, which is the form used here.)

**Step 2** (`moment_top`, `gamma_identity`). The ages are the roots of
`∏_{r<l} (s + r) = s^l + Σ_{1≤m<l} adamsCoeff l m s^m`, so
`ν_l = -Σ_{1≤m<l} (adamsCoeff l m · m!/l!) ν_m`, and for all `y`, `z`

  `γ_l H^{l+1} z = -(H^l ν_l y - H^{l+1}/(l+1)! z)
        - Σ_{1≤m<l} (adamsCoeff l m · m!/l!) (H^l ν_m y - H^{l+1}/(m+1)! z)`.

**Step 3** (`memory_bounded_apply`). For `v ∈ unseen l` and `m < l`, `A^{l-m} v ∈ unseen m`;
Step 1 there, Step 1 at `m = l` and Step 2 with `y = A^l v`, `z = P A^{l+1} v` give, with
`β_m = |adamsCoeff l m| m!/l!` (`memBeta`) and `t = ‖𝒯‖`,

  `γ_l H^{l+1} ‖P A^{l+1} v‖ ≤ ((1 + Σ_m β_m x^{l-m}) t + e_l + Σ_m β_m x^{l-m} e_m) ‖v‖`,

which is inequality (bounded) of the report; `memory_bounded` is the same for `c_i`.

**The paper's form** (`memory_lead`): for `x = H ‖A‖ ≤ 1`,

  `(1 + b_l H ‖A‖) ‖𝒯‖ ≥ γ_l c_i H^{l+1} - (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2}`

with `b_l = Σ_m β_m` (`memB`), `C_1 = ε_l + Σ_m β_m ε_m`, `ε_m = Σ_{p≥m+2} 1/p!` (`memC1`),
`C_2 = ς_l + Σ_m β_m ς_m`, `ς_m = Σ_{r<l} Σ_{p≥m+1} r^p/p!` (`memC2`). For `l = 1`:
`γ = 1/2`, `b = 0`, `C_1 = e - 5/2`, `C_2 = 0` (`memory_lead_one`); for `l = 2`: `γ = 5/12`,
`b = β_1 = 1/2`, `C_1 = 3e/2 - 47/12`, `C_2 = 3e/2 - 7/2` (`memory_lead_two`).

Not in this file: the converse of Theorem 4.10 (a rule with coefficients `O(H)` and defect
`O(H^{l+2})` when `c_i = 0`), and rows that run after their partners.
-/
import CoSimFoundations.AdamsConstants

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Filtration

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The states that subsystem `i` is not shown up to the order `m`: `P v = 0` and
`C (A^q v) = 0` for `q < m` (the paper's `𝒱^{[m]}`; `𝒱_i^0` is the case `m = l`). -/
def unseen (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (m : ℕ) : Submodule ℝ E where
  carrier := {v | P v = 0 ∧ ∀ q < m, C ((A ^ q) v) = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add, ha, hb, add_zero], fun q hq => ?_⟩
    rw [map_add, map_add, ha' q hq, hb' q hq, add_zero]
  zero_mem' := ⟨map_zero P, fun q _ => by rw [map_zero, map_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨by rw [map_smul, ha, smul_zero], fun q hq => ?_⟩
    rw [map_smul, map_smul, ha' q hq, smul_zero]

/-- Membership in the space of states not shown. -/
theorem mem_unseen {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {m : ℕ} {v : E} :
    v ∈ unseen P C A m ↔ P v = 0 ∧ ∀ q < m, C ((A ^ q) v) = 0 :=
  Iff.rfl

/-- `A^{q+1} v = A^q (A v)`. -/
theorem pow_succ_apply' (A : E →L[ℝ] E) (q : ℕ) (v : E) : (A ^ (q + 1)) v = (A ^ q) (A v) := by
  rw [pow_succ]
  rfl

/-- `A^{p+q} v = A^p (A^q v)`. -/
theorem pow_add_apply' (A : E →L[ℝ] E) (p q : ℕ) (v : E) :
    (A ^ (p + q)) v = (A ^ p) ((A ^ q) v) := by
  rw [pow_add]
  rfl

variable {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- **Filtration (i):** `A` maps the states not shown up to the order `m + 1` into those not
shown up to the order `m`. -/
theorem map_mem_unseen (hA : P ∘L A = Ai ∘L P + L ∘L C) {m : ℕ} {v : E}
    (hv : v ∈ unseen P C A (m + 1)) : A v ∈ unseen P C A m := by
  obtain ⟨hP, hC⟩ := mem_unseen.1 hv
  refine mem_unseen.2 ⟨?_, fun q hq => ?_⟩
  · have h : P (A v) = Ai (P v) + L (C v) := by
      have h' := congrArg (fun T : E →L[ℝ] F => T v) hA
      simpa using h'
    have hC0 : C v = 0 := by simpa using hC 0 (Nat.succ_pos m)
    rw [h, hP, hC0, map_zero, map_zero, add_zero]
  · rw [← pow_succ_apply']
    exact hC (q + 1) (by omega)

/-- **Filtration (i), iterated:** `A^j` maps `unseen (m + j)` into `unseen m`. -/
theorem pow_mem_unseen (hA : P ∘L A = Ai ∘L P + L ∘L C) {m : ℕ} (j : ℕ) {v : E}
    (hv : v ∈ unseen P C A (m + j)) : (A ^ j) v ∈ unseen P C A m := by
  induction j generalizing v with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ_apply']
    exact ih (map_mem_unseen hA (show v ∈ unseen P C A (m + j + 1) from hv))

/-- **Filtration (ii):** `P A^p v = 0` for `v` not shown up to the order `m` and `p ≤ m`. -/
theorem proj_pow_eq_zero (hA : P ∘L A = Ai ∘L P + L ∘L C) {m p : ℕ} (hp : p ≤ m) {v : E}
    (hv : v ∈ unseen P C A m) : P ((A ^ p) v) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hv' : v ∈ unseen P C A (j + p) := by rwa [add_comm] at hv
  exact (mem_unseen.1 (pow_mem_unseen hA p hv')).1

/-- The `p`-th moment of the coefficients of the samples, applied to a state:
`ν_p y = Σ_{r<l} ((-r)^p / p!) g r (C y)`. -/
noncomputable def moment (g : ℕ → G →L[ℝ] F) (C : E →L[ℝ] G) (l p : ℕ) (y : E) : F :=
  ∑ r ∈ range l, ((-(r : ℝ)) ^ p / (p ! : ℝ)) • g r (C y)

/-- **Step 2, the moments:** with `l` samples the `l`-th moment is a fixed combination of the
lower ones, `ν_l = -Σ_{1≤m<l} (adamsCoeff l m · m!/l!) ν_m`. -/
theorem moment_top (g : ℕ → G →L[ℝ] F) (C : E →L[ℝ] G) {l : ℕ} (hl : 1 ≤ l) (y : E) :
    moment g C l l y =
      -∑ m ∈ Ico 1 l, (adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)) • moment g C l m y := by
  unfold moment
  simp only [smul_sum, smul_smul]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun r hr => ?_
  rw [← sum_smul, ← neg_smul, neg_pow_eq_neg_sum hl (mem_range.1 hr), neg_div, sum_div]
  congr 2
  refine sum_congr rfl fun m _ => ?_
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hl' : (l ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- A weighted sum of vectors `h μ_m - b_m z`. -/
theorem sum_smul_smul_sub (s : Finset ℕ) (a b : ℕ → ℝ) (h : ℝ) (μ : ℕ → F) (z : F) :
    ∑ m ∈ s, a m • (h • μ m - b m • z) =
      h • ∑ m ∈ s, a m • μ m - (∑ m ∈ s, a m * b m) • z := by
  rw [smul_sum, sum_smul, ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [smul_sub, smul_comm (a m) h, mul_smul]

/-- The constant `γ_l` in terms of the coefficients of the node polynomial:
`γ_l h = h/(l+1)! + Σ_{1≤m<l} (adamsCoeff l m · m!/l!) h/(m+1)!`. -/
theorem adamsGamma_mul {l : ℕ} (hl : 1 ≤ l) (h : ℝ) :
    adamsGamma l * h = h / ((l + 1)! : ℝ) +
      ∑ m ∈ Ico 1 l, adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ) * (h / ((m + 1)! : ℝ)) := by
  have hl' : (l ! : ℝ) ≠ 0 := by positivity
  have hsum : ∑ m ∈ Ico 1 l, adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ) * (h / ((m + 1)! : ℝ)) =
      (l ! : ℝ)⁻¹ * h * ∑ m ∈ Ico 1 l, adamsCoeff l m / ((m : ℝ) + 1) := by
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    have hm : (m ! : ℝ) ≠ 0 := by positivity
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hl1 : (l : ℝ) + 1 ≠ 0 := by positivity
  unfold adamsGamma
  rw [hsum, sum_range_succ_split _ hl, adamsCoeff_zero hl, adamsCoeff_self, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **Step 2 of the proof of Theorem 4.10, for every `l ≥ 1`:** the identity for the top moment
from the node polynomial, in the form used in Step 3 (`y = A^l v`, `z = P A^{l+1} v`). -/
theorem gamma_identity (g : ℕ → G →L[ℝ] F) (C : E →L[ℝ] G) {l : ℕ} (hl : 1 ≤ l) (H : ℝ) (y : E)
    (z : F) :
    (adamsGamma l * H ^ (l + 1)) • z =
      -(H ^ l • moment g C l l y - (H ^ (l + 1) / ((l + 1)! : ℝ)) • z) -
        ∑ m ∈ Ico 1 l, (adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)) •
          (H ^ l • moment g C l m y - (H ^ (l + 1) / ((m + 1)! : ℝ)) • z) := by
  rw [sum_smul_smul_sub (Ico 1 l) (fun m => adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ))
    (fun m => H ^ (l + 1) / ((m + 1)! : ℝ)) (H ^ l) (fun m => moment g C l m y) z,
    adamsGamma_mul hl, add_smul, moment_top g C hl y, smul_neg]
  abel

end Filtration

section Taylor

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The Taylor polynomial of `exp (c • A) v` with the tail of the series as remainder. -/
theorem exists_exp_smul_apply_eq (A : E →L[ℝ] E) (c : ℝ) {b : ℕ} (hb : 0 < b) (v : E) :
    ∃ ρ : E, exp (c • A) v = ∑ n ∈ range b, ((n ! : ℝ)⁻¹ * c ^ n) • (A ^ n) v + ρ ∧
      ‖ρ‖ ≤ expTail b (|c| * ‖A‖) * ‖v‖ := by
  refine ⟨(exp (c • A) - ∑ n ∈ range b, ((n ! : ℝ)⁻¹) • (c • A) ^ n) v, ?_, ?_⟩
  · have h : (∑ n ∈ range b, ((n ! : ℝ)⁻¹) • (c • A) ^ n) v =
        ∑ n ∈ range b, ((n ! : ℝ)⁻¹ * c ^ n) • (A ^ n) v := by
      simp [smul_pow, smul_smul]
    rw [← h]
    simp
  · have h := norm_exp_sub_sum_le_expTail (c • A) hb
    rw [norm_smul, Real.norm_eq_abs] at h
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))

variable {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- The own state after one step of the reference, for a state not shown up to the order `m`:
`P U v = H^{m+1}/(m+1)! P A^{m+1} v + ρ` with `‖ρ‖ ≤ Σ_{p≥m+2} x^p/p! ‖v‖`. -/
theorem exists_proj_exp_apply_eq (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) {H : ℝ}
    (hH : 0 ≤ H) {m : ℕ} {v : E} (hv : v ∈ unseen P C A m) :
    ∃ ρ : F, P (exp (H • A) v) = (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v) + ρ ∧
      ‖ρ‖ ≤ expTail (m + 2) (H * ‖A‖) * ‖v‖ := by
  obtain ⟨ρ, h1, h2⟩ := exists_exp_smul_apply_eq A H (b := m + 2) (by omega) v
  rw [abs_of_nonneg hH] at h2
  refine ⟨P ρ, ?_, ?_⟩
  · rw [h1, map_add, map_sum, sum_range_succ, sum_eq_zero, zero_add, map_smul]
    · congr 2
      rw [div_eq_inv_mul]
    · intro n hn
      rw [map_smul, proj_pow_eq_zero hA (by have := mem_range.1 hn; omega) hv, smul_zero]
  · calc ‖P ρ‖ ≤ ‖P‖ * ‖ρ‖ := P.le_opNorm ρ
      _ ≤ 1 * ‖ρ‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ expTail (m + 2) (H * ‖A‖) * ‖v‖ := by rw [one_mul]; exact h2

/-- The sample of age `r` of the reference, for a state not shown up to the order `m`:
`T C U^{-r} v = H^m ((-r)^m/m!) T C A^m v + ρ` with `‖ρ‖ ≤ ‖T ∘ C‖ Σ_{p≥m+1} (r x)^p/p! ‖v‖`. -/
theorem exists_sample_apply_eq (T : G →L[ℝ] F) {H : ℝ} (hH : 0 ≤ H) {m : ℕ} {v : E}
    (hv : v ∈ unseen P C A m) (r : ℕ) :
    ∃ ρ : F, T (C ((exp (-(H • A)) ^ r) v)) =
        (H ^ m * ((-(r : ℝ)) ^ m / (m ! : ℝ))) • T (C ((A ^ m) v)) + ρ ∧
      ‖ρ‖ ≤ ‖T ∘L C‖ * (expTail (m + 1) (r * (H * ‖A‖)) * ‖v‖) := by
  have hpow : exp (-(H • A)) ^ r = exp ((-(r * H)) • A) := by
    let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_neg, smul_smul, neg_smul]
  obtain ⟨ρ, h1, h2⟩ := exists_exp_smul_apply_eq A (-(r * H)) (b := m + 1) (by omega) v
  rw [abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg r) hH), mul_assoc] at h2
  obtain ⟨-, hC⟩ := mem_unseen.1 hv
  refine ⟨(T ∘L C) ρ, ?_, ?_⟩
  · change (T ∘L C) ((exp (-(H • A)) ^ r) v) = _
    rw [hpow, h1, map_add, map_sum, sum_range_succ, sum_eq_zero, zero_add, map_smul,
      ContinuousLinearMap.comp_apply]
    · congr 2
      ring
    · intro n hn
      rw [map_smul, ContinuousLinearMap.comp_apply, hC n (mem_range.1 hn), map_zero, smul_zero]
  · exact ((T ∘L C).le_opNorm ρ).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

/-- The local defect of the rule of a subsystem that runs before all of its partners with `l`
held samples (eq. `eq:localdefect`): `𝒯 = P U - Fi P - Σ_{r<l} g r C U^{-r}`, `U = exp (H • A)`. -/
noncomputable def localDefect (P : E →L[ℝ] F) (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F)
    (C : E →L[ℝ] G) (A : E →L[ℝ] E) (H : ℝ) (l : ℕ) : E →L[ℝ] F :=
  P ∘L exp (H • A) - Fi ∘L P - ∑ r ∈ range l, (g r ∘L C) ∘L (exp (-(H • A)) ^ r)

/-- The remainder of Step 1: `e_m = Σ_{p≥m+2} x^p/p! + w H Σ_{r<l} Σ_{p≥m+1} (r x)^p/p!`. -/
noncomputable def memE (l m : ℕ) (w H x : ℝ) : ℝ :=
  expTail (m + 2) x + w * H * ∑ r ∈ range l, expTail (m + 1) (r * x)

/-- The remainder of Step 1 is nonnegative. -/
theorem memE_nonneg (l m : ℕ) {w H x : ℝ} (hw : 0 ≤ w) (hH : 0 ≤ H) (hx : 0 ≤ x) :
    0 ≤ memE l m w H x :=
  add_nonneg (expTail_nonneg _ hx) (mul_nonneg (mul_nonneg hw hH)
    (sum_nonneg fun r _ => expTail_nonneg _ (mul_nonneg (Nat.cast_nonneg r) hx)))

/-- **Step 1 of the proof of Theorem 4.10** (report, inequality (key)): on the states not shown
up to the order `m`, the `m`-th moment of the coefficients is forced to its Adams value up to
the local defect: `‖H^m ν_m A^m v - H^{m+1}/(m+1)! P A^{m+1} v‖ ≤ (‖𝒯‖ + e_m) ‖v‖`. -/
theorem memory_key_step (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) {l : ℕ}
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) {m : ℕ} {v : E}
    (hv : v ∈ unseen P C A m) :
    ‖H ^ m • moment g C l m ((A ^ m) v) -
        (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v)‖ ≤
      (‖localDefect P Fi g C A H l‖ + memE l m w H (H * ‖A‖)) * ‖v‖ := by
  obtain ⟨ρ0, h0, hρ0⟩ := exists_proj_exp_apply_eq hA hP hH hv
  choose ρ h1 hρ using fun r => exists_sample_apply_eq (g r) hH hv r
  obtain ⟨hPv, -⟩ := mem_unseen.1 hv
  have hT : localDefect P Fi g C A H l v =
      (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v) + ρ0 -
        H ^ m • moment g C l m ((A ^ m) v) - ∑ r ∈ range l, ρ r := by
    unfold localDefect moment
    simp only [_root_.sub_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]
    rw [h0, hPv, map_zero, sub_zero, sum_congr rfl fun r _ => h1 r, sum_add_distrib, smul_sum]
    simp only [smul_smul]
    abel
  have hkey : H ^ m • moment g C l m ((A ^ m) v) -
      (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (m + 1)) v) =
      ρ0 - localDefect P Fi g C A H l v - ∑ r ∈ range l, ρ r := by
    rw [hT]
    abel
  rw [hkey]
  have hsum : ‖∑ r ∈ range l, ρ r‖ ≤
      ∑ r ∈ range l, w * H * (expTail (m + 1) (r * (H * ‖A‖)) * ‖v‖) := by
    refine norm_sum_le_of_le _ fun r hr => (hρ r).trans ?_
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [expTail_zero]
    · exact mul_le_mul_of_nonneg_right (hw r hr0 (mem_range.1 hr))
        (mul_nonneg (expTail_nonneg _ (by positivity)) (norm_nonneg _))
  have h5 : ∑ r ∈ range l, w * H * (expTail (m + 1) (r * (H * ‖A‖)) * ‖v‖) =
      w * H * (∑ r ∈ range l, expTail (m + 1) (r * (H * ‖A‖))) * ‖v‖ := by
    rw [mul_sum, sum_mul]
    exact sum_congr rfl fun r _ => by ring
  have hTv := (localDefect P Fi g C A H l).le_opNorm v
  have h3 := norm_sub_le (ρ0 - localDefect P Fi g C A H l v) (∑ r ∈ range l, ρ r)
  have h4 := norm_sub_le ρ0 (localDefect P Fi g C A H l v)
  unfold memE
  rw [h5] at hsum
  linarith

end Taylor

section Constants

/-- `β_m = |adamsCoeff l m| m!/l!`, the weight of the `m`-th moment in the `l`-th. -/
noncomputable def memBeta (l m : ℕ) : ℝ :=
  |adamsCoeff l m| * (m ! : ℝ) / (l ! : ℝ)

/-- `β_m ≥ 0`. -/
theorem memBeta_nonneg (l m : ℕ) : 0 ≤ memBeta l m := by
  unfold memBeta
  positivity

/-- `β_m` is the absolute value of the coefficient in Step 2. -/
theorem abs_adamsCoeff_mul_div (l m : ℕ) :
    |adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)| = memBeta l m := by
  unfold memBeta
  rw [abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]

/-- The constant `b_l = Σ_{1≤m<l} β_m` of `eq:memorylead`. -/
noncomputable def memB (l : ℕ) : ℝ :=
  ∑ m ∈ Ico 1 l, memBeta l m

/-- The constant `C_1 = ε_l + Σ_{1≤m<l} β_m ε_m`, `ε_m = Σ_{p≥m+2} 1/p!`, of `eq:memorylead`. -/
noncomputable def memC1 (l : ℕ) : ℝ :=
  expTail (l + 2) 1 + ∑ m ∈ Ico 1 l, memBeta l m * expTail (m + 2) 1

/-- The constant `C_2 = ς_l + Σ_{1≤m<l} β_m ς_m`, `ς_m = Σ_{r<l} Σ_{p≥m+1} r^p/p!`, of
`eq:memorylead`. -/
noncomputable def memC2 (l : ℕ) : ℝ :=
  ∑ r ∈ range l, expTail (l + 1) r +
    ∑ m ∈ Ico 1 l, memBeta l m * ∑ r ∈ range l, expTail (m + 1) r

/-- `b_l ≥ 0`. -/
theorem memB_nonneg (l : ℕ) : 0 ≤ memB l :=
  sum_nonneg fun m _ => memBeta_nonneg l m

/-- `C_1 ≥ 0`. -/
theorem memC1_nonneg (l : ℕ) : 0 ≤ memC1 l :=
  add_nonneg (expTail_nonneg _ zero_le_one) (sum_nonneg fun m _ =>
    mul_nonneg (memBeta_nonneg l m) (expTail_nonneg _ zero_le_one))

/-- `C_2 ≥ 0`. -/
theorem memC2_nonneg (l : ℕ) : 0 ≤ memC2 l :=
  add_nonneg (sum_nonneg fun r _ => expTail_nonneg _ (Nat.cast_nonneg r))
    (sum_nonneg fun m _ => mul_nonneg (memBeta_nonneg l m)
      (sum_nonneg fun r _ => expTail_nonneg _ (Nat.cast_nonneg r)))

/-- The remainder of Step 1 for `x ≤ 1`: `e_m ≤ ε_m x^{m+2} + w H ς_m x^{m+1}`. -/
theorem memE_le (l m : ℕ) {w H x : ℝ} (hw : 0 ≤ w) (hH : 0 ≤ H) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    memE l m w H x ≤ expTail (m + 2) 1 * x ^ (m + 2) +
      w * H * (∑ r ∈ range l, expTail (m + 1) r) * x ^ (m + 1) := by
  have h1 : expTail (m + 2) x ≤ expTail (m + 2) 1 * x ^ (m + 2) := by
    have h := expTail_mul_le (m + 2) zero_le_one hx0 hx1
    rwa [one_mul, mul_comm] at h
  have h2 : ∑ r ∈ range l, expTail (m + 1) (r * x) ≤
      (∑ r ∈ range l, expTail (m + 1) r) * x ^ (m + 1) := by
    rw [sum_mul]
    refine sum_le_sum fun r _ => ?_
    have h := expTail_mul_le (m + 1) (Nat.cast_nonneg r) hx0 hx1
    rwa [mul_comm (x ^ (m + 1))] at h
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hw hH)
  unfold memE
  linarith

/-- If `c ‖R u‖ ≤ D ‖u‖` for all `u` and `D ≥ 0`, then `c ‖R‖ ≤ D`. -/
theorem mul_opNorm_le_of_forall {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (R : V →L[ℝ] W) {c D : ℝ} (hD : 0 ≤ D)
    (h : ∀ u, c * ‖R u‖ ≤ D * ‖u‖) : c * ‖R‖ ≤ D := by
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg _)).trans hD
  · have h1 : ‖R‖ ≤ D / c := by
      refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hD hc.le) fun u => ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm]
      exact h u
    rw [le_div_iff₀ hc] at h1
    linarith

end Constants

section Main

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- **Theorem B of the report, inequality (bounded), on a state not shown** (Steps 1 to 3 of the
proof of Theorem 4.10, every `l ≥ 1`). For `v` with `P v = 0` and `C A^q v = 0`, `q < l`:
`γ_l H^{l+1} ‖P A^{l+1} v‖ ≤ ((1 + Σ_m β_m x^{l-m}) ‖𝒯‖ + e_l + Σ_m β_m x^{l-m} e_m) ‖v‖`,
sums over `1 ≤ m < l`, `x = H ‖A‖`. -/
theorem memory_bounded_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) {l : ℕ} (hl : 1 ≤ l)
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) {v : E} (hv : v ∈ unseen P C A l) :
    adamsGamma l * H ^ (l + 1) * ‖P ((A ^ (l + 1)) v)‖ ≤
      ((1 + ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m)) * ‖localDefect P Fi g C A H l‖ +
        memE l l w H (H * ‖A‖) +
        ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) * memE l m w H (H * ‖A‖)) * ‖v‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have ht0 : 0 ≤ ‖localDefect P Fi g C A H l‖ := norm_nonneg _
  have hkl := memory_key_step hA hP Fi g hH hw hv
  have hkm : ∀ m ∈ Ico 1 l,
      ‖H ^ l • moment g C l m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v)‖ ≤
      (H * ‖A‖) ^ (l - m) * (‖localDefect P Fi g C A H l‖ + memE l m w H (H * ‖A‖)) * ‖v‖ := by
    intro m hm
    obtain ⟨-, hml⟩ := mem_Ico.1 hm
    have hv' : (A ^ (l - m)) v ∈ unseen P C A m :=
      pow_mem_unseen hA (l - m) (by rwa [Nat.add_sub_cancel' hml.le])
    have h := memory_key_step hA hP Fi g hH hw hv'
    rw [← pow_add_apply', ← pow_add_apply', Nat.add_sub_cancel' hml.le,
      (by omega : m + 1 + (l - m) = l + 1)] at h
    have he : H ^ l • moment g C l m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v) =
        H ^ (l - m) • (H ^ m • moment g C l m ((A ^ l) v) -
          (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v)) := by
      have e1 : H ^ (l - m) * H ^ m = H ^ l := by rw [← pow_add, Nat.sub_add_cancel hml.le]
      have e2 : H ^ (l - m) * (H ^ (m + 1) / ((m + 1)! : ℝ)) = H ^ (l + 1) / ((m + 1)! : ℝ) := by
        rw [← mul_div_assoc, ← pow_add, (by omega : l - m + (m + 1) = l + 1)]
      rw [smul_sub, smul_smul, smul_smul, e1, e2]
    have hvn : ‖(A ^ (l - m)) v‖ ≤ ‖A‖ ^ (l - m) * ‖v‖ :=
      ((A ^ (l - m)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_pow_le' A (by omega)) (norm_nonneg v))
    rw [he, norm_smul, Real.norm_of_nonneg (pow_nonneg hH _)]
    calc H ^ (l - m) * ‖H ^ m • moment g C l m ((A ^ l) v) -
          (H ^ (m + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v)‖
        ≤ H ^ (l - m) * ((‖localDefect P Fi g C A H l‖ + memE l m w H (H * ‖A‖)) *
            (‖A‖ ^ (l - m) * ‖v‖)) :=
          mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hvn
            (add_nonneg ht0 (memE_nonneg l m hw0 hH hx0)))) (pow_nonneg hH _)
      _ = (H * ‖A‖) ^ (l - m) * (‖localDefect P Fi g C A H l‖ + memE l m w H (H * ‖A‖)) *
            ‖v‖ := by
          rw [mul_pow]
          ring
  have hid := gamma_identity g C hl H ((A ^ l) v) (P ((A ^ (l + 1)) v))
  have hsum : ‖∑ m ∈ Ico 1 l, (adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)) •
      (H ^ l • moment g C l m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v))‖ ≤
      ∑ m ∈ Ico 1 l, memBeta l m * ((H * ‖A‖) ^ (l - m) *
        (‖localDefect P Fi g C A H l‖ + memE l m w H (H * ‖A‖)) * ‖v‖) := by
    refine norm_sum_le_of_le _ fun m hm => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_adamsCoeff_mul_div]
    exact mul_le_mul_of_nonneg_left (hkm m hm) (memBeta_nonneg l m)
  have hsumeq : ∑ m ∈ Ico 1 l, memBeta l m * ((H * ‖A‖) ^ (l - m) *
        (‖localDefect P Fi g C A H l‖ + memE l m w H (H * ‖A‖)) * ‖v‖) =
      ((∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m)) * ‖localDefect P Fi g C A H l‖ +
        ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) * memE l m w H (H * ‖A‖)) * ‖v‖ := by
    simp only [add_mul, sum_mul]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have h1 : adamsGamma l * H ^ (l + 1) * ‖P ((A ^ (l + 1)) v)‖ ≤
      ‖(adamsGamma l * H ^ (l + 1)) • P ((A ^ (l + 1)) v)‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have h2 := norm_sub_le (-(H ^ l • moment g C l l ((A ^ l) v) -
      (H ^ (l + 1) / ((l + 1)! : ℝ)) • P ((A ^ (l + 1)) v)))
    (∑ m ∈ Ico 1 l, (adamsCoeff l m * (m ! : ℝ) / (l ! : ℝ)) •
      (H ^ l • moment g C l m ((A ^ l) v) -
        (H ^ (l + 1) / ((m + 1)! : ℝ)) • P ((A ^ (l + 1)) v)))
  rw [← hid, norm_neg] at h2
  rw [hsumeq] at hsum
  linarith

/-- **Theorem B of the report, inequality (bounded)**, with
`c_i = ‖P A^{l+1}` restricted to the states not shown`‖`:
`γ_l H^{l+1} c_i ≤ (1 + Σ_m β_m x^{l-m}) ‖𝒯‖ + e_l + Σ_m β_m x^{l-m} e_m`. -/
theorem memory_bounded (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) {l : ℕ} (hl : 1 ≤ l)
    (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) :
    adamsGamma l * H ^ (l + 1) * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ ≤
      (1 + ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m)) * ‖localDefect P Fi g C A H l‖ +
        memE l l w H (H * ‖A‖) +
        ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) * memE l m w H (H * ‖A‖) := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hβ : 0 ≤ ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) :=
    sum_nonneg fun m _ => mul_nonneg (memBeta_nonneg l m) (pow_nonneg hx0 _)
  refine mul_opNorm_le_of_forall _ ?_ fun u => memory_bounded_apply hA hP Fi g hH hw0 hl hw u.2
  refine add_nonneg (add_nonneg (mul_nonneg (by linarith) (norm_nonneg _))
    (memE_nonneg l l hw0 hH hx0)) (sum_nonneg fun m _ => ?_)
  exact mul_nonneg (mul_nonneg (memBeta_nonneg l m) (pow_nonneg hx0 _))
    (memE_nonneg l m hw0 hH hx0)

/-- **Theorem 4.10, inequality `eq:memorylead`, on a state not shown**, for `H ‖A‖ ≤ 1`:
`γ_l H^{l+1} ‖P A^{l+1} v‖ ≤
  ((1 + b_l H ‖A‖) ‖𝒯‖ + (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2}) ‖v‖`. -/
theorem memory_lead_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) (hx1 : H * ‖A‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) {v : E}
    (hv : v ∈ unseen P C A l) :
    adamsGamma l * H ^ (l + 1) * ‖P ((A ^ (l + 1)) v)‖ ≤
      ((1 + memB l * (H * ‖A‖)) * ‖localDefect P Fi g C A H l‖ +
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2)) * ‖v‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have ht0 : 0 ≤ ‖localDefect P Fi g C A H l‖ := norm_nonneg _
  refine (memory_bounded_apply hA hP Fi g hH hw0 hl hw hv).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
  -- (a) the factor of the defect
  have ha : ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) ≤ memB l * (H * ‖A‖) := by
    unfold memB
    rw [sum_mul]
    refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (memBeta_nonneg l m)
    have h := pow_le_pow_of_le_one hx0 hx1 (by have := (mem_Ico.1 hm).2; omega : 1 ≤ l - m)
    rwa [pow_one] at h
  -- (b) the remainders
  have hb : ∑ m ∈ Ico 1 l, memBeta l m * (H * ‖A‖) ^ (l - m) * memE l m w H (H * ‖A‖) ≤
      ∑ m ∈ Ico 1 l, (memBeta l m * expTail (m + 2) 1 * (H * ‖A‖) ^ (l + 2) +
        memBeta l m * (∑ r ∈ range l, expTail (m + 1) r) * (w * H * (H * ‖A‖) ^ (l + 1))) := by
    refine sum_le_sum fun m hm => ?_
    have hml := (mem_Ico.1 hm).2
    have h := mul_le_mul_of_nonneg_left (memE_le l m hw0 hH hx0 hx1)
      (mul_nonneg (memBeta_nonneg l m) (pow_nonneg hx0 (l - m)))
    refine h.trans (le_of_eq ?_)
    have e1 : (H * ‖A‖) ^ (l - m) * (H * ‖A‖) ^ (m + 2) = (H * ‖A‖) ^ (l + 2) := by
      rw [← pow_add, (by omega : l - m + (m + 2) = l + 2)]
    have e2 : (H * ‖A‖) ^ (l - m) * (H * ‖A‖) ^ (m + 1) = (H * ‖A‖) ^ (l + 1) := by
      rw [← pow_add, (by omega : l - m + (m + 1) = l + 1)]
    rw [← e1, ← e2]
    ring
  have hc := memE_le l l hw0 hH hx0 hx1
  rw [sum_add_distrib, ← sum_mul, ← sum_mul] at hb
  have hmul := mul_le_mul_of_nonneg_right ha ht0
  unfold memC1 memC2
  have e3 : (H * ‖A‖) ^ (l + 2) = ‖A‖ ^ (l + 2) * H ^ (l + 2) := by rw [mul_pow, mul_comm]
  have e4 : w * H * (H * ‖A‖) ^ (l + 1) = w * ‖A‖ ^ (l + 1) * H ^ (l + 2) := by
    rw [mul_pow]
    ring
  rw [e3, e4] at hb
  rw [e3] at hc
  have e5 : w * H * (∑ r ∈ range l, expTail (l + 1) r) * (H * ‖A‖) ^ (l + 1) =
      (∑ r ∈ range l, expTail (l + 1) r) * (w * ‖A‖ ^ (l + 1) * H ^ (l + 2)) := by
    rw [mul_pow]
    ring
  rw [e5] at hc
  nlinarith [hb, hc, hmul]

/-- **Theorem 4.10 (one order per held sample), inequality `eq:memorylead`.** Let subsystem `i`
(projection `P`, `‖P‖ ≤ 1`, driven through its own state and the outputs `C` of its partners:
`P ∘ A = Ai ∘ P + L ∘ C`) run before all of its partners with `l ≥ 1` held samples, with
coefficients `‖g r ∘ C‖ ≤ w H` on the samples of the ages `1 ≤ r < l`; `Fi` and `g 0` are
arbitrary. Then, for `H ‖A‖ ≤ 1`,
`γ_l c_i H^{l+1} - (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1}) H^{l+2} ≤ (1 + b_l H ‖A‖) ‖𝒯‖`,
with `c_i` the norm of `P A^{l+1}` on the states not shown, `γ_l = adamsGamma l` and the
constants `b_l = memB l`, `C_1 = memC1 l`, `C_2 = memC2 l`, which depend on `l` only. -/
theorem memory_lead (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) (hx1 : H * ‖A‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) (hw : ∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) :
    adamsGamma l * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) -
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) ≤
      (1 + memB l * (H * ‖A‖)) * ‖localDefect P Fi g C A H l‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have hD : 0 ≤ (1 + memB l * (H * ‖A‖)) * ‖localDefect P Fi g C A H l‖ +
      (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) := by
    have h1 := memB_nonneg l
    have h2 := memC1_nonneg l
    have h3 := memC2_nonneg l
    positivity
  have h := mul_opNorm_le_of_forall ((P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL) hD
    fun u => memory_lead_apply hA hP Fi g hH hw0 hx1 hl hw u.2
  linarith

/-- `b_1 = 0`. -/
theorem memB_one : memB 1 = 0 := by
  simp [memB]

/-- `C_1 = e - 5/2` for one held sample. -/
theorem memC1_one : memC1 1 = Real.exp 1 - 5 / 2 := by
  simp [memC1, expTail_three_one]

/-- `C_2 = 0` for one held sample. -/
theorem memC2_one : memC2 1 = 0 := by
  simp [memC2, expTail_zero]

/-- `β_1 = 1/2` for two held samples. -/
theorem memBeta_two_one : memBeta 2 1 = 1 / 2 := by
  simp [memBeta, adamsCoeff_two_one, Nat.factorial]

/-- `b_2 = 1/2`. -/
theorem memB_two : memB 2 = 1 / 2 := by
  have hI : Ico 1 2 = ({1} : Finset ℕ) := by decide
  simp [memB, hI, memBeta_two_one]

/-- `C_1 = 3e/2 - 47/12` for two held samples. -/
theorem memC1_two : memC1 2 = 3 / 2 * Real.exp 1 - 47 / 12 := by
  have hI : Ico 1 2 = ({1} : Finset ℕ) := by decide
  simp [memC1, hI, memBeta_two_one, expTail_three_one, expTail_four_one]
  ring

/-- `C_2 = 3e/2 - 7/2` for two held samples. -/
theorem memC2_two : memC2 2 = 3 / 2 * Real.exp 1 - 7 / 2 := by
  have hI : Ico 1 2 = ({1} : Finset ℕ) := by decide
  simp [memC2, hI, memBeta_two_one, sum_range_succ, expTail_zero, expTail_two_one,
    expTail_three_one]
  ring

/-- **Theorem 4.10 for one held sample** (the paper's Corollary 4.3 (i) with its remainder): for
`H ‖A‖ ≤ 1`, `½ c_i H² - (e - 5/2) ‖A‖³ H³ ≤ ‖𝒯‖`, with `c_i` the norm of `P A²` on the states
with `P v = 0`, `C v = 0`. Every coefficient of the rule is arbitrary. -/
theorem memory_lead_one (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H : ℝ} (hH : 0 ≤ H) (hx1 : H * ‖A‖ ≤ 1) :
    1 / 2 * ‖(P ∘L (A ^ 2)) ∘L (unseen P C A 1).subtypeL‖ * H ^ 2 -
        (Real.exp 1 - 5 / 2) * ‖A‖ ^ 3 * H ^ 3 ≤ ‖localDefect P Fi g C A H 1‖ := by
  have h := memory_lead hA hP Fi g hH (le_refl (0 : ℝ)) hx1 (le_refl 1)
    (fun r h1 h2 => absurd h1 (by omega))
  rw [adamsGamma_one, memB_one, memC1_one, memC2_one] at h
  norm_num at h
  linarith

/-- **Theorem 4.10 for two held samples**, with explicit constants (`γ_2 = 5/12`, `β_1 = 1/2`):
if the coefficient of the past sample satisfies `‖g 1 ∘ C‖ ≤ w H`, then for `H ‖A‖ ≤ 1`,
`(5/12) c_i H³ - ((3e/2 - 47/12) ‖A‖⁴ + (3e/2 - 7/2) w ‖A‖³) H⁴ ≤ (1 + ½ H ‖A‖) ‖𝒯‖`,
with `c_i` the norm of `P A³` on the states with `P v = 0`, `C v = 0`, `C A v = 0`. -/
theorem memory_lead_two (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (Fi : F →L[ℝ] F)
    (g : ℕ → G →L[ℝ] F) {H w : ℝ} (hH : 0 ≤ H) (hw0 : 0 ≤ w) (hx1 : H * ‖A‖ ≤ 1)
    (hw : ‖g 1 ∘L C‖ ≤ w * H) :
    5 / 12 * ‖(P ∘L (A ^ 3)) ∘L (unseen P C A 2).subtypeL‖ * H ^ 3 -
        ((3 / 2 * Real.exp 1 - 47 / 12) * ‖A‖ ^ 4 +
          (3 / 2 * Real.exp 1 - 7 / 2) * w * ‖A‖ ^ 3) * H ^ 4 ≤
      (1 + 1 / 2 * (H * ‖A‖)) * ‖localDefect P Fi g C A H 2‖ := by
  have hw' : ∀ r, 1 ≤ r → r < 2 → ‖g r ∘L C‖ ≤ w * H := by
    intro r h1 h2
    have hr : r = 1 := by omega
    rw [hr]
    exact hw
  have h := memory_lead hA hP Fi g hH hw0 hx1 (by norm_num : 1 ≤ 2) hw'
  rw [adamsGamma_two, memB_two, memC1_two, memC2_two] at h
  exact h

end Main

end CoSimFoundations
