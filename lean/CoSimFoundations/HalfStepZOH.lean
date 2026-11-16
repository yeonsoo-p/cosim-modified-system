/-
The half-step relation with the exact objects, and the zero-order hold
(the paper, Theorem "half a macro step", `thm:half`, equation (half), and the sentence
"For the zero-order hold the first two terms vanish"; the first equation of (staggered)).

`HalfStep` proves the relation in a Taylor normal form,
  `X - U = (F - 1 - H A₀ - ½H² A₀²) + (M + N - H A_c - ½H² A₀ A_c) + ½H² A_ς A + O(H³)`.
The paper prints it with the local maps and the coefficients of the zero-order hold,
  `X - U = (F - e^{H A₀}) + (G - G°) C + ½H² A_ς A + O(H³)`,   `G° C = (∫₀ᴴ e^{s A₀} ds) A_c`.
This module defines `G° C` and proves the printed form with an explicit constant.

**The coefficients of the zero-order hold.** No measure theory is used in the definition:
  `phiOne Z = Σ_j Z^j / (j+1)!`   (the function `φ₁` on real matrices, a series in the topology of
  the entries), `zohKernel A H = H • phiOne (H • A₀)`, `zohCoupling A H = zohKernel A H * A_c`.
* `opE_phiOne`: `opE (phiOne Z) = phi 1 (opE Z)`, the bridge to `Phi` (`φ_b` in a Banach algebra).
* `opE_zohKernel_eq_integral`, `zohKernel_apply_eq_integral`: the definition agrees with the
  integral, `zohKernel A H = ∫₀ᴴ e^{s A₀} ds`, as operators (Bochner integral) and entry by entry
  (from `moment_formula` with `a = 0` and the substitution `s ↦ H - s`).

**Bounds** (`H ≥ 0`, spectral norms, `α₀ = ‖A₀‖`, `γ = ‖A_c‖`):
* `norm_exp_blockDiag_bracket_le`: `‖e^{H A₀} - 1 - H A₀ - ½H² A₀²‖ ≤ α₀³/6 · e^{H α₀} · H³`
  (`norm_opE_exp_sub_quadratic_le`; `norm_local_bracket_le` of `HalfStep` is the same bound for a
  scheme with `F = e^{H A₀}`);
* `norm_zohCoupling_bracket_le`: `‖G°C - H A_c - ½H² A₀ A_c‖ ≤ α₀²γ/6 · e^{H α₀} · H³`.
  Proof: `φ₁(W) = 1 + W/2 + W² φ₃(W)` (`phi_one_eq`, from the recursion `phi_succ`) and
  `‖W² φ₃(W)‖ ≤ ‖W‖²/6 · e^{‖W‖}` (`norm_sq_mul_phi_three_le`, term by term:
  `(j+3)! ≥ 6 j!`), so `H φ₁(H Z) - H - ½H² Z = H (H Z)² φ₃(H Z)`.
  Here `γ ≤ ‖A‖ + α₀` (`norm_opE_coupling_le`).

**The relation as printed** (`Consistent.norm_half_step_zoh_le`, in the rows of a subsystem
`Consistent.half_step_zoh_row`): for a consistent scheme
  `‖X - U - (F - e^{H A₀}) - (M + N - G°C) - ½H² A_ς A‖ ≤ (√(card κ) C₃ + zohC α₀ γ H) H³`,
`C₃ = reactionC a b c ‖A‖ H` the constant of `HalfStep`, `zohC α₀ γ H = (α₀³/6 + α₀²γ/6) e^{H α₀}`.
**The zero-order hold** (`Consistent.norm_zoh_step_le`, `Consistent.zoh_step_row`): if
`F = e^{H A₀}` and `M + N = G°C`, then `‖X - U - ½H² A_ς A‖` has the same bound.

**The block pattern** (`zohCoupling_apply_eq_zero_of_same`,
`zohCoupling_apply_eq_zero_of_not_partner`): `G°C` has no entry inside a subsystem and, if `A`
has none between subsystems that are not partners, none there. Split by the stages
(`zohOld`, `zohNew`, `zohOld_add_zohNew`) it has the pattern that `HeldScheme` requires of `M`
and `N` (`zohOld_apply_eq_zero`, `zohNew_apply_eq_zero`).

**Staggered readout, the first equation** (`zoh_staggered`). Let the subsystems of stage `0` be
class `a` and the others class `b`, with no partners inside a class. With `P = firstMask` the
mask of class `a`, `A_a = P A` and `A_b = (1 - P) A` (the block rows of the two classes), a
scheme with `F = e^{H A₀}` and `M + N = G°C` has `X = e^{H A_b} e^{H A_a}`. Proof:
* in a Banach algebra, if `K D = 0` and `K K = 0` then `e^{D + K} = e^D + φ₁(D) K`
  (`exp_add_eq_of_mul_eq_zero`: `(D + K)^{j+1} = D^{j+1} + D^j K`), and for an idempotent `P`
  that commutes with `Z`, `e^{P Z} = 1 - P + P e^Z` and `φ₁(P Z) P = P φ₁(Z)`
  (`exp_proj_mul`, `phi_one_proj_mul`); hence `e^{H P A} = 1 - P + P (e^{H A₀} + G°C)` if `P`
  commutes with `A₀` and `P A_c P = 0` (`exp_smul_proj_mul_add`, `exp_smul_proj_mul`);
* `P N = 0`, `(1 - P) M = 0`, `N (1 - P) = 0`, so `N N = 0`, `X = F + M + N (F + M)`, and the
  product of the two exponentials is the same matrix (`staggered_algebra`).

**The zero-order hold as a scheme** (`zoh`): on the subsystems, partners and stages of a scheme
`S`, and for `A` without blocks between subsystems that are not partners, the `HeldScheme` with
`F = e^{H A₀}`, `M = zohOld`, `N = zohNew` and `X = (Σ_{k < B} N^k) (F + M)`, `B` larger than
every stage: `N^B = 0` because a product of `k` new samples descends `k` stages
(`pow_apply_eq_zero_of_stage`), so `X = F + M + N X` (`add_mul_geom_sum_mul`). The theorems above
apply to it (`zoh_X_staggered`, `norm_zoh_sub_le`).

Not formalised here: the constants `a`, `b`, `c` of the consistency of the zero-order hold
(`norm_zoh_sub_le` takes `(S.zoh A hA H).Consistent A U H a b c` as a hypothesis).
-/
import CoSimFoundations.HalfStep
import CoSimFoundations.BlockExp
import CoSimFoundations.Phi

open Matrix
open scoped RealInnerProductSpace Nat

namespace CoSimFoundations

/-! ### `φ₁` in a Banach algebra -/

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `e^Z = 1 + Z φ₁(Z)`. -/
theorem exp_eq_one_add_mul_phi_one (Z : 𝔸) : NormedSpace.exp Z = 1 + Z * phi 1 Z := by
  have h : phi 0 Z = (((0 ! : ℕ) : ℝ))⁻¹ • (1 : 𝔸) + Z * phi 1 Z := phi_succ 0 Z
  rwa [phi_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul] at h

/-- `φ₁(W) = 1 + W/2 + W² φ₃(W)`. -/
theorem phi_one_eq (W : 𝔸) : phi 1 W = 1 + (2 : ℝ)⁻¹ • W + W * W * phi 3 W := by
  have h1 : phi 1 W = (((1 ! : ℕ) : ℝ))⁻¹ • (1 : 𝔸) + W * phi 2 W := phi_succ 1 W
  have h2 : phi 2 W = (((2 ! : ℕ) : ℝ))⁻¹ • (1 : 𝔸) + W * phi 3 W := phi_succ 2 W
  have f1 : ((1 ! : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have f2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [f1, inv_one, one_smul] at h1
  rw [f2] at h2
  rw [h1, h2, mul_add, mul_smul_comm, mul_one, mul_assoc, add_assoc]

/-- `‖W² φ₃(W)‖ ≤ ‖W‖²/6 · e^{‖W‖}`: term by term, `‖W^{j+2}‖/(j+3)! ≤ ‖W‖²/6 · ‖W‖^j/j!`. -/
theorem norm_sq_mul_phi_three_le (W : 𝔸) :
    ‖W * W * phi 3 W‖ ≤ ‖W‖ ^ 2 / 6 * Real.exp ‖W‖ := by
  have hs : HasSum (fun j : ℕ => W * W * ((((j + 3)! : ℕ) : ℝ)⁻¹ • W ^ j))
      (W * W * phi 3 W) := (summable_phi 3 W).hasSum.mul_left (W * W)
  have hg : HasSum (fun j : ℕ => ‖W‖ ^ 2 / 6 * (‖W‖ ^ j / (j ! : ℝ)))
      (‖W‖ ^ 2 / 6 * Real.exp ‖W‖) := by
    have h : HasSum (fun j : ℕ => ‖W‖ ^ j / (j ! : ℝ)) (Real.exp ‖W‖) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp ‖W‖
    exact h.mul_left _
  refine hs.norm_le_of_bounded hg fun j => ?_
  show ‖W * W * ((((j + 3)! : ℕ) : ℝ)⁻¹ • W ^ j)‖ ≤ ‖W‖ ^ 2 / 6 * (‖W‖ ^ j / (j ! : ℝ))
  have e : W * W * ((((j + 3)! : ℕ) : ℝ)⁻¹ • W ^ j) = (((j + 3)! : ℕ) : ℝ)⁻¹ • W ^ (j + 2) := by
    rw [mul_smul_comm, ← sq, ← pow_add, add_comm 2 j]
  have h1 : ‖W ^ (j + 2)‖ ≤ ‖W‖ ^ j * ‖W‖ ^ 2 := by
    rw [← pow_add]
    exact norm_pow_le' W (by omega)
  have h2 : (j ! : ℝ) * 6 ≤ (((j + 3)! : ℕ) : ℝ) := by
    have h := Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add j 3)
    have h6 : (3 ! : ℕ) = 6 := by norm_num [Nat.factorial]
    rw [h6] at h
    exact_mod_cast h
  have hj : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  rw [e, norm_smul, norm_inv, Real.norm_natCast]
  calc ((((j + 3)! : ℕ) : ℝ))⁻¹ * ‖W ^ (j + 2)‖
      ≤ ((j ! : ℝ) * 6)⁻¹ * (‖W‖ ^ j * ‖W‖ ^ 2) := by gcongr
    _ = ‖W‖ ^ 2 / 6 * (‖W‖ ^ j / (j ! : ℝ)) := by field_simp

/-- **The second-order remainder of the kernel of the zero-order hold.** For `H ≥ 0`,
`‖H φ₁(H Z) - H - ½H² Z‖ ≤ ‖Z‖²/6 · e^{H‖Z‖} · H³`. -/
theorem norm_smul_phi_one_sub_le (Z : 𝔸) {H : ℝ} (hH : 0 ≤ H) :
    ‖H • phi 1 (H • Z) - H • (1 : 𝔸) - (H ^ 2 / 2) • Z‖ ≤
      ‖Z‖ ^ 2 / 6 * Real.exp (H * ‖Z‖) * H ^ 3 := by
  have e2 : H • ((2 : ℝ)⁻¹ • (H • Z)) = (H ^ 2 / 2) • Z := by
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have e : H • phi 1 (H • Z) - H • (1 : 𝔸) - (H ^ 2 / 2) • Z =
      H • (H • Z * (H • Z) * phi 3 (H • Z)) := by
    rw [phi_one_eq (H • Z), smul_add, smul_add, e2]
    abel
  have h := norm_sq_mul_phi_three_le (H • Z)
  rw [norm_smul, Real.norm_of_nonneg hH] at h
  rw [e, norm_smul, Real.norm_of_nonneg hH]
  calc H * ‖H • Z * (H • Z) * phi 3 (H • Z)‖
      ≤ H * ((H * ‖Z‖) ^ 2 / 6 * Real.exp (H * ‖Z‖)) := mul_le_mul_of_nonneg_left h hH
    _ = ‖Z‖ ^ 2 / 6 * Real.exp (H * ‖Z‖) * H ^ 3 := by ring

/-- `H φ₁(H Z) = ∫₀ᴴ e^{s Z} ds` (`moment_formula` with `a = 0`, and `s ↦ H - s`). -/
theorem smul_phi_one_eq_integral (Z : 𝔸) (H : ℝ) :
    H • phi 1 (H • Z) = ∫ s in (0 : ℝ)..H, NormedSpace.exp (s • Z) := by
  have h := moment_formula Z H 0
  simp only [pow_zero, one_smul, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add,
    pow_one] at h
  have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := H)
    (fun s : ℝ => NormedSpace.exp (s • Z)) H
  rw [sub_self, sub_zero] at h2
  rw [← h]
  exact h2

/-- If `K D = 0` and `K K = 0`, then `e^{D + K} = e^D + φ₁(D) K`: the powers are
`(D + K)^{j+1} = D^{j+1} + D^j K`. -/
theorem exp_add_eq_of_mul_eq_zero {D K : 𝔸} (hKD : K * D = 0) (hKK : K * K = 0) :
    NormedSpace.exp (D + K) = NormedSpace.exp D + phi 1 D * K := by
  have hpow : ∀ j : ℕ, (D + K) ^ (j + 1) = D ^ (j + 1) + D ^ j * K := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_mul, zero_add, pow_one, pow_one]
    | succ j ih =>
      calc (D + K) ^ (j + 1 + 1) = (D ^ (j + 1) + D ^ j * K) * (D + K) := by rw [pow_succ, ih]
        _ = D ^ (j + 1) * D + D ^ (j + 1) * K + D ^ j * (K * D) + D ^ j * (K * K) := by
            simp only [mul_add, add_mul, mul_assoc]
            abel
        _ = D ^ (j + 1 + 1) + D ^ (j + 1) * K := by
            rw [hKD, hKK, mul_zero, add_zero, add_zero, ← pow_succ]
  have h1 : HasSum (fun j : ℕ => (D + K) * ((((j + 1)! : ℕ) : ℝ)⁻¹ • (D + K) ^ j))
      ((D + K) * phi 1 (D + K)) := (summable_phi 1 (D + K)).hasSum.mul_left _
  have h2 : HasSum (fun j : ℕ => D * ((((j + 1)! : ℕ) : ℝ)⁻¹ • D ^ j)) (D * phi 1 D) :=
    (summable_phi 1 D).hasSum.mul_left _
  have h3 : HasSum (fun j : ℕ => ((((j + 1)! : ℕ) : ℝ)⁻¹ • D ^ j) * K) (phi 1 D * K) :=
    (summable_phi 1 D).hasSum.mul_right _
  have e : (fun j : ℕ => (D + K) * ((((j + 1)! : ℕ) : ℝ)⁻¹ • (D + K) ^ j)) =
      fun j : ℕ => D * ((((j + 1)! : ℕ) : ℝ)⁻¹ • D ^ j) + ((((j + 1)! : ℕ) : ℝ)⁻¹ • D ^ j) * K :=
    funext fun j => by
      simp only [mul_smul_comm, smul_mul_assoc, ← pow_succ']
      rw [hpow, smul_add]
  rw [e] at h1
  have e1 : (D + K) * phi 1 (D + K) = D * phi 1 D + phi 1 D * K := h1.unique (h2.add h3)
  rw [exp_eq_one_add_mul_phi_one (D + K), e1, exp_eq_one_add_mul_phi_one D, add_assoc]

/-- For an idempotent `P` that commutes with `Z`: `(P Z)^j P = P Z^j`. -/
theorem proj_mul_pow_mul {P Z : 𝔸} (hP : P * P = P) (hc : P * Z = Z * P) (j : ℕ) :
    (P * Z) ^ j * P = P * Z ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul, mul_one]
  | succ j ih =>
    calc (P * Z) ^ (j + 1) * P = (P * Z) ^ j * (P * (Z * P)) := by
          rw [pow_succ, mul_assoc, mul_assoc]
      _ = (P * Z) ^ j * P * Z := by rw [← hc, ← mul_assoc P P Z, hP, mul_assoc]
      _ = P * Z ^ (j + 1) := by rw [ih, mul_assoc, ← pow_succ]

/-- For an idempotent `P` that commutes with `Z`: `φ₁(P Z) P = P φ₁(Z)`. -/
theorem phi_one_proj_mul {P Z : 𝔸} (hP : P * P = P) (hc : P * Z = Z * P) :
    phi 1 (P * Z) * P = P * phi 1 Z := by
  have h1 : HasSum (fun j : ℕ => ((((j + 1)! : ℕ) : ℝ)⁻¹ • (P * Z) ^ j) * P)
      (phi 1 (P * Z) * P) := (summable_phi 1 (P * Z)).hasSum.mul_right P
  have h2 : HasSum (fun j : ℕ => P * ((((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j)) (P * phi 1 Z) :=
    (summable_phi 1 Z).hasSum.mul_left P
  have e : (fun j : ℕ => ((((j + 1)! : ℕ) : ℝ)⁻¹ • (P * Z) ^ j) * P) =
      fun j : ℕ => P * ((((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j) :=
    funext fun j => by rw [smul_mul_assoc, proj_mul_pow_mul hP hc, mul_smul_comm]
  rw [e] at h1
  exact h1.unique h2

/-- For an idempotent `P` that commutes with `Z`: `e^{P Z} = 1 - P + P e^Z`. -/
theorem exp_proj_mul {P Z : 𝔸} (hP : P * P = P) (hc : P * Z = Z * P) :
    NormedSpace.exp (P * Z) = 1 - P + P * NormedSpace.exp Z := by
  have hpow : ∀ j : ℕ, (P * Z) ^ (j + 1) = P * Z ^ (j + 1) := fun j => by
    rw [pow_succ, ← mul_assoc, proj_mul_pow_mul hP hc, mul_assoc, ← pow_succ]
  have h1 : HasSum (fun j : ℕ => P * Z * ((((j + 1)! : ℕ) : ℝ)⁻¹ • (P * Z) ^ j))
      (P * Z * phi 1 (P * Z)) := (summable_phi 1 (P * Z)).hasSum.mul_left _
  have h2 : HasSum (fun j : ℕ => P * (Z * ((((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j)))
      (P * (Z * phi 1 Z)) := ((summable_phi 1 Z).hasSum.mul_left Z).mul_left P
  have e : (fun j : ℕ => P * Z * ((((j + 1)! : ℕ) : ℝ)⁻¹ • (P * Z) ^ j)) =
      fun j : ℕ => P * (Z * ((((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j)) :=
    funext fun j => by
      simp only [mul_smul_comm, ← pow_succ']
      rw [hpow]
  rw [e] at h1
  have h3 : P * Z * phi 1 (P * Z) = P * (Z * phi 1 Z) := h1.unique h2
  rw [exp_eq_one_add_mul_phi_one (P * Z), h3, exp_eq_one_add_mul_phi_one Z, mul_add, mul_one]
  abel

/-- **The exponential of the rows of a class.** Let `P` be idempotent, commute with `D` and
satisfy `P C P = 0`. Then `e^{H P (D + C)} = 1 - P + P (e^{H D} + H φ₁(H D) C)`. -/
theorem exp_smul_proj_mul_add {P D C : 𝔸} (hP : P * P = P) (hPD : P * D = D * P)
    (hPC : P * C * P = 0) (H : ℝ) :
    NormedSpace.exp (H • (P * (D + C))) =
      1 - P + P * (NormedSpace.exp (H • D) + H • phi 1 (H • D) * C) := by
  have hc : P * (H • D) = H • D * P := by rw [mul_smul_comm, smul_mul_assoc, hPD]
  have e : H • (P * (D + C)) = P * (H • D) + H • (P * C) := by
    rw [mul_add, smul_add, mul_smul_comm]
  have hKD : H • (P * C) * (P * (H • D)) = 0 := by
    rw [smul_mul_assoc, ← mul_assoc, hPC, zero_mul, smul_zero]
  have hKK : H • (P * C) * (H • (P * C)) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, hPC, zero_mul, smul_zero, smul_zero]
  have h3 : phi 1 (P * (H • D)) * (H • (P * C)) = P * (H • phi 1 (H • D) * C) := by
    calc phi 1 (P * (H • D)) * (H • (P * C)) = H • (phi 1 (P * (H • D)) * P * C) := by
          rw [mul_smul_comm, mul_assoc]
      _ = H • (P * phi 1 (H • D) * C) := by rw [phi_one_proj_mul hP hc]
      _ = P * (H • phi 1 (H • D) * C) := by rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [e, exp_add_eq_of_mul_eq_zero hKD hKK, exp_proj_mul hP hc, h3, mul_add, add_assoc]

/-- The algebra of the staggered identity: if `P P = P`, `P M = M`, `N P = N` and `F P = P F`,
then `(P + (1 - P) F + N) (1 - P + P F + M) = F + M + N F + N M`. -/
theorem staggered_algebra {R : Type*} [Ring R] {P F M N : R} (z1 : P * P - P = 0)
    (z3 : M - P * M = 0) (z4 : N - N * P = 0) (z5 : F * P - P * F = 0) :
    (P + (1 - P) * F + N) * (1 - P + P * F + M) = F + M + (N * F + N * M) := by
  have key : (P + (1 - P) * F + N) * (1 - P + P * F + M) - (F + M + (N * F + N * M)) =
      -(P * P - P) + (P * P - P) * F + (P * P - P) * F - (1 - P) * (F * P - P * F)
        - (M - P * M) + (1 - P) * (F * P - P * F) * F - (P * P - P) * F * F
        + (1 - P) * F * (M - P * M) + (1 - P) * (F * P - P * F) * M - (P * P - P) * F * M
        + (N - N * P) - (N - N * P) * F := by
    noncomm_ring
  rw [← sub_eq_zero, key, z1, z3, z4, z5]
  simp

/-- If `N^B = 0`, then `Y' = (Σ_{k < B} N^k) Y` solves `Y' = Y + N Y'`. -/
theorem add_mul_geom_sum_mul {R : Type*} [Ring R] {N : R} {B : ℕ} (hB : N ^ B = 0) (Y : R) :
    (∑ k ∈ Finset.range B, N ^ k) * Y = Y + N * ((∑ k ∈ Finset.range B, N ^ k) * Y) := by
  have h := mul_neg_geom_sum N B
  rw [hB, sub_zero, sub_mul, one_mul, sub_eq_iff_eq_add] at h
  refine (congrArg (fun T => T * Y) h).trans ?_
  rw [add_mul, one_mul, mul_assoc]

end Algebra

open OneStep

variable {n : ℕ}

/-! ### `φ₁` of a matrix -/

/-- `φ₁(Z) = Σ_j Z^j / (j+1)!` for a real matrix (the series converges entry by entry). -/
noncomputable def phiOne (Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑' j : ℕ, (((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j

/-- The series of `φ₁` of a real matrix converges (entrywise). -/
theorem summable_phiOne (Z : Matrix (Fin n) (Fin n) ℝ) :
    Summable fun j : ℕ => (((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j := by
  refine Pi.summable.2 fun p => Pi.summable.2 fun q => ?_
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖opE Z‖) fun k => ?_
  have e : ((((k + 1)! : ℕ) : ℝ)⁻¹ • Z ^ k) p q = (((k + 1)! : ℕ) : ℝ)⁻¹ * (Z ^ k) p q := rfl
  have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h1 : ((((k + 1)! : ℕ) : ℝ))⁻¹ ≤ ((k ! : ℝ))⁻¹ :=
    inv_anti₀ hk (by exact_mod_cast Nat.factorial_le (Nat.le_add_right k 1))
  rw [e, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, div_eq_inv_mul]
  exact mul_le_mul h1 (abs_pow_apply_le Z k p q) (abs_nonneg _) (inv_nonneg.2 hk.le)

/-- The series of `φ₁` of a real matrix has the sum `phiOne`. -/
theorem hasSum_phiOne (Z : Matrix (Fin n) (Fin n) ℝ) :
    HasSum (fun j : ℕ => (((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j) (phiOne Z) :=
  (summable_phiOne Z).hasSum

/-- **The bridge to `Phi`:** the operator of `φ₁` of a matrix is `φ₁` of its operator. -/
theorem opE_phiOne (Z : Matrix (Fin n) (Fin n) ℝ) : opE (phiOne Z) = phi 1 (opE Z) := by
  have hc : Continuous (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) :=
    LinearMap.continuous_of_finiteDimensional
      (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  have h := ((hasSum_phiOne Z).map (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) hc).tsum_eq
  refine h.symm.trans (tsum_congr fun j => ?_)
  show opE ((((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j) = (((j + 1)! : ℕ) : ℝ)⁻¹ • opE Z ^ j
  rw [opE_smul]
  exact congrArg (fun T => (((j + 1)! : ℕ) : ℝ)⁻¹ • T) (map_pow _ Z j)

/-- `e^Z = 1 + Z φ₁(Z)` for a real matrix. -/
theorem exp_eq_one_add_mul_phiOne (Z : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp Z = 1 + Z * phiOne Z := by
  have h : opE (NormedSpace.exp Z) = opE (1 + Z * phiOne Z) := by
    rw [opE_exp, opE_add, opE_one, opE_mul, opE_phiOne]
    exact exp_eq_one_add_mul_phi_one _
  exact (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective h

namespace HeldScheme

section Pattern

variable {κ : Type*} (S : HeldScheme n κ)

/-- The powers of a matrix without entries between different subsystems have none either. -/
theorem pow_apply_eq_zero_of_block {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ p q, S.sub p ≠ S.sub q → Z p q = 0) (j : ℕ) :
    ∀ p q, S.sub p ≠ S.sub q → (Z ^ j) p q = 0 := by
  induction j with
  | zero =>
    intro p q hpq
    rw [pow_zero, Matrix.one_apply_ne fun e => hpq (congrArg S.sub e)]
  | succ j ih =>
    intro p q hpq
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : S.sub p = S.sub r
    · rw [hZ r q fun e => hpq (hr.trans e), mul_zero]
    · rw [ih p r hr, zero_mul]

/-- `φ₁` of a matrix without entries between different subsystems has none either. -/
theorem phiOne_apply_eq_zero_of_block {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ p q, S.sub p ≠ S.sub q → Z p q = 0) {p q : Fin n} (hpq : S.sub p ≠ S.sub q) :
    phiOne Z p q = 0 := by
  have h := Pi.hasSum.1 (Pi.hasSum.1 (hasSum_phiOne Z) p) q
  have h0 : (fun j : ℕ => ((((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j) p q) = fun _ => (0 : ℝ) :=
    funext fun j => by
      show (((j + 1)! : ℕ) : ℝ)⁻¹ * (Z ^ j) p q = 0
      rw [S.pow_apply_eq_zero_of_block hZ j p q hpq, mul_zero]
  have h' : HasSum (fun j : ℕ => ((((j + 1)! : ℕ) : ℝ)⁻¹ • Z ^ j) p q) (0 : ℝ) := by
    rw [h0]
    exact hasSum_zero
  exact h.unique h'

/-- The exponential of a matrix without entries between different subsystems has none either. -/
theorem exp_apply_eq_zero_of_block {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ p q, S.sub p ≠ S.sub q → Z p q = 0) {p q : Fin n} (hpq : S.sub p ≠ S.sub q) :
    NormedSpace.exp Z p q = 0 := by
  rw [exp_eq_one_add_mul_phiOne, Matrix.add_apply,
    Matrix.one_apply_ne fun e => hpq (congrArg S.sub e), zero_add, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : S.sub p = S.sub r
  · rw [S.phiOne_apply_eq_zero_of_block hZ fun e => hpq (hr.trans e), mul_zero]
  · rw [hZ p r hr, zero_mul]

/-- A product of `k` matrices that carry new samples only descends `k` stages: if `N` has
entries only from an earlier stage, `(N^k)_{pq} = 0` unless `stage q + k ≤ stage p`. -/
theorem pow_apply_eq_zero_of_stage {N : Matrix (Fin n) (Fin n) ℝ}
    (hN : ∀ p q, ¬ S.stage (S.sub q) < S.stage (S.sub p) → N p q = 0) (k : ℕ) :
    ∀ p q, S.stage (S.sub p) < S.stage (S.sub q) + k → (N ^ k) p q = 0 := by
  induction k with
  | zero =>
    intro p q h
    rw [pow_zero, Matrix.one_apply_ne fun e => by subst e; omega]
  | succ k ih =>
    intro p q h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : S.stage (S.sub q) < S.stage (S.sub r)
    · rw [ih p r (by omega), zero_mul]
    · rw [hN r q hr, mul_zero]

/-- A number larger than the stage of every state. -/
def stageBound : ℕ := (Finset.univ.sup fun p : Fin n => S.stage (S.sub p)) + 1

/-- A matrix with entries only from an earlier stage is nilpotent: `N^B = 0`, `B = stageBound`. -/
theorem pow_stageBound_eq_zero {N : Matrix (Fin n) (Fin n) ℝ}
    (hN : ∀ p q, ¬ S.stage (S.sub q) < S.stage (S.sub p) → N p q = 0) :
    N ^ S.stageBound = 0 := by
  ext p q
  have hp : S.stage (S.sub p) ≤ Finset.univ.sup fun p : Fin n => S.stage (S.sub p) :=
    Finset.le_sup (f := fun p : Fin n => S.stage (S.sub p)) (Finset.mem_univ p)
  rw [Matrix.zero_apply]
  exact S.pow_apply_eq_zero_of_stage hN _ p q (by rw [stageBound]; omega)

/-- The mask of the first class: the diagonal `0/1` matrix of the states whose subsystem runs
at stage `0`. -/
def firstMask : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun r => if S.stage (S.sub r) = 0 then 1 else 0

/-- The mask of the first class is idempotent. -/
theorem firstMask_mul_self : S.firstMask * S.firstMask = S.firstMask := by
  rw [firstMask, Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  by_cases h : S.stage (S.sub r) = 0 <;> simp [h]

/-- The complement of the mask of the first class: the states of the later stages. -/
theorem one_sub_firstMask :
    1 - S.firstMask = diagonal fun r => if S.stage (S.sub r) = 0 then (0 : ℝ) else 1 := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    by_cases h : S.stage (S.sub p) = 0 <;> simp [firstMask, h]
  · simp [firstMask, hpq]

/-- The mask of the first class commutes with every matrix that has no entries between
different subsystems. -/
theorem firstMask_mul_comm {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : ∀ p q, S.sub p ≠ S.sub q → T p q = 0) : S.firstMask * T = T * S.firstMask := by
  ext p q
  rw [firstMask, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : S.sub p = S.sub q
  · rw [h, mul_comm]
  · rw [hT p q h, mul_zero, zero_mul]

/-- The first class uses no new samples: `P N = 0`. -/
theorem firstMask_mul_N : S.firstMask * S.N = 0 := by
  ext p q
  rw [firstMask, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : S.stage (S.sub p) = 0
  · rw [S.hN p q fun h => Nat.not_lt_zero _ (hp ▸ h.2), mul_zero]
  · rw [ite_eq_right hp, zero_mul]

/-- If no two subsystems of a class are partners, the later class uses no old samples:
`(1 - P) M = 0`. -/
theorem one_sub_firstMask_mul_M
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) :
    (1 - S.firstMask) * S.M = 0 := by
  ext p q
  rw [S.one_sub_firstMask, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : S.stage (S.sub p) = 0
  · rw [ite_eq_left hp, zero_mul]
  · have hM : S.M p q = 0 := S.hM p q fun h => h.2 (by
      have hq : S.stage (S.sub q) = 0 := by
        by_contra hq
        exact hp ((hbip _ _ h.1).2 hq)
      rw [hq]
      exact Nat.pos_of_ne_zero hp)
    rw [hM, mul_zero]

/-- If no two subsystems of a class are partners, no new sample comes from the later class:
`N (1 - P) = 0`. -/
theorem N_mul_one_sub_firstMask
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) :
    S.N * (1 - S.firstMask) = 0 := by
  ext p q
  rw [S.one_sub_firstMask, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hq : S.stage (S.sub q) = 0
  · rw [ite_eq_left hq, mul_zero]
  · rw [S.hN p q fun h => Nat.not_lt_zero _ ((hbip _ _ h.1).2 hq ▸ h.2), zero_mul]

end Pattern

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The coefficients of the zero-order hold -/

/-- The kernel of the zero-order hold, `∫₀ᴴ e^{s A₀} ds = H φ₁(H A₀)`
(`opE_zohKernel_eq_integral`, `zohKernel_apply_eq_integral`). -/
noncomputable def zohKernel (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  H • phiOne (H • S.blockDiag A)

/-- **The coupling matrix of the zero-order hold**, the paper's `G° C`:
`(∫₀ᴴ e^{s A₀} ds) A_c`. -/
noncomputable def zohCoupling (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S.zohKernel A H * S.coupling A

/-- **The kernel is the integral, as operators:** `H φ₁(H A₀) = ∫₀ᴴ e^{s A₀} ds`. -/
theorem opE_zohKernel_eq_integral (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    opE (S.zohKernel A H) =
      ∫ s in (0 : ℝ)..H, opE (NormedSpace.exp (s • S.blockDiag A)) := by
  rw [zohKernel, opE_smul, opE_phiOne, opE_smul, smul_phi_one_eq_integral]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show NormedSpace.exp (s • opE (S.blockDiag A)) = opE (NormedSpace.exp (s • S.blockDiag A))
  rw [opE_exp, opE_smul]

/-- **The kernel is the integral, entry by entry:**
`(H φ₁(H A₀))_{pq} = ∫₀ᴴ (e^{s A₀})_{pq} ds`. -/
theorem zohKernel_apply_eq_integral (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) (p q : Fin n) :
    S.zohKernel A H p q = ∫ s in (0 : ℝ)..H, NormedSpace.exp (s • S.blockDiag A) p q := by
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    (innerSL ℝ (unitE p)).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (unitE q))
  have hL : ∀ T : Matrix (Fin n) (Fin n) ℝ, L (opE T) = T p q := fun T => by
    show ⟪unitE p, opE T (unitE q)⟫ = T p q
    exact inner_unitE_opE T p q
  have hc : Continuous fun s : ℝ => opE (NormedSpace.exp (s • S.blockDiag A)) := by
    have e : (fun s : ℝ => opE (NormedSpace.exp (s • S.blockDiag A))) =
        fun s : ℝ => NormedSpace.exp (s • opE (S.blockDiag A)) :=
      funext fun s => by rw [opE_exp, opE_smul]
    rw [e]
    let _ : NormedAlgebra ℚ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
      NormedAlgebra.restrictScalars ℚ ℝ _
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have h1 := L.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 H)
  rw [← S.opE_zohKernel_eq_integral] at h1
  rw [← hL (S.zohKernel A H), ← h1]
  exact intervalIntegral.integral_congr fun s _ => hL _

/-! ### The block pattern of the coefficients -/

/-- The kernel of the zero-order hold has no entry between different subsystems. -/
theorem zohKernel_apply_eq_zero (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) {p q : Fin n}
    (hpq : S.sub p ≠ S.sub q) : S.zohKernel A H p q = 0 := by
  have hZ : ∀ p q, S.sub p ≠ S.sub q → (H • S.blockDiag A) p q = 0 := fun p q h => by
    rw [Matrix.smul_apply, S.blockDiag_apply, ite_eq_right h, smul_zero]
  rw [zohKernel, Matrix.smul_apply, S.phiOne_apply_eq_zero_of_block hZ hpq, smul_zero]

/-- The coupling part has no entry between subsystems that are not partners, if `A` has none
between different subsystems that are not partners. -/
theorem coupling_apply_eq_zero_of_not_partner {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {p q : Fin n} (hnp : ¬ S.partner (S.sub p) (S.sub q)) : S.coupling A p q = 0 := by
  rw [S.coupling_apply]
  by_cases e : S.sub p = S.sub q
  · rw [ite_eq_left e]
  · rw [ite_eq_right e]
    exact hA p q e hnp

/-- An entry of `G° C` vanishes if the coupling part has no entry from the subsystem of its row
to its column. -/
theorem zohCoupling_apply_eq_zero {A : Matrix (Fin n) (Fin n) ℝ} (H : ℝ) {p q : Fin n}
    (h : ∀ r, S.sub r = S.sub p → S.coupling A r q = 0) : S.zohCoupling A H p q = 0 := by
  rw [zohCoupling, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : S.sub p = S.sub r
  · rw [h r hr.symm, mul_zero]
  · rw [S.zohKernel_apply_eq_zero A H hr, zero_mul]

/-- **`G° C` has no entry inside a subsystem.** -/
theorem zohCoupling_apply_eq_zero_of_same (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) {p q : Fin n}
    (hpq : S.sub p = S.sub q) : S.zohCoupling A H p q = 0 :=
  S.zohCoupling_apply_eq_zero H fun r hr => by
    rw [S.coupling_apply, ite_eq_left (hr.trans hpq)]

/-- **`G° C` has no entry between subsystems that are not partners**, if `A` has none between
different subsystems that are not partners. -/
theorem zohCoupling_apply_eq_zero_of_not_partner {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    {p q : Fin n} (hnp : ¬ S.partner (S.sub p) (S.sub q)) : S.zohCoupling A H p q = 0 :=
  S.zohCoupling_apply_eq_zero H fun r hr =>
    S.coupling_apply_eq_zero_of_not_partner hA (by rw [hr]; exact hnp)

/-- The part of `G° C` on the new samples: the entries from a subsystem of an earlier stage. -/
noncomputable def zohNew (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    if S.stage (S.sub q) < S.stage (S.sub p) then S.zohCoupling A H p q else 0

/-- The part of `G° C` on the old samples: the entries from a subsystem that does not run at an
earlier stage. -/
noncomputable def zohOld (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    if S.stage (S.sub q) < S.stage (S.sub p) then 0 else S.zohCoupling A H p q

/-- The two parts add up to `G° C`. -/
theorem zohOld_add_zohNew (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.zohOld A H + S.zohNew A H = S.zohCoupling A H := by
  ext p q
  by_cases h : S.stage (S.sub q) < S.stage (S.sub p) <;> simp [zohOld, zohNew, h]

/-- The part on the new samples has the pattern that `HeldScheme` requires of `N`. -/
theorem zohNew_apply_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    {p q : Fin n}
    (h : ¬ (S.partner (S.sub p) (S.sub q) ∧ S.stage (S.sub q) < S.stage (S.sub p))) :
    S.zohNew A H p q = 0 := by
  by_cases hs : S.stage (S.sub q) < S.stage (S.sub p)
  · have e : S.zohNew A H p q = S.zohCoupling A H p q := by simp [zohNew, hs]
    rw [e]
    exact S.zohCoupling_apply_eq_zero_of_not_partner hA H fun hp => h ⟨hp, hs⟩
  · simp [zohNew, hs]

/-- The part on the old samples has the pattern that `HeldScheme` requires of `M`. -/
theorem zohOld_apply_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    {p q : Fin n}
    (h : ¬ (S.partner (S.sub p) (S.sub q) ∧ ¬ S.stage (S.sub q) < S.stage (S.sub p))) :
    S.zohOld A H p q = 0 := by
  by_cases hs : S.stage (S.sub q) < S.stage (S.sub p)
  · simp [zohOld, hs]
  · have e : S.zohOld A H p q = S.zohCoupling A H p q := by simp [zohOld, hs]
    rw [e]
    exact S.zohCoupling_apply_eq_zero_of_not_partner hA H fun hp => h ⟨hp, hs⟩

/-- **The zero-order hold as a scheme**, on the subsystems, partners and stages of `S`, for a
matrix `A` without blocks between subsystems that are not partners: `F = e^{H A₀}`, the old
samples carry `zohOld`, the new samples `zohNew` (together `G° C`), and
`X = (Σ_{k < B} N^k) (F + M)`, which solves `X = F + M + N X` because `N^B = 0`. -/
noncomputable def zoh (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    HeldScheme n κ where
  sub := S.sub
  partner := S.partner
  stage := S.stage
  F := NormedSpace.exp (H • S.blockDiag A)
  N := S.zohNew A H
  M := S.zohOld A H
  X := (∑ k ∈ Finset.range S.stageBound, S.zohNew A H ^ k) *
    (NormedSpace.exp (H • S.blockDiag A) + S.zohOld A H)
  hF := fun p q h => S.exp_apply_eq_zero_of_block
    (fun p q h => by rw [Matrix.smul_apply, S.blockDiag_apply, ite_eq_right h, smul_zero]) h
  hN := fun _ _ h => S.zohNew_apply_eq_zero hA H h
  hM := fun _ _ h => S.zohOld_apply_eq_zero hA H h
  hX := add_mul_geom_sum_mul
    (S.pow_stageBound_eq_zero fun p q h => by simp [zohNew, h]) _

/-- The local maps of the zero-order hold are `e^{H A₀}`. -/
theorem zoh_F (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (S.zoh A hA H).F = NormedSpace.exp (H • (S.zoh A hA H).blockDiag A) := rfl

/-- The coefficients of the samples of the zero-order hold add up to `G° C`. -/
theorem zoh_M_add_N (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (S.zoh A hA H).M + (S.zoh A hA H).N = (S.zoh A hA H).zohCoupling A H :=
  S.zohOld_add_zohNew A H

/-! ### The two Taylor remainders -/

/-- **The exact local maps to second order:**
`‖e^{H A₀} - 1 - H A₀ - ½H² A₀²‖ ≤ ‖A₀‖³/6 · e^{H‖A₀‖} · H³` for `H ≥ 0`. -/
theorem norm_exp_blockDiag_bracket_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE (NormedSpace.exp (H • S.blockDiag A) - 1 - H • S.blockDiag A -
      (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A))‖ ≤
      ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 := by
  have e : NormedSpace.exp (H • S.blockDiag A) - 1 - H • S.blockDiag A -
      (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A) =
      NormedSpace.exp (H • S.blockDiag A) -
        (1 + H • S.blockDiag A + (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) := by
    abel
  rw [e]
  exact norm_opE_exp_sub_quadratic_le _ hH

/-- **The coefficients of the zero-order hold to second order:**
`‖G°C - H A_c - ½H² A₀ A_c‖ ≤ ‖A₀‖²‖A_c‖/6 · e^{H‖A₀‖} · H³` for `H ≥ 0`. -/
theorem norm_zohCoupling_bracket_le (A : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ‖opE (S.zohCoupling A H - H • S.coupling A -
      (H ^ 2 / 2) • (S.blockDiag A * S.coupling A))‖ ≤
      ‖opE (S.blockDiag A)‖ ^ 2 / 6 * ‖opE (S.coupling A)‖ *
        Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 := by
  have e : S.zohCoupling A H - H • S.coupling A -
      (H ^ 2 / 2) • (S.blockDiag A * S.coupling A) =
      (S.zohKernel A H - H • (1 : Matrix (Fin n) (Fin n) ℝ) - (H ^ 2 / 2) • S.blockDiag A) *
        S.coupling A := by
    rw [zohCoupling, sub_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  have h1 : ‖opE (S.zohKernel A H - H • (1 : Matrix (Fin n) (Fin n) ℝ) -
      (H ^ 2 / 2) • S.blockDiag A)‖ ≤
      ‖opE (S.blockDiag A)‖ ^ 2 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 := by
    rw [zohKernel, opE_sub, opE_sub, opE_smul, opE_phiOne, opE_smul, opE_smul, opE_one,
      opE_smul]
    exact norm_smul_phi_one_sub_le (opE (S.blockDiag A)) hH
  rw [e, opE_mul]
  calc ‖opE (S.zohKernel A H - H • (1 : Matrix (Fin n) (Fin n) ℝ) -
        (H ^ 2 / 2) • S.blockDiag A) * opE (S.coupling A)‖
      ≤ ‖opE (S.zohKernel A H - H • (1 : Matrix (Fin n) (Fin n) ℝ) -
          (H ^ 2 / 2) • S.blockDiag A)‖ * ‖opE (S.coupling A)‖ := norm_mul_le _ _
    _ ≤ ‖opE (S.blockDiag A)‖ ^ 2 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 *
          ‖opE (S.coupling A)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖opE (S.blockDiag A)‖ ^ 2 / 6 * ‖opE (S.coupling A)‖ *
          Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 := by ring

/-- The constant of the two Taylor remainders, `(α₀³/6 + α₀²γ/6) e^{H α₀}` with `α₀ = ‖A₀‖`
and `γ = ‖A_c‖`. -/
noncomputable def zohC (α₀ γ H : ℝ) : ℝ := (α₀ ^ 3 / 6 + α₀ ^ 2 / 6 * γ) * Real.exp (H * α₀)

/-- The remainder of the printed relation is the remainder of the normal form of `HalfStep`
plus the two Taylor remainders. -/
theorem zoh_remainder_eq (A U : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    S.X - U - (S.F - NormedSpace.exp (H • S.blockDiag A)) -
        (S.M + S.N - S.zohCoupling A H) - (H ^ 2 / 2) • (S.signedCoupling A * A) =
      (S.X - U - S.halfStepLead A H) +
        (NormedSpace.exp (H • S.blockDiag A) - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) +
        (S.zohCoupling A H - H • S.coupling A -
          (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) := by
  rw [halfStepLead]
  abel

/-! ### The exponential of the rows of a class -/

/-- **The exponential of the rows of a class.** Let `P` be idempotent, commute with `A₀` and
satisfy `P A_c P = 0` (the mask of a class of subsystems without partners inside the class).
Then `e^{H P A} = 1 - P + P (e^{H A₀} + G°C)`: the rows of the class are those of the zero-order
hold, the other rows those of the identity. -/
theorem exp_smul_proj_mul (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P * P = P)
    (hPD : P * S.blockDiag A = S.blockDiag A * P) (hPC : P * S.coupling A * P = 0) :
    NormedSpace.exp (H • (P * A)) =
      1 - P + P * (NormedSpace.exp (H • S.blockDiag A) + S.zohCoupling A H) := by
  have hA : A = S.blockDiag A + S.coupling A := (S.blockDiag_add_coupling A).symm
  have h := exp_smul_proj_mul_add (P := opE P) (D := opE (S.blockDiag A))
    (C := opE (S.coupling A)) (by rw [← opE_mul, hP]) (by rw [← opE_mul, ← opE_mul, hPD])
    (by rw [← opE_mul, ← opE_mul, hPC]; exact map_zero _) H
  have e1 : opE (NormedSpace.exp (H • (P * A))) =
      NormedSpace.exp (H • (opE P * (opE (S.blockDiag A) + opE (S.coupling A)))) := by
    rw [opE_exp, opE_smul, opE_mul, ← opE_add, ← hA]
  have e2 : opE (1 - P + P * (NormedSpace.exp (H • S.blockDiag A) + S.zohCoupling A H)) =
      1 - opE P + opE P * (NormedSpace.exp (H • opE (S.blockDiag A)) +
        H • phi 1 (H • opE (S.blockDiag A)) * opE (S.coupling A)) := by
    rw [opE_add, opE_sub, opE_one, opE_mul, opE_add, opE_exp, opE_smul, zohCoupling, opE_mul,
      zohKernel, opE_smul, opE_phiOne, opE_smul]
  exact (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective (e1.trans (h.trans e2.symm))

/-- If no two subsystems of a class are partners, the coupling has no block inside the first
class: `P A_c P = 0`. -/
theorem firstMask_coupling_firstMask {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) :
    S.firstMask * S.coupling A * S.firstMask = 0 := by
  ext p q
  rw [firstMask, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : S.stage (S.sub p) = 0
  · by_cases hq : S.stage (S.sub q) = 0
    · rw [S.coupling_apply_eq_zero_of_not_partner hA fun h => (hbip _ _ h).1 hp hq, mul_zero,
        zero_mul]
    · rw [ite_eq_right hq, mul_zero]
  · rw [ite_eq_right hp, zero_mul, zero_mul]

/-- If no two subsystems of a class are partners, the coupling has no block inside the later
class: `(1 - P) A_c (1 - P) = 0`. -/
theorem one_sub_firstMask_coupling {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) :
    (1 - S.firstMask) * S.coupling A * (1 - S.firstMask) = 0 := by
  ext p q
  rw [S.one_sub_firstMask, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : S.stage (S.sub p) = 0
  · rw [ite_eq_left hp, zero_mul, zero_mul]
  · by_cases hq : S.stage (S.sub q) = 0
    · rw [ite_eq_left hq, mul_zero]
    · rw [S.coupling_apply_eq_zero_of_not_partner hA fun h => hp ((hbip _ _ h).2 hq), mul_zero,
        zero_mul]

/-- **Staggered readout, the first equation** (the paper, equation (staggered)): on a bipartite
coupling graph the zero-order hold that executes class `a` and then class `b` has the one-step
map `X = e^{H A_b} e^{H A_a}`. Class `a` are the subsystems of stage `0`, class `b` the others;
no two subsystems of a class are partners (`hbip`); `A_a = P A` and `A_b = (1 - P) A` are the
block rows of `A` of the two classes, `P = firstMask`; the scheme is the zero-order hold:
`F = e^{H A₀}` and `M + N = G°C`. -/
theorem zoh_staggered {A : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0))
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A))
    (hMN : S.M + S.N = S.zohCoupling A H) :
    S.X = NormedSpace.exp (H • ((1 - S.firstMask) * A)) *
      NormedSpace.exp (H • (S.firstMask * A)) := by
  have hP := S.firstMask_mul_self
  have hbd : ∀ p q, S.sub p ≠ S.sub q → S.blockDiag A p q = 0 := fun p q h => by
    rw [S.blockDiag_apply, ite_eq_right h]
  have hPD := S.firstMask_mul_comm hbd
  have hPF := S.firstMask_mul_comm S.hF
  have hPN := S.firstMask_mul_N
  have hQM := S.one_sub_firstMask_mul_M hbip
  have hNQ := S.N_mul_one_sub_firstMask hbip
  have hPM : S.firstMask * S.M = S.M := by
    have h := hQM
    rw [sub_mul, one_mul, sub_eq_zero] at h
    exact h.symm
  have hQN : (1 - S.firstMask) * S.N = S.N := by rw [sub_mul, one_mul, hPN, sub_zero]
  have hQ : (1 - S.firstMask) * (1 - S.firstMask) = 1 - S.firstMask := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hP, sub_self, sub_zero]
  have hQD : (1 - S.firstMask) * S.blockDiag A = S.blockDiag A * (1 - S.firstMask) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hPD]
  have Ea : NormedSpace.exp (H • (S.firstMask * A)) =
      1 - S.firstMask + S.firstMask * S.F + S.M := by
    rw [S.exp_smul_proj_mul A H hP hPD (S.firstMask_coupling_firstMask hA hbip), ← hF, ← hMN,
      mul_add, mul_add, hPN, add_zero, hPM, add_assoc]
  have Eb : NormedSpace.exp (H • ((1 - S.firstMask) * A)) =
      S.firstMask + (1 - S.firstMask) * S.F + S.N := by
    rw [S.exp_smul_proj_mul A H hQ hQD (S.one_sub_firstMask_coupling hA hbip), ← hF, ← hMN,
      mul_add, mul_add, hQM, zero_add, hQN, sub_sub_cancel, add_assoc]
  have hNN : S.N * S.N = 0 := by
    calc S.N * S.N = S.N * ((1 - S.firstMask) * S.N) := by rw [hQN]
      _ = 0 := by rw [← mul_assoc, hNQ, zero_mul]
  have hNX : S.N * S.X = S.N * S.F + S.N * S.M := by
    rw [S.hX, mul_add, mul_add, ← mul_assoc, hNN, zero_mul, add_zero]
  have hX2 : S.X = S.F + S.M + (S.N * S.F + S.N * S.M) := by
    rw [← hNX]
    exact S.hX
  have z1 : S.firstMask * S.firstMask - S.firstMask = 0 := by rw [hP, sub_self]
  have z3 : S.M - S.firstMask * S.M = 0 := by rw [hPM, sub_self]
  have z4 : S.N - S.N * S.firstMask = 0 := by rw [← hNQ, mul_sub, mul_one]
  have z5 : S.F * S.firstMask - S.firstMask * S.F = 0 := by rw [hPF, sub_self]
  rw [Eb, Ea, hX2]
  exact (staggered_algebra z1 z3 z4 z5).symm

/-- **Staggered readout, the first equation, for the zero-order hold** `S.zoh A hA H`: if no
two subsystems of a class are partners (class `a`: stage `0`; class `b`: the later stages), its
one-step map is `X = e^{H A_b} e^{H A_a}`, `A_a = P A`, `A_b = (1 - P) A`, `P = firstMask`. -/
theorem zoh_X_staggered {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hbip : ∀ s t, S.partner s t → (S.stage s = 0 ↔ S.stage t ≠ 0)) :
    (S.zoh A hA H).X = NormedSpace.exp (H • ((1 - S.firstMask) * A)) *
      NormedSpace.exp (H • (S.firstMask * A)) :=
  (S.zoh A hA H).zoh_staggered hA hbip (S.zoh_F A hA H) (S.zoh_M_add_N A hA H)

/-- The coupling part is not larger than `‖A‖ + ‖A₀‖`. -/
theorem norm_opE_coupling_le (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖opE (S.coupling A)‖ ≤ ‖opE A‖ + ‖opE (S.blockDiag A)‖ := by
  rw [coupling, opE_sub]
  exact norm_sub_le _ _

variable {S}

/-! ### The relation as printed, and the zero-order hold -/

/-- **The half-step relation as printed in the paper, in the rows of a subsystem.** For a
consistent scheme with one held sample, in any order of execution, `x` supported on a subsystem
`s` and every vector `y`:
`|⟪x, (X - U - (F - e^{H A₀}) - (M + N - G°C) - ½H² A_ς A) y⟫| ≤ (C₃ + zohC) H³ ‖x‖ ‖y‖`,
`C₃ = reactionC a b c ‖A‖ H`, `zohC = (‖A₀‖³/6 + ‖A₀‖²‖A_c‖/6) e^{H‖A₀‖}`. -/
theorem Consistent.half_step_zoh_row {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s : κ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (S.X - U - (S.F - NormedSpace.exp (H • S.blockDiag A)) -
        (S.M + S.N - S.zohCoupling A H) - (H ^ 2 / 2) • (S.signedCoupling A * A)) y⟫| ≤
      (reactionC a b c ‖opE A‖ H + zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H) * H ^ 3 *
        (‖x‖ * ‖y‖) := by
  have hxy : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have r0 : |⟪x, opE (S.X - U - S.halfStepLead A H) y⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
    rw [S.inner_halfStepLead]
    exact h.half_step_row hx y
  have r1 := (abs_inner_opE_le (NormedSpace.exp (H • S.blockDiag A) - 1 - H • S.blockDiag A -
    (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) x y).trans
    (mul_le_mul_of_nonneg_right (S.norm_exp_blockDiag_bracket_le A h.hH) hxy)
  have r2 := (abs_inner_opE_le (S.zohCoupling A H - H • S.coupling A -
    (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) x y).trans
    (mul_le_mul_of_nonneg_right (S.norm_zohCoupling_bracket_le A h.hH) hxy)
  rw [S.zoh_remainder_eq, inner_opE_add, inner_opE_add]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add r0 r1) r2).trans_eq ?_
  rw [zohC]
  ring

/-- **The half-step relation as printed in the paper** (Theorem "half a macro step",
equation (half)), in the spectral norm: for a consistent scheme with one held sample, in any
order of execution,
`‖X - U - (F - e^{H A₀}) - (M + N - G°C) - ½H² A_ς A‖ ≤ (√(card κ) C₃ + zohC) H³`,
`G°C = (∫₀ᴴ e^{s A₀} ds) A_c` the coupling matrix of the zero-order hold (`zohCoupling`),
`C₃ = reactionC a b c ‖A‖ H`, `zohC = (‖A₀‖³/6 + ‖A₀‖²‖A_c‖/6) e^{H‖A₀‖}`. -/
theorem Consistent.norm_half_step_zoh_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) :
    ‖opE (S.X - U - (S.F - NormedSpace.exp (H • S.blockDiag A)) -
        (S.M + S.N - S.zohCoupling A H) - (H ^ 2 / 2) • (S.signedCoupling A * A))‖ ≤
      (Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
        zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H) * H ^ 3 := by
  rw [S.zoh_remainder_eq, opE_add, opE_add]
  refine norm_add₃_le.trans ?_
  refine (add_le_add (add_le_add h.norm_half_step_le (S.norm_exp_blockDiag_bracket_le A h.hH))
    (S.norm_zohCoupling_bracket_le A h.hH)).trans_eq ?_
  rw [zohC]
  ring

/-- **The zero-order hold, in the rows of a subsystem:** if `F = e^{H A₀}` and `M + N = G°C`,
the first two terms of the relation vanish; for `x` supported on a subsystem and every `y`,
`|⟪x, (X - U - ½H² A_ς A) y⟫| ≤ (C₃ + zohC) H³ ‖x‖ ‖y‖`. -/
theorem Consistent.zoh_step_row {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hF : S.F = NormedSpace.exp (H • S.blockDiag A))
    (hMN : S.M + S.N = S.zohCoupling A H) {s : κ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (y : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (S.X - U - (H ^ 2 / 2) • (S.signedCoupling A * A)) y⟫| ≤
      (reactionC a b c ‖opE A‖ H + zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H) * H ^ 3 *
        (‖x‖ * ‖y‖) := by
  have h1 := h.half_step_zoh_row hx y
  rwa [← hF, sub_self, sub_zero, ← hMN, sub_self, sub_zero] at h1

/-- **The zero-order hold** (Theorem "half a macro step": "For the zero-order hold the first
two terms vanish"): for a consistent scheme with `F = e^{H A₀}` and `M + N = G°C`,
`‖X - U - ½H² A_ς A‖ ≤ (√(card κ) C₃ + zohC) H³`. -/
theorem Consistent.norm_zoh_step_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) (hMN : S.M + S.N = S.zohCoupling A H) :
    ‖opE (S.X - U - (H ^ 2 / 2) • (S.signedCoupling A * A))‖ ≤
      (Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
        zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H) * H ^ 3 := by
  have h1 := h.norm_half_step_zoh_le
  rwa [← hF, sub_self, sub_zero, ← hMN, sub_self, sub_zero] at h1

/-- **The zero-order hold `S.zoh A hA H`:** if it is consistent with constants `a`, `b`, `c`,
its one-step map obeys `‖X - U - ½H² A_ς A‖ ≤ (√(card κ) C₃ + zohC) H³`. -/
theorem norm_zoh_sub_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0}
    {H a b c : ℝ} (h : (S.zoh A hA H).Consistent A U H a b c) :
    ‖opE ((S.zoh A hA H).X - U - (H ^ 2 / 2) • (S.signedCoupling A * A))‖ ≤
      (Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
        zohC ‖opE (S.blockDiag A)‖ ‖opE (S.coupling A)‖ H) * H ^ 3 :=
  h.norm_zoh_step_le (S.zoh_F A hA H) (S.zoh_M_add_N A hA H)

end HeldScheme

end CoSimFoundations
