/-
The least injection and added damping with partner weights only (the paper, Section 6, the
paragraph after the proof of Proposition "the reaction").

**Paper.** With partner weights only, `F_i = e^{H A_i}`, the coefficients reach the matrices
`𝒵_pw` between partners only, and `ι = H λ_max (S + R) + O(H²)`, `μ = -H λ_min (S + R) + O(H²)`
with `R ∈ 𝓡_pw = sym 𝒵_pw`, `S = sym (½ A_ς A)`. The least injection rate is `H i_σ + O(H²)`,
`i_σ = min_R λ_max (S + R)`, the least added damping `H m_σ + O(H²)`, `m_σ = min_R -λ_min (S + R)`,
both attained. If two subsystems are partners exactly when they lie in different groups of a
partition into groups of mutually non-partner subsystems, then `i_σ` and `m_σ` are the extreme
values of the blocks of `S` on the groups.

**What is formalised, and in which class.** This is the coefficient class with the local maps
fixed, `F = e^{H A₀}`, and arbitrary coefficients of the partner samples (`HeldScheme` with
`hF : S.F = e^{H A₀}`); the realisation of these coefficients by bounded weight functions
(`W_ij(s) = L_ij + ΔW_ij(s)`, the paper's `B_i w + A_i B_i w'`) is not formalised. No subsystem is
its own partner (`hself`).
* `reachPW Θ`: the elements of the reach without block-diagonal part (`F` fixed).
* **Trace zero** (`norm_opE_le_mul_lamMax`, `norm_opE_le_mul_neg_lamMin`): a symmetric matrix
  with zero diagonal has `‖R‖ ≤ n λ_max (R)` and `‖R‖ ≤ n (-λ_min (R))`: the least values are
  attained (`exists_least_injection_pw`, `exists_least_damping_pw`, through
  `exists_forall_le_of_coercive` of `LeastRunError`).
* **Every scheme of the class** (`Consistent.least_injection_pw_le`,
  `Consistent.least_damping_pw_le`): for all bounds `ι`, `μ` of the form of `Δ_R`,
  `ι ≥ H i - K H²` and `μ ≥ H m - K H²` for every `i ≤ λ_max (sym (P + Z))`,
  `m ≤ -λ_min (sym (P + Z))` on `reachPW Θ`, `K = diffLeadC b c ‖A‖ + √(card κ) C₃ +
  ‖A₀‖³/6 e^{H‖A₀‖}`.
* **Attained in the class** (`least_injection_pw_attained`, `least_damping_pw_attained`): the
  scheme `reachScheme` of a minimiser has `F = e^{H A₀}` and `|ι - H i_σ| ≤ K' H²`, resp.
  `|μ - H m_σ| ≤ K' H²`.
* **Groups** (`isLeast_injection_pw_groups`, `isLeast_damping_pw_groups`; all states are outputs,
  `Θ = 0`, as for scalar stores): for a partition `σ` of the states into groups (each subsystem in
  one group) with `partner ↔ different groups`, `i_σ = max_k λ_max (S_k)` and
  `m_σ = -min_k λ_min (S_k)`, `S_k` the block of `S = sym P` on group `k`
  (`lamMax_eq_iSup_parts`, `lamMin_eq_iInf_parts`, interlacing).
-/
import CoSimFoundations.LeastSpread
import CoSimFoundations.LeastRunError

open Matrix Metric
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-! ### A symmetric matrix with zero diagonal -/

/-- **Trace zero, upper side:** a symmetric matrix with zero diagonal has `‖R‖ ≤ n λ_max (R)`. -/
theorem norm_opE_le_mul_lamMax {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsSymm)
    (hdiag : ∀ p, R p p = 0) : ‖opE R‖ ≤ n * lamMax R := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Subsingleton.elim R 0, show opE (0 : Matrix (Fin 0) (Fin 0) ℝ) = 0 from map_zero _,
      norm_zero, Nat.cast_zero, zero_mul]
  have htr : R.trace = 0 := by simp [Matrix.trace, hdiag]
  -- `-⟪x, R x⟫ ≤ (n - 1) λ_max ‖x‖²`
  have hlow : ∀ x : EuclideanSpace ℝ (Fin n),
      -⟪x, opE R x⟫ ≤ ((n : ℝ) - 1) * lamMax R * ‖x‖ ^ 2 := by
    intro x
    have h := quadForm_le_trace_add (-R) (ι := lamMax R) (fun y => by
      rw [neg_mulVec, dotProduct_neg]
      have := dotProduct_le_lamMax R y
      linarith) (WithLp.ofLp x)
    rw [neg_mulVec, dotProduct_neg, trace_neg, htr, neg_zero, zero_add] at h
    rw [inner_opE_eq_dotProduct, ← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    linarith
  have := nonempty_sphere hn
  have hpos : 0 ≤ lamMax R := by
    obtain ⟨u⟩ := this
    have h1 := hlow u
    have h2 := inner_le_lamMax R u
    rw [mem_sphere_zero_iff_norm.1 u.2, one_pow, mul_one] at h1 h2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  refine norm_opE_le_of_abs_inner_self_le hR (by positivity) fun x => ?_
  rw [abs_le]
  have h1 := hlow x
  have h2 := inner_le_lamMax R x
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := sq_nonneg ‖x‖
  constructor <;> nlinarith [mul_nonneg hpos hx]

/-- **Trace zero, lower side:** a symmetric matrix with zero diagonal has
`‖R‖ ≤ n (-λ_min (R))`. -/
theorem norm_opE_le_mul_neg_lamMin {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsSymm)
    (hdiag : ∀ p, R p p = 0) : ‖opE R‖ ≤ n * -lamMin R := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Subsingleton.elim R 0, show opE (0 : Matrix (Fin 0) (Fin 0) ℝ) = 0 from map_zero _,
      norm_zero, Nat.cast_zero, zero_mul]
  have h := norm_opE_le_mul_lamMax (R := -R) hR.neg (fun p => by rw [neg_apply, hdiag, neg_zero])
  have e := lamMax_neg_smul hn R (H := 1) zero_le_one
  rw [one_smul, one_mul] at e
  rwa [norm_opE_neg, e] at h

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

variable (S) in
/-- **What partner weights reach** (`F = e^{H A₀}` fixed): the elements of the reach without
block-diagonal part. -/
def reachPW (Θ : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {Z | Z ∈ S.reach Θ ∧ S.blockDiag Z = 0}
  add_mem' := by
    rintro Z Z' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨(S.reach Θ).add_mem h1 h1', by rw [S.blockDiag_add, h2, h2', add_zero]⟩
  zero_mem' := ⟨(S.reach Θ).zero_mem, by
    ext p q
    rw [S.blockDiag_apply]
    split_ifs <;> rfl⟩
  smul_mem' := by
    rintro c Z ⟨h1, h2⟩
    exact ⟨(S.reach Θ).smul_mem c h1, by rw [S.blockDiag_smul, h2, smul_zero]⟩

/-- The symmetric part of an element of `reachPW` has zero diagonal. -/
theorem sym_apply_self_of_mem_reachPW {Θ Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : Z ∈ S.reachPW Θ) (p : Fin n) : sym Z p p = 0 := by
  have h : Z p p = 0 := by
    have := congrFun (congrFun hZ.2 p) p
    rwa [S.blockDiag_apply, ite_eq_left rfl, Matrix.zero_apply] at this
  simp [sym, h]

/-! ### The least values exist -/

/-- **The least injection value is attained** over `reachPW Θ`: some `Z₀` minimises
`λ_max (sym (P + Z))`. -/
theorem exists_least_injection_pw (P Θ : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n) :
    ∃ Z₀ ∈ S.reachPW Θ, ∀ Z ∈ S.reachPW Θ, lamMax (sym (P + Z₀)) ≤ lamMax (sym (P + Z)) := by
  let 𝓡 := (S.reachPW Θ).map symL
  have hR : ∀ R ∈ 𝓡, R.IsSymm ∧ ∀ p, R p p = 0 := by
    intro R hR
    obtain ⟨Z, hZ, rfl⟩ := Submodule.mem_map.1 hR
    exact ⟨isSymm_sym Z, S.sym_apply_self_of_mem_reachPW hZ⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨R₀, hR₀, hmin⟩ := exists_forall_le_of_coercive (𝓡 := 𝓡)
    (f := fun R => lamMax (sym P + R)) (L := 1) (c := 1 / n) (d := ‖opE (sym P)‖)
    (fun R R' => by
      have h := lamMax_add_le (sym P + R') (R - R')
      rw [show sym P + R' + (R - R') = sym P + R by abel] at h
      linarith)
    (by positivity) (fun R hRm => by
      obtain ⟨hs, hd⟩ := hR R hRm
      have h1 := norm_opE_le_mul_lamMax hs hd
      have h2 := lamMax_add_le (sym P + R) (-sym P)
      rw [show sym P + R + -sym P = R by abel, norm_opE_neg] at h2
      have h3 : 1 / (n : ℝ) * ‖opE R‖ ≤ lamMax R := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hnpos]
        linarith
      linarith)
  obtain ⟨Z₀, hZ₀, rfl⟩ := Submodule.mem_map.1 hR₀
  refine ⟨Z₀, hZ₀, fun Z hZ => ?_⟩
  have h : lamMax (sym P + sym Z₀) ≤ lamMax (sym P + sym Z) :=
    hmin (symL Z) (Submodule.mem_map_of_mem hZ)
  rwa [sym_add, sym_add]

/-- **The least added damping is attained** over `reachPW Θ`: some `Z₀` minimises
`-λ_min (sym (P + Z))`. -/
theorem exists_least_damping_pw (P Θ : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n) :
    ∃ Z₀ ∈ S.reachPW Θ, ∀ Z ∈ S.reachPW Θ, -lamMin (sym (P + Z₀)) ≤ -lamMin (sym (P + Z)) := by
  obtain ⟨Z₀, hZ₀, h⟩ := S.exists_least_injection_pw (-P) Θ hn
  refine ⟨-Z₀, (S.reachPW Θ).neg_mem hZ₀, fun Z hZ => ?_⟩
  have h1 := h (-Z) ((S.reachPW Θ).neg_mem hZ)
  have e : ∀ W : Matrix (Fin n) (Fin n) ℝ, lamMax (sym (-P + -W)) = -lamMin (sym (P + W)) := by
    intro W
    have := lamMax_neg_smul hn (sym (P + W)) (H := 1) zero_le_one
    rw [one_smul, one_mul, ← sym_neg, neg_add] at this
    exact this
  have e0 := e (-Z₀)
  rw [neg_neg] at e0
  rw [e Z, e0] at h1
  exact h1

/-! ### Every scheme of the class -/

/-- The second bracket has no block-diagonal part if no subsystem is its own partner. -/
theorem sample_bracket_blockDiag {A : Matrix (Fin n) (Fin n) ℝ} (H : ℝ)
    (hself : ∀ s, ¬ S.partner s s) :
    S.blockDiag (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) =
      0 := by
  ext p q
  rw [S.blockDiag_apply, Matrix.zero_apply]
  split_ifs with hpq
  · have hc : ∀ r, S.sub r = S.sub p → S.coupling A r q = 0 := fun r hr => by
      rw [S.coupling_apply, ite_eq_left (hr.trans hpq)]
    have h2 : (S.blockDiag A * S.coupling A) p q = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : S.sub p = S.sub r
      · rw [hc r hr.symm, mul_zero]
      · rw [S.blockDiag_apply, ite_eq_right hr, zero_mul]
    have hnp : ¬ S.partner (S.sub p) (S.sub q) := by rw [hpq]; exact hself _
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply, S.hM p q (fun h' => hnp h'.1), S.hN p q (fun h' => hnp h'.1),
      hc p rfl, h2]
    simp
  · rfl

/-- **The partner part of a scheme with exact local maps:** for a consistent scheme with
`F = e^{H A₀}` whose coupling and coefficients act through the outputs, no subsystem its own
partner, `0 < H`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, the matrix `Z' = H⁻² (M + N - H A_c - ½H² A₀ A_c)`
lies in `reachPW Θ` and `‖Δ - H (P + Z')‖ ≤ K H²`,
`K = diffLeadC b c ‖A‖ + √(card κ) C₃ + ‖A₀‖³/6 e^{H‖A₀‖}`. -/
theorem Consistent.exists_reachPW [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (hself : ∀ s, ¬ S.partner s s)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) :
    ∃ Z ∈ S.reachPW Θ, ‖opE (difference A H S.X - H • (S.halfStepTerm A + Z))‖ ≤
      (diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 := by
  set B1 := S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)
  set B2 := S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)
  set Z' := (H ^ 2)⁻¹ • B2
  have hZL : S.reachLead A H = (H ^ 2)⁻¹ • B1 + Z' := by rw [reachLead, smul_add]
  -- `Z'` is in `reachPW`
  have hZ'r : Z' ∈ S.reach Θ := by
    have hmem := h.reachLead_mem hΘ hAΘ hGΘ
    have hB1 : (H ^ 2)⁻¹ • B1 ∈ S.reach Θ := S.mem_reach_of_block fun p q hne => by
      rw [Matrix.smul_apply, show B1 p q = 0 from S.local_bracket_apply_eq_zero A H hne,
        smul_zero]
    have := (S.reach Θ).sub_mem hmem hB1
    rwa [hZL, add_sub_cancel_left] at this
  have hZ' : Z' ∈ S.reachPW Θ := ⟨hZ'r, by
    rw [S.blockDiag_smul, show S.blockDiag B2 = 0 from S.sample_bracket_blockDiag H hself,
      smul_zero]⟩
  refine ⟨Z', hZ', ?_⟩
  -- the estimate
  have h1 := h.norm_difference_sub_le hH hbH hAH
  have h2 := h.norm_sub_reachLead_le hH.ne'
  have h3 : ‖opE B1‖ ≤
      ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 3 :=
    S.norm_local_bracket_le A hH.le hF
  have e1 : H ^ 2 • (S.halfStepTerm A + S.reachLead A H) =
      H ^ 2 • (S.halfStepTerm A + Z') + B1 := by
    rw [hZL, smul_add, smul_add, smul_add, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hH.ne'),
      one_smul]
    abel
  have e2 : S.X - U - H ^ 2 • (S.halfStepTerm A + Z') =
      (S.X - U - H ^ 2 • (S.halfStepTerm A + S.reachLead A H)) + B1 := by
    rw [e1]
    abel
  have e3 : H⁻¹ • (S.X - U - H ^ 2 • (S.halfStepTerm A + Z')) =
      H⁻¹ • (S.X - U) - H • (S.halfStepTerm A + Z') := by
    rw [smul_sub, smul_smul, show H⁻¹ * H ^ 2 = H by field_simp]
  have e : difference A H S.X - H • (S.halfStepTerm A + Z') =
      (difference A H S.X - H⁻¹ • (S.X - U)) +
        (H⁻¹ • (S.X - U - H ^ 2 • (S.halfStepTerm A + S.reachLead A H)) + H⁻¹ • B1) := by
    rw [← smul_add, ← e2, e3]
    abel
  rw [e, OneStep.opE_add, OneStep.opE_add]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add le_rfl (norm_add_le _ _)).trans ?_
  have n2 : ‖opE (H⁻¹ • (S.X - U - H ^ 2 • (S.halfStepTerm A + S.reachLead A H)))‖ ≤
      Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H ^ 2 := by
    rw [OneStep.opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le),
      inv_mul_le_iff₀ hH]
    exact h2.trans_eq (by ring)
  have n3 : ‖opE (H⁻¹ • B1)‖ ≤
      ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖) * H ^ 2 := by
    rw [OneStep.opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le),
      inv_mul_le_iff₀ hH]
    exact h3.trans_eq (by ring)
  linarith

/-- **The least injection rate with partner weights only, every scheme** (`ι ≥ H i_σ - O(H²)`).
For a consistent scheme with `F = e^{H A₀}` (the class of partner weights) whose coupling and
coefficients act through the outputs, no subsystem its own partner, `0 < H`, `b H ≤ 1/3`,
`H ‖A‖ ≤ 1/4`, every `i ≤ λ_max (sym (½ A_ς A + Z))` on `reachPW Θ`, and every bound `ι` of the
injection (`-ι ‖v‖² ≤ ⟪v, Δ_R v⟫`): `H i - K H² ≤ ι`. -/
theorem Consistent.least_injection_pw_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (hn : 0 < n) (hself : ∀ s, ¬ S.partner s s)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) {i : ℝ}
    (hi : ∀ Z ∈ S.reachPW Θ, i ≤ lamMax (sym (S.halfStepTerm A + Z))) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H * i - (diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 ≤ ι := by
  obtain ⟨Z, hZ, hE⟩ := h.exists_reachPW hH hbH hAH hself hF hΘ hAΘ hGΘ
  set K := diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
    ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)
  have := nonempty_sphere hn
  have hmax : lamMax (sym (S.halfStepTerm A + Z)) ≤ (ι + K * H ^ 2) / H := by
    refine lamMax_le_of fun x => ?_
    have h1 := hlo x
    rw [inner_numDissipation_self] at h1
    have h2 := abs_le.1 (abs_inner_opE_self_le
      (difference A H S.X - H • (S.halfStepTerm A + Z)) x)
    have h3 : ⟪x, opE (difference A H S.X - H • (S.halfStepTerm A + Z)) x⟫ =
        ⟪x, opE (modifiedSystem H S.X - A) x⟫ - H * ⟪x, opE (S.halfStepTerm A + Z) x⟫ := by
      rw [inner_opE_sub, inner_opE_smul]
      rfl
    have h4 := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖x‖)
    have h5 : ⟪x, opE (sym (S.halfStepTerm A + Z)) x⟫ = ⟪x, opE (S.halfStepTerm A + Z) x⟫ := by
      rw [inner_sym]
      ring
    rw [h5, div_mul_eq_mul_div, le_div_iff₀ hH]
    nlinarith [h2.1]
  have h6 := hi Z hZ
  rw [le_div_iff₀ hH] at hmax
  nlinarith

/-- **The least added damping with partner weights only, every scheme** (`μ ≥ H m_σ - O(H²)`).
Under the hypotheses of `Consistent.least_injection_pw_le`, for every
`m ≤ -λ_min (sym (½ A_ς A + Z))` on `reachPW Θ` and every bound `μ` of the added damping
(`⟪v, Δ_R v⟫ ≤ μ ‖v‖²`): `H m - K H² ≤ μ`. -/
theorem Consistent.least_damping_pw_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ}
    {H a b c : ℝ} (h : S.Consistent A U H a b c) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (hn : 0 < n) (hself : ∀ s, ¬ S.partner s s)
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) {m : ℝ}
    (hm : ∀ Z ∈ S.reachPW Θ, m ≤ -lamMin (sym (S.halfStepTerm A + Z))) {μ : ℝ}
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H * m - (diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 2 ≤ μ := by
  obtain ⟨Z, hZ, hE⟩ := h.exists_reachPW hH hbH hAH hself hF hΘ hAΘ hGΘ
  set K := diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H +
    ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)
  have := nonempty_sphere hn
  have hmin : -((μ + K * H ^ 2) / H) ≤ lamMin (sym (S.halfStepTerm A + Z)) := by
    refine le_lamMin_of fun x => ?_
    have h1 := hhi x
    rw [inner_numDissipation_self] at h1
    have h2 := abs_le.1 (abs_inner_opE_self_le
      (difference A H S.X - H • (S.halfStepTerm A + Z)) x)
    have h3 : ⟪x, opE (difference A H S.X - H • (S.halfStepTerm A + Z)) x⟫ =
        ⟪x, opE (modifiedSystem H S.X - A) x⟫ - H * ⟪x, opE (S.halfStepTerm A + Z) x⟫ := by
      rw [inner_opE_sub, inner_opE_smul]
      rfl
    have h4 := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖x‖)
    have h5 : ⟪x, opE (sym (S.halfStepTerm A + Z)) x⟫ = ⟪x, opE (S.halfStepTerm A + Z) x⟫ := by
      rw [inner_sym]
      ring
    rw [h5]
    have key : -(μ + K * H ^ 2) * ‖x‖ ^ 2 ≤ H * ⟪x, opE (S.halfStepTerm A + Z) x⟫ := by
      nlinarith [h2.2]
    rw [show -((μ + K * H ^ 2) / H) * ‖x‖ ^ 2 = (-(μ + K * H ^ 2) * ‖x‖ ^ 2) / H by ring,
      div_le_iff₀ hH]
    linarith
  have h6 := hm Z hZ
  have h7 : -lamMin (sym (S.halfStepTerm A + Z)) ≤ (μ + K * H ^ 2) / H := by linarith
  rw [le_div_iff₀ hH] at h7
  nlinarith

/-! ### Attained in the class -/

/-- **The least injection rate with partner weights only is attained** (attainment, in the
coefficient class). For `A` without blocks between subsystems that are not partners, `A_c Θ = 0`,
at least one state: there is `Z₀ ∈ reachPW Θ` minimising `λ_max (sym (½ A_ς A + Z))`, and its
scheme `reachScheme` has exact local maps `F = e^{H A₀}`, coefficients acting through the outputs,
and injection rate `|-λ_min (Δ_R) - H λ_max (sym (½ A_ς A + Z₀))| ≤ K' H²` for `0 < H`,
`‖A‖ ≤ β`, `‖Z₀‖ ≤ β²`, `H β ≤ 1/27`, `σ H β ≤ 1/6`. -/
theorem least_injection_pw_attained [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hAΘ : S.coupling A * Θ = 0) (hn : 0 < n) :
    ∃ Z₀, ∃ hZ₀ : Z₀ ∈ S.reachPW Θ,
      (∀ Z ∈ S.reachPW Θ, lamMax (sym (S.halfStepTerm A + Z₀)) ≤
        lamMax (sym (S.halfStepTerm A + Z))) ∧
      ∀ {H β : ℝ}, 0 < H → ‖opE A‖ ≤ β → ‖opE Z₀‖ ≤ β ^ 2 → H * β ≤ 1 / 27 →
        Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6 →
        (S.reachScheme A hA Z₀ hZ₀.1.1 H).F = NormedSpace.exp (H • S.blockDiag A) ∧
        ((S.reachScheme A hA Z₀ hZ₀.1.1 H).M + (S.reachScheme A hA Z₀ hZ₀.1.1 H).N) * Θ = 0 ∧
        |-lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z₀ hZ₀.1.1 H).X)) -
            H * lamMax (sym (S.halfStepTerm A + Z₀))| ≤
          (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
            reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 := by
  obtain ⟨Z₀, hZ₀, hmin⟩ := S.exists_least_injection_pw (S.halfStepTerm A) Θ hn
  refine ⟨Z₀, hZ₀, hmin, fun {H β} hH hAβ hZβ hβH hσ => ⟨?_, reachScheme_samples_mul_eq_zero hAΘ
    hZ₀.1.2, ?_⟩⟩
  · rw [reachScheme_F, hZ₀.2, smul_zero, add_zero]
  · obtain ⟨-, h2⟩ := reachScheme_extremes (hA := hA) (hZ := hZ₀.1.1) hn hH hAβ hZβ hβH hσ
    rw [show -lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z₀ hZ₀.1.1 H).X)) -
        H * lamMax (sym (S.halfStepTerm A + Z₀)) =
        -(lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z₀ hZ₀.1.1 H).X)) +
          H * lamMax (sym (S.halfStepTerm A + Z₀))) by ring, abs_neg]
    exact h2

/-- **The least added damping with partner weights only is attained** (attainment, in the
coefficient class): as `least_injection_pw_attained`, for `-λ_min` and the added damping
`μ = λ_max (Δ_R)`. -/
theorem least_damping_pw_attained [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hAΘ : S.coupling A * Θ = 0) (hn : 0 < n) :
    ∃ Z₀, ∃ hZ₀ : Z₀ ∈ S.reachPW Θ,
      (∀ Z ∈ S.reachPW Θ, -lamMin (sym (S.halfStepTerm A + Z₀)) ≤
        -lamMin (sym (S.halfStepTerm A + Z))) ∧
      ∀ {H β : ℝ}, 0 < H → ‖opE A‖ ≤ β → ‖opE Z₀‖ ≤ β ^ 2 → H * β ≤ 1 / 27 →
        Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6 →
        (S.reachScheme A hA Z₀ hZ₀.1.1 H).F = NormedSpace.exp (H • S.blockDiag A) ∧
        ((S.reachScheme A hA Z₀ hZ₀.1.1 H).M + (S.reachScheme A hA Z₀ hZ₀.1.1 H).N) * Θ = 0 ∧
        |lamMax (numDissipation A (modifiedSystem H (S.reachScheme A hA Z₀ hZ₀.1.1 H).X)) -
            H * -lamMin (sym (S.halfStepTerm A + Z₀))| ≤
          (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
            reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 := by
  obtain ⟨Z₀, hZ₀, hmin⟩ := S.exists_least_damping_pw (S.halfStepTerm A) Θ hn
  refine ⟨Z₀, hZ₀, hmin, fun {H β} hH hAβ hZβ hβH hσ => ⟨?_, reachScheme_samples_mul_eq_zero hAΘ
    hZ₀.1.2, ?_⟩⟩
  · rw [reachScheme_F, hZ₀.2, smul_zero, add_zero]
  · obtain ⟨h1, -⟩ := reachScheme_extremes (hA := hA) (hZ := hZ₀.1.1) hn hH hAβ hZβ hβH hσ
    rw [show lamMax (numDissipation A (modifiedSystem H (S.reachScheme A hA Z₀ hZ₀.1.1 H).X)) -
        H * -lamMin (sym (S.halfStepTerm A + Z₀)) =
        lamMax (numDissipation A (modifiedSystem H (S.reachScheme A hA Z₀ hZ₀.1.1 H).X)) +
          H * lamMin (sym (S.halfStepTerm A + Z₀)) by ring]
    exact h1

/-! ### Groups of mutually non-partner subsystems -/

section Groups

variable {G : Type*} [Fintype G] [DecidableEq G] {mk : G → ℕ}

/-- The matrix that keeps the entries within the groups of `σ`. -/
def withinGroups (σ : (Σ k, Fin (mk k)) ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if (σ.symm p).1 = (σ.symm q).1 then M p q else 0

/-- A matrix of `reachPW 0` has no entries within a group, if subsystems lie in one group and
partners in different groups. -/
theorem reachPW_apply_within (σ : (Σ k, Fin (mk k)) ≃ Fin n)
    (hgrp : ∀ p q, S.sub p ≠ S.sub q →
      (S.partner (S.sub p) (S.sub q) ↔ (σ.symm p).1 ≠ (σ.symm q).1))
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ S.reachPW 0) {p q : Fin n}
    (hpq : (σ.symm p).1 = (σ.symm q).1) : Z p q = 0 := by
  by_cases hs : S.sub p = S.sub q
  · have := congrFun (congrFun hZ.2 p) q
    rwa [S.blockDiag_apply, ite_eq_left hs, Matrix.zero_apply] at this
  · exact hZ.1.1 p q hs fun h => ((hgrp p q hs).1 h) hpq

/-- The symmetric part of `P + Z` has the blocks of `sym P` on the groups. -/
theorem partBlock_sym_add (σ : (Σ k, Fin (mk k)) ≃ Fin n)
    (hgrp : ∀ p q, S.sub p ≠ S.sub q →
      (S.partner (S.sub p) (S.sub q) ↔ (σ.symm p).1 ≠ (σ.symm q).1))
    (P : Matrix (Fin n) (Fin n) ℝ) {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ S.reachPW 0)
    (k : G) : partBlock σ (sym (P + Z)) k = partBlock σ (sym P) k := by
  ext i j
  simp only [partBlock, Matrix.submatrix_apply, sym_add, Matrix.add_apply]
  have h1 : Z (σ ⟨k, i⟩) (σ ⟨k, j⟩) = 0 :=
    S.reachPW_apply_within σ hgrp hZ (by simp)
  have h2 : Z (σ ⟨k, j⟩) (σ ⟨k, i⟩) = 0 :=
    S.reachPW_apply_within σ hgrp hZ (by simp)
  simp [sym, h1, h2]

/-- The cross-group part of `sym P`, negated, is in `reachPW 0`. -/
theorem neg_crossGroups_mem (σ : (Σ k, Fin (mk k)) ≃ Fin n)
    (hgrp : ∀ p q, S.sub p ≠ S.sub q →
      (S.partner (S.sub p) (S.sub q) ↔ (σ.symm p).1 ≠ (σ.symm q).1))
    (hsame : ∀ p q, S.sub p = S.sub q → (σ.symm p).1 = (σ.symm q).1)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    withinGroups σ (sym P) - sym P ∈ S.reachPW 0 := by
  refine ⟨⟨fun p q hne hnp => ?_, by rw [Matrix.mul_zero]⟩, ?_⟩
  · have hg : (σ.symm p).1 = (σ.symm q).1 := by
      by_contra hg
      exact hnp ((hgrp p q hne).2 hg)
    simp [withinGroups, hg]
  · ext p q
    rw [S.blockDiag_apply, Matrix.zero_apply]
    split_ifs with hs
    · simp [withinGroups, hsame p q hs]
    · rfl

/-- **The least injection value for groups** (equality; all states are outputs, `Θ = 0`):
if every subsystem lies in one group and two subsystems are partners exactly when they lie in
different groups (all groups nonempty), then the least `λ_max (sym (P + Z))` over `reachPW 0` is
the largest `λ_max` of the blocks of `sym P` on the groups. -/
theorem isLeast_injection_pw_groups (σ : (Σ k, Fin (mk k)) ≃ Fin n) (hmk : ∀ k, 0 < mk k)
    (hgrp : ∀ p q, S.sub p ≠ S.sub q →
      (S.partner (S.sub p) (S.sub q) ↔ (σ.symm p).1 ≠ (σ.symm q).1))
    (hsame : ∀ p q, S.sub p = S.sub q → (σ.symm p).1 = (σ.symm q).1)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    IsLeast {r | ∃ Z ∈ S.reachPW 0, r = lamMax (sym (P + Z))}
      (⨆ k, lamMax (partBlock σ (sym P) k)) := by
  have hemb : ∀ k, Function.Injective (fun i : Fin (mk k) => σ ⟨k, i⟩) := fun k =>
    σ.injective.comp sigma_mk_injective
  refine ⟨⟨_, S.neg_crossGroups_mem σ hgrp hsame P, ?_⟩, ?_⟩
  · have e : sym (P + (withinGroups σ (sym P) - sym P)) = withinGroups σ (sym P) := by
      rw [sym_add, sym_sub, sym_of_isSymm (isSymm_sym P), add_sub_cancel]
      refine sym_of_isSymm ?_
      ext p q
      simp only [withinGroups, Matrix.transpose_apply, Matrix.of_apply]
      by_cases hg : (σ.symm p).1 = (σ.symm q).1
      · rw [ite_eq_left hg.symm, ite_eq_left hg]
        exact (isSymm_sym P).apply p q
      · rw [ite_eq_right fun e => hg e.symm, ite_eq_right hg]
    rw [e, lamMax_eq_iSup_parts σ _ (fun a b hab => by simp [withinGroups, hab]) hmk]
    congr 1
    funext k
    congr 1
    ext i j
    simp [partBlock, withinGroups]
  · rintro _ ⟨Z, hZ, rfl⟩
    rcases isEmpty_or_nonempty G with hG | hG
    · have := isEmpty_sphere_of_isEmpty σ
      rw [Real.iSup_of_isEmpty, (lamMax_lamMin_of_isEmpty _).1]
    · refine ciSup_le fun k => ?_
      rw [← S.partBlock_sym_add σ hgrp P hZ k]
      exact lamMax_submatrix_le (hmk k) _ (hemb k)

/-- **The least added damping for groups** (equality; `Θ = 0`): under the hypotheses of
`isLeast_injection_pw_groups`, the least `-λ_min (sym (P + Z))` over `reachPW 0` is
`-min_k λ_min` of the blocks of `sym P` on the groups. -/
theorem isLeast_damping_pw_groups (σ : (Σ k, Fin (mk k)) ≃ Fin n) (hmk : ∀ k, 0 < mk k)
    (hgrp : ∀ p q, S.sub p ≠ S.sub q →
      (S.partner (S.sub p) (S.sub q) ↔ (σ.symm p).1 ≠ (σ.symm q).1))
    (hsame : ∀ p q, S.sub p = S.sub q → (σ.symm p).1 = (σ.symm q).1)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    IsLeast {r | ∃ Z ∈ S.reachPW 0, r = -lamMin (sym (P + Z))}
      (-⨅ k, lamMin (partBlock σ (sym P) k)) := by
  have hemb : ∀ k, Function.Injective (fun i : Fin (mk k) => σ ⟨k, i⟩) := fun k =>
    σ.injective.comp sigma_mk_injective
  refine ⟨⟨_, S.neg_crossGroups_mem σ hgrp hsame P, ?_⟩, ?_⟩
  · have e : sym (P + (withinGroups σ (sym P) - sym P)) = withinGroups σ (sym P) := by
      rw [sym_add, sym_sub, sym_of_isSymm (isSymm_sym P), add_sub_cancel]
      refine sym_of_isSymm ?_
      ext p q
      simp only [withinGroups, Matrix.transpose_apply, Matrix.of_apply]
      by_cases hg : (σ.symm p).1 = (σ.symm q).1
      · rw [ite_eq_left hg.symm, ite_eq_left hg]
        exact (isSymm_sym P).apply p q
      · rw [ite_eq_right fun e => hg e.symm, ite_eq_right hg]
    rw [e, lamMin_eq_iInf_parts σ _ (fun a b hab => by simp [withinGroups, hab]) hmk]
    congr 2
    funext k
    congr 1
    ext i j
    simp [partBlock, withinGroups]
  · rintro _ ⟨Z, hZ, rfl⟩
    rcases isEmpty_or_nonempty G with hG | hG
    · have := isEmpty_sphere_of_isEmpty σ
      rw [Real.iInf_of_isEmpty, (lamMax_lamMin_of_isEmpty _).2]
    · refine neg_le_neg (le_ciInf fun k => ?_)
      rw [← S.partBlock_sym_add σ hgrp P hZ k]
      exact lamMin_le_lamMin_submatrix (hmk k) _ (hemb k)

end Groups

end HeldScheme

end CoSimFoundations
