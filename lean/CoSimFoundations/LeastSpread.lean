/-
The least spread of the numerical dissipation (the paper, Theorem "the amount", `cor:amount`, eq.
`eq:amount`).

**Paper.** `d_σ = min_{Z ∈ 𝒵} ‖sym (½ A_ς A + Z)‖`. To leading order the injection rates and added
dampings of the schemes with one held sample fill the half-plane `μ + ι ≥ 2 H d_σ`: every scheme
has `μ + ι ≥ 2 H d_σ - O(H²)`, and for all `a`, `b` with `a + b ≥ 2 d_σ` some scheme has
`ι = H a + O(H²)` and `μ = H b + O(H²)`. For subsystems `i ≠ j` that are not partners,
`2 d_σ ≥ ‖Σ_k τ_k A_ik A_kj‖`, `τ_k = ½ (ς_ik + ς_jk)`.

**What is formalised.** Setting of `Reach` and `AmountLead`: `P = halfStepTerm A`, the reach
`reach Θ`, `Δ_R = numDissipation A (modifiedSystem H X) = -sym Δ`, `λ_max`, `λ_min`, `spr` of
`ReachCompletion` (the extreme values of the form). The injection rate is `ι = -λ_min (Δ_R)`, the
added damping `μ = λ_max (Δ_R)`; the lower bound holds for all bounds `μ`, `ι` of the form.

* **Extreme values** (`lamMax_add_le`, `le_lamMin_add`, `abs_lamMax_add_sub_le`,
  `abs_lamMin_add_sub_le`, `lamMax_sub_smul_one`, `lamMin_sub_smul_one`, `lamMax_neg_smul`,
  `lamMin_neg_smul`): `λ_max`, `λ_min` move by at most `‖E‖` under `M ↦ M + E`, shift with
  `c 1`, and `λ_max (-H M) = -H λ_min (M)` for `H ≥ 0`.
* **The least value** (`exists_isLeast_sym_reach`): `d = min_{Z ∈ reach Θ} ‖sym (P + Z)‖` is
  attained, and the least spread of `sym (P + Z)` over the reach is `2 d`.
* **Every scheme** (`Consistent.least_spread_le`): for a consistent scheme whose coupling and
  coefficients act through the outputs, `0 < H`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, and all `μ`, `ι` with
  `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫ ≤ μ ‖v‖²`: `μ + ι ≥ 2 H d - 2 (K + √(card κ) C₃) H²`,
  `K = diffLeadC b c ‖A‖`, `C₃ = reactionC a b c ‖A‖ H`.
* **The scheme that reaches `Z`** (`norm_numDissipation_reachScheme_le`,
  `reachScheme_extremes`): `‖Δ_R + H sym (P + Z)‖ ≤ (K + reachK σ β) H²`, hence
  `|λ_max (Δ_R) + H λ_min (sym (P + Z))|` and `|λ_min (Δ_R) + H λ_max (sym (P + Z))|` are at most
  that, for `‖A‖ ≤ β`, `‖Z‖ ≤ β²`, `H β ≤ 1/27`, `σ H β ≤ 1/6`.
* **Every point of the half-plane** (`exists_reach_extremes`, `least_spread_attained`): if two
  states lie in different subsystems, then for all `a`, `b` with `a + b ≥ 2 d` there is `Z` in
  the reach with `λ_max (sym (P + Z)) = a`, `λ_min (sym (P + Z)) = -b` (a minimiser plus a multiple
  of the mask of one subsystem, by the intermediate value theorem, minus a multiple of `1`), and
  its scheme has `|ι - H a| ≤ K' H²`, `|μ - H b| ≤ K' H²`.
* **The pair bound** (`abs_inner_pair_le_least`, eq. `eq:amount`): with skew coupling, for
  subsystems `s ≠ t` that are not partners, `x` supported on `s` and `y` on `t`,
  `|⟪x, ½ A (ς_s + ς_t) A y⟫| ≤ 2 d ‖x‖ ‖y‖`, where `½ A (ς_s + ς_t) A` has the block
  `Σ_k τ_k A_sk A_kt` between `s` and `t`.

The equality in eq. `eq:amount` for disjoint forced pairs is not formalised here (the matrix fact
is `pair_blocks` of `ReachCompletionExamples`).
-/
import CoSimFoundations.Reach
import CoSimFoundations.AmountLead

open Matrix Metric
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

/-! ### The symmetric part is linear -/

section Sym

theorem sym_add (M N : Matrix (Fin n) (Fin n) ℝ) : sym (M + N) = sym M + sym N := by
  rw [sym, sym, sym, transpose_add, ← smul_add]
  congr 1
  abel

theorem sym_sub (M N : Matrix (Fin n) (Fin n) ℝ) : sym (M - N) = sym M - sym N := by
  rw [sym, sym, sym, transpose_sub, ← smul_sub]
  congr 1
  abel

theorem sym_smul (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : sym (c • M) = c • sym M := by
  rw [sym, sym, transpose_smul, ← smul_add, smul_comm]

theorem sym_neg (M : Matrix (Fin n) (Fin n) ℝ) : sym (-M) = -sym M := by
  rw [sym, sym, transpose_neg, ← neg_add, smul_neg]

/-- The symmetric part of a symmetric matrix is the matrix. -/
theorem sym_of_isSymm {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) : sym M = M := by
  rw [sym, hM.eq, ← two_smul ℝ M, smul_smul]
  norm_num

/-- The symmetric part is symmetric. -/
theorem isSymm_sym (M : Matrix (Fin n) (Fin n) ℝ) : (sym M).IsSymm := by
  unfold Matrix.IsSymm sym
  rw [transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- `‖opE (-E)‖ = ‖opE E‖`. -/
theorem norm_opE_neg (E : Matrix (Fin n) (Fin n) ℝ) : ‖opE (-E)‖ = ‖opE E‖ := by
  rw [show opE (-E) = -opE E from map_neg (toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) E, norm_neg]

/-- The symmetric part is not larger than the matrix. -/
theorem norm_opE_sym_le (M : Matrix (Fin n) (Fin n) ℝ) : ‖opE (sym M)‖ ≤ ‖opE M‖ := by
  rw [sym, opE_smul, norm_smul, opE_add]
  have h1 := norm_add_le (opE M) (opE Mᵀ)
  rw [norm_opE_transpose] at h1
  rw [Real.norm_of_nonneg (by norm_num)]
  linarith

/-- The matrix element of the symmetric part: `⟪x, sym M y⟫ = ½ (⟪x, M y⟫ + ⟪y, M x⟫)`. -/
theorem inner_sym (M : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (sym M) y⟫ = 1 / 2 * (⟪x, opE M y⟫ + ⟪y, opE M x⟫) := by
  rw [sym, inner_opE_smul, inner_opE_add, ← OneStep.inner_opE_transpose M x y]

/-- The symmetric part as a linear map. -/
noncomputable def symL : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := sym
  map_add' := sym_add
  map_smul' := sym_smul

end Sym

/-! ### The extreme values of the form -/

section Extremes

/-- `λ_max (M + E) ≤ λ_max (M) + ‖E‖`. -/
theorem lamMax_add_le (M E : Matrix (Fin n) (Fin n) ℝ) :
    lamMax (M + E) ≤ lamMax M + ‖opE E‖ := by
  rcases isEmpty_or_nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with h | h
  · rw [(lamMax_lamMin_of_isEmpty (M + E)).1, (lamMax_lamMin_of_isEmpty M).1, zero_add]
    exact norm_nonneg _
  · refine lamMax_le_of fun x => ?_
    rw [inner_opE_add, add_mul]
    have h1 := inner_le_lamMax M x
    have h2 := (le_abs_self _).trans (abs_inner_opE_self_le E x)
    linarith

/-- `λ_min (M) - ‖E‖ ≤ λ_min (M + E)`. -/
theorem le_lamMin_add (M E : Matrix (Fin n) (Fin n) ℝ) :
    lamMin M - ‖opE E‖ ≤ lamMin (M + E) := by
  rcases isEmpty_or_nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with h | h
  · rw [(lamMax_lamMin_of_isEmpty (M + E)).2, (lamMax_lamMin_of_isEmpty M).2, zero_sub,
      neg_nonpos]
    exact norm_nonneg _
  · refine le_lamMin_of fun x => ?_
    rw [inner_opE_add, sub_mul]
    have h1 := lamMin_le_inner M x
    have h2 := neg_le_of_abs_le (abs_inner_opE_self_le E x)
    linarith

/-- `|λ_max (M + E) - λ_max (M)| ≤ ‖E‖`. -/
theorem abs_lamMax_add_sub_le (M E : Matrix (Fin n) (Fin n) ℝ) :
    |lamMax (M + E) - lamMax M| ≤ ‖opE E‖ := by
  have h1 := lamMax_add_le M E
  have h2 := lamMax_add_le (M + E) (-E)
  rw [add_neg_cancel_right, norm_opE_neg] at h2
  rw [abs_le]
  constructor <;> linarith

/-- `|λ_min (M + E) - λ_min (M)| ≤ ‖E‖`. -/
theorem abs_lamMin_add_sub_le (M E : Matrix (Fin n) (Fin n) ℝ) :
    |lamMin (M + E) - lamMin M| ≤ ‖opE E‖ := by
  have h1 := le_lamMin_add M E
  have h2 := le_lamMin_add (M + E) (-E)
  rw [add_neg_cancel_right, norm_opE_neg] at h2
  rw [abs_le]
  constructor <;> linarith

/-- `|spr (M + E) - spr (M)| ≤ 2 ‖E‖`. -/
theorem abs_spr_add_sub_le (M E : Matrix (Fin n) (Fin n) ℝ) :
    |spr (M + E) - spr M| ≤ 2 * ‖opE E‖ := by
  have h1 := abs_le.1 (abs_lamMax_add_sub_le M E)
  have h2 := abs_le.1 (abs_lamMin_add_sub_le M E)
  rw [spr, spr, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `λ_max (M - c 1) = λ_max (M) - c` (`n ≥ 1`). -/
theorem lamMax_sub_smul_one (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    lamMax (M - c • 1) = lamMax M - c := by
  have := nonempty_sphere hn
  refine le_antisymm (lamMax_le_of fun x => ?_) ?_
  · rw [inner_opE_sub_smul_one, sub_mul]
    linarith [inner_le_lamMax M x]
  · have h : lamMax M ≤ lamMax (M - c • 1) + c := lamMax_le_of fun x => by
      have h1 := inner_le_lamMax (M - c • 1) x
      rw [inner_opE_sub_smul_one] at h1
      rw [add_mul]
      linarith
    linarith

/-- `λ_min (M - c 1) = λ_min (M) - c` (`n ≥ 1`). -/
theorem lamMin_sub_smul_one (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    lamMin (M - c • 1) = lamMin M - c := by
  have := nonempty_sphere hn
  refine le_antisymm ?_ (le_lamMin_of fun x => ?_)
  · have h : lamMin M - c ≤ lamMin (M - c • 1) := le_lamMin_of fun x => by
      have h1 := lamMin_le_inner M x
      rw [inner_opE_sub_smul_one, sub_mul]
      linarith
    have h' : lamMin (M - c • 1) + c ≤ lamMin M := le_lamMin_of fun x => by
      have h1 := lamMin_le_inner (M - c • 1) x
      rw [inner_opE_sub_smul_one] at h1
      rw [add_mul]
      linarith
    linarith
  · rw [inner_opE_sub_smul_one, sub_mul]
    linarith [lamMin_le_inner M x]

/-- `λ_max (0) = 0` (`n ≥ 1`). -/
theorem lamMax_zero (hn : 0 < n) : lamMax (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  have := nonempty_sphere hn
  simp [lamMax]

/-- **`λ_max (-H M) = -H λ_min (M)`** for `H ≥ 0` (`n ≥ 1`). -/
theorem lamMax_neg_smul (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    lamMax (-(H • M)) = -(H * lamMin M) := by
  have := nonempty_sphere hn
  rcases hH.eq_or_lt with h0 | hpos
  · subst h0
    rw [zero_smul, neg_zero, zero_mul, neg_zero, lamMax_zero hn]
  have e : ∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE (-(H • M)) x⟫ = -(H * ⟪x, opE M x⟫) := by
    intro x
    rw [show -(H • M) = (-H) • M by rw [neg_smul], inner_opE_smul]
    ring
  refine le_antisymm (lamMax_le_of fun x => ?_) ?_
  · rw [e]
    have h1 := mul_le_mul_of_nonneg_left (lamMin_le_inner M x) hpos.le
    linarith
  · have h : -lamMax (-(H • M)) / H ≤ lamMin M := le_lamMin_of fun x => by
      have h1 := inner_le_lamMax (-(H • M)) x
      rw [e] at h1
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      linarith
    rw [div_le_iff₀ hpos] at h
    linarith

/-- **`λ_min (-H M) = -H λ_max (M)`** for `H ≥ 0` (`n ≥ 1`). -/
theorem lamMin_neg_smul (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) {H : ℝ} (hH : 0 ≤ H) :
    lamMin (-(H • M)) = -(H * lamMax M) := by
  have h := lamMax_neg_smul hn (-(H • M)) (H := 1) zero_le_one
  have e : -((1 : ℝ) • -(H • M)) = H • M := by rw [one_smul, neg_neg]
  rw [e, one_mul] at h
  -- `λ_max (H M) = H λ_max (M)`
  have h2 := lamMax_neg_smul hn (-M) hH
  rw [smul_neg, neg_neg] at h2
  have h3 := lamMax_neg_smul hn M (H := 1) zero_le_one
  rw [one_smul, one_mul] at h3
  have h4 := lamMax_neg_smul hn (-M) (H := 1) zero_le_one
  rw [one_smul, neg_neg, one_mul] at h4
  -- `λ_min (-M) = -λ_max (M)`
  have h5 : lamMin (-M) = -lamMax M := by linarith
  rw [h2, h5] at h
  linarith

end Extremes

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

/-! ### The least value -/

/-- **The least norm and the least spread of the symmetric part over the reach** (`d_σ` is
attained, and `min_Z spr (sym (P + Z)) = 2 d_σ`, since `c 1 ∈ reach Θ`). -/
theorem exists_isLeast_sym_reach (P : Matrix (Fin n) (Fin n) ℝ) (Θ : Matrix (Fin n) (Fin n) ℝ) :
    ∃ d, IsLeast {r | ∃ Z ∈ S.reach Θ, r = ‖opE (sym (P + Z))‖} d ∧
      IsLeast {r | ∃ Z ∈ S.reach Θ, r = spr (sym (P + Z))} (2 * d) := by
  let 𝓡 := (S.reach Θ).map symL
  have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ 𝓡 :=
    Submodule.mem_map.2 ⟨1, S.one_mem_reach Θ, sym_of_isSymm isSymm_one⟩
  have hsym : ∀ R ∈ 𝓡, R.IsSymm := by
    intro R hR
    obtain ⟨Z, -, rfl⟩ := Submodule.mem_map.1 hR
    exact isSymm_sym Z
  obtain ⟨d, hd1, hd2⟩ := exists_isLeast_norm_isLeast_spr (isSymm_sym P) h1 hsym
  have e : ∀ Z, sym (P + Z) = sym P + symL Z := fun Z => sym_add P Z
  refine ⟨d, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨R, hR, hR'⟩ := hd1.1
    obtain ⟨Z, hZ, rfl⟩ := Submodule.mem_map.1 hR
    exact ⟨Z, hZ, by rw [e]; exact hR'⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    rw [e]
    exact hd1.2 ⟨_, Submodule.mem_map_of_mem hZ, rfl⟩
  · obtain ⟨R, hR, hR'⟩ := hd2.1
    obtain ⟨Z, hZ, rfl⟩ := Submodule.mem_map.1 hR
    exact ⟨Z, hZ, by rw [e]; exact hR'⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    rw [e]
    exact hd2.2 ⟨_, Submodule.mem_map_of_mem hZ, rfl⟩

/-! ### Every scheme -/

/-- `Δ_R = -sym Δ`. -/
theorem numDissipation_eq_neg_sym (A At : Matrix (Fin n) (Fin n) ℝ) :
    numDissipation A At = -sym (At - A) := rfl

/-- **The least spread, every scheme** (the paper, `cor:amount`: `μ + ι ≥ 2 H d_σ - O(H²)`). For a
consistent scheme whose coupling and coefficients of the samples act through the outputs,
`0 < H`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`, at least one state, every `d ≤ ‖sym (½ A_ς A + Z)‖` on the
reach, and all `μ`, `ι` with `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫ ≤ μ ‖v‖²`:
`2 H d - 2 (K + √(card κ) C₃) H² ≤ μ + ι`, `K = diffLeadC b c ‖A‖`, `C₃ = reactionC a b c ‖A‖ H`. -/
theorem Consistent.least_spread_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) (hn : 0 < n) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) {d : ℝ}
    (hd : ∀ Z ∈ S.reach Θ, d ≤ ‖opE (sym (S.halfStepTerm A + Z))‖) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    2 * H * d - 2 * (diffLeadC b c ‖opE A‖ +
        Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H) * H ^ 2 ≤ μ + ι := by
  set K := diffLeadC b c ‖opE A‖ + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H
  set Δ := difference A H S.X
  set Z := S.reachLead A H
  have hZ : Z ∈ S.reach Θ := h.reachLead_mem hΘ hAΘ hGΘ
  -- `Δ = H (P + Z) + E`, `‖E‖ ≤ K H²`
  have hE : ‖opE (Δ - H • (S.halfStepTerm A + Z))‖ ≤ K * H ^ 2 := by
    have h1 := h.norm_difference_sub_halfStepLead_le hH hbH hAH
    rwa [S.halfStepLead_eq A hH.ne', smul_smul,
      show H⁻¹ * H ^ 2 = H by field_simp] at h1
  set E := Δ - H • (S.halfStepTerm A + Z) with hEdef
  -- `μ + ι ≥ 0`
  have hμι : 0 ≤ μ + ι := by
    obtain ⟨u⟩ := nonempty_sphere hn
    have h1 := hlo u
    have h2 := hhi u
    rw [mem_sphere_zero_iff_norm.1 u.2] at h1 h2
    linarith
  -- the centred numerical dissipation
  set T := numDissipation A (modifiedSystem H S.X) -
    ((μ - ι) / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) with hTdef
  have hT : ‖opE T‖ ≤ (μ + ι) / 2 := by
    have hsym : T.IsSymm := (isSymm_numDissipation A _).sub (isSymm_one.smul _)
    refine norm_opE_le_of_abs_inner_self_le hsym (by linarith) fun v => ?_
    rw [hTdef, inner_opE_sub_smul_one, abs_le]
    have h1 := hlo v
    have h2 := hhi v
    constructor <;> linarith
  -- `T = -H sym (P + Z') - sym E` with `Z' = Z + ((μ - ι)/(2H)) 1` in the reach
  set Z' := Z + ((μ - ι) / 2 / H) • (1 : Matrix (Fin n) (Fin n) ℝ) with hZ'def
  have hZ' : Z' ∈ S.reach Θ :=
    (S.reach Θ).add_mem hZ ((S.reach Θ).smul_mem _ (S.one_mem_reach Θ))
  have eT : T = -(H • sym (S.halfStepTerm A + Z')) - sym E := by
    have eΔ : Δ = H • (S.halfStepTerm A + Z) + E := by rw [hEdef]; abel
    have e1 : sym (S.halfStepTerm A + Z') =
        sym (S.halfStepTerm A + Z) + ((μ - ι) / 2 / H) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      rw [hZ'def, show S.halfStepTerm A + (Z + ((μ - ι) / 2 / H) • 1) =
        (S.halfStepTerm A + Z) + ((μ - ι) / 2 / H) • 1 by rw [add_assoc], sym_add, sym_smul,
        sym_of_isSymm isSymm_one]
    rw [hTdef, numDissipation_eq_neg_sym, show modifiedSystem H S.X - A = Δ from rfl, eΔ, e1,
      sym_add, sym_smul, smul_add, smul_smul, mul_div_cancel₀ _ hH.ne']
    abel
  have h3 : H * ‖opE (sym (S.halfStepTerm A + Z'))‖ ≤ (μ + ι) / 2 + K * H ^ 2 := by
    have e2 : H • sym (S.halfStepTerm A + Z') = -(T + sym E) := by rw [eT]; abel
    have h4 : ‖opE (H • sym (S.halfStepTerm A + Z'))‖ ≤ ‖opE T‖ + ‖opE (sym E)‖ := by
      rw [e2, norm_opE_neg, opE_add]
      exact norm_add_le _ _
    rw [opE_smul, norm_smul, Real.norm_of_nonneg hH.le] at h4
    linarith [norm_opE_sym_le E]
  have h5 := mul_le_mul_of_nonneg_left (hd Z' hZ') hH.le
  linarith

/-! ### The scheme that reaches `Z` -/

variable {A : Matrix (Fin n) (Fin n) ℝ}
  {hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0}
  {Z : Matrix (Fin n) (Fin n) ℝ}
  {hZ : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → Z p q = 0} {H : ℝ}

/-- **The numerical dissipation of the scheme that reaches `Z`:**
`‖Δ_R + H sym (½ A_ς A + Z)‖ ≤ (K + reachK σ β) H²`, `K = diffLeadC (9β) ((6 + 27σ) β²) ‖A‖`, for
`0 < H`, `‖A‖ ≤ β`, `‖Z‖ ≤ β²`, `H β ≤ 1/27`, `σ H β ≤ 1/6`. -/
theorem norm_numDissipation_reachScheme_le [Fintype κ] {β : ℝ} (hH : 0 < H)
    (hAβ : ‖opE A‖ ≤ β) (hZβ : ‖opE Z‖ ≤ β ^ 2) (hβH : H * β ≤ 1 / 27)
    (hσ : Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6) :
    ‖opE (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ H).X) +
        H • sym (S.halfStepTerm A + Z))‖ ≤
      (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
        reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans hAβ
  have hβH4 : H * β ≤ 1 / 4 := by linarith
  have hc := reachScheme_consistent (hA := hA) (hZ := hZ) hH.le hAβ hZβ hβH4 hσ
  have hbH : 9 * β * H ≤ 1 / 3 := by linarith
  have hAH : H * ‖opE A‖ ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hAβ hH.le).trans hβH4
  have h1 := hc.norm_difference_sub_le hH hbH hAH
  have h2 := norm_reachScheme_sub_le (hA := hA) (hZ := hZ) hH.le hAβ hZβ hβH4 hσ
  set X := (S.reachScheme A hA Z hZ H).X
  have e : numDissipation A (modifiedSystem H X) + H • sym (S.halfStepTerm A + Z) =
      -sym ((difference A H X - H⁻¹ • (X - NormedSpace.exp (H • A))) +
        H⁻¹ • (X - NormedSpace.exp (H • A) - H ^ 2 • (S.halfStepTerm A + Z))) := by
    have e2 : (difference A H X - H⁻¹ • (X - NormedSpace.exp (H • A))) +
        H⁻¹ • (X - NormedSpace.exp (H • A) - H ^ 2 • (S.halfStepTerm A + Z)) =
        difference A H X - H • (S.halfStepTerm A + Z) := by
      rw [smul_sub H⁻¹ (X - NormedSpace.exp (H • A)), smul_smul,
        show H⁻¹ * H ^ 2 = H by field_simp]
      abel
    rw [e2, sym_sub, sym_smul, numDissipation_eq_neg_sym]
    show -sym (difference A H X) + _ = _
    abel
  rw [e, norm_opE_neg]
  refine (norm_opE_sym_le _).trans ?_
  rw [opE_add]
  refine (norm_add_le _ _).trans ?_
  have h3 : ‖opE (H⁻¹ • (X - NormedSpace.exp (H • A) - H ^ 2 • (S.halfStepTerm A + Z)))‖ ≤
      reachK (Real.sqrt (Fintype.card κ)) β * H ^ 2 := by
    rw [opE_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le), inv_mul_le_iff₀ hH]
    exact h2.trans_eq (by ring)
  have h4 := add_le_add h1 h3
  linarith

/-- **The injection rate and the added damping of the scheme that reaches `Z`:** under the
hypotheses of `norm_numDissipation_reachScheme_le` and `n ≥ 1`,
`|λ_max (Δ_R) + H λ_min (sym (P + Z))| ≤ K' H²` and `|λ_min (Δ_R) + H λ_max (sym (P + Z))| ≤ K' H²`,
`K' = diffLeadC (9β) ((6 + 27σ) β²) ‖A‖ + reachK σ β`: `μ = -H λ_min + O(H²)`,
`ι = H λ_max + O(H²)`. -/
theorem reachScheme_extremes [Fintype κ] (hn : 0 < n) {β : ℝ} (hH : 0 < H)
    (hAβ : ‖opE A‖ ≤ β) (hZβ : ‖opE Z‖ ≤ β ^ 2) (hβH : H * β ≤ 1 / 27)
    (hσ : Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6) :
    |lamMax (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ H).X)) +
        H * lamMin (sym (S.halfStepTerm A + Z))| ≤
      (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
        reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 ∧
    |lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ H).X)) +
        H * lamMax (sym (S.halfStepTerm A + Z))| ≤
      (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
        reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 := by
  have h := norm_numDissipation_reachScheme_le (hA := hA) (hZ := hZ) hH hAβ hZβ hβH hσ
  set D := numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ H).X)
  set M := sym (S.halfStepTerm A + Z)
  have e : D = -(H • M) + (D + H • M) := by abel
  have h1 := abs_lamMax_add_sub_le (-(H • M)) (D + H • M)
  have h2 := abs_lamMin_add_sub_le (-(H • M)) (D + H • M)
  rw [← e, lamMax_neg_smul hn M hH.le] at h1
  rw [← e, lamMin_neg_smul hn M hH.le] at h2
  constructor
  · rw [show lamMax D + H * lamMin M = lamMax D - -(H * lamMin M) by ring]
    exact h1.trans h
  · rw [show lamMin D + H * lamMax M = lamMin D - -(H * lamMax M) by ring]
    exact h2.trans h

/-! ### Every point of the half-plane -/

/-- The mask of a subsystem is symmetric and in the reach. -/
theorem mask_mem_reach (Θ : Matrix (Fin n) (Fin n) ℝ) (s : κ) : S.mask s ∈ S.reach Θ :=
  S.mem_reach_of_block fun p q h => by
    rw [mask, diagonal_apply_ne _ fun e => h (congrArg S.sub e)]

/-- **Every point of the half-plane, the matrices**. If two states lie in
different subsystems and `d` is the least value of `‖sym (P + Z)‖` over the reach, then for all
`a`, `b` with `a + b ≥ 2 d` there is `Z ∈ reach Θ` with `λ_max (sym (P + Z)) = a` and
`λ_min (sym (P + Z)) = -b`. -/
theorem exists_reach_extremes (P : Matrix (Fin n) (Fin n) ℝ) {Θ : Matrix (Fin n) (Fin n) ℝ}
    {d : ℝ} (hd : IsLeast {r | ∃ Z ∈ S.reach Θ, r = ‖opE (sym (P + Z))‖} d) {p₀ q₀ : Fin n}
    (hpq : S.sub p₀ ≠ S.sub q₀) {a b : ℝ} (hab : 2 * d ≤ a + b) :
    ∃ Z ∈ S.reach Θ, lamMax (sym (P + Z)) = a ∧ lamMin (sym (P + Z)) = -b := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) p₀.isLt
  obtain ⟨⟨Z₀, hZ₀, hd₀⟩, -⟩ := hd
  obtain ⟨M, hMdef⟩ : ∃ M, M = sym (P + Z₀) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = S.mask (S.sub p₀) := ⟨_, rfl⟩
  rw [← hMdef] at hd₀
  have hd0 : 0 ≤ d := by rw [hd₀]; exact norm_nonneg _
  have hEs : sym E = E :=
    sym_of_isSymm (by rw [Matrix.IsSymm, hEdef, HeldScheme.mask, diagonal_transpose])
  have hEr : E ∈ S.reach Θ := hEdef ▸ mask_mem_reach Θ _
  have hEp : ∀ p, E p p = if S.sub p = S.sub p₀ then 1 else 0 := fun p => by
    rw [hEdef, HeldScheme.mask, diagonal_apply_eq]
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun t => spr (M + t • E) := ⟨_, rfl⟩
  -- continuity
  have hf : Continuous f := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (2 * ‖opE E‖))
      fun t t' => ?_).continuous
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq, hfdef]
    have e : M + t • E = (M + t' • E) + (t - t') • E := by rw [sub_smul]; abel
    have h := abs_spr_add_sub_le (M + t' • E) ((t - t') • E)
    rw [← e, opE_smul, norm_smul, Real.norm_eq_abs] at h
    show |spr (M + t • E) - spr (M + t' • E)| ≤ 2 * ‖opE E‖ * |t - t'|
    linarith
  -- the two ends
  have hT : 0 ≤ a + b + 2 * d := by linarith
  have hf0 : f 0 ≤ a + b := by
    have h := spr_le_two_mul_norm_sub M 0
    rw [zero_smul, sub_zero, ← hd₀] at h
    rw [hfdef]
    show spr (M + (0 : ℝ) • E) ≤ a + b
    rw [zero_smul, add_zero]
    linarith
  have hfT : a + b ≤ f (a + b + 2 * d) := by
    have := nonempty_sphere hn
    have hM : ∀ p, |M p p| ≤ d := fun p => by
      have h := abs_inner_opE_le M (unitE p) (unitE p)
      rwa [inner_unitE_opE, norm_unitE, mul_one, mul_one, ← hd₀] at h
    have h1 := inner_le_lamMax (M + (a + b + 2 * d) • E) (unitE p₀)
    have h2 := lamMin_le_inner (M + (a + b + 2 * d) • E) (unitE q₀)
    rw [inner_unitE_opE, norm_unitE, one_pow, mul_one, Matrix.add_apply, Matrix.smul_apply,
      hEp, ite_eq_left rfl, smul_eq_mul, mul_one] at h1
    rw [inner_unitE_opE, norm_unitE, one_pow, mul_one, Matrix.add_apply, Matrix.smul_apply,
      hEp, ite_eq_right fun e => hpq e.symm, smul_eq_mul, mul_zero, add_zero] at h2
    have h3 := abs_le.1 (hM p₀)
    have h4 := abs_le.1 (hM q₀)
    rw [hfdef]
    show a + b ≤ lamMax (M + (a + b + 2 * d) • E) - lamMin (M + (a + b + 2 * d) • E)
    linarith [h3.1, h4.2]
  -- the intermediate value
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hT hf.continuousOn ⟨hf0, hfT⟩
  refine ⟨Z₀ + t • E - (lamMax (M + t • E) - a) • 1, (S.reach Θ).sub_mem
    ((S.reach Θ).add_mem hZ₀ ((S.reach Θ).smul_mem t hEr))
    ((S.reach Θ).smul_mem _ (S.one_mem_reach Θ)), ?_⟩
  have e : sym (P + (Z₀ + t • E - (lamMax (M + t • E) - a) • 1)) =
      M + t • E - (lamMax (M + t • E) - a) • 1 := by
    rw [show P + (Z₀ + t • E - (lamMax (M + t • E) - a) • 1) =
      (P + Z₀) + t • E - (lamMax (M + t • E) - a) • 1 by abel, sym_sub, sym_add,
      sym_smul, sym_smul, hEs, sym_of_isSymm isSymm_one, ← hMdef]
  rw [e, lamMax_sub_smul_one hn, lamMin_sub_smul_one hn]
  have ht' : lamMax (M + t • E) - lamMin (M + t • E) = a + b := by rw [← ht, hfdef]; rfl
  constructor <;> linarith

/-- **Every point of the half-plane, the schemes** (the paper, `cor:amount`: "for all `a`, `b` with
`a + b ≥ 2 d_σ` some scheme has `ι = H a + O(H²)` and `μ = H b + O(H²)`"). If two states lie in
different subsystems, `A` has no blocks between subsystems that are not partners and `A_c Θ = 0`,
and `d` is the least value of `‖sym (½ A_ς A + Z)‖` over the reach, then for all `a`, `b` with
`a + b ≥ 2 d` there is `Z` in the reach such that its scheme (`reachScheme`, consistent, its
coefficients acting through the outputs) has, for `0 < H`, `‖A‖ ≤ β`, `‖Z‖ ≤ β²`, `H β ≤ 1/27`,
`σ H β ≤ 1/6`: `|ι - H a| ≤ K' H²` and `|μ - H b| ≤ K' H²` with `ι = -λ_min (Δ_R)`,
`μ = λ_max (Δ_R)`, `K' = diffLeadC (9β) ((6 + 27σ) β²) ‖A‖ + reachK σ β`. -/
theorem least_spread_attained [Fintype κ]
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hAΘ : S.coupling A * Θ = 0) {d : ℝ}
    (hd : IsLeast {r | ∃ Z ∈ S.reach Θ, r = ‖opE (sym (S.halfStepTerm A + Z))‖} d)
    {p₀ q₀ : Fin n} (hpq : S.sub p₀ ≠ S.sub q₀) {a b : ℝ} (hab : 2 * d ≤ a + b) :
    ∃ Z, ∃ hZ : Z ∈ S.reach Θ, ∀ {H β : ℝ}, 0 < H → ‖opE A‖ ≤ β → ‖opE Z‖ ≤ β ^ 2 →
      H * β ≤ 1 / 27 → Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6 →
      ((S.reachScheme A hA Z hZ.1 H).M + (S.reachScheme A hA Z hZ.1 H).N) * Θ = 0 ∧
      |-lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ.1 H).X)) - H * a| ≤
        (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
          reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 ∧
      |lamMax (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ.1 H).X)) - H * b| ≤
        (diffLeadC (9 * β) ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2) ‖opE A‖ +
          reachK (Real.sqrt (Fintype.card κ)) β) * H ^ 2 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) p₀.isLt
  obtain ⟨Z, hZ, ha, hb⟩ := exists_reach_extremes (S.halfStepTerm A) hd hpq hab
  refine ⟨Z, hZ, fun {H β} hH hAβ hZβ hβH hσ => ?_⟩
  obtain ⟨h1, h2⟩ := reachScheme_extremes (hA := hA) (hZ := hZ.1) hn hH hAβ hZβ hβH hσ
  rw [ha] at h2
  rw [hb] at h1
  refine ⟨reachScheme_samples_mul_eq_zero hAΘ hZ.2, ?_, ?_⟩
  · rw [show -lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ.1 H).X)) -
        H * a = -(lamMin (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ.1 H).X)) +
          H * a) by ring, abs_neg]
    exact h2
  · rw [show lamMax (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ.1 H).X)) - H * b =
        lamMax (numDissipation A (modifiedSystem H (S.reachScheme A hA Z hZ.1 H).X)) +
          H * -b by ring]
    exact h1

/-! ### The pair bound -/

/-- Between subsystems `s ≠ t` that are not partners, with skew coupling, the symmetric
combination of the half-step term: `⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫ = ⟪x, A (ς_s + ς_t) A y⟫`. -/
theorem inner_signedCoupling_mul_sym_of_skew
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s t : κ} (hst : s ≠ t)
    (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ + ⟪y, opE (S.signedCoupling A * A) x⟫ =
      ⟪x, opE (A * (S.sgn s + S.sgn t) * A) y⟫ := by
  have e1 : ⟪x, opE (S.signedCoupling A * A) y⟫ = ⟪x, opE (A * S.sgn s * A) y⟫ := by
    refine inner_opE_congr hx hy fun p q hp hq => ?_
    obtain ⟨hne, hnp₁, -⟩ := S.sub_ne_of_eq hst hnp hp hq
    rw [S.signedCoupling_mul_apply_eq_sgn hA hne hnp₁, hp]
  have e2 : ⟪y, opE (S.signedCoupling A * A) x⟫ = ⟪y, opE (A * S.sgn t * A) x⟫ := by
    refine inner_opE_congr hy hx fun p q hp hq => ?_
    obtain ⟨hne, hnp₁, -⟩ := S.sub_ne_of_eq hst.symm hnp' hp hq
    rw [S.signedCoupling_mul_apply_eq_sgn hA hne hnp₁, hp]
  have e3 : ⟪y, opE (A * S.sgn t * A) x⟫ = ⟪x, opE (A * S.sgn t * A) y⟫ := by
    rw [OneStep.inner_opE_transpose]
    refine inner_opE_congr hx hy fun p q hp hq => ?_
    rw [Matrix.transpose_apply]
    exact skew_entry (S := S) hA hskew _ (by rw [hp, hq]; exact hst) (by rw [hp, hq]; exact hnp)
      (by rw [hp, hq]; exact hnp')
  rw [e1, e2, e3, Matrix.mul_add, Matrix.add_mul, inner_opE_add]

/-- **The pair bound** (the paper, eq. `eq:amount`: `2 d_σ ≥ ‖Σ_k τ_k A_ik A_kj‖`). With skew
coupling (`A q p = -A p q` between different subsystems), subsystems `s ≠ t` that are not partners,
`x` supported on `s` and `y` on `t`, and the least value `d` of `‖sym (½ A_ς A + Z)‖` over the
reach: `|⟪x, ½ A (ς_s + ς_t) A y⟫| ≤ 2 d ‖x‖ ‖y‖`; the block of `½ A (ς_s + ς_t) A` between `s` and
`t` is `Σ_k τ_k A_sk A_kt`, `τ_k = ½ (ς_sk + ς_tk)`. -/
theorem abs_inner_pair_le_least
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {Θ : Matrix (Fin n) (Fin n) ℝ} {d : ℝ}
    (hd : IsLeast {r | ∃ Z ∈ S.reach Θ, r = ‖opE (sym (S.halfStepTerm A + Z))‖} d) {s t : κ}
    (hst : s ≠ t) (hnp : ¬ S.partner s t) (hnp' : ¬ S.partner t s)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    |⟪x, opE ((1 / 2 : ℝ) • (A * (S.sgn s + S.sgn t) * A)) y⟫| ≤ 2 * d * (‖x‖ * ‖y‖) := by
  obtain ⟨⟨Z, hZ, rfl⟩, -⟩ := hd
  have hZst : ⟪x, opE Z y⟫ = 0 := inner_opE_eq_zero hx hy fun p q hp hq =>
    hZ.1 p q (by rw [hp, hq]; exact hst) (by rw [hp, hq]; exact hnp)
  have hZts : ⟪y, opE Z x⟫ = 0 := inner_opE_eq_zero hy hx fun p q hp hq =>
    hZ.1 p q (by rw [hp, hq]; exact hst.symm) (by rw [hp, hq]; exact hnp')
  have e : ⟪x, opE ((1 / 2 : ℝ) • (A * (S.sgn s + S.sgn t) * A)) y⟫ =
      2 * ⟪x, opE (sym (S.halfStepTerm A + Z)) y⟫ := by
    rw [inner_sym, inner_opE_add, inner_opE_add, hZst, hZts, halfStepTerm, inner_opE_smul,
      inner_opE_smul, inner_opE_smul, ← S.inner_signedCoupling_mul_sym_of_skew hA hskew hst hnp
        hnp' hx hy]
    ring
  rw [e, abs_mul, abs_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_inner_opE_le _ x y) zero_le_two

end HeldScheme

end CoSimFoundations
