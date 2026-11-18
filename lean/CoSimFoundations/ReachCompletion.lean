/-
The least spread and the least norm of the numerical dissipation over what the coefficients reach
(the paper), general part. Pure linear
algebra on real matrices over `Fin n`; the spectral norm is `‖opE M‖`. The closed forms for the
examples are in `ReachCompletionExamples`.

**Extreme values.** `lamMax M` and `lamMin M` are the supremum and the infimum of `⟪x, M x⟫` over
unit vectors (`λ_max` and `λ_min` of `sym M`; both `0` for `n = 0`), `spr M = lamMax M - lamMin M`.
`lamMax_le_iff`, `le_lamMin_iff`: they are the least upper and the greatest lower bound of the
form, the convention of `SpreadLaw`.

* **Spread and centred norm** (`spr_le_two_mul_norm_sub`, `spr_eq_two_mul_norm_sub_mid`,
  `isLeast_two_mul_norm_sub`): `spr M ≤ 2 ‖M - c 1‖` for every `c`, with equality for symmetric
  `M` and `c = (λ_max + λ_min) / 2`. Over a subspace `𝓡` of symmetric matrices that contains the
  identity (`exists_isLeast_norm_isLeast_spr`): the least norm `d` of `S + R`,
  `R ∈ 𝓡`, is attained (`exists_forall_norm_opE_add_le`, finite dimension) and the least spread
  is `2 d`.
* **Interlacing** (`lamMax_submatrix_le`, `lamMin_le_lamMin_submatrix`, `spr_submatrix_le`): a
  principal compression `M.submatrix e e`, `e` injective, has `λ_max` at most, `λ_min` at least and
  spread at most those of `M`.
* **Orthogonal rows** (`norm_opE_sum_eq_iSup`): if the rows of `N_i` lie in group `i` of
  a partition of the coordinates and `N_i N_jᵀ = 0` for `i ≠ j` (the row spaces are mutually
  orthogonal), then `‖Σ_i N_i‖ = max_i ‖N_i‖`.
* **Components** (`lamMax_eq_iSup_parts`, `lamMin_eq_iInf_parts`): for a matrix that is a
  direct sum of blocks over a partition `σ : (Σ k, Fin (m_k)) ≃ Fin n` of the coordinates (all
  parts nonempty), `λ_max` is the largest `λ_max` of the blocks and `λ_min` the least `λ_min`.
-/
import CoSimFoundations.SpreadLaw
import CoSimFoundations.OwnOutputBlock

open Matrix Metric
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n m : ℕ}

/-! ### The extreme values of the form and the spread -/

section Extremes

/-- `λ_max (M)`: the supremum of the form `⟪x, M x⟫` over unit vectors (`λ_max (sym M)`; `0` for
`n = 0`). -/
noncomputable def lamMax (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ x : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪(x : EuclideanSpace ℝ (Fin n)), opE M x⟫

/-- `λ_min (M)`: the infimum of the form `⟪x, M x⟫` over unit vectors (`λ_min (sym M)`; `0` for
`n = 0`). -/
noncomputable def lamMin (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨅ x : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪(x : EuclideanSpace ℝ (Fin n)), opE M x⟫

/-- The spread `spr (M) = λ_max (M) - λ_min (M)`. -/
noncomputable def spr (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := lamMax M - lamMin M

/-- `|⟪x, M x⟫| ≤ ‖M‖ ‖x‖²`. -/
theorem abs_inner_opE_self_le (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE M x⟫| ≤ ‖opE M‖ * ‖x‖ ^ 2 := by
  rw [sq]
  exact abs_inner_opE_le M x x

/-- The form is bounded above on unit vectors. -/
theorem bddAbove_form (M : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove (Set.range fun x : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ⟪(x : EuclideanSpace ℝ (Fin n)), opE M x⟫) := by
  refine ⟨‖opE M‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := abs_inner_opE_self_le M x
  rw [mem_sphere_zero_iff_norm.1 x.2, one_pow, mul_one] at h
  exact (le_abs_self _).trans h

/-- The form is bounded below on unit vectors. -/
theorem bddBelow_form (M : Matrix (Fin n) (Fin n) ℝ) :
    BddBelow (Set.range fun x : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ⟪(x : EuclideanSpace ℝ (Fin n)), opE M x⟫) := by
  refine ⟨-‖opE M‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := abs_inner_opE_self_le M x
  rw [mem_sphere_zero_iff_norm.1 x.2, one_pow, mul_one] at h
  exact neg_le_of_abs_le h

/-- The form at `x` is `‖x‖²` times the form at the unit vector `x / ‖x‖`. -/
theorem inner_opE_self_eq_smul (M : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) :
    ⟪x, opE M x⟫ = ‖x‖ ^ 2 * ⟪‖x‖⁻¹ • x, opE M (‖x‖⁻¹ • x)⟫ := by
  have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  field_simp

/-- `x / ‖x‖` is a unit vector. -/
theorem mem_sphere_inv_norm_smul {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- `⟪x, M x⟫ ≤ λ_max (M) ‖x‖²` for every `x`. -/
theorem inner_le_lamMax (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE M x⟫ ≤ lamMax M * ‖x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h : _ ≤ lamMax M := le_ciSup (bddAbove_form M) ⟨_, mem_sphere_inv_norm_smul hx⟩
  rw [inner_opE_self_eq_smul M hx, mul_comm (lamMax M)]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- `λ_min (M) ‖x‖² ≤ ⟪x, M x⟫` for every `x`. -/
theorem lamMin_le_inner (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    lamMin M * ‖x‖ ^ 2 ≤ ⟪x, opE M x⟫ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h : lamMin M ≤ _ := ciInf_le (bddBelow_form M) ⟨_, mem_sphere_inv_norm_smul hx⟩
  rw [inner_opE_self_eq_smul M hx, mul_comm (lamMin M)]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- With at least one coordinate there are unit vectors. -/
theorem nonempty_sphere (hn : 0 < n) :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ⟨⟨unitE ⟨0, hn⟩, mem_sphere_zero_iff_norm.2 (norm_unitE _)⟩⟩

/-- Unit vectors exist only with at least one coordinate. -/
theorem pos_of_nonempty_sphere [h : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    0 < n := by
  obtain ⟨x⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (x : EuclideanSpace ℝ (Fin 0)) = 0 := PiLp.ext fun i => i.elim0
    have h1 := mem_sphere_zero_iff_norm.1 x.2
    rw [h0, norm_zero] at h1
    exact absurd h1 zero_ne_one
  · exact hn

/-- Any upper bound of the form is at least `λ_max` (unit vectors exist). -/
theorem lamMax_le_of [Nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    {M : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (h : ∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE M x⟫ ≤ μ * ‖x‖ ^ 2) : lamMax M ≤ μ :=
  ciSup_le fun x => by
    have h1 := h x
    rwa [mem_sphere_zero_iff_norm.1 x.2, one_pow, mul_one] at h1

/-- Any lower bound of the form is at most `λ_min` (unit vectors exist). -/
theorem le_lamMin_of [Nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    {M : Matrix (Fin n) (Fin n) ℝ} {ι : ℝ}
    (h : ∀ x : EuclideanSpace ℝ (Fin n), ι * ‖x‖ ^ 2 ≤ ⟪x, opE M x⟫) : ι ≤ lamMin M :=
  le_ciInf fun x => by
    have h1 := h x
    rwa [mem_sphere_zero_iff_norm.1 x.2, one_pow, mul_one] at h1

/-- **`λ_max` is the least upper bound of the form** (`n ≥ 1`). -/
theorem lamMax_le_iff (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    lamMax M ≤ μ ↔ ∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE M x⟫ ≤ μ * ‖x‖ ^ 2 := by
  have := nonempty_sphere hn
  refine ⟨fun h x => (inner_le_lamMax M x).trans ?_, lamMax_le_of⟩
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- **`λ_min` is the greatest lower bound of the form** (`n ≥ 1`). -/
theorem le_lamMin_iff (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (ι : ℝ) :
    ι ≤ lamMin M ↔ ∀ x : EuclideanSpace ℝ (Fin n), ι * ‖x‖ ^ 2 ≤ ⟪x, opE M x⟫ := by
  have := nonempty_sphere hn
  refine ⟨fun h x => le_trans ?_ (lamMin_le_inner M x), le_lamMin_of⟩
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- Without unit vectors (`n = 0`) both extreme values are `0`. -/
theorem lamMax_lamMin_of_isEmpty [IsEmpty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (M : Matrix (Fin n) (Fin n) ℝ) : lamMax M = 0 ∧ lamMin M = 0 :=
  ⟨Real.iSup_of_isEmpty _, Real.iInf_of_isEmpty _⟩

/-- `λ_min ≤ λ_max`. -/
theorem lamMin_le_lamMax (M : Matrix (Fin n) (Fin n) ℝ) : lamMin M ≤ lamMax M := by
  rcases isEmpty_or_nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with h | h
  · rw [(lamMax_lamMin_of_isEmpty M).1, (lamMax_lamMin_of_isEmpty M).2]
  · obtain ⟨u⟩ := h
    exact (ciInf_le (bddBelow_form M) u).trans (le_ciSup (bddAbove_form M) u)

/-- The spread is not negative. -/
theorem spr_nonneg (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ spr M :=
  sub_nonneg.2 (lamMin_le_lamMax M)

/-- `x ⬝ᵥ M x ≤ λ_max (M) (x ⬝ᵥ x)` for vectors of `Fin n → ℝ`. -/
theorem dotProduct_le_lamMax (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ lamMax M * (x ⬝ᵥ x) := by
  have h := inner_le_lamMax M (WithLp.toLp 2 x)
  rwa [inner_opE_eq_dotProduct, ← real_inner_self_eq_norm_sq, inner_eq_dotProduct] at h

/-- `λ_min (M) (x ⬝ᵥ x) ≤ x ⬝ᵥ M x` for vectors of `Fin n → ℝ`. -/
theorem lamMin_mul_le_dotProduct (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    lamMin M * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  have h := lamMin_le_inner M (WithLp.toLp 2 x)
  rwa [inner_opE_eq_dotProduct, ← real_inner_self_eq_norm_sq, inner_eq_dotProduct] at h

end Extremes

/-! ### The spread and the centred norm -/

section Centred

/-- **The norm of a symmetric matrix from its form.** If `T` is symmetric and
`|⟪x, T x⟫| ≤ r ‖x‖²` for all `x`, then `‖T‖ ≤ r`. -/
theorem norm_opE_le_of_abs_inner_self_le {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm)
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ x : EuclideanSpace ℝ (Fin n), |⟪x, opE T x⟫| ≤ r * ‖x‖ ^ 2) :
    ‖opE T‖ ≤ r := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ (isSymmetric_opE hT)]
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hr]
  · have hpos : 0 < ‖x‖ ^ 2 := by positivity
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real, real_inner_comm, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h x

/-- The form of `M - c • 1`: `⟪x, (M - c) x⟫ = ⟪x, M x⟫ - c ‖x‖²`. -/
theorem inner_opE_sub_smul_one (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (M - c • 1) x⟫ = ⟪x, opE M x⟫ - c * ‖x‖ ^ 2 := by
  rw [inner_opE_sub, inner_opE_smul, opE_one, one_apply_eq_self, real_inner_self_eq_norm_sq]

/-- **The spread is at most twice the norm of any shift:** `spr (M) ≤ 2 ‖M - c 1‖` for every
real `c` (any square matrix). -/
theorem spr_le_two_mul_norm_sub (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    spr M ≤ 2 * ‖opE (M - c • 1)‖ := by
  rcases isEmpty_or_nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with h | h
  · rw [spr, (lamMax_lamMin_of_isEmpty M).1, (lamMax_lamMin_of_isEmpty M).2, sub_zero]
    positivity
  · have h1 : lamMax M ≤ c + ‖opE (M - c • 1)‖ := lamMax_le_of fun x => by
      have h2 := (le_abs_self _).trans (abs_inner_opE_self_le (M - c • 1) x)
      rw [inner_opE_sub_smul_one] at h2
      linarith
    have h3 : c - ‖opE (M - c • 1)‖ ≤ lamMin M := le_lamMin_of fun x => by
      have h2 := neg_le_of_abs_le (abs_inner_opE_self_le (M - c • 1) x)
      rw [inner_opE_sub_smul_one] at h2
      linarith
    rw [spr]
    linarith

/-- **The spread and the centred norm.** For a symmetric matrix `M` and
`c = (λ_max + λ_min) / 2`: `spr (M) = 2 ‖M - c 1‖`. -/
theorem spr_eq_two_mul_norm_sub_mid {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) :
    spr M = 2 * ‖opE (M - ((lamMax M + lamMin M) / 2) • 1)‖ := by
  refine le_antisymm (spr_le_two_mul_norm_sub M _) ?_
  have hsym : (M - ((lamMax M + lamMin M) / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)).IsSymm :=
    hM.sub (isSymm_one.smul _)
  have h := norm_opE_le_of_abs_inner_self_le hsym (r := spr M / 2)
    (div_nonneg (spr_nonneg M) zero_le_two) fun x => by
      rw [inner_opE_sub_smul_one, abs_le, spr]
      have h1 := inner_le_lamMax M x
      have h2 := lamMin_le_inner M x
      constructor <;> nlinarith
  linarith

/-- **The spread is twice the least norm of a shift.** For a symmetric matrix:
`spr (M) = 2 min_c ‖M - c 1‖`, the minimum attained at `c = (λ_max + λ_min) / 2`. -/
theorem isLeast_two_mul_norm_sub {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) :
    IsLeast {r | ∃ c : ℝ, r = 2 * ‖opE (M - c • 1)‖} (spr M) :=
  ⟨⟨_, spr_eq_two_mul_norm_sub_mid hM⟩, by
    rintro _ ⟨c, rfl⟩
    exact spr_le_two_mul_norm_sub M c⟩

/-- If `λ_max + λ_min = 0`, the spread of a symmetric matrix is twice its norm. -/
theorem spr_eq_two_mul_norm_of_add_eq_zero {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    (h : lamMax M + lamMin M = 0) : spr M = 2 * ‖opE M‖ := by
  rw [spr_eq_two_mul_norm_sub_mid hM, h, zero_div, zero_smul, sub_zero]

/-- **The least norm on a coset of a subspace is attained** (finite dimension): for every matrix
`S` and subspace `𝓡` there is `R₀ ∈ 𝓡` with `‖S + R₀‖ ≤ ‖S + R‖` for all `R ∈ 𝓡`. -/
theorem exists_forall_norm_opE_add_le (S : Matrix (Fin n) (Fin n) ℝ)
    (𝓡 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    ∃ R₀ ∈ 𝓡, ∀ R ∈ 𝓡, ‖opE (S + R₀)‖ ≤ ‖opE (S + R)‖ := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    { toFun := opE
      map_add' := opE_add
      map_smul' := fun c A => opE_smul c A }
  let V := 𝓡.map L
  have hV : IsClosed (V : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
    V.closed_of_finiteDimensional
  obtain ⟨T, hT, hTd⟩ := hV.exists_infDist_eq_dist ⟨0, V.zero_mem⟩ (-opE S)
  obtain ⟨R₀, hR₀, rfl⟩ := Submodule.mem_map.1 hT
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  have h := Metric.infDist_le_dist_of_mem (x := -opE S) (Submodule.mem_map_of_mem (f := L) hR)
  rw [hTd, dist_eq_norm, dist_eq_norm] at h
  have e : ∀ R' : Matrix (Fin n) (Fin n) ℝ, -opE S - L R' = -opE (S + R') := fun R' => by
    show -opE S - opE R' = -opE (S + R')
    rw [opE_add]
    abel
  rwa [e, e, norm_neg, norm_neg] at h

/-- **Least spread and least norm over a subspace that contains the identity**
(`spr (M) = 2 min_c ‖M - c 1‖` and `c 1 ∈ 𝓡`). For a symmetric `S` and a subspace `𝓡` of symmetric
matrices with `1 ∈ 𝓡`: the least norm `d = min_{R ∈ 𝓡} ‖S + R‖` is attained and the least spread
`min_{R ∈ 𝓡} spr (S + R)` is attained and equals `2 d`. -/
theorem exists_isLeast_norm_isLeast_spr {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsSymm)
    {𝓡 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} (h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ 𝓡)
    (hsym : ∀ R ∈ 𝓡, R.IsSymm) :
    ∃ d : ℝ, IsLeast {r | ∃ R ∈ 𝓡, r = ‖opE (S + R)‖} d ∧
      IsLeast {r | ∃ R ∈ 𝓡, r = spr (S + R)} (2 * d) := by
  obtain ⟨R₀, hR₀, hmin⟩ := exists_forall_norm_opE_add_le S 𝓡
  have hlow : ∀ R ∈ 𝓡, 2 * ‖opE (S + R₀)‖ ≤ spr (S + R) := fun R hR => by
    rw [spr_eq_two_mul_norm_sub_mid (hS.add (hsym R hR))]
    have e : S + R - ((lamMax (S + R) + lamMin (S + R)) / 2) • 1 =
        S + (R - ((lamMax (S + R) + lamMin (S + R)) / 2) • 1) := by abel
    rw [e]
    have := hmin (R - ((lamMax (S + R) + lamMin (S + R)) / 2) • 1)
      (𝓡.sub_mem hR (𝓡.smul_mem _ h1))
    linarith
  refine ⟨_, ⟨⟨R₀, hR₀, rfl⟩, ?_⟩, ⟨⟨R₀, hR₀, ?_⟩, ?_⟩⟩
  · rintro _ ⟨R, hR, rfl⟩
    exact hmin R hR
  · refine le_antisymm (hlow R₀ hR₀) ?_
    have h := spr_le_two_mul_norm_sub (S + R₀) 0
    rwa [zero_smul, sub_zero] at h
  · rintro _ ⟨R, hR, rfl⟩
    exact hlow R hR

end Centred

/-! ### Interlacing for a principal compression -/

section Compression

variable {e : Fin m → Fin n}

/-- The vector of `Fin n` that is `y` on the range of `e` and zero elsewhere. -/
noncomputable def extendE (e : Fin m → Fin n) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Function.extend e (WithLp.ofLp y) 0)

/-- The form of a principal compression is the form of the matrix on the extended vector. -/
theorem inner_opE_extendE (M : Matrix (Fin n) (Fin n) ℝ) (he : Function.Injective e)
    (y : EuclideanSpace ℝ (Fin m)) :
    ⟪extendE e y, opE M (extendE e y)⟫ = ⟪y, opE (M.submatrix e e) y⟫ := by
  have hx : ∀ i, (extendE e y) (e i) = y i := fun i => he.extend_apply _ _ i
  have hz : ∀ p ∉ Set.range e, (extendE e y) p = 0 := fun p hp =>
    Function.extend_apply' _ _ _ hp
  rw [inner_opE_eq_sum, inner_opE_eq_sum]
  symm
  refine Fintype.sum_of_injective e he _ _ (fun p hp => ?_) (fun i => ?_)
  · simp only [hz p hp, zero_mul, Finset.sum_const_zero]
  · simp only [hx]
    refine Fintype.sum_of_injective e he _ _ (fun q hq => ?_) (fun k => ?_)
    · simp only [hz q hq, mul_zero]
    · simp only [hx, Matrix.submatrix_apply]

/-- The extended vector has the same norm. -/
theorem norm_extendE (he : Function.Injective e) (y : EuclideanSpace ℝ (Fin m)) :
    ‖extendE e y‖ = ‖y‖ := by
  have h := inner_opE_extendE (1 : Matrix (Fin n) (Fin n) ℝ) he y
  rw [submatrix_one e he, opE_one, opE_one, one_apply_eq_self, one_apply_eq_self,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **Interlacing, `λ_max`.** The largest value of a principal compression is at most that of the
matrix: `λ_max (M_{e e}) ≤ λ_max (M)` for injective `e` (`m ≥ 1`). -/
theorem lamMax_submatrix_le (hm : 0 < m) (M : Matrix (Fin n) (Fin n) ℝ)
    (he : Function.Injective e) : lamMax (M.submatrix e e) ≤ lamMax M := by
  have := nonempty_sphere hm
  refine lamMax_le_of fun y => ?_
  rw [← inner_opE_extendE M he, ← norm_extendE he y]
  exact inner_le_lamMax M _

/-- **Interlacing, `λ_min`.** `λ_min (M) ≤ λ_min (M_{e e})` for injective `e` (`m ≥ 1`). -/
theorem lamMin_le_lamMin_submatrix (hm : 0 < m) (M : Matrix (Fin n) (Fin n) ℝ)
    (he : Function.Injective e) : lamMin M ≤ lamMin (M.submatrix e e) := by
  have := nonempty_sphere hm
  refine le_lamMin_of fun y => ?_
  rw [← inner_opE_extendE M he, ← norm_extendE he y]
  exact lamMin_le_inner M _

/-- **Interlacing for the spread.** The spread of a principal compression is at most the spread
of the matrix: `spr (M_{e e}) ≤ spr (M)` for injective `e`. -/
theorem spr_submatrix_le (M : Matrix (Fin n) (Fin n) ℝ) (he : Function.Injective e) :
    spr (M.submatrix e e) ≤ spr M := by
  rcases isEmpty_or_nonempty (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) with h | h
  · rw [spr, (lamMax_lamMin_of_isEmpty (M.submatrix e e)).1,
      (lamMax_lamMin_of_isEmpty (M.submatrix e e)).2, sub_zero]
    exact spr_nonneg M
  · have hm := pos_of_nonempty_sphere (n := m)
    have h1 := lamMax_submatrix_le hm M he
    have h2 := lamMin_le_lamMin_submatrix hm M he
    rw [spr, spr]
    linarith

end Compression

/-! ### Orthogonal rows -/

section Rows

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal `0/1` matrix of the coordinates of group `i`. -/
noncomputable def gmask (grp : Fin n → ι) (i : ι) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun p => if grp p = i then 1 else 0

theorem norm_opE_gmask_le (grp : Fin n → ι) (i : ι) : ‖opE (gmask grp i)‖ ≤ 1 :=
  norm_opE_diagonal_le _ zero_le_one fun p => by by_cases h : grp p = i <;> simp [h]

/-- The parts of a vector on the groups: `Σ_i ‖x_i‖² = ‖x‖²`. -/
theorem sum_norm_sq_gmask (grp : Fin n → ι) (y : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ‖opE (gmask grp i) y‖ ^ 2 = ‖y‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, gmask, opE_diagonal_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (grp p)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The transpose has the same spectral norm. -/
theorem norm_opE_transpose (T : Matrix (Fin n) (Fin n) ℝ) : ‖opE Tᵀ‖ = ‖opE T‖ := by
  refine le_antisymm (norm_opE_transpose_le T) ?_
  have h := norm_opE_transpose_le Tᵀ
  rwa [transpose_transpose] at h

/-- Pythagoras for pairwise orthogonal vectors. -/
theorem norm_sum_sq_of_pairwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (h : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) : ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i (fun j _ hj => h i j (Ne.symm hj))
    (fun hi => absurd (Finset.mem_univ i) hi), real_inner_self_eq_norm_sq]

/-- **Orthogonal rows**. If the rows of `N_i` lie in group `i` of a partition `grp` of
the coordinates and `N_i N_jᵀ = 0` for `i ≠ j` (the row spaces are mutually orthogonal), then
`‖Σ_i N_i‖ = max_i ‖N_i‖`. -/
theorem norm_opE_sum_eq_iSup (grp : Fin n → ι) (N : ι → Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i p q, grp p ≠ i → N i p q = 0) (horth : ∀ i j, i ≠ j → N i * (N j)ᵀ = 0) :
    ‖opE (∑ i, N i)‖ = ⨆ i, ‖opE (N i)‖ := by
  have hK0 : 0 ≤ ⨆ i, ‖opE (N i)‖ := Real.iSup_nonneg fun i => norm_nonneg _
  have hNK : ∀ i, ‖opE (N i)‖ ≤ ⨆ i, ‖opE (N i)‖ := fun i =>
    le_ciSup (f := fun i => ‖opE (N i)‖) (Finite.bddAbove_range _) i
  refine le_antisymm ?_ (Real.iSup_le (fun i => ?_) (norm_nonneg _))
  · rw [← norm_opE_transpose]
    refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun y => ?_
    have hcol : ∀ i, (N i)ᵀ = (N i)ᵀ * gmask grp i := by
      intro i
      ext p q
      by_cases hq : grp q = i
      · simp [gmask, hq]
      · simp [gmask, hq, hrow i q p hq]
    have happ : opE (∑ i, N i)ᵀ y = ∑ i, opE (N i)ᵀ (opE (gmask grp i) y) := by
      rw [transpose_sum, show opE (∑ i, (N i)ᵀ) = ∑ i, opE (N i)ᵀ from map_sum _ _ _,
        _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_lhs => rw [hcol i]
      rw [opE_mul_apply]
    have horth' : ∀ i j, i ≠ j →
        ⟪opE (N i)ᵀ (opE (gmask grp i) y), opE (N j)ᵀ (opE (gmask grp j) y)⟫ = 0 := by
      intro i j hij
      rw [inner_opE_transpose, transpose_transpose, ← opE_mul_apply, horth j i (Ne.symm hij)]
      simp
    have hsq : ‖opE (∑ i, N i)ᵀ y‖ ^ 2 ≤ ((⨆ i, ‖opE (N i)‖) * ‖y‖) ^ 2 := by
      rw [happ, norm_sum_sq_of_pairwise _ horth', mul_pow, ← sum_norm_sq_gmask grp y,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 := (opE (N i)ᵀ).le_opNorm (opE (gmask grp i) y)
      rw [norm_opE_transpose] at h1
      have h2 : ‖opE (N i)‖ * ‖opE (gmask grp i) y‖ ≤
          (⨆ i, ‖opE (N i)‖) * ‖opE (gmask grp i) y‖ :=
        mul_le_mul_of_nonneg_right (hNK i) (norm_nonneg _)
      calc ‖opE (N i)ᵀ (opE (gmask grp i) y)‖ ^ 2
          ≤ ((⨆ i, ‖opE (N i)‖) * ‖opE (gmask grp i) y‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
        _ = (⨆ i, ‖opE (N i)‖) ^ 2 * ‖opE (gmask grp i) y‖ ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))).1 hsq
  · have hmask : gmask grp i * ∑ j, N j = N i := by
      ext p q
      simp only [gmask, Matrix.diagonal_mul, Matrix.sum_apply]
      by_cases hp : grp p = i
      · rw [ite_eq_left hp, one_mul, Finset.sum_eq_single i]
        · intro j _ hj
          exact hrow j p q fun h => hj (h.symm.trans hp)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [ite_eq_right hp, zero_mul, hrow i p q hp]
    rw [← hmask, opE_mul]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_opE_gmask_le grp i))

end Rows

/-! ### Components -/

section Components

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {mk : κ → ℕ}

/-- The block of `M` on the part `k` of a partition `σ` of the coordinates. -/
def partBlock (σ : (Σ k, Fin (mk k)) ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℝ) (k : κ) :
    Matrix (Fin (mk k)) (Fin (mk k)) ℝ :=
  M.submatrix (fun i => σ ⟨k, i⟩) (fun i => σ ⟨k, i⟩)

/-- The part of a vector on the part `k` of a partition `σ` of the coordinates. -/
noncomputable def partVec (σ : (Σ k, Fin (mk k)) ≃ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (k : κ) : EuclideanSpace ℝ (Fin (mk k)) :=
  WithLp.toLp 2 fun i => x (σ ⟨k, i⟩)

/-- The form of a direct sum is the sum of the forms of the blocks. -/
theorem inner_opE_eq_sum_partBlock (σ : (Σ k, Fin (mk k)) ≃ Fin n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ a b : Σ k, Fin (mk k), a.1 ≠ b.1 → M (σ a) (σ b) = 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE M x⟫ = ∑ k, ⟪partVec σ x k, opE (partBlock σ M k) (partVec σ x k)⟫ := by
  simp only [inner_opE_eq_sum, partVec, partBlock, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp σ, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp σ, Fintype.sum_sigma, Finset.sum_eq_single k]
  · intro k' _ hk'
    exact Finset.sum_eq_zero fun j _ => by
      rw [hM ⟨k, i⟩ ⟨k', j⟩ (Ne.symm hk'), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The norm squared is the sum over the parts. -/
theorem norm_sq_eq_sum_partVec (σ : (Σ k, Fin (mk k)) ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ k, ‖partVec σ x k‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, partVec]
  rw [← Equiv.sum_comp σ, Fintype.sum_sigma]

/-- Without parts there are no unit vectors. -/
theorem isEmpty_sphere_of_isEmpty [IsEmpty κ] (σ : (Σ k, Fin (mk k)) ≃ Fin n) :
    IsEmpty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ⟨fun x => by
    have h0 : (x : EuclideanSpace ℝ (Fin n)) = 0 := PiLp.ext fun p => isEmptyElim (σ.symm p).1
    have h1 := mem_sphere_zero_iff_norm.1 x.2
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1⟩

/-- **Components, `λ_max`**. If `M` is a direct sum of blocks over a partition
`σ : (Σ k, Fin (m_k)) ≃ Fin n` of the coordinates (`M (σ a) (σ b) = 0` for `a`, `b` in different
parts) and every part is nonempty, then `λ_max (M) = max_k λ_max (M_k)`. -/
theorem lamMax_eq_iSup_parts (σ : (Σ k, Fin (mk k)) ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ a b : Σ k, Fin (mk k), a.1 ≠ b.1 → M (σ a) (σ b) = 0) (hmk : ∀ k, 0 < mk k) :
    lamMax M = ⨆ k, lamMax (partBlock σ M k) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have := isEmpty_sphere_of_isEmpty σ
    rw [(lamMax_lamMin_of_isEmpty M).1, Real.iSup_of_isEmpty]
  · obtain ⟨k₀⟩ := id hκ
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (σ ⟨k₀, ⟨0, hmk k₀⟩⟩).isLt
    have := nonempty_sphere hn
    have hemb : ∀ k, Function.Injective (fun i : Fin (mk k) => σ ⟨k, i⟩) := fun k =>
      σ.injective.comp sigma_mk_injective
    refine le_antisymm (lamMax_le_of fun x => ?_)
      (ciSup_le fun k => lamMax_submatrix_le (hmk k) M (hemb k))
    rw [inner_opE_eq_sum_partBlock σ M hM, norm_sq_eq_sum_partVec σ x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => (inner_le_lamMax _ _).trans ?_
    exact mul_le_mul_of_nonneg_right
      (le_ciSup (f := fun k => lamMax (partBlock σ M k)) (Finite.bddAbove_range _) k)
      (sq_nonneg _)

/-- **Components, `λ_min`**. Under the hypotheses of `lamMax_eq_iSup_parts`,
`λ_min (M) = min_k λ_min (M_k)`. -/
theorem lamMin_eq_iInf_parts (σ : (Σ k, Fin (mk k)) ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ a b : Σ k, Fin (mk k), a.1 ≠ b.1 → M (σ a) (σ b) = 0) (hmk : ∀ k, 0 < mk k) :
    lamMin M = ⨅ k, lamMin (partBlock σ M k) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have := isEmpty_sphere_of_isEmpty σ
    rw [(lamMax_lamMin_of_isEmpty M).2, Real.iInf_of_isEmpty]
  · obtain ⟨k₀⟩ := id hκ
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (σ ⟨k₀, ⟨0, hmk k₀⟩⟩).isLt
    have := nonempty_sphere hn
    have hemb : ∀ k, Function.Injective (fun i : Fin (mk k) => σ ⟨k, i⟩) := fun k =>
      σ.injective.comp sigma_mk_injective
    refine le_antisymm (le_ciInf fun k => lamMin_le_lamMin_submatrix (hmk k) M (hemb k))
      (le_lamMin_of fun x => ?_)
    rw [inner_opE_eq_sum_partBlock σ M hM, norm_sq_eq_sum_partVec σ x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => le_trans ?_ (lamMin_le_inner _ _)
    exact mul_le_mul_of_nonneg_right
      (ciInf_le (f := fun k => lamMin (partBlock σ M k)) (Finite.bddBelow_range _) k)
      (sq_nonneg _)

end Components

end CoSimFoundations
