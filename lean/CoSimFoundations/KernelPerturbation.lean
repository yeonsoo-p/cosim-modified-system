/-
The kernel of a surjective map under a perturbation (the paper, Theorem `thm:memory` (i),
proof: "the orthogonal projection onto the kernel of independent maps depends continuously on
them").

**Setting.** `E`, `Y`, `Z` real normed spaces, `Y` complete. `N₀ N : E → Y` bounded, `N₀` with a
bounded right inverse `R` (`N₀ ∘ R = id`; in finite dimension every surjective map has one,
`exists_rightInverse_of_surjective`), and `‖N - N₀‖ ≤ ε`.

**Statements.**
* `exists_ker_near`: every `v ∈ ker N` has a `v₀ ∈ ker N₀` with `‖v - v₀‖ ≤ ‖R‖ ε ‖v‖`
  (`v₀ = v - R N₀ v`, and `N₀ v = (N₀ - N) v`). No smallness of `ε` is needed, and a generalised
  inverse, `N₀ R N₀ = N₀`, suffices (`exists_ker_near_of_generalized`; every map between
  finite-dimensional spaces has one, `exists_generalizedInverse`). Hence the upper bound
  `restrNorm_ker_le_of_generalized` below holds without surjectivity of `N₀`.
* `exists_rightInverse_near`: if `ε ‖R‖ < 1`, then `N` has the right inverse
  `R' = R (N R)⁻¹` with `‖R'‖ ≤ ‖R‖ / (1 - ε ‖R‖)`: `N R = 1 - (N₀ - N) R` is invertible by
  the Neumann series. In particular `N` is surjective.
* `exists_ker_near'`: hence every `v₀ ∈ ker N₀` has a `v ∈ ker N` with
  `‖v - v₀‖ ≤ ‖R‖ / (1 - ε ‖R‖) · ε ‖v₀‖`.
* The norm of a map `D : E → Z` restricted to a subspace `V` is `restrNorm D V`, the operator
  norm of `D` composed with the inclusion of `V` (as `visBound` and `unseenRate` are defined).
  `restrNorm_ker_le`: `‖D|ker N‖ ≤ ‖D|ker N₀‖ + 2 ‖R‖ ε ‖D‖`, and
  `abs_restrNorm_ker_sub_le`: for `ε ‖R‖ < 1`,

    `| ‖D|ker N‖ - ‖D|ker N₀‖ | ≤ 2 ‖R‖ ε ‖D‖ / (1 - ε ‖R‖)`.

  Proof of the first: for `v ∈ ker N` and its `v₀`, `‖D v‖ ≤ ‖D v₀‖ + ‖D‖ ‖v - v₀‖`,
  `‖v₀‖ ≤ (1 + ‖R‖ ε) ‖v‖` and `‖D|ker N₀‖ ≤ ‖D‖`. The second is the first for both orders
  of the two maps.

No inner product is used: the statement about the orthogonal projections of the paper is
replaced by the two statements about nearby vectors, which are what the restricted norms need.
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace CoSimFoundations

section RestrictedNorm

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The norm of a bounded map restricted to a subspace: the operator norm of `D` composed with
the inclusion of `V`, that is, the least `c` with `‖D v‖ ≤ c ‖v‖` for `v ∈ V`. -/
noncomputable def restrNorm (D : E →L[ℝ] Z) (V : Submodule ℝ E) : ℝ :=
  ‖D ∘L V.subtypeL‖

/-- The restricted norm is not negative. -/
theorem restrNorm_nonneg (D : E →L[ℝ] Z) (V : Submodule ℝ E) : 0 ≤ restrNorm D V :=
  norm_nonneg (D ∘L V.subtypeL)

/-- On the subspace the map is bounded by its restricted norm. -/
theorem norm_apply_le_restrNorm (D : E →L[ℝ] Z) {V : Submodule ℝ E} {v : E} (hv : v ∈ V) :
    ‖D v‖ ≤ restrNorm D V * ‖v‖ :=
  (D ∘L V.subtypeL).le_opNorm ⟨v, hv⟩

/-- The restricted norm is the least bound on the subspace. -/
theorem restrNorm_le_of_forall (D : E →L[ℝ] Z) (V : Submodule ℝ E) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v ∈ V, ‖D v‖ ≤ c * ‖v‖) : restrNorm D V ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc fun v => h v v.2

/-- The restricted norm is at most the norm. -/
theorem restrNorm_le_norm (D : E →L[ℝ] Z) (V : Submodule ℝ E) : restrNorm D V ≤ ‖D‖ :=
  restrNorm_le_of_forall D V (norm_nonneg D) fun v _ => D.le_opNorm v

/-- Two maps that differ by at most `c ‖v‖` on a subspace have restricted norms that differ by
at most `c`. -/
theorem abs_restrNorm_sub_le (D D' : E →L[ℝ] Z) (V : Submodule ℝ E) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v ∈ V, ‖D v - D' v‖ ≤ c * ‖v‖) : |restrNorm D V - restrNorm D' V| ≤ c := by
  have key : ∀ T T' : E →L[ℝ] Z, (∀ v ∈ V, ‖T v - T' v‖ ≤ c * ‖v‖) →
      restrNorm T V ≤ restrNorm T' V + c := by
    intro T T' hT
    refine restrNorm_le_of_forall T V (add_nonneg (restrNorm_nonneg T' V) hc) fun v hv => ?_
    have h1 : ‖T v‖ ≤ ‖T' v‖ + ‖T v - T' v‖ := by
      have h2 := norm_add_le (T' v) (T v - T' v)
      rwa [add_sub_cancel] at h2
    have h3 := norm_apply_le_restrNorm T' hv
    have h4 := hT v hv
    linarith
  have h1 := key D D' h
  have h2 := key D' D fun v hv => by rw [norm_sub_rev]; exact h v hv
  rw [abs_le]
  constructor <;> linarith

/-- Two maps that agree on a subspace have the same restricted norm. -/
theorem restrNorm_congr (D D' : E →L[ℝ] Z) (V : Submodule ℝ E) (h : ∀ v ∈ V, D v = D' v) :
    restrNorm D V = restrNorm D' V := by
  have h1 := abs_restrNorm_sub_le D D' V le_rfl fun v hv => by
    rw [h v hv, sub_self, norm_zero, zero_mul]
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h1)

/-- The restricted norm of a multiple: `‖(c D)|V‖ = |c| ‖D|V‖`. -/
theorem restrNorm_smul_abs (D : E →L[ℝ] Z) (V : Submodule ℝ E) (c : ℝ) :
    restrNorm (c • D) V = |c| * restrNorm D V := by
  have hc : 0 ≤ |c| := abs_nonneg c
  have hval : ∀ v : E, ‖(c • D) v‖ = |c| * ‖D v‖ := fun v => by
    rw [_root_.smul_apply, norm_smul, Real.norm_eq_abs]
  refine le_antisymm ?_ ?_
  · refine restrNorm_le_of_forall _ V (mul_nonneg hc (restrNorm_nonneg D V)) fun v hv => ?_
    rw [hval, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_apply_le_restrNorm D hv) hc
  · rcases hc.eq_or_lt with h0 | hc'
    · rw [← h0, zero_mul]
      exact restrNorm_nonneg _ V
    · rw [← le_div_iff₀' hc']
      refine restrNorm_le_of_forall D V (div_nonneg (restrNorm_nonneg _ V) hc) fun v hv => ?_
      have h1 := norm_apply_le_restrNorm (c • D) hv
      rw [hval] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀' hc']
      exact h1

/-- The restricted norm of a multiple: `‖(c D)|V‖ = c ‖D|V‖` for `c ≥ 0`. -/
theorem restrNorm_smul (D : E →L[ℝ] Z) (V : Submodule ℝ E) {c : ℝ} (hc : 0 ≤ c) :
    restrNorm (c • D) V = c * restrNorm D V := by
  rw [restrNorm_smul_abs, abs_of_nonneg hc]

end RestrictedNorm

section Kernel

variable {E Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **A vector of the kernel of the perturbed map is near the kernel of the map, for a
generalised inverse.** If `N₀ R N₀ = N₀` and `‖N - N₀‖ ≤ ε`, every `v` with `N v = 0` has a `v₀`
with `N₀ v₀ = 0` and `‖v - v₀‖ ≤ ‖R‖ ε ‖v‖`. (`N₀` need not be surjective.) -/
theorem exists_ker_near_of_generalized {N₀ N : E →L[ℝ] Y} {R : Y →L[ℝ] E} {ε : ℝ}
    (hR : ∀ v, N₀ (R (N₀ v)) = N₀ v) (hN : ‖N - N₀‖ ≤ ε) {v : E} (hv : N v = 0) :
    ∃ v₀ : E, N₀ v₀ = 0 ∧ ‖v - v₀‖ ≤ ‖R‖ * ε * ‖v‖ := by
  refine ⟨v - R (N₀ v), ?_, ?_⟩
  · rw [map_sub, hR, sub_self]
  · have h1 : N₀ v = -((N - N₀) v) := by
      rw [_root_.sub_apply, hv, zero_sub, neg_neg]
    have h2 : ‖N₀ v‖ ≤ ε * ‖v‖ := by
      rw [h1, norm_neg]
      exact ((N - N₀).le_opNorm v).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg v))
    rw [sub_sub_cancel]
    calc ‖R (N₀ v)‖ ≤ ‖R‖ * ‖N₀ v‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (ε * ‖v‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg R)
      _ = ‖R‖ * ε * ‖v‖ := by ring

/-- A right inverse is a generalised inverse. -/
theorem generalized_of_rightInverse {N₀ : E →L[ℝ] Y} {R : Y →L[ℝ] E}
    (hR : N₀ ∘L R = ContinuousLinearMap.id ℝ Y) (v : E) : N₀ (R (N₀ v)) = N₀ v := by
  have h := congrArg (fun T : Y →L[ℝ] Y => T (N₀ v)) hR
  simpa using h

/-- **A vector of the kernel of the perturbed map is near the kernel of the map.** If
`N₀ ∘ R = id` and `‖N - N₀‖ ≤ ε`, every `v` with `N v = 0` has a `v₀` with `N₀ v₀ = 0` and
`‖v - v₀‖ ≤ ‖R‖ ε ‖v‖`. -/
theorem exists_ker_near {N₀ N : E →L[ℝ] Y} {R : Y →L[ℝ] E} {ε : ℝ}
    (hR : N₀ ∘L R = ContinuousLinearMap.id ℝ Y) (hN : ‖N - N₀‖ ≤ ε) {v : E} (hv : N v = 0) :
    ∃ v₀ : E, N₀ v₀ = 0 ∧ ‖v - v₀‖ ≤ ‖R‖ * ε * ‖v‖ :=
  exists_ker_near_of_generalized (generalized_of_rightInverse hR) hN hv

/-- **A map near a map with a right inverse has a right inverse.** If `N₀ ∘ R = id`,
`‖N - N₀‖ ≤ ε` and `ε ‖R‖ < 1`, then `N ∘ R' = id` for some `R'` with
`‖R'‖ ≤ ‖R‖ / (1 - ε ‖R‖)` (`R' = R (N R)⁻¹`, Neumann series). -/
theorem exists_rightInverse_near [CompleteSpace Y] {N₀ N : E →L[ℝ] Y} {R : Y →L[ℝ] E} {ε : ℝ}
    (hR : N₀ ∘L R = ContinuousLinearMap.id ℝ Y) (hN : ‖N - N₀‖ ≤ ε) (hε : ε * ‖R‖ < 1) :
    ∃ R' : Y →L[ℝ] E, N ∘L R' = ContinuousLinearMap.id ℝ Y ∧ ‖R'‖ ≤ ‖R‖ / (1 - ε * ‖R‖) := by
  set t : Y →L[ℝ] Y := (N₀ - N) ∘L R with ht
  have ht1 : ‖t‖ ≤ ε * ‖R‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hN (norm_nonneg R)
  have ht2 : ‖t‖ < 1 := lt_of_le_of_lt ht1 hε
  have hNR : N ∘L R = 1 - t := by
    rw [ht, ContinuousLinearMap.sub_comp, hR, ContinuousLinearMap.one_def]
    abel
  set S : Y →L[ℝ] Y := ∑' n : ℕ, t ^ n with hS
  have hmul : (1 - t) * S = 1 := mul_neg_geom_series t ht2
  have hS1 : ‖S‖ ≤ (1 - ε * ‖R‖)⁻¹ := by
    have h1 := tsum_geometric_le_of_norm_lt_one t ht2
    have h2 : ‖(1 : Y →L[ℝ] Y)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h3 : (1 - ‖t‖)⁻¹ ≤ (1 - ε * ‖R‖)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    linarith
  refine ⟨R ∘L S, ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_assoc, hNR]
    exact hmul
  · calc ‖R ∘L S‖ ≤ ‖R‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖R‖ * (1 - ε * ‖R‖)⁻¹ := mul_le_mul_of_nonneg_left hS1 (norm_nonneg R)
      _ = ‖R‖ / (1 - ε * ‖R‖) := (div_eq_mul_inv _ _).symm

/-- **A vector of the kernel of the map is near the kernel of the perturbed map.** If
`N₀ ∘ R = id`, `‖N - N₀‖ ≤ ε` and `ε ‖R‖ < 1`, every `v₀` with `N₀ v₀ = 0` has a `v` with
`N v = 0` and `‖v - v₀‖ ≤ ‖R‖ / (1 - ε ‖R‖) · ε ‖v₀‖`. -/
theorem exists_ker_near' [CompleteSpace Y] {N₀ N : E →L[ℝ] Y} {R : Y →L[ℝ] E} {ε : ℝ}
    (hR : N₀ ∘L R = ContinuousLinearMap.id ℝ Y) (hN : ‖N - N₀‖ ≤ ε) (hε : ε * ‖R‖ < 1)
    {v₀ : E} (hv₀ : N₀ v₀ = 0) :
    ∃ v : E, N v = 0 ∧ ‖v - v₀‖ ≤ ‖R‖ / (1 - ε * ‖R‖) * ε * ‖v₀‖ := by
  obtain ⟨R', hR', hR'n⟩ := exists_rightInverse_near hR hN hε
  have hN' : ‖N₀ - N‖ ≤ ε := by rwa [norm_sub_rev]
  obtain ⟨v, hv, hvn⟩ := exists_ker_near hR' hN' hv₀
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hN
  refine ⟨v, hv, ?_⟩
  rw [norm_sub_rev]
  exact hvn.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hR'n hε0) (norm_nonneg v₀))

/-- **The restricted norm on the kernel of the perturbed map, one direction, for a generalised
inverse.** If `N₀ R N₀ = N₀` and `‖N - N₀‖ ≤ ε`, then
`‖D|ker N‖ ≤ ‖D|ker N₀‖ + 2 ‖R‖ ε ‖D‖` for every bounded `D`. Neither surjectivity of `N₀` nor
smallness of `ε` is needed. -/
theorem restrNorm_ker_le_of_generalized {N₀ N : E →L[ℝ] Y} {R : Y →L[ℝ] E} {ε : ℝ}
    (hR : ∀ v, N₀ (R (N₀ v)) = N₀ v) (hN : ‖N - N₀‖ ≤ ε) (D : E →L[ℝ] Z) :
    restrNorm D (LinearMap.ker (N : E →ₗ[ℝ] Y)) ≤
      restrNorm D (LinearMap.ker (N₀ : E →ₗ[ℝ] Y)) + 2 * ‖R‖ * ε * ‖D‖ := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hN
  have hc : 0 ≤ ‖R‖ * ε := mul_nonneg (norm_nonneg R) hε0
  refine restrNorm_le_of_forall D _ ?_ fun v hv => ?_
  · have := restrNorm_nonneg D (LinearMap.ker (N₀ : E →ₗ[ℝ] Y))
    have := mul_nonneg hc (norm_nonneg D)
    linarith
  · have hv' : N v = 0 := by simpa using hv
    obtain ⟨v₀, hv₀, hd⟩ := exists_ker_near_of_generalized hR hN hv'
    have hv₀' : v₀ ∈ LinearMap.ker (N₀ : E →ₗ[ℝ] Y) := by simpa using hv₀
    set n₀ := restrNorm D (LinearMap.ker (N₀ : E →ₗ[ℝ] Y)) with hn₀
    have hn₀0 : 0 ≤ n₀ := restrNorm_nonneg D _
    have hn₀D : n₀ ≤ ‖D‖ := restrNorm_le_norm D _
    have h1 : ‖D v‖ ≤ ‖D v₀‖ + ‖D (v - v₀)‖ := by
      have h2 := norm_add_le (D v₀) (D (v - v₀))
      rwa [← map_add, add_sub_cancel] at h2
    have h2 : ‖D v₀‖ ≤ n₀ * ‖v₀‖ := norm_apply_le_restrNorm D hv₀'
    have h3 : ‖v₀‖ ≤ ‖v‖ + ‖R‖ * ε * ‖v‖ := by
      have h4 := norm_sub_norm_le v₀ v
      rw [norm_sub_rev] at h4
      linarith
    have h5 : ‖D (v - v₀)‖ ≤ ‖D‖ * (‖R‖ * ε * ‖v‖) :=
      (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg D))
    have h6 : n₀ * ‖v₀‖ ≤ n₀ * (‖v‖ + ‖R‖ * ε * ‖v‖) := mul_le_mul_of_nonneg_left h3 hn₀0
    have h7 : n₀ * (‖R‖ * ε * ‖v‖) ≤ ‖D‖ * (‖R‖ * ε * ‖v‖) :=
      mul_le_mul_of_nonneg_right hn₀D (mul_nonneg hc (norm_nonneg v))
    nlinarith

/-- **The restricted norm on the kernel of the perturbed map, one direction.** If `N₀ ∘ R = id`
and `‖N - N₀‖ ≤ ε`, then `‖D|ker N‖ ≤ ‖D|ker N₀‖ + 2 ‖R‖ ε ‖D‖` for every bounded `D`. -/
theorem restrNorm_ker_le {N₀ N : E →L[ℝ] Y} {R : Y →L[ℝ] E} {ε : ℝ}
    (hR : N₀ ∘L R = ContinuousLinearMap.id ℝ Y) (hN : ‖N - N₀‖ ≤ ε) (D : E →L[ℝ] Z) :
    restrNorm D (LinearMap.ker (N : E →ₗ[ℝ] Y)) ≤
      restrNorm D (LinearMap.ker (N₀ : E →ₗ[ℝ] Y)) + 2 * ‖R‖ * ε * ‖D‖ :=
  restrNorm_ker_le_of_generalized (generalized_of_rightInverse hR) hN D

/-- **The restricted norm depends Lipschitz-continuously on the map whose kernel it is taken
on** (the paper, proof of Theorem `thm:memory` (i)). If `N₀ ∘ R = id`, `‖N - N₀‖ ≤ ε` and
`ε ‖R‖ < 1`, then for every bounded `D`

  `| ‖D|ker N‖ - ‖D|ker N₀‖ | ≤ 2 ‖R‖ ε ‖D‖ / (1 - ε ‖R‖)`. -/
theorem abs_restrNorm_ker_sub_le [CompleteSpace Y] {N₀ N : E →L[ℝ] Y} {R : Y →L[ℝ] E} {ε : ℝ}
    (hR : N₀ ∘L R = ContinuousLinearMap.id ℝ Y) (hN : ‖N - N₀‖ ≤ ε) (hε : ε * ‖R‖ < 1)
    (D : E →L[ℝ] Z) :
    |restrNorm D (LinearMap.ker (N : E →ₗ[ℝ] Y)) -
        restrNorm D (LinearMap.ker (N₀ : E →ₗ[ℝ] Y))| ≤
      2 * ‖R‖ * ε * ‖D‖ / (1 - ε * ‖R‖) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hN
  have hden : 0 < 1 - ε * ‖R‖ := by linarith
  have hden1 : 1 - ε * ‖R‖ ≤ 1 := by
    have := mul_nonneg hε0 (norm_nonneg R)
    linarith
  have hnum : 0 ≤ 2 * ‖R‖ * ε * ‖D‖ := by positivity
  have h1 := restrNorm_ker_le hR hN D
  obtain ⟨R', hR', hR'n⟩ := exists_rightInverse_near hR hN hε
  have hN' : ‖N₀ - N‖ ≤ ε := by rwa [norm_sub_rev]
  have h2 := restrNorm_ker_le hR' hN' D
  have h3 : 2 * ‖R'‖ * ε * ‖D‖ ≤ 2 * ‖R‖ * ε * ‖D‖ / (1 - ε * ‖R‖) := by
    have h4 : 2 * ‖R'‖ * ε * ‖D‖ ≤ 2 * (‖R‖ / (1 - ε * ‖R‖)) * ε * ‖D‖ := by
      have := mul_nonneg hε0 (norm_nonneg D)
      nlinarith
    have h5 : 2 * (‖R‖ / (1 - ε * ‖R‖)) * ε * ‖D‖ = 2 * ‖R‖ * ε * ‖D‖ / (1 - ε * ‖R‖) := by
      field_simp
    linarith
  have h6 : 2 * ‖R‖ * ε * ‖D‖ ≤ 2 * ‖R‖ * ε * ‖D‖ / (1 - ε * ‖R‖) := by
    rw [le_div_iff₀ hden]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end Kernel

section FiniteDimension

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- In finite dimension a surjective bounded map has a bounded right inverse: independent maps
are a stacked map with a right inverse. -/
theorem exists_rightInverse_of_surjective (N₀ : E →L[ℝ] Y) (h : Function.Surjective N₀) :
    ∃ R : Y →L[ℝ] E, N₀ ∘L R = ContinuousLinearMap.id ℝ Y := by
  obtain ⟨g, hg⟩ := (N₀ : E →ₗ[ℝ] Y).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 h)
  refine ⟨LinearMap.toContinuousLinearMap g, ?_⟩
  ext y
  have h1 := LinearMap.congr_fun hg y
  simpa using h1

/-- In finite dimension every bounded map has a bounded generalised inverse, `N₀ R N₀ = N₀`. -/
theorem exists_generalizedInverse (N₀ : E →L[ℝ] Y) :
    ∃ R : Y →L[ℝ] E, ∀ v, N₀ (R (N₀ v)) = N₀ v := by
  set f : E →ₗ[ℝ] Y := (N₀ : E →ₗ[ℝ] Y) with hf
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨R, hRg⟩ := g.exists_extend
  refine ⟨LinearMap.toContinuousLinearMap R, fun v => ?_⟩
  have h1 : R (f v) = g (f.rangeRestrict v) := by
    have h2 := LinearMap.congr_fun hRg (f.rangeRestrict v)
    simpa using h2
  have h3 : f.rangeRestrict (g (f.rangeRestrict v)) = f.rangeRestrict v :=
    LinearMap.congr_fun hg (f.rangeRestrict v)
  have h4 : f (g (f.rangeRestrict v)) = f v := congrArg Subtype.val h3
  change f (R (f v)) = f v
  rw [h1, h4]

end FiniteDimension

end CoSimFoundations
