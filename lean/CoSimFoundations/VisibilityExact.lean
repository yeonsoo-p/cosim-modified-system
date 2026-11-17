/-
The visibility bound is exact (the paper, Definition 4.1 and Theorem 4.2, converse).

Setting as in `VisibilityFloor`: `Pr : E → Eᵢ` the projection onto subsystem `i`, `U` the
monolithic step, `N k : E → Y k` the monolithic samples shown to the subsystem. The *states not
shown* are `𝒱 = ker Pr ⊓ ⋂_k ker (N k)` (`notShown`), and the *visibility bound* is the norm of the
restriction of the block row `Pr ∘ U` to `𝒱` (`visBound`),

  `f = max {‖Pr (U v)‖ : v ∈ 𝒱, ‖v‖ = 1}`   (`norm_apply_le_visBound`, `isGreatest_visBound`).

Statements.
* Linear algebra (any field): `ker T ≤ ker R` iff `R = G ∘ T` for some linear `G`
  (`ker_le_ker_iff_exists_comp`). With `T` the stacking of `Pr` and of the samples: a map `R`
  vanishes on `𝒱` iff `R = F ∘ Pr + Σ_k G k ∘ N k` for some `F`, `G`
  (`exists_rule_iff_ker_le`). Proof: `R` factors through the range of `T`, and a linear map on a
  subspace extends to the whole space.
* Hence `f = 0` iff the block row is a rule on the monolithic samples,
  `Pr ∘ U = F ∘ Pr + Σ_k G k ∘ N k` (`visBound_eq_zero_iff_exists_rule`).
* The equality behind Definition 4.1 (`isLeast_visBound`): for a finite-dimensional inner product
  space `E`,

    `min_{F, G} ‖Pr ∘ U - F ∘ Pr - Σ_k G k ∘ N k‖ = f`.

  `≥` holds for every rule because the rule vanishes on `𝒱` (`visBound_le_norm_rule`; no inner
  product needed). `≤`: the map `Pr ∘ U ∘ (1 - P)`, `P` the orthogonal projection onto `𝒱`,
  vanishes on `𝒱` and is therefore a rule; what it leaves is `Pr ∘ U ∘ P`, of norm `f`.
* With `visibility_floor` this gives the inequality of Theorem 4.2 for the `f` of Definition 4.1
  (`visBound_le_scheme`).
* The converse of Theorem 4.2 as a statement about schemes, for one held sample and scalar stores
  in any order of execution (`exists_exact_infoStep_iff`): the monolithic step `U` is the one-step
  map of a scheme with full access on the coupling graph if and only if every row of `U` vanishes
  on the states not shown to its store. Proof: the rules of the stores say `(1 - N) U = F + M`,
  and the one-step map is the only solution of this relation (`InfoForm`).

Not formalised: the step map of a scheme with several held samples, and therefore the converse
for more than one held sample (there the rule has to be shown to leave invariant the graph on which
the stored samples are those of the monolithic system, by induction over the stages).
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import CoSimFoundations.VisibilityFloor
import CoSimFoundations.InfoForm

namespace CoSimFoundations

section LinearAlgebra

variable {K E W Z Ei : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup W]
  [Module K W] [AddCommGroup Z] [Module K Z] [AddCommGroup Ei] [Module K Ei]
  {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ k, AddCommGroup (Y k)] [∀ k, Module K (Y k)]

/-- **Factorisation through a map with smaller kernel.** If `R` vanishes on the kernel of `T`,
then `R = G ∘ T` for a linear map `G`. -/
theorem exists_comp_eq_of_ker_le (T : E →ₗ[K] W) (R : E →ₗ[K] Z)
    (h : LinearMap.ker T ≤ LinearMap.ker R) : ∃ G : W →ₗ[K] Z, G ∘ₗ T = R := by
  have hk : LinearMap.ker T.rangeRestrict ≤ LinearMap.ker R := by
    rw [LinearMap.ker_rangeRestrict]
    exact h
  obtain ⟨G, hG⟩ :=
    (T.rangeRestrict.liftOfSurjective T.surjective_rangeRestrict ⟨R, hk⟩).exists_extend
  refine ⟨G, LinearMap.ext fun x => ?_⟩
  have h1 := LinearMap.congr_fun hG (T.rangeRestrict x)
  rw [LinearMap.equivOfSurjective_apply] at h1
  exact h1

/-- `R` vanishes on the kernel of `T` if and only if `R` factors through `T`. -/
theorem ker_le_ker_iff_exists_comp (T : E →ₗ[K] W) (R : E →ₗ[K] Z) :
    LinearMap.ker T ≤ LinearMap.ker R ↔ ∃ G : W →ₗ[K] Z, G ∘ₗ T = R := by
  constructor
  · exact exists_comp_eq_of_ker_le T R
  · rintro ⟨G, rfl⟩
    exact LinearMap.ker_le_ker_comp T G

/-- **A map is a rule on the information iff it vanishes on what is not shown.** For linear maps
`Pr` (the own state) and `N k` (the samples), a linear map `R` has the form
`R = F ∘ Pr + Σ_k G k ∘ N k` if and only if it vanishes on `ker Pr ⊓ ⋂_k ker (N k)`. -/
theorem exists_rule_iff_ker_le (Pr : E →ₗ[K] Ei) (N : ∀ k, E →ₗ[K] Y k) (R : E →ₗ[K] Z) :
    (∃ (F : Ei →ₗ[K] Z) (G : ∀ k, Y k →ₗ[K] Z), R = F ∘ₗ Pr + ∑ k, G k ∘ₗ N k) ↔
      LinearMap.ker Pr ⊓ ⨅ k, LinearMap.ker (N k) ≤ LinearMap.ker R := by
  classical
  constructor
  · rintro ⟨F, G, rfl⟩ v hv
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mem_ker.1 hv.1,
      map_zero, zero_add, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun k _ => by
      rw [LinearMap.comp_apply, LinearMap.mem_ker.1 (hv.2 k), map_zero]
  · intro h
    have hk : LinearMap.ker (Pr.prod (LinearMap.pi N)) ≤ LinearMap.ker R := by
      rw [LinearMap.ker_prod, LinearMap.ker_pi]
      exact h
    obtain ⟨Gt, hGt⟩ := exists_comp_eq_of_ker_le _ R hk
    refine ⟨Gt ∘ₗ LinearMap.inl K Ei (∀ k, Y k),
      fun k => Gt ∘ₗ LinearMap.inr K Ei (∀ k, Y k) ∘ₗ LinearMap.single K Y k, ?_⟩
    ext x
    have hx : ((Pr x, fun k => N k x) : Ei × (∀ k, Y k)) =
        (Pr x, 0) + ∑ k, ((0 : Ei), Pi.single k (N k x)) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_add, Prod.snd_sum, zero_add]
        exact (LinearMap.sum_single_apply _ (fun k => N k x)).symm
    have hT : Pr.prod (LinearMap.pi N) x = (Pr x, fun k => N k x) := rfl
    rw [← hGt, LinearMap.comp_apply, hT, hx, map_add, map_sum]
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.coe_single]

end LinearAlgebra

section Normed

variable {E Ei : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Ei] [NormedSpace ℝ Ei]
  {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ k, NormedAddCommGroup (Y k)]
  [∀ k, NormedSpace ℝ (Y k)]

/-- **The states not shown to the subsystem** (the paper, Definition 4.1): its own state vanishes and
so does every sample that it would be shown. -/
def notShown (Pr : E →L[ℝ] Ei) (N : ∀ k, E →L[ℝ] Y k) : Submodule ℝ E :=
  LinearMap.ker (Pr : E →ₗ[ℝ] Ei) ⊓ ⨅ k, LinearMap.ker (N k : E →ₗ[ℝ] Y k)

/-- Membership in the states not shown. -/
theorem mem_notShown {Pr : E →L[ℝ] Ei} {N : ∀ k, E →L[ℝ] Y k} {v : E} :
    v ∈ notShown Pr N ↔ Pr v = 0 ∧ ∀ k, N k v = 0 := by
  simp [notShown, Submodule.mem_inf, Submodule.mem_iInf]

/-- **The visibility bound** (the paper, Definition 4.1): the norm of the block row `Pr ∘ U` of the
monolithic step on the states not shown. -/
noncomputable def visBound (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k) : ℝ :=
  ‖(Pr.comp U).comp (notShown Pr N).subtypeL‖

/-- The visibility bound is not negative. -/
theorem visBound_nonneg (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k) :
    0 ≤ visBound Pr U N := norm_nonneg ((Pr.comp U).comp (notShown Pr N).subtypeL)

/-- The response of the subsystem to a state not shown is at most the visibility bound. -/
theorem norm_apply_le_visBound (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k)
    {v : E} (hv : v ∈ notShown Pr N) : ‖Pr (U v)‖ ≤ visBound Pr U N * ‖v‖ :=
  ((Pr.comp U).comp (notShown Pr N).subtypeL).le_opNorm ⟨v, hv⟩

/-- The visibility bound is the least constant with this property. -/
theorem visBound_le_of_forall (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ v ∈ notShown Pr N, ‖Pr (U v)‖ ≤ c * ‖v‖) :
    visBound Pr U N ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc fun v => h v v.2

/-- **The visibility bound is a maximum** (the paper, Definition 4.1): in finite dimension, if some
state is not shown, the bound is the largest response `‖Pr (U v)‖` to a unit state `v` not shown.
(If every state is shown the bound is zero, `visBound_eq_zero_iff`.) -/
theorem isGreatest_visBound [FiniteDimensional ℝ E] (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E)
    (N : ∀ k, E →L[ℝ] Y k) (hV : notShown Pr N ≠ ⊥) :
    IsGreatest {r : ℝ | ∃ v ∈ notShown Pr N, ‖v‖ = 1 ∧ r = ‖Pr (U v)‖} (visBound Pr U N) := by
  have : Nontrivial (notShown Pr N) := Submodule.nontrivial_iff_ne_bot.2 hV
  change IsGreatest _ ‖(Pr.comp U).comp (notShown Pr N).subtypeL‖
  set T := (Pr.comp U).comp (notShown Pr N).subtypeL
  constructor
  · have hne : (Metric.sphere (0 : notShown Pr N) 1).Nonempty :=
      NormedSpace.sphere_nonempty.2 zero_le_one
    obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : notShown Pr N) 1).exists_isMaxOn hne
      (continuous_norm.comp T.continuous).continuousOn
    have hx1 : ‖x‖ = 1 := by simpa using hx
    refine ⟨x, x.2, hx1, le_antisymm ?_ ?_⟩
    · refine T.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy => ?_
      exact hmax (show y ∈ Metric.sphere (0 : notShown Pr N) 1 by simpa using hy)
    · have h1 := T.le_opNorm x
      rw [hx1, mul_one] at h1
      exact h1
  · rintro r ⟨v, hv, hv1, rfl⟩
    have h1 := norm_apply_le_visBound Pr U N hv
    rw [hv1, mul_one] at h1
    exact h1

/-- The visibility bound vanishes iff the block row vanishes on the states not shown. -/
theorem visBound_eq_zero_iff (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k) :
    visBound Pr U N = 0 ↔ ∀ v ∈ notShown Pr N, Pr (U v) = 0 := by
  constructor
  · intro h v hv
    have h1 := norm_apply_le_visBound Pr U N hv
    rw [h, zero_mul] at h1
    exact norm_le_zero_iff.1 h1
  · intro h
    refine le_antisymm (visBound_le_of_forall Pr U N le_rfl fun v hv => ?_) (visBound_nonneg _ _ _)
    rw [h v hv, norm_zero, zero_mul]

/-- **No rule on the monolithic samples comes closer to the block row than the visibility
bound**: `f ≤ ‖Pr ∘ U - F ∘ Pr - Σ_k G k ∘ N k‖` for all `F`, `G`. -/
theorem visBound_le_norm_rule (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k)
    (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei) :
    visBound Pr U N ≤ ‖Pr.comp U - F.comp Pr - ∑ k, (G k).comp (N k)‖ := by
  refine visBound_le_of_forall Pr U N (norm_nonneg _) fun v hv => ?_
  obtain ⟨h1, h2⟩ := mem_notShown.1 hv
  have h3 : (Pr.comp U - F.comp Pr - ∑ k, (G k).comp (N k)) v = Pr (U v) := by
    simp [h1, h2]
  rw [← h3]
  exact ContinuousLinearMap.le_opNorm _ v

/-- **Theorem 4.2 with the bound of Definition 4.1.** Every scheme whose subsystem obeys
`Pr ∘ P = F ∘ Pr + Σ_k G k ∘ M k` (`M k` the samples it uses) satisfies
`f ≤ ‖Pr ∘ (P - U)‖ + Σ_k ‖G k‖ ‖M k - N k‖`, with `f` the visibility bound. -/
theorem visBound_le_scheme (Pr : E →L[ℝ] Ei) (P U : E →L[ℝ] E) (N M : ∀ k, E →L[ℝ] Y k)
    (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei)
    (hstep : Pr.comp P = F.comp Pr + ∑ k, (G k).comp (M k)) :
    visBound Pr U N ≤ ‖Pr.comp (P - U)‖ + ∑ k, ‖G k‖ * ‖M k - N k‖ :=
  visibility_floor Pr P U Set.univ N (fun FG _ => visBound_le_norm_rule Pr U N FG.1 FG.2) F G
    (Set.mem_univ _) M hstep

/-- **A map that vanishes on the states not shown is a rule on the monolithic samples.** If the
own state and the samples are finite-dimensional and the continuous map `R` vanishes on the
states not shown, then `R = F ∘ Pr + Σ_k G k ∘ N k` with continuous `F` and `G k`. -/
theorem exists_rule_of_notShown_le [FiniteDimensional ℝ Ei] [∀ k, FiniteDimensional ℝ (Y k)]
    (Pr : E →L[ℝ] Ei) (N : ∀ k, E →L[ℝ] Y k) (R : E →L[ℝ] Ei)
    (hk : notShown Pr N ≤ LinearMap.ker (R : E →ₗ[ℝ] Ei)) :
    ∃ (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei), R = F.comp Pr + ∑ k, (G k).comp (N k) := by
  have hk' : LinearMap.ker (Pr : E →ₗ[ℝ] Ei) ⊓ ⨅ k, LinearMap.ker (N k : E →ₗ[ℝ] Y k) ≤
      LinearMap.ker (R : E →ₗ[ℝ] Ei) := hk
  obtain ⟨F, G, hFG⟩ := (exists_rule_iff_ker_le _ _ _).2 hk'
  refine ⟨LinearMap.toContinuousLinearMap F, fun k => LinearMap.toContinuousLinearMap (G k), ?_⟩
  ext x
  have hx := LinearMap.congr_fun hFG x
  simpa [LinearMap.sum_apply] using hx

/-- **The visibility bound vanishes iff the block row is a rule on the monolithic samples**
(the paper, Theorem 4.2, the step of the converse): `f = 0` iff
`Pr ∘ U = F ∘ Pr + Σ_k G k ∘ N k` for some `F`, `G`. -/
theorem visBound_eq_zero_iff_exists_rule [FiniteDimensional ℝ Ei] [∀ k, FiniteDimensional ℝ (Y k)]
    (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k) :
    visBound Pr U N = 0 ↔
      ∃ (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei),
        Pr.comp U = F.comp Pr + ∑ k, (G k).comp (N k) := by
  constructor
  · intro h
    exact exists_rule_of_notShown_le Pr N (Pr.comp U) fun v hv =>
      (visBound_eq_zero_iff Pr U N).1 h v hv
  · rintro ⟨F, G, h⟩
    refine le_antisymm ?_ (visBound_nonneg _ _ _)
    have h1 := visBound_le_norm_rule Pr U N F G
    rwa [h, add_sub_cancel_left, sub_self, norm_zero] at h1

end Normed

section Exact

variable {E Ei : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Ei] [NormedSpace ℝ Ei] [FiniteDimensional ℝ Ei]
  {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ k, NormedAddCommGroup (Y k)]
  [∀ k, NormedSpace ℝ (Y k)] [∀ k, FiniteDimensional ℝ (Y k)]

/-- **The best rule.** Some rule on the monolithic samples leaves exactly the block row on the
states not shown: `Pr ∘ U - F ∘ Pr - Σ_k G k ∘ N k = Pr ∘ U ∘ P`, `P` the orthogonal projection
onto the states not shown. -/
theorem exists_rule_eq_comp_starProjection (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E)
    (N : ∀ k, E →L[ℝ] Y k) :
    ∃ (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei),
      Pr.comp U - F.comp Pr - ∑ k, (G k).comp (N k) =
        (Pr.comp U).comp (notShown Pr N).starProjection := by
  set R₀ : E →L[ℝ] Ei :=
    (Pr.comp U).comp (ContinuousLinearMap.id ℝ E - (notShown Pr N).starProjection) with hR₀
  have hk : notShown Pr N ≤ LinearMap.ker (R₀ : E →ₗ[ℝ] Ei) := fun v hv => by
    have hv' : (notShown Pr N).starProjection v = v :=
      Submodule.starProjection_eq_self_iff.2 hv
    simp [hR₀, hv']
  obtain ⟨F, G, hFG⟩ := exists_rule_of_notShown_le Pr N R₀ hk
  refine ⟨F, G, ?_⟩
  rw [sub_sub, ← hFG, hR₀, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
    sub_sub_cancel]

/-- **The equality behind Definition 4.1** (the paper, Theorem 4.2): the visibility bound is the
least distance, in the operator norm, of the block row `Pr ∘ U` of the monolithic step from the
rules `F ∘ Pr + Σ_k G k ∘ N k` on the monolithic samples, and the distance is attained. -/
theorem isLeast_visBound (Pr : E →L[ℝ] Ei) (U : E →L[ℝ] E) (N : ∀ k, E →L[ℝ] Y k) :
    IsLeast {r : ℝ | ∃ (F : Ei →L[ℝ] Ei) (G : ∀ k, Y k →L[ℝ] Ei),
      r = ‖Pr.comp U - F.comp Pr - ∑ k, (G k).comp (N k)‖} (visBound Pr U N) := by
  constructor
  · obtain ⟨F, G, h⟩ := exists_rule_eq_comp_starProjection Pr U N
    refine ⟨F, G, le_antisymm (visBound_le_norm_rule Pr U N F G) ?_⟩
    rw [h]
    refine ContinuousLinearMap.opNorm_le_bound _ (visBound_nonneg _ _ _) fun x => ?_
    calc ‖Pr (U ((notShown Pr N).starProjection x))‖
        ≤ visBound Pr U N * ‖(notShown Pr N).starProjection x‖ :=
          norm_apply_le_visBound Pr U N (Submodule.starProjection_apply_mem _ x)
      _ ≤ visBound Pr U N * ‖x‖ :=
          mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ x)
            (visBound_nonneg _ _ _)
  · rintro r ⟨F, G, rfl⟩
    exact visBound_le_norm_rule Pr U N F G

end Exact

section OneSample

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear map `ℝ → ℝ` is the multiplication by its value at `1`. -/
private theorem apply_eq_apply_one_mul (f : ℝ →ₗ[ℝ] ℝ) (x : ℝ) : f x = f 1 * x := by
  have h := f.map_smul x 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at h
  rw [h, mul_comm]

/-- **The converse of the visibility theorem for one held sample** (the paper, Theorem 4.2; scalar
stores, any order of execution). The monolithic step `U` is the one-step map of a scheme with one
held sample and full access on the coupling graph (`infoStep`, coefficients `G i j` only between
partners) if and only if, for every store `i`, the row `i` of `U` vanishes on the states not shown
to `i`: the states `v` with `v i = 0` whose samples shown to `i` vanish, the new sample
`(U v) j` of a partner at an earlier stage and the old sample `v j` of any other partner. -/
theorem exists_exact_infoStep_iff (U : Matrix ι ι ℝ) (stage : ι → ℕ) (partner : ι → ι → Prop) :
    (∃ (F : ι → ℝ) (G : Matrix ι ι ℝ), (∀ i, G i i = 0) ∧ (∀ i j, ¬ partner i j → G i j = 0) ∧
        U = infoStep stage (diagonal F) G) ↔
      ∀ (i : ι) (v : ι → ℝ), v i = 0 →
        (∀ j, partner i j → j ≠ i → (if stage j < stage i then (U *ᵥ v) j else v j) = 0) →
        (U *ᵥ v) i = 0 := by
  classical
  constructor
  · rintro ⟨F, G, hG0, hG, rfl⟩ i v hvi hs
    rw [infoStep_diagonal_mulVec_apply, hvi, mul_zero, zero_add]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hp : partner i j
    · by_cases hji : j = i
      · rw [hji, hG0, zero_mul]
      · rw [hs j hp hji, mul_zero]
    · rw [hG i j hp, zero_mul]
  · intro h
    have key : ∀ i, ∃ (f : ℝ) (g : ι → ℝ), g i = 0 ∧ (∀ j, ¬ partner i j → g j = 0) ∧
        ∀ v : ι → ℝ, (U *ᵥ v) i = f * v i +
          ∑ j, g j * (if stage j < stage i then (U *ᵥ v) j else v j) := by
      intro i
      -- the sample of store `j` shown to store `i`, as a linear functional of the state
      let S : ι → ((ι → ℝ) →ₗ[ℝ] ℝ) := fun j =>
        if stage j < stage i then LinearMap.proj j ∘ₗ U.mulVecLin else LinearMap.proj j
      have hS : ∀ j v, S j v = if stage j < stage i then (U *ᵥ v) j else v j := by
        intro j v
        simp only [S]
        split_ifs <;> simp
      let Nk : ι → ((ι → ℝ) →ₗ[ℝ] ℝ) := fun j => if partner i j ∧ j ≠ i then S j else 0
      have hk : LinearMap.ker (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) ⊓ ⨅ j, LinearMap.ker (Nk j) ≤
          LinearMap.ker (LinearMap.proj i ∘ₗ U.mulVecLin : (ι → ℝ) →ₗ[ℝ] ℝ) := by
        intro v hv
        rw [Submodule.mem_inf, Submodule.mem_iInf] at hv
        refine h i v hv.1 fun j hp hji => ?_
        have h1 := LinearMap.mem_ker.1 (hv.2 j)
        simp only [Nk, ite_eq_left (And.intro hp hji)] at h1
        rw [← hS j v]
        exact h1
      obtain ⟨F₀, G₀, hFG⟩ := (exists_rule_iff_ker_le _ _ _).2 hk
      refine ⟨F₀ 1, fun j => if partner i j ∧ j ≠ i then G₀ j 1 else 0, by simp,
        fun j hj => by simp [hj], fun v => ?_⟩
      have hv := LinearMap.congr_fun hFG v
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.proj_apply, Matrix.mulVecLin_apply] at hv
      rw [hv, apply_eq_apply_one_mul F₀]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hp : partner i j ∧ j ≠ i
      · simp only [Nk, ite_eq_left hp]
        rw [apply_eq_apply_one_mul (G₀ j), hS j v]
      · simp only [Nk, ite_eq_right hp, LinearMap.zero_apply, map_zero, zero_mul]
    choose F G hGii hG hrow using key
    refine ⟨F, Matrix.of G, hGii, hG, Matrix.mulVec_injective (funext fun v => ?_)⟩
    refine (eq_infoStep_mulVec_iff stage (diagonal F) (Matrix.of G) v (U *ᵥ v)).2 fun i => ?_
    rw [mulVec_diagonal]
    exact hrow i v

end OneSample

end CoSimFoundations
