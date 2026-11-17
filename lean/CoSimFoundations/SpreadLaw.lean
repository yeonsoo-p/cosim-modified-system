/-
The spread form of the trade-off between injection and damping (the paper, Section 6: Theorem
"injection or damping", `thm:triple`, and Corollary "the amount", `cor:amount`; Section 4,
Corollary "the blocks that the coefficients do not reach" (a), eq. `eq:parts`).

**1. The spread form** (`abs_inner_add_inner_le_spread`, `two_mul_abs_inner_le_spread`,
`spread_law`, `spread_law_symm`). Let `S` be a real symmetric matrix (or a self-adjoint operator on
a real inner product space, of any dimension) and `μ`, `ι` reals with
  `-ι · xᵀ x ≤ xᵀ S x ≤ μ · xᵀ x`   for all `x`
(the least such numbers are `μ = λ_max (S)` and `ι = -λ_min (S)`; no eigenvalue is used). Then for
orthonormal `e`, `f`
  `2 |eᵀ S f| ≤ μ + ι`,   that is   `λ_max (S) - λ_min (S) ≥ 2 |eᵀ S f|`
(the classical bound on the spread of a symmetric matrix, Mirsky). Without symmetry the same proof
gives `|eᵀ S f + fᵀ S e| ≤ μ + ι`. There is no factor `n`.
Proof: `u = e + f` and `v = e - f` have squared length `2`, and
`uᵀ S u - vᵀ S v = 2 (eᵀ S f + fᵀ S e)`; the upper bound on one and the lower bound on the other.

**2. The local form** (`abs_inner_add_inner_le_local` of `TripleLawGeneral.lean`,
`two_mul_abs_inner_le_local`, `spread_law_local`, `spread_law_local_symm`). With the lower bound
alone:
  `2 |eᵀ S f| ≤ eᵀ S e + fᵀ S f + 2 ι`
(the lower bound on `u` and on `v`). Only the two vectors enter. This is the first step of the
paper's proof of `thm:triple`: `P = S + ι` is positive semidefinite, hence
`eᵀ P e + fᵀ P f ≥ 2 |eᵀ P f|`.

**3. The spread form and the trace form** (`inner_le_trace_add`, `quadForm_le_trace_add`).
The trace form of `TripleLawGeneral.lean`
(`damping_add_injection_ge`) is `2 |eᵀ S f| ≤ tr S + n ι`. If `-ι` is a lower bound of the form of
an `n × n` matrix `S`, then `μ = tr S + (n - 1) ι` is an upper bound:
  `xᵀ S x ≤ (tr S + (n - 1) ι) · xᵀ x`
(a unit vector is completed to an orthonormal basis; the trace is the sum of the form over the
basis and each of the other `n - 1` terms is at least `-ι`). The spread form with this `μ` is the
trace form, `μ + ι = tr S + n ι`. So the spread form implies the trace form, and with the least
`μ` it is at least as strong: `λ_max (S) - λ_min (S) ≤ tr S - n λ_min (S)`. The two coincide for
`n = 2`. The local form implies the trace form as well (that is the proof in
`TripleLawGeneral.lean`); the local form and the spread form do not imply each other.

**4. A co-simulation, one-step form** (`Consistent.half_step_forced_sym`,
`Consistent.spread_forced`, `Consistent.spread_forced_local`, `Consistent.spread_forced_leg`,
`Consistent.spread_forced_leg_sym`, `Consistent.spread_forced_conservative`,
`Consistent.spread_forced_skew`, `Consistent.spread_forced_jacobi`). Setting of `HalfStep` and
`LegRule`: a `HeldScheme` (`X = F + M + N * X`), `U = exp (H • A)`, `S.Consistent A U H a b c`,
the signed coupling `A_ς = signedCoupling A`, `C₃ = reactionC a b c ‖A‖ H`. Let `i ≠ j` be
subsystems that are not partners (in either direction), `x` a unit vector supported on `i`, `y`
one supported on `j`.
`Consistent.half_step_forced` in both directions gives
  `|⟪x, (X - U) y⟫ + ⟪y, (X - U) x⟫ - ½H² (⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫)| ≤ 2 C₃ H³`.
If `-ι ‖v‖² ≤ ⟪v, (X - U) v⟫ ≤ μ ‖v‖²` for all `v`, the spread form for `X - U` gives
  `μ + ι ≥ ½H² |⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫| - 2 C₃ H³`,
and the local form, with the lower bound alone,
  `⟪x, (X - U) x⟫ + ⟪y, (X - U) y⟫ + 2 ι ≥ ½H² |⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫| - 2 C₃ H³`.
No symmetry of the coupling is used. The right-hand side is then evaluated:
* a single common partner `k` (`A p r A r q = 0` and `A q r A r p = 0` unless `r` is a state of
  `k`), the link `i`-`k` of kind `ε₁`, the link `k`-`j` of kind `ε₂` (`LegRule.lean`):
  `⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫ = (ς_{ik} + ε₁ ε₂ ς_{jk}) ⟪x, A mask_k A y⟫`, hence
    `μ + ι ≥ ½H² |ς_{ik} + ε₁ ε₂ ς_{jk}| |⟪x, A mask_k A y⟫| - 2 C₃ H³`;
  if the factor of the leg rule is one, `ε₁ ε₂ ς_{jk} ς_{ik} = 1` (links of the same kind and `k`
  not between `i` and `j`, or links of different kinds and `k` between them), this is
    `μ + ι ≥ H² |⟪x, A mask_k A y⟫| - 2 C₃ H³`,   `⟪x, A mask_k A y⟫ = xᵀ A_{ik} A_{kj} y`;
  if the factor is `-1` the right-hand side is `-2 C₃ H³` and nothing is forced (a numerical
  interconnection);
* power-conserving coupling (`hskew`: `A q p = -A p q` between different subsystems) and a single
  common partner `k` with `ς_{ik} = ς_{jk}`: the same bound `H² |⟪x, A mask_k A y⟫| - 2 C₃ H³`
  (the condition on `A q r A r p` follows from the one on `A p r A r q`);
* power-conserving coupling and any number of common partners:
    `μ + ι ≥ ½H² |⟪x, A (ς_i + ς_j) A y⟫| - 2 C₃ H³`,
  the sum `Σ_k (ς_{ik} + ς_{jk}) xᵀ A_{ik} A_{kj} y` of `eq:amount`; in a Jacobi scheme (all
  subsystems at the same stage) this is `μ + ι ≥ H² |⟪x, A² y⟫| - 2 C₃ H³`.

Item 4 is the one-step form: it is a statement about the one-step error `X - U` at the given macro
step, with an explicit remainder, and not about the modified system `Ã` and its difference `Δ`. No
modified system is assumed to exist. To leading order `X - U = H Δ`, and with the paper's
`Δ_R = -sym Δ` the bounds read `μ = H · (injection rate ι of the paper)` and
`ι = H · λ_max (Δ_R)`; this reading is not formalised here. (The statement of `cor:amount` for `Δ`
with its remainder, in the trace form and for coordinate directions, is `Consistent.amount` in
`ForcedParts.lean`.)
-/
import CoSimFoundations.TripleLawGeneral
import CoSimFoundations.LegRule

open Module Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

/-! ### Operators on a real inner product space -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The spread form for a linear map and an orthonormal pair.** If
`-ι ‖x‖² ≤ ⟪x, T x⟫ ≤ μ ‖x‖²` for all `x`, then `|⟪e, T f⟫ + ⟪f, T e⟫| ≤ μ + ι` for orthonormal
`e`, `f`. The space may have any dimension and `T` need not be symmetric. -/
theorem abs_inner_add_inner_le_spread (T : E →ₗ[ℝ] E) {μ ι : ℝ}
    (hlo : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) (hhi : ∀ x : E, ⟪x, T x⟫ ≤ μ * ‖x‖ ^ 2) {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    |⟪e, T f⟫ + ⟪f, T e⟫| ≤ μ + ι := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal he hf hef
  have up := hhi (e + f)
  have lp := hlo (e + f)
  have um := hhi (e - f)
  have lm := hlo (e - f)
  rw [hp, map_add, inner_add_left, inner_add_right, inner_add_right] at up lp
  rw [hm, map_sub, inner_sub_left, inner_sub_right, inner_sub_right] at um lm
  rw [abs_le]
  constructor <;> linarith

/-- **The spread form for a self-adjoint linear map.** If `T` is self-adjoint and
`-ι ‖x‖² ≤ ⟪x, T x⟫ ≤ μ ‖x‖²` for all `x` (as `μ = λ_max`, `ι = -λ_min`), then
`2 |⟪e, T f⟫| ≤ μ + ι` for orthonormal `e`, `f`. -/
theorem two_mul_abs_inner_le_spread (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {μ ι : ℝ}
    (hlo : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) (hhi : ∀ x : E, ⟪x, T x⟫ ≤ μ * ‖x‖ ^ 2) {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    2 * |⟪e, T f⟫| ≤ μ + ι := by
  have h := abs_inner_add_inner_le_spread T hlo hhi he hf hef
  rw [inner_apply_comm_of_isSymmetric hT e f, ← two_mul, abs_mul, abs_two] at h
  exact h

/-- **The local form for a self-adjoint linear map.** If `T` is self-adjoint and
`-ι ‖x‖² ≤ ⟪x, T x⟫` for all `x`, then `2 |⟪e, T f⟫| ≤ ⟪e, T e⟫ + ⟪f, T f⟫ + 2 ι` for orthonormal
`e`, `f`. -/
theorem two_mul_abs_inner_le_local (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {ι : ℝ}
    (hlo : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) :
    2 * |⟪e, T f⟫| ≤ ⟪e, T e⟫ + ⟪f, T f⟫ + 2 * ι := by
  have h := abs_inner_add_inner_le_local T hlo he hf hef
  rw [inner_apply_comm_of_isSymmetric hT e f, ← two_mul, abs_mul, abs_two] at h
  exact h

variable [FiniteDimensional ℝ E]

/-- The form of a linear map on a unit vector against the trace: if `-ι ‖x‖² ≤ ⟪x, T x⟫` for all
`x`, then `⟪e, T e⟫ ≤ tr T + (n - 1) ι` for a unit vector `e`, `n` the dimension. -/
theorem inner_le_trace_add_of_norm_eq_one (T : E →ₗ[ℝ] E) {ι : ℝ}
    (hι : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) {e : E} (he : ‖e‖ = 1) :
    ⟪e, T e⟫ ≤ LinearMap.trace ℝ E T + ((finrank ℝ E : ℝ) - 1) * ι := by
  classical
  have hon : Orthonormal ℝ ((↑) : ({e} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro v hv w hw
    rw [Set.mem_singleton_iff.1 hv, Set.mem_singleton_iff.1 hw, ite_eq_left rfl,
      real_inner_self_eq_norm_sq, he, one_pow]
  rw [← Finset.coe_singleton] at hon
  have h := sum_inner_sub_le_trace_sub T hι hon
  rw [Finset.sum_singleton] at h
  linarith

/-- **An upper bound of the form from the trace and a lower bound.** If `-ι ‖x‖² ≤ ⟪x, T x⟫` for
all `x`, then `⟪x, T x⟫ ≤ (tr T + (n - 1) ι) ‖x‖²` for all `x`, `n` the dimension: `λ_max` is at
most the trace minus `n - 1` times `λ_min`. -/
theorem inner_le_trace_add (T : E →ₗ[ℝ] E) {ι : ℝ} (hι : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫)
    (x : E) :
    ⟪x, T x⟫ ≤ (LinearMap.trace ℝ E T + ((finrank ℝ E : ℝ) - 1) * ι) * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · rw [hx, map_zero, inner_zero_left, norm_zero]
    simp
  · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    have h := inner_le_trace_add_of_norm_eq_one T hι hnorm
    rw [map_smul, real_inner_smul_left, real_inner_smul_right] at h
    have h2 := mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
    have e2 : ‖x‖⁻¹ * (‖x‖⁻¹ * ⟪x, T x⟫) * ‖x‖ ^ 2 = ⟪x, T x⟫ := by
      field_simp
    rwa [e2] at h2

end Operator

/-! ### Matrices -/

section MatrixForm

variable {n : ℕ}

/-- **The spread form for any matrix and any orthonormal pair.** If
`-ι · xᵀ x ≤ xᵀ S x ≤ μ · xᵀ x` for all `x`, then `|eᵀ S f + fᵀ S e| ≤ μ + ι` for orthonormal
`e`, `f`. -/
theorem spread_law (S : Matrix (Fin n) (Fin n) ℝ) {μ ι : ℝ}
    (hlo : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x))
    (hhi : ∀ x : Fin n → ℝ, x ⬝ᵥ (S *ᵥ x) ≤ μ * (x ⬝ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    |e ⬝ᵥ (S *ᵥ f) + f ⬝ᵥ (S *ᵥ e)| ≤ μ + ι := by
  have h := abs_inner_add_inner_le_spread _ (le_inner_opE_of_le_dotProduct S hlo)
    (inner_opE_le_of_dotProduct_le S hhi) (norm_toLp_eq_one_of_dotProduct_self he)
    (norm_toLp_eq_one_of_dotProduct_self hf) ((inner_eq_dotProduct _ _).trans hef)
  rwa [ContinuousLinearMap.coe_coe, inner_opE_eq_dotProduct, inner_opE_eq_dotProduct] at h

/-- **The spread form** (the bound of Mirsky on the spread of a symmetric matrix, in the form of
`thm:triple`). For a real symmetric matrix `S`, reals `μ`, `ι` with
`-ι · xᵀ x ≤ xᵀ S x ≤ μ · xᵀ x` for all `x` (as `μ = λ_max (S)`, `ι = -λ_min (S)`) and
orthonormal vectors `e`, `f`: `2 |eᵀ S f| ≤ μ + ι`, that is
`λ_max (S) - λ_min (S) ≥ 2 |eᵀ S f|`. -/
theorem spread_law_symm (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {μ ι : ℝ}
    (hlo : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x))
    (hhi : ∀ x : Fin n → ℝ, x ⬝ᵥ (S *ᵥ x) ≤ μ * (x ⬝ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 * |e ⬝ᵥ (S *ᵥ f)| ≤ μ + ι := by
  have h := two_mul_abs_inner_le_spread _ (isSymmetric_opE hS)
    (le_inner_opE_of_le_dotProduct S hlo) (inner_opE_le_of_dotProduct_le S hhi)
    (norm_toLp_eq_one_of_dotProduct_self he) (norm_toLp_eq_one_of_dotProduct_self hf)
    ((inner_eq_dotProduct _ _).trans hef)
  rwa [ContinuousLinearMap.coe_coe, inner_opE_eq_dotProduct] at h

/-- **The local form for any matrix and any orthonormal pair.** If `-ι · xᵀ x ≤ xᵀ S x` for all
`x`, then `|eᵀ S f + fᵀ S e| ≤ eᵀ S e + fᵀ S f + 2 ι` for orthonormal `e`, `f`. -/
theorem spread_law_local (S : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hlo : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    |e ⬝ᵥ (S *ᵥ f) + f ⬝ᵥ (S *ᵥ e)| ≤ e ⬝ᵥ (S *ᵥ e) + f ⬝ᵥ (S *ᵥ f) + 2 * ι := by
  have h := abs_inner_add_inner_le_local _ (le_inner_opE_of_le_dotProduct S hlo)
    (norm_toLp_eq_one_of_dotProduct_self he) (norm_toLp_eq_one_of_dotProduct_self hf)
    ((inner_eq_dotProduct _ _).trans hef)
  simp only [ContinuousLinearMap.coe_coe, inner_opE_eq_dotProduct] at h
  exact h

/-- **The local form.** For a real symmetric matrix `S`, a real `ι` with `-ι · xᵀ x ≤ xᵀ S x` for
all `x` (as `ι = -λ_min (S)`) and orthonormal vectors `e`, `f`:
`2 |eᵀ S f| ≤ eᵀ S e + fᵀ S f + 2 ι`. Only the two vectors enter. -/
theorem spread_law_local_symm (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {ι : ℝ}
    (hlo : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 * |e ⬝ᵥ (S *ᵥ f)| ≤ e ⬝ᵥ (S *ᵥ e) + f ⬝ᵥ (S *ᵥ f) + 2 * ι := by
  have h := two_mul_abs_inner_le_local _ (isSymmetric_opE hS)
    (le_inner_opE_of_le_dotProduct S hlo) (norm_toLp_eq_one_of_dotProduct_self he)
    (norm_toLp_eq_one_of_dotProduct_self hf) ((inner_eq_dotProduct _ _).trans hef)
  simp only [ContinuousLinearMap.coe_coe, inner_opE_eq_dotProduct] at h
  exact h

/-- **The upper bound that the trace gives.** If `-ι · xᵀ x ≤ xᵀ S x` for all `x`, then
`xᵀ S x ≤ (tr S + (n - 1) ι) · xᵀ x` for all `x`: with a lower bound `-ι` of the form of an
`n × n` matrix, `μ = tr S + (n - 1) ι` is an upper bound (`λ_max ≤ tr S - (n - 1) λ_min`). -/
theorem quadForm_le_trace_add (S : Matrix (Fin n) (Fin n) ℝ) {ι : ℝ}
    (hι : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) (x : Fin n → ℝ) :
    x ⬝ᵥ (S *ᵥ x) ≤ (S.trace + ((n : ℝ) - 1) * ι) * (x ⬝ᵥ x) := by
  have h := inner_le_trace_add _ (le_inner_opE_of_le_dotProduct S hι) (WithLp.toLp 2 x)
  rw [trace_opE, finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe,
    inner_opE_eq_dotProduct, ← real_inner_self_eq_norm_sq, inner_eq_dotProduct] at h
  exact h

end MatrixForm

/-! ### A co-simulation, one-step form -/

open OneStep

namespace HeldScheme

variable {n : ℕ} {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

section Legs

variable (S)

/-- **The half-step term through a single common partner, in entries.** Let `p` be a state of `i`
and `k ≠ i` the only subsystem through which `p` and `q` are joined (`A p r * A r q = 0` unless
`r` is a state of `k`). Then `(A_ς A) p q = ς_{ik} (A mask_k A) p q`. -/
theorem signedCoupling_mul_apply_leg {A : Matrix (Fin n) (Fin n) ℝ} {i k : κ} (hki : k ≠ i)
    {p q : Fin n} (hp : S.sub p = i) (hpq : ∀ r, S.sub r ≠ k → A p r * A r q = 0) :
    (S.signedCoupling A * A) p q = S.sg i k * (A * S.mask k * A) p q := by
  rw [S.signedCoupling_mul_apply, S.mul_mask_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hp]
  by_cases hr : S.sub r = k
  · have hri : S.sub r ≠ i := by rw [hr]; exact hki
    rw [ite_eq_right hri, ite_eq_left hr, hr]
    ring
  · have z : S.sg i (S.sub r) * A p r * A r q = 0 := by rw [mul_assoc, hpq r hr, mul_zero]
    rw [z, ite_self, ite_eq_right hr, mul_zero]

/-- **The half-step term through a single common partner, for the block.** If `k ≠ i` is the only
subsystem through which `i` and `j` are joined, then for `x` supported on `i` and `y` on `j`:
`⟪x, A_ς A y⟫ = ς_{ik} ⟪x, A mask_k A y⟫`, that is `[A_ς A]_{ij} = ς_{ik} A_{ik} A_{kj}`. -/
theorem inner_signedCoupling_mul_leg {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} (hki : k ≠ i)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ = S.sg i k * ⟪x, opE (A * S.mask k * A) y⟫ := by
  rw [← inner_opE_smul]
  refine inner_opE_congr hx hy fun p q hp hq => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact S.signedCoupling_mul_apply_leg hki hp fun r => hpq p q r hp hq

/-- **The symmetric combination of the half-step term through a single common partner.** If `k`,
different from `i` and `j`, is the only subsystem through which `i` and `j` are joined, the link
`i`-`k` has the kind `ε₁` and the link `k`-`j` the kind `ε₂`, then for `x` supported on `i` and
`y` on `j`: `⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫ = (ς_{ik} + ε₁ ε₂ ς_{jk}) ⟪x, A mask_k A y⟫`. -/
theorem inner_signedCoupling_mul_leg_sym {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ}
    (hki : k ≠ i) (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A q r * A r p = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ + ⟪y, opE (S.signedCoupling A * A) x⟫ =
      (S.sg i k + ε₁ * ε₂ * S.sg j k) * ⟪x, opE (A * S.mask k * A) y⟫ := by
  rw [S.inner_leg_rule hki hkj h₁ h₂ hpq hqp hx hy, S.inner_signedCoupling_mul_leg hki hpq hx hy]
  linear_combination
    (ε₁ * ε₂ * S.sg j k * ⟪x, opE (A * S.mask k * A) y⟫) * S.sg_mul_self i k

end Legs

/-- If `|u - w| ≤ r` and `|u| ≤ m`, then `|w| - r ≤ m`. -/
theorem abs_sub_le_of_abs_sub_le {u w r m : ℝ} (h1 : |u - w| ≤ r) (h2 : |u| ≤ m) :
    |w| - r ≤ m := by
  have h3 := abs_sub_abs_le_abs_sub w u
  rw [abs_sub_comm] at h3
  linarith

section Forced

variable {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- **The symmetric combination of the one-step error between two subsystems that are not
partners** (one-step form of `eq:parts`, numerical dissipation; no symmetry of the coupling is
assumed). For a consistent scheme, subsystems `i ≠ j` that are not partners, `x` supported on `i`
and `y` on `j`:
`|⟪x, (X - U) y⟫ + ⟪y, (X - U) x⟫ - ½H² (⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫)| ≤ 2 C₃ H³ ‖x‖ ‖y‖`,
`C₃ = reactionC a b c ‖A‖ H`: `Consistent.half_step_forced` in the two directions. -/
theorem Consistent.half_step_forced_sym (h : S.Consistent A U H a b c) {i j : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) :
    |⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫ -
        H ^ 2 / 2 * (⟪x, opE (S.signedCoupling A * A) y⟫ +
          ⟪y, opE (S.signedCoupling A * A) x⟫)| ≤
      2 * reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖y‖) := by
  have h1 := abs_le.1 (h.half_step_forced hij hnp hx hy)
  have h2 := abs_le.1 (h.half_step_forced hij.symm hnp' hy hx)
  rw [mul_comm ‖y‖ ‖x‖] at h2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The symmetric combination of the half-step term, with the factor `½H²` outside the modulus,
against any bound `B` of the symmetric combination of the one-step error, for unit vectors. -/
theorem Consistent.forced_sym_le (h : S.Consistent A U H a b c) {i j : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {B : ℝ} (hB : |⟪x, opE (S.X - U) y⟫ + ⟪y, opE (S.X - U) x⟫| ≤ B) :
    H ^ 2 / 2 * |⟪x, opE (S.signedCoupling A * A) y⟫ + ⟪y, opE (S.signedCoupling A * A) x⟫| -
        2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤ B := by
  have h1 := h.half_step_forced_sym hij hnp hnp' hx hy
  rw [hx1, hy1, mul_one, mul_one] at h1
  have h2 := abs_sub_le_of_abs_sub_le h1 hB
  rwa [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ H ^ 2 / 2)] at h2

/-- **The spread form for a co-simulation, one-step form** (one-step counterpart of `cor:amount`
with the spread in place of `ν + n ι`). For a consistent scheme, subsystems `i ≠ j` that are not
partners, unit vectors `x` supported on `i` and `y` on `j`, and reals `μ`, `ι` with
`-ι ‖v‖² ≤ ⟪v, (X - U) v⟫ ≤ μ ‖v‖²` for all `v`:
`½H² |⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫| - 2 C₃ H³ ≤ μ + ι`, `C₃ = reactionC a b c ‖A‖ H`.
No symmetry of the coupling is assumed. This is a statement about the one-step error `X - U` at
the given macro step, not about the modified system. -/
theorem Consistent.spread_forced (h : S.Consistent A U H a b c) {i j : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (S.X - U) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE (S.X - U) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H ^ 2 / 2 * |⟪x, opE (S.signedCoupling A * A) y⟫ + ⟪y, opE (S.signedCoupling A * A) x⟫| -
        2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤ μ + ι :=
  h.forced_sym_le hij hnp hnp' hx hy hx1 hy1
    (abs_inner_add_inner_le_spread
      (opE (S.X - U) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) hlo hhi hx1 hy1
      (inner_eq_zero_of_support hij hx hy))

/-- **The local form for a co-simulation, one-step form.** For a consistent scheme, subsystems
`i ≠ j` that are not partners, unit vectors `x` supported on `i` and `y` on `j`, and a real `ι`
with `-ι ‖v‖² ≤ ⟪v, (X - U) v⟫` for all `v`:
`½H² |⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫| - 2 C₃ H³ ≤ ⟪x, (X - U) x⟫ + ⟪y, (X - U) y⟫ + 2 ι`.
This is a statement about the one-step error `X - U`, not about the modified system. -/
theorem Consistent.spread_forced_local (h : S.Consistent A U H a b c) {i j : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (S.X - U) v⟫) :
    H ^ 2 / 2 * |⟪x, opE (S.signedCoupling A * A) y⟫ + ⟪y, opE (S.signedCoupling A * A) x⟫| -
        2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤
      ⟪x, opE (S.X - U) x⟫ + ⟪y, opE (S.X - U) y⟫ + 2 * ι :=
  h.forced_sym_le hij hnp hnp' hx hy hx1 hy1
    (abs_inner_add_inner_le_local
      (opE (S.X - U) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) hlo hx1 hy1
      (inner_eq_zero_of_support hij hx hy))

/-- **The spread form through a single common partner with links of two kinds, one-step form.**
In the setting of `Consistent.spread_forced`, let `k`, different from `i` and `j`, be the only
subsystem through which `i` and `j` are joined, the link `i`-`k` of kind `ε₁` and the link `k`-`j`
of kind `ε₂` (`-1` conservative, `1` dissipative). Then
`½H² |(ς_{ik} + ε₁ ε₂ ς_{jk}) ⟪x, A mask_k A y⟫| - 2 C₃ H³ ≤ μ + ι`,
with `⟪x, A mask_k A y⟫ = xᵀ A_{ik} A_{kj} y`. -/
theorem Consistent.spread_forced_leg (h : S.Consistent A U H a b c) {i j k : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {ε₁ ε₂ : ℝ} (hki : k ≠ i) (hkj : k ≠ j)
    (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A q r * A r p = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (S.X - U) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE (S.X - U) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H ^ 2 / 2 * |(S.sg i k + ε₁ * ε₂ * S.sg j k) * ⟪x, opE (A * S.mask k * A) y⟫| -
        2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤ μ + ι := by
  have h1 := h.spread_forced hij hnp hnp' hx hy hx1 hy1 hlo hhi
  rwa [S.inner_signedCoupling_mul_leg_sym hki hkj h₁ h₂ hpq hqp hx hy] at h1

/-- **The spread form through a single common partner when the forced block is symmetric,
one-step form.** In the setting of `Consistent.spread_forced_leg`, if the factor of the leg rule
is one, `ε₁ ε₂ ς_{jk} ς_{ik} = 1` (two links of the same kind and `k` not between `i` and `j`, or
links of different kinds and `k` between them), then
`H² |⟪x, A mask_k A y⟫| - 2 C₃ H³ ≤ μ + ι`: the macro step squared times `|xᵀ A_{ik} A_{kj} y|`.
This is a statement about the one-step error `X - U`, not about the modified system. -/
theorem Consistent.spread_forced_leg_sym (h : S.Consistent A U H a b c) {i j k : κ}
    (hij : i ≠ j) (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {ε₁ ε₂ : ℝ} (hki : k ≠ i)
    (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hsym : ε₁ * ε₂ * (S.sg j k * S.sg i k) = 1)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A q r * A r p = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (S.X - U) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE (S.X - U) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H ^ 2 * |⟪x, opE (A * S.mask k * A) y⟫| - 2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤
      μ + ι := by
  have h1 := h.spread_forced_leg hij hnp hnp' hki hkj h₁ h₂ hpq hqp hx hy hx1 hy1 hlo hhi
  have e : S.sg i k + ε₁ * ε₂ * S.sg j k = 2 * S.sg i k := by
    linear_combination S.sg i k * hsym - ε₁ * ε₂ * S.sg j k * S.sg_mul_self i k
  rw [e, abs_mul, abs_mul, abs_two, S.abs_sg i k] at h1
  linarith

/-- **The spread form for power-conserving coupling and a single common partner that does not run
between the two subsystems, one-step form** (one-step counterpart of the last statement of
`cor:amount`). For a consistent scheme with power-conserving coupling (`A q p = -A p q` between
different subsystems), subsystems `i ≠ j` that are not partners and are joined only through
`k ≠ i, j` (`A p r * A r q = 0` unless `r` is a state of `k`), with `ς_{ik} = ς_{jk}` (`k` runs
before both or before neither), unit vectors `x` supported on `i` and `y` on `j`, and reals `μ`,
`ι` with `-ι ‖v‖² ≤ ⟪v, (X - U) v⟫ ≤ μ ‖v‖²` for all `v`:
`H² |⟪x, A mask_k A y⟫| - 2 C₃ H³ ≤ μ + ι`, `⟪x, A mask_k A y⟫ = xᵀ A_{ik} A_{kj} y`,
`C₃ = reactionC a b c ‖A‖ H`. This is a statement about the one-step error `X - U`, not about the
modified system. -/
theorem Consistent.spread_forced_conservative (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {i j k : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) (hki : k ≠ i) (hkj : k ≠ j)
    (hs : S.sg i k = S.sg j k)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (S.X - U) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE (S.X - U) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H ^ 2 * |⟪x, opE (A * S.mask k * A) y⟫| - 2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤
      μ + ι := by
  have hkind := forall_linkKind_neg_one_iff.2 hskew
  have hqp : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A q r * A r p = 0 := by
    intro p q r hp hq hr
    by_cases hri : S.sub r = i
    · have hqr : S.sub q ≠ S.sub r := by rw [hq, hri]; exact hij.symm
      have hnqr : ¬ S.partner (S.sub q) (S.sub r) := by rw [hq, hri]; exact hnp'
      rw [h.hA q r hqr hnqr, zero_mul]
    · by_cases hrj : S.sub r = j
      · have hrp : S.sub r ≠ S.sub p := by rw [hrj, hp]; exact hij.symm
        have hnrp : ¬ S.partner (S.sub r) (S.sub p) := by rw [hrj, hp]; exact hnp'
        rw [h.hA r p hrp hnrp, mul_zero]
      · have hrq : S.sub r ≠ S.sub q := by rw [hq]; exact hrj
        have hpr : S.sub p ≠ S.sub r := by rw [hp]; exact fun e => hri e.symm
        rw [hskew r q hrq, hskew p r hpr]
        linear_combination hpq p q r hp hq hr
  have hsym : (-1 : ℝ) * (-1) * (S.sg j k * S.sg i k) = 1 := by
    rw [hs]
    linear_combination S.sg_mul_self j k
  exact h.spread_forced_leg_sym hij hnp hnp' hki hkj (hkind i k hki.symm) (hkind k j hkj) hsym
    hpq hqp hx hy hx1 hy1 hlo hhi

/-- Between different subsystems that are not partners the block of `A_ς A` is the block of
`A ς_s A`: for `x` supported on `s` and `y` on `t`, `⟪x, A_ς A y⟫ = ⟪x, A ς_s A y⟫` (the block
`A_{ss} A_{st}` by which the two differ vanishes). -/
theorem Consistent.inner_signedCoupling_mul_eq_sgn (h : S.Consistent A U H a b c) {s t : κ}
    (hst : s ≠ t) (hnp : ¬ S.partner s t) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hy : ∀ q, S.sub q ≠ t → y q = 0) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ = ⟪x, opE (A * S.sgn s * A) y⟫ := by
  refine inner_opE_congr hx hy fun p q hp hq => ?_
  obtain ⟨hne, hnp', -⟩ := S.sub_ne_of_eq hst hnp hp hq
  rw [S.signedCoupling_mul_apply_eq_sgn h.hA hne hnp', hp]

/-- **The symmetric combination of the half-step term for power-conserving coupling.** For a
consistent scheme with `A q p = -A p q` between different subsystems, subsystems `i ≠ j` that are
not partners, `x` supported on `i` and `y` on `j`:
`⟪x, A_ς A y⟫ + ⟪y, A_ς A x⟫ = ⟪x, A (ς_i + ς_j) A y⟫`, the sum
`Σ_k (ς_{ik} + ς_{jk}) xᵀ A_{ik} A_{kj} y` of `eq:parts`. -/
theorem Consistent.inner_signedCoupling_mul_sym_skew (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {i j : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ + ⟪y, opE (S.signedCoupling A * A) x⟫ =
      ⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫ := by
  rw [h.inner_signedCoupling_mul_eq_sgn hij hnp hx hy,
    h.inner_signedCoupling_mul_eq_sgn hij.symm hnp' hy hx,
    h.inner_sgn_swap hskew hij hnp hnp' j hx hy, Matrix.mul_add, Matrix.add_mul, inner_opE_add]

/-- **The spread form for power-conserving coupling, one-step form** (one-step counterpart of
`eq:amount` with the spread in place of `ν + n ι`; any number of common partners). For a
consistent scheme with `A q p = -A p q` between different subsystems, subsystems `i ≠ j` that are
not partners, unit vectors `x` supported on `i` and `y` on `j`, and reals `μ`, `ι` with
`-ι ‖v‖² ≤ ⟪v, (X - U) v⟫ ≤ μ ‖v‖²` for all `v`:
`½H² |⟪x, A (ς_i + ς_j) A y⟫| - 2 C₃ H³ ≤ μ + ι`, where
`⟪x, A (ς_i + ς_j) A y⟫ = Σ_k (ς_{ik} + ς_{jk}) xᵀ A_{ik} A_{kj} y`. This is a statement about the
one-step error `X - U`, not about the modified system. -/
theorem Consistent.spread_forced_skew (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {i j : κ} (hij : i ≠ j)
    (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (S.X - U) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE (S.X - U) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H ^ 2 / 2 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| -
        2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤ μ + ι := by
  have h1 := h.spread_forced hij hnp hnp' hx hy hx1 hy1 hlo hhi
  rwa [h.inner_signedCoupling_mul_sym_skew hskew hij hnp hnp' hx hy] at h1

/-- **The spread form in a Jacobi scheme with power-conserving coupling, one-step form** (one-step
counterpart of the second statement of `cor:amount`). If all subsystems run at the same stage,
then in the setting of `Consistent.spread_forced_skew`:
`H² |⟪x, A² y⟫| - 2 C₃ H³ ≤ μ + ι`, with `⟪x, A² y⟫ = xᵀ [A²]_{ij} y`. This is a statement about
the one-step error `X - U`, not about the modified system. -/
theorem Consistent.spread_forced_jacobi (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hJ : ∀ k k' : κ, S.stage k = S.stage k')
    {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j) (hnp' : ¬ S.partner j i)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) {μ ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (S.X - U) v⟫)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE (S.X - U) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H ^ 2 * |⟪x, opE (A * A) y⟫| - 2 * reactionC a b c ‖opE A‖ H * H ^ 3 ≤ μ + ι := by
  have h1 := h.spread_forced_skew hskew hij hnp hnp' hx hy hx1 hy1 hlo hhi
  rw [mul_sgn_add_mul_of_jacobi hJ, inner_opE_smul, abs_mul, abs_neg, abs_two] at h1
  linarith

end Forced

end HeldScheme

end CoSimFoundations
