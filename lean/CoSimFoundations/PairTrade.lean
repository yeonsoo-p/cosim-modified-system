/-
The trade between injection and damping for two orthonormal states (the paper, Section "The
trade between injection and damping", Theorem `thm:triple`).

**Statement.** `S` a real symmetric matrix (or a self-adjoint linear map on a real inner product
space of any dimension), `ι` and `μ` reals with `-ι |x|² ≤ ⟨x, S x⟩ ≤ μ |x|²` for all `x` (as
`ι = -λ_min`, `μ = λ_max`), `e`, `f` orthonormal, `c = ⟨e, S f⟩` and
`d = ½ (⟨e, S e⟩ + ⟨f, S f⟩)`. Then
  `ι ≥ |c| - d`   and   `μ ≥ |c| + d`,
and their sum is the spread form `μ + ι ≥ 2 |c|`. The first inequality uses the lower bound
alone, the second the upper bound alone.

**Proof.** `e + f` and `e - f` have squared length `2`, and
`⟨e ± f, S (e ± f)⟩ = 2 d ± 2 c`; the lower bound on both gives `-2 ι ≤ 2 d - 2 |c|`, the upper
bound on both `2 d + 2 |c| ≤ 2 μ`.

**Forms.**
* `abs_inner_add_inner_add_le_mu`: any linear map, `|⟨e, T f⟩ + ⟨f, T e⟩| + ⟨e, T e⟩ + ⟨f, T f⟩
  ≤ 2 μ` (the companion of `abs_inner_add_inner_le_local` of `SpreadLaw`).
* `pair_trade_iota`, `pair_trade_mu`, `pair_trade_spread`: self-adjoint linear maps.
* `pair_trade_iota_matrix`, `pair_trade_mu_matrix`, `pair_trade_spread_matrix`: symmetric
  matrices and dot products, the form of `spread_law_symm`.
* `pair_trade_iota_opE`, `pair_trade_mu_opE`: operators of symmetric matrices on Euclidean
  space, the form of `AmountLead`.
* `HeldScheme.pair_trade_iota_blocks`, `HeldScheme.pair_trade_mu_blocks`: unit vectors supported
  on two different subsystems (they are orthogonal).
* `HeldScheme.Consistent.amount_pair_iota`, `HeldScheme.Consistent.amount_pair_mu`: for the
  numerical dissipation `Δ_R` of a consistent scheme with power-conserving coupling and two
  subsystems `i ≠ j` that are not partners, unit `x` on `i` and `y` on `j`,
  `d = ½ (⟨x, Δ_R x⟩ + ⟨y, Δ_R y⟩)`:
    `ι ≥ (H/4) |⟨x, A (ς_i + ς_j) A y⟩| - ½ K H² - d`,
    `μ ≥ (H/4) |⟨x, A (ς_i + ς_j) A y⟩| - ½ K H² + d`,   `K = amountC a b c ‖A‖`.
-/
import CoSimFoundations.AmountLead

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

/-! ### Linear maps on a real inner product space -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The upper bound on an orthonormal pair, for any linear map.** If `⟪x, T x⟫ ≤ μ ‖x‖²` for
all `x`, then `|⟪e, T f⟫ + ⟪f, T e⟫| + ⟪e, T e⟫ + ⟪f, T f⟫ ≤ 2 μ` for orthonormal `e`, `f`. Only
the upper bound is used, on `e + f` and on `e - f`. -/
theorem abs_inner_add_inner_add_le_mu (T : E →ₗ[ℝ] E) {μ : ℝ}
    (hhi : ∀ x : E, ⟪x, T x⟫ ≤ μ * ‖x‖ ^ 2) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) :
    |⟪e, T f⟫ + ⟪f, T e⟫| + ⟪e, T e⟫ + ⟪f, T f⟫ ≤ 2 * μ := by
  have hp : ‖e + f‖ ^ 2 = 2 := by rw [norm_add_sq_real, he, hf, hef]; norm_num
  have hm : ‖e - f‖ ^ 2 = 2 := by rw [norm_sub_sq_real, he, hf, hef]; norm_num
  have up := hhi (e + f)
  have um := hhi (e - f)
  rw [hp, map_add, inner_add_left, inner_add_right, inner_add_right] at up
  rw [hm, map_sub, inner_sub_left, inner_sub_right, inner_sub_right] at um
  have h : |⟪e, T f⟫ + ⟪f, T e⟫| ≤ 2 * μ - ⟪e, T e⟫ - ⟪f, T f⟫ :=
    abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- **The trade for two orthonormal states, injection.** If `T` is self-adjoint and
`-ι ‖x‖² ≤ ⟪x, T x⟫` for all `x`, then for orthonormal `e`, `f`:
`|c| - d ≤ ι` with `c = ⟪e, T f⟫` and `d = ½ (⟪e, T e⟫ + ⟪f, T f⟫)`. -/
theorem pair_trade_iota (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {ι : ℝ}
    (hlo : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) :
    |⟪e, T f⟫| - (⟪e, T e⟫ + ⟪f, T f⟫) / 2 ≤ ι := by
  have h := two_mul_abs_inner_le_local T hT hlo he hf hef
  linarith

/-- **The trade for two orthonormal states, damping.** If `T` is self-adjoint and
`⟪x, T x⟫ ≤ μ ‖x‖²` for all `x`, then for orthonormal `e`, `f`:
`|c| + d ≤ μ` with `c = ⟪e, T f⟫` and `d = ½ (⟪e, T e⟫ + ⟪f, T f⟫)`. -/
theorem pair_trade_mu (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {μ : ℝ}
    (hhi : ∀ x : E, ⟪x, T x⟫ ≤ μ * ‖x‖ ^ 2) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) :
    |⟪e, T f⟫| + (⟪e, T e⟫ + ⟪f, T f⟫) / 2 ≤ μ := by
  have h := abs_inner_add_inner_add_le_mu T hhi he hf hef
  rw [inner_apply_comm_of_isSymmetric hT e f, ← two_mul, abs_mul, abs_two] at h
  linarith

/-- **The spread form from the two trades:** `2 |⟪e, T f⟫| ≤ μ + ι`, the sum of
`pair_trade_iota` and `pair_trade_mu`. -/
theorem pair_trade_spread (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {μ ι : ℝ}
    (hlo : ∀ x : E, -ι * ‖x‖ ^ 2 ≤ ⟪x, T x⟫) (hhi : ∀ x : E, ⟪x, T x⟫ ≤ μ * ‖x‖ ^ 2) {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    2 * |⟪e, T f⟫| ≤ μ + ι := by
  have h1 := pair_trade_iota T hT hlo he hf hef
  have h2 := pair_trade_mu T hT hhi he hf hef
  linarith

end Operator

variable {n : ℕ}

/-! ### Symmetric matrices and dot products -/

/-- **The trade for two orthonormal states, injection** (matrices). For a real symmetric matrix
`S` with `-ι · xᵀ x ≤ xᵀ S x` for all `x` and orthonormal `e`, `f`:
`|eᵀ S f| - ½ (eᵀ S e + fᵀ S f) ≤ ι`. -/
theorem pair_trade_iota_matrix (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {ι : ℝ}
    (hlo : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    |e ⬝ᵥ (S *ᵥ f)| - (e ⬝ᵥ (S *ᵥ e) + f ⬝ᵥ (S *ᵥ f)) / 2 ≤ ι := by
  have h := spread_law_local_symm S hS hlo he hf hef
  linarith

/-- **The trade for two orthonormal states, damping** (matrices). For a real symmetric matrix
`S` with `xᵀ S x ≤ μ · xᵀ x` for all `x` and orthonormal `e`, `f`:
`|eᵀ S f| + ½ (eᵀ S e + fᵀ S f) ≤ μ`. -/
theorem pair_trade_mu_matrix (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {μ : ℝ}
    (hhi : ∀ x : Fin n → ℝ, x ⬝ᵥ (S *ᵥ x) ≤ μ * (x ⬝ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    |e ⬝ᵥ (S *ᵥ f)| + (e ⬝ᵥ (S *ᵥ e) + f ⬝ᵥ (S *ᵥ f)) / 2 ≤ μ := by
  have hfe : f ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hef
  have up := hhi (e + f)
  have um := hhi (e - f)
  simp only [mulVec_add, add_dotProduct, dotProduct_add, he, hf, hef, hfe] at up
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub, he, hf, hef, hfe] at um
  rw [dotProduct_mulVec_comm_of_isSymm hS e f] at up um
  have h : |e ⬝ᵥ (S *ᵥ f)| ≤ μ - (e ⬝ᵥ (S *ᵥ e) + f ⬝ᵥ (S *ᵥ f)) / 2 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- **The spread form from the two trades** (matrices): `2 |eᵀ S f| ≤ μ + ι`. -/
theorem pair_trade_spread_matrix (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) {μ ι : ℝ}
    (hlo : ∀ x : Fin n → ℝ, -ι * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x))
    (hhi : ∀ x : Fin n → ℝ, x ⬝ᵥ (S *ᵥ x) ≤ μ * (x ⬝ᵥ x)) {e f : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (hf : f ⬝ᵥ f = 1) (hef : e ⬝ᵥ f = 0) :
    2 * |e ⬝ᵥ (S *ᵥ f)| ≤ μ + ι := by
  have h1 := pair_trade_iota_matrix S hS hlo he hf hef
  have h2 := pair_trade_mu_matrix S hS hhi he hf hef
  linarith

/-! ### Operators of symmetric matrices -/

/-- **The trade for two orthonormal states, injection** (operators on Euclidean space). If `T`
is symmetric and `-ι ‖v‖² ≤ ⟪v, T v⟫` for all `v`, then for orthonormal `e`, `f`:
`|⟪e, T f⟫| - ½ (⟪e, T e⟫ + ⟪f, T f⟫) ≤ ι`. -/
theorem pair_trade_iota_opE {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE T v⟫)
    {e f : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    |⟪e, opE T f⟫| - (⟪e, opE T e⟫ + ⟪f, opE T f⟫) / 2 ≤ ι := by
  have h := abs_inner_add_inner_le_local
    ((opE T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) hlo he hf hef
  rw [ContinuousLinearMap.coe_coe, inner_opE_comm_of_isSymm hT e f, ← two_mul, abs_mul,
    abs_two] at h
  linarith

/-- **The trade for two orthonormal states, damping** (operators on Euclidean space). If `T` is
symmetric and `⟪v, T v⟫ ≤ μ ‖v‖²` for all `v`, then for orthonormal `e`, `f`:
`|⟪e, T f⟫| + ½ (⟪e, T e⟫ + ⟪f, T f⟫) ≤ μ`. -/
theorem pair_trade_mu_opE {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm) {μ : ℝ}
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE T v⟫ ≤ μ * ‖v‖ ^ 2)
    {e f : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    |⟪e, opE T f⟫| + (⟪e, opE T e⟫ + ⟪f, opE T f⟫) / 2 ≤ μ := by
  have h := abs_inner_add_inner_add_le_mu
    ((opE T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) hhi he hf hef
  rw [ContinuousLinearMap.coe_coe, inner_opE_comm_of_isSymm hT e f, ← two_mul, abs_mul,
    abs_two] at h
  linarith

namespace HeldScheme

variable {κ : Type*}

/-! ### Unit vectors of two subsystems -/

/-- **The trade on two subsystems, injection:** if `T` is symmetric and `-ι ‖v‖² ≤ ⟪v, T v⟫`
for all `v`, then for subsystems `i ≠ j`, a unit vector `x` supported on `i` and a unit vector
`y` supported on `j`: `|⟪x, T y⟫| - ½ (⟪x, T x⟫ + ⟪y, T y⟫) ≤ ι`. -/
theorem pair_trade_iota_blocks (S : HeldScheme n κ) {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsSymm) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), -ι * ‖v‖ ^ 2 ≤ ⟪v, opE T v⟫) {i j : κ} (hij : i ≠ j)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    |⟪x, opE T y⟫| - (⟪x, opE T x⟫ + ⟪y, opE T y⟫) / 2 ≤ ι :=
  pair_trade_iota_opE hT hlo hx1 hy1 (inner_eq_zero_of_support hij hx hy)

/-- **The trade on two subsystems, damping:** if `T` is symmetric and `⟪v, T v⟫ ≤ μ ‖v‖²` for
all `v`, then for subsystems `i ≠ j`, a unit vector `x` supported on `i` and a unit vector `y`
supported on `j`: `|⟪x, T y⟫| + ½ (⟪x, T x⟫ + ⟪y, T y⟫) ≤ μ`. -/
theorem pair_trade_mu_blocks (S : HeldScheme n κ) {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsSymm) {μ : ℝ}
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v, opE T v⟫ ≤ μ * ‖v‖ ^ 2) {i j : κ} (hij : i ≠ j)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    |⟪x, opE T y⟫| + (⟪x, opE T x⟫ + ⟪y, opE T y⟫) / 2 ≤ μ :=
  pair_trade_mu_opE hT hhi hx1 hy1 (inner_eq_zero_of_support hij hx hy)

/-! ### The numerical dissipation of a scheme -/

section Amount

variable {S : HeldScheme n κ} {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}

/-- **The injection that a consistent scheme cannot avoid, on two subsystems.** For a
consistent scheme with power-conserving coupling, `H > 0`, `b H ≤ 1/3`, `H ‖A‖ ≤ 1/4`,
subsystems `i ≠ j` that are not partners, unit vectors `x` supported on `i` and `y` on `j`,
`Δ_R = numDissipation A (modifiedSystem H S.X)` and `ι` with `-ι ‖v‖² ≤ ⟪v, Δ_R v⟫` for all `v`:
`(H/4) |⟪x, A (ς_i + ς_j) A y⟫| - ½ K H² - ½ (⟪x, Δ_R x⟫ + ⟪y, Δ_R y⟫) ≤ ι`,
`K = amountC a b c ‖A‖`. -/
theorem Consistent.amount_pair_iota (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {ι : ℝ}
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),
      -ι * ‖v‖ ^ 2 ≤ ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫) :
    H / 4 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 / 2 -
        (⟪x, opE (numDissipation A (modifiedSystem H S.X)) x⟫ +
          ⟪y, opE (numDissipation A (modifiedSystem H S.X)) y⟫) / 2 ≤ ι := by
  have h1 := h.amount_block hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1
  have h2 := S.pair_trade_iota_blocks (isSymm_numDissipation A _) hlo hij hx hy hx1 hy1
  linarith

/-- **The damping that a consistent scheme cannot avoid, on two subsystems.** In the setting of
`Consistent.amount_pair_iota`, with `μ` such that `⟪v, Δ_R v⟫ ≤ μ ‖v‖²` for all `v`:
`(H/4) |⟪x, A (ς_i + ς_j) A y⟫| - ½ K H² + ½ (⟪x, Δ_R x⟫ + ⟪y, Δ_R y⟫) ≤ μ`. -/
theorem Consistent.amount_pair_mu (h : S.Consistent A U H a b c)
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) (hH : 0 < H) (hbH : b * H ≤ 1 / 3)
    (hAH : H * ‖opE A‖ ≤ 1 / 4) {i j : κ} (hij : i ≠ j) (hnp : ¬ S.partner i j)
    (hnp' : ¬ S.partner j i) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ j → y q = 0) (hx1 : ‖x‖ = 1)
    (hy1 : ‖y‖ = 1) {μ : ℝ}
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, opE (numDissipation A (modifiedSystem H S.X)) v⟫ ≤ μ * ‖v‖ ^ 2) :
    H / 4 * |⟪x, opE (A * (S.sgn i + S.sgn j) * A) y⟫| - amountC a b c ‖opE A‖ * H ^ 2 / 2 +
        (⟪x, opE (numDissipation A (modifiedSystem H S.X)) x⟫ +
          ⟪y, opE (numDissipation A (modifiedSystem H S.X)) y⟫) / 2 ≤ μ := by
  have h1 := h.amount_block hskew hH hbH hAH hij hnp hnp' hx hy hx1 hy1
  have h2 := S.pair_trade_mu_blocks (isSymm_numDissipation A _) hhi hij hx hy hx1 hy1
  linarith

end Amount

end HeldScheme

end CoSimFoundations
