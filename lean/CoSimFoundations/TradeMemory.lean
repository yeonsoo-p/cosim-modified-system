/-
The trade between energy and damping with `l` held samples: the constants and the matrices (the
paper).

**The constants.** `γ_l^0 = adamsGamma l = ∫₀¹ binom(s + l - 1, l) ds` (old samples) and
`γ_l^1 = lateGamma l = ∫₀¹ binom(s + l - 2, l) ds` (the new sample and old ones);
`adamsKernel l s = binom(s + l - 1, l) = (1/l!) ∏_{r<l} (s + r)`.

* `lateGamma_eq_sub` (Pascal's rule): `γ_l^1 = γ_l^0 - γ_{l-1}^0` for `l ≥ 1`.
* `adamsGamma_pos`, `lateGamma_neg`: `γ_l^0 > 0` for every `l` and `γ_l^1 < 0` for `l ≥ 1`.
* `adamsGamma_lt_pred`, `half_adamsGamma_pred_lt`: `½ γ_{l-1}^0 < γ_l^0 < γ_{l-1}^0` (the second
  for `l ≥ 1`, the first for `l ≥ 2`), from `b_l(s) = b_{l-1}(s) (s + l - 1)/l` and
  `(l - 1)/l < (s + l - 1)/l < 1` on `(0, 1)`.
* `abs_lateGamma_lt`: `|γ_l^1| < γ_l^0` for `l ≥ 2`; `abs_lateGamma_one`: equality for `l = 1`.
* `kindGamma_trade_eq_zero_iff`: with `kindGamma l σ` the constant of the kind `σ` (`false` old,
  `true` new), for `l ≥ 1`: `(γ_l^a + (-1)^{l+1} γ_l^b)/2 = 0` exactly when `l` is even and
  `a = b`, or `l = 1` and `a ≠ b`; for odd `l ≥ 3` never (`kindGamma_trade_ne_zero_of_odd`). This
  is the entry `[sym D_l]_{ab} / p` between the end stores of a chain of scalar stores `l + 1`
  links apart (the entry itself, a sum over walks, is not formalised here).

**The matrices** (matrix level). `rowReach sub V` is the subspace of the matrices
whose rows of subsystem `i` (the coordinates `p` with `sub p = i`) vanish on the subspace `V i`
(the paper's `𝒵_l`, with `V i = 𝒱_i^0`). If every vector of `V i` vanishes on the coordinates of
`i` (`𝒱_i^0 ⊆ ker Π_i`), the identity is in the reach (`one_mem_rowReach`).

* **The entries that no scheme changes** (`inner_sym_add_of_mem_rowReach`): for `e` supported on
  subsystem `a` with `e ∈ V b`, and `e'` supported on `b` with `e' ∈ V a`,
  `⟪e, sym (D + Z) e'⟫ = ⟪e, sym D e'⟫` for every `Z` in the reach.
* **Lower bounds** (`abs_inner_sym_le_norm_of_mem_rowReach`,
  `two_mul_abs_inner_sym_le_spr_of_mem_rowReach`): for unit `e`, `e'` as above,
  `‖sym (D + Z)‖ ≥ |⟪e, sym D e'⟫|`, and for `a ≠ b`, `spr (sym (D + Z)) ≥ 2 |⟪e, sym D e'⟫|`.
* **The least value** (`exists_isLeast_sym_of_one_mem`, `exists_isLeast_rowReach`): over a
  subspace that contains the identity, `d = min_Z ‖sym (D + Z)‖` is attained and the least spread
  of `sym (D + Z)` is `2 d`, attained; `d ≥ |⟪e, sym D e'⟫|` (`abs_inner_sym_le_least_rowReach`).
* **Every point of the half-plane** (`exists_extremes_of_one_mem`, `exists_rowReach_extremes`):
  if two states lie in different subsystems, for all `a`, `b` with `a + b ≥ 2 d` there is `Z` in
  the reach with `λ_max (sym (D + Z)) = a` and `λ_min (sym (D + Z)) = -b`.

The passage from the matrices to the schemes (the modified system of a scheme with `l` held
samples) is in `TradeMemoryScheme`.
-/
import CoSimFoundations.MemoryLateConstants
import CoSimFoundations.LeastSpread

open Finset Matrix Metric
open scoped Nat RealInnerProductSpace

namespace CoSimFoundations

open OneStep

/-! ### The constants -/

section Constants

/-- The integrand of the constant of the old samples:
`b_l(s) = binom(s + l - 1, l) = (1/l!) ∏_{r<l} (s + r)`. -/
noncomputable def adamsKernel (l : ℕ) (s : ℝ) : ℝ := ((l ! : ℝ))⁻¹ * ∏ r ∈ range l, (s + r)

/-- The node product `∏_{r<l} (s + r)` is continuous in `s`. -/
theorem continuous_prod_range_add (l : ℕ) :
    Continuous fun s : ℝ => ∏ r ∈ range l, (s + (r : ℝ)) :=
  continuous_finsetProd _ fun _ _ => continuous_id.add continuous_const

/-- The node product is positive for `s > 0`. -/
theorem prod_range_add_pos (l : ℕ) {s : ℝ} (hs : 0 < s) : 0 < ∏ r ∈ range l, (s + (r : ℝ)) :=
  prod_pos fun r _ => add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg r)

/-- The kernel is integrable on `[0, 1]`. -/
theorem intervalIntegrable_adamsKernel (l : ℕ) :
    IntervalIntegrable (adamsKernel l) MeasureTheory.volume 0 1 :=
  (continuous_const.mul (continuous_prod_range_add l)).intervalIntegrable 0 1

/-- `γ_l^0 = ∫₀¹ b_l(s) ds`. -/
theorem adamsGamma_eq_integral_kernel (l : ℕ) :
    adamsGamma l = ∫ s in (0 : ℝ)..1, adamsKernel l s := by
  rw [adamsGamma_eq_integral, ← intervalIntegral.integral_const_mul]
  rfl

/-- **A combination of two consecutive constants as one integral:**
`c₁ γ_{m+1}^0 + c₂ γ_m^0 = (1/(m+1)!) ∫₀¹ (c₁ (s + m) + c₂ (m + 1)) ∏_{r<m} (s + r) ds`. -/
theorem mul_adamsGamma_succ_add (m : ℕ) (c₁ c₂ : ℝ) :
    c₁ * adamsGamma (m + 1) + c₂ * adamsGamma m =
      (((m + 1)! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1,
        (c₁ * (s + m) + c₂ * (m + 1)) * ∏ r ∈ range m, (s + (r : ℝ)) := by
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  symm
  calc (((m + 1)! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1,
        (c₁ * (s + m) + c₂ * (m + 1)) * ∏ r ∈ range m, (s + (r : ℝ))
      = ∫ s in (0 : ℝ)..1, (c₁ * adamsKernel (m + 1) s + c₂ * adamsKernel m s) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [adamsKernel]
        rw [prod_range_succ, Nat.factorial_succ]
        push_cast
        field_simp
    _ = c₁ * adamsGamma (m + 1) + c₂ * adamsGamma m := by
        rw [intervalIntegral.integral_add ((intervalIntegrable_adamsKernel _).const_mul _)
            ((intervalIntegrable_adamsKernel _).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          adamsGamma_eq_integral_kernel, adamsGamma_eq_integral_kernel]

/-- **Pascal's rule for the constants:** `γ_{m+1}^1 = γ_{m+1}^0 - γ_m^0`. -/
theorem lateGamma_succ (m : ℕ) : lateGamma (m + 1) = adamsGamma (m + 1) - adamsGamma m := by
  have h := mul_adamsGamma_succ_add m 1 (-1)
  rw [one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  rw [h, lateGamma_eq_integral (by omega), Nat.add_sub_cancel]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- **Pascal's rule for the constants**: `γ_l^1 = γ_l^0 - γ_{l-1}^0` for `l ≥ 1`. -/
theorem lateGamma_eq_sub {l : ℕ} (hl : 1 ≤ l) :
    lateGamma l = adamsGamma l - adamsGamma (l - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hl
  rw [lateGamma_succ, Nat.add_sub_cancel]

/-- **The constant of the old samples is positive:** `γ_l^0 > 0`. -/
theorem adamsGamma_pos (l : ℕ) : 0 < adamsGamma l := by
  rw [adamsGamma_eq_integral]
  exact mul_pos (by positivity) (intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_prod_range_add l).intervalIntegrable 0 1)
    (fun s hs => prod_range_add_pos l hs.1) zero_lt_one)

/-- A combination `c₁ γ_{m+1}^0 + c₂ γ_m^0` is positive if its integrand is positive on `(0, 1)`. -/
theorem mul_adamsGamma_succ_add_pos (m : ℕ) {c₁ c₂ : ℝ}
    (h : ∀ s : ℝ, 0 < s → s < 1 → 0 < c₁ * (s + m) + c₂ * (m + 1)) :
    0 < c₁ * adamsGamma (m + 1) + c₂ * adamsGamma m := by
  have hc : Continuous fun s : ℝ =>
      (c₁ * (s + m) + c₂ * (m + 1)) * ∏ r ∈ range m, (s + (r : ℝ)) := by
    have h1 : Continuous fun s : ℝ => c₁ * (s + m) + c₂ * (m + 1) := by fun_prop
    exact h1.mul (continuous_prod_range_add m)
  have hf : (0 : ℝ) < (((m + 1)! : ℝ))⁻¹ := by positivity
  rw [mul_adamsGamma_succ_add]
  exact mul_pos hf (intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable 0 1)
    (fun s hs => mul_pos (h s hs.1 hs.2) (prod_range_add_pos m hs.1)) zero_lt_one)

/-- **The constants decrease:** `γ_{m+1}^0 < γ_m^0`. -/
theorem adamsGamma_succ_lt (m : ℕ) : adamsGamma (m + 1) < adamsGamma m := by
  have h := mul_adamsGamma_succ_add_pos m (c₁ := -1) (c₂ := 1) fun s _ hs1 => by linarith
  linarith

/-- **Less than halving:** `γ_m^0 < 2 γ_{m+1}^0` for `m ≥ 1`. -/
theorem adamsGamma_lt_two_mul_succ {m : ℕ} (hm : 1 ≤ m) :
    adamsGamma m < 2 * adamsGamma (m + 1) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := mul_adamsGamma_succ_add_pos m (c₁ := 2) (c₂ := -1) fun s hs0 _ => by linarith
  linarith

/-- `γ_l^0 < γ_{l-1}^0` for `l ≥ 1`. -/
theorem adamsGamma_lt_pred {l : ℕ} (hl : 1 ≤ l) : adamsGamma l < adamsGamma (l - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hl
  rw [Nat.add_sub_cancel]
  exact adamsGamma_succ_lt m

/-- `½ γ_{l-1}^0 < γ_l^0` for `l ≥ 2`. -/
theorem half_adamsGamma_pred_lt {l : ℕ} (hl : 2 ≤ l) : adamsGamma (l - 1) / 2 < adamsGamma l := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ l)
  rw [Nat.add_sub_cancel]
  have := adamsGamma_lt_two_mul_succ (m := m) (by omega)
  linarith

/-- **The constant of the new sample is negative:** `γ_l^1 < 0` for `l ≥ 1`. -/
theorem lateGamma_neg {l : ℕ} (hl : 1 ≤ l) : lateGamma l < 0 := by
  rw [lateGamma_eq_sub hl]
  linarith [adamsGamma_lt_pred hl]

/-- **The new sample weighs less:** `|γ_l^1| < γ_l^0` for `l ≥ 2`. -/
theorem abs_lateGamma_lt {l : ℕ} (hl : 2 ≤ l) : |lateGamma l| < adamsGamma l := by
  rw [abs_of_neg (lateGamma_neg (by omega)), lateGamma_eq_sub (by omega)]
  linarith [half_adamsGamma_pred_lt hl]

/-- For one held sample the two constants have the same modulus: `|γ_1^1| = γ_1^0 = 1/2`. -/
theorem abs_lateGamma_one : |lateGamma 1| = adamsGamma 1 := by
  rw [lateGamma_one, adamsGamma_one]
  norm_num [abs_of_neg]

/-- `γ_l^σ`, the constant of the kind `σ` of the samples: `false` for old samples (`adamsGamma`),
`true` for the new sample and old ones (`lateGamma`). -/
noncomputable def kindGamma (l : ℕ) (σ : Bool) : ℝ :=
  if σ then lateGamma l else adamsGamma l

/-- The constant of old samples. -/
theorem kindGamma_false (l : ℕ) : kindGamma l false = adamsGamma l := rfl

/-- The constant of the new sample and old ones. -/
theorem kindGamma_true (l : ℕ) : kindGamma l true = lateGamma l := rfl

/-- **Which kinds spare the trade** (chains of scalar stores). For `l ≥ 1` and kinds `a`, `b`
of the samples at the two end stores: `(γ_l^a + (-1)^{l+1} γ_l^b)/2 = 0` exactly when `l` is even
and the kinds are equal, or `l = 1` and the kinds differ. -/
theorem kindGamma_trade_eq_zero_iff {l : ℕ} (hl : 1 ≤ l) (a b : Bool) :
    (kindGamma l a + (-1) ^ (l + 1) * kindGamma l b) / 2 = 0 ↔
      (Even l ∧ a = b) ∨ (l = 1 ∧ a ≠ b) := by
  have h0 := adamsGamma_pos l
  have h1 := lateGamma_neg hl
  rw [div_eq_zero_iff, or_iff_left (two_ne_zero (α := ℝ))]
  rcases Nat.even_or_odd l with he | ho
  · have hl1 : l ≠ 1 := by
      rintro rfl
      exact absurd he (by decide)
    have hr : (Even l ∧ a = b) ∨ (l = 1 ∧ a ≠ b) ↔ a = b := by
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · exact absurd h hl1
      · intro h
        exact Or.inl ⟨he, h⟩
    rw [(Even.add_one he).neg_one_pow, hr]
    cases a <;> cases b
    · exact iff_of_true (by rw [kindGamma_false]; ring) rfl
    · exact iff_of_false (by rw [kindGamma_false, kindGamma_true]; intro h; linarith)
        (by decide)
    · exact iff_of_false (by rw [kindGamma_false, kindGamma_true]; intro h; linarith)
        (by decide)
    · exact iff_of_true (by rw [kindGamma_true]; ring) rfl
  · rw [(Odd.add_one ho).neg_one_pow, one_mul]
    rcases eq_or_ne l 1 with rfl | hl1
    · cases a <;> cases b <;>
        norm_num [kindGamma_false, kindGamma_true, adamsGamma_one, lateGamma_one]
    · have h2 := abs_lateGamma_lt (by omega : 2 ≤ l)
      rw [abs_of_neg h1] at h2
      have hne : ¬ Even l := Nat.not_even_iff_odd.2 ho
      refine iff_of_false ?_ (by simp [hne, hl1])
      cases a <;> cases b
      · rw [kindGamma_false]; intro h; linarith
      · rw [kindGamma_false, kindGamma_true]; intro h; linarith
      · rw [kindGamma_false, kindGamma_true]; intro h; linarith
      · rw [kindGamma_true]; intro h; linarith

/-- **For odd `l ≥ 3` no choice of kinds spares the trade:** `(γ_l^a + γ_l^b)/2 ≠ 0`. -/
theorem kindGamma_trade_ne_zero_of_odd {l : ℕ} (hl : 3 ≤ l) (ho : Odd l) (a b : Bool) :
    (kindGamma l a + (-1) ^ (l + 1) * kindGamma l b) / 2 ≠ 0 := by
  rw [Ne, kindGamma_trade_eq_zero_iff (by omega)]
  rintro (⟨he, -⟩ | ⟨rfl, -⟩)
  · exact (Nat.not_even_iff_odd.2 ho) he
  · omega

end Constants

/-! ### The reach by rows -/

section Rows

variable {n : ℕ} {κ : Type*} {sub : Fin n → κ} {V : κ → Submodule ℝ (EuclideanSpace ℝ (Fin n))}

/-- **The reach of the rules with `l` held samples, by rows** (`𝒵_l`): the matrices
whose rows of subsystem `i` (the coordinates `p` with `sub p = i`) vanish on the subspace `V i`
(the paper's `𝒱_i^0`). -/
def rowReach (sub : Fin n → κ) (V : κ → Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {Z | ∀ p, ∀ v ∈ V (sub p), ∑ q, Z p q * v q = 0}
  add_mem' := by
    intro Z Z' hZ hZ' p v hv
    simp only [Matrix.add_apply, add_mul, sum_add_distrib, hZ p v hv, hZ' p v hv, add_zero]
  zero_mem' := by
    intro p v _
    simp
  smul_mem' := by
    intro c Z hZ p v hv
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, hZ p v hv, mul_zero]

/-- Membership in the reach by rows, with the operator. -/
theorem mem_rowReach {Z : Matrix (Fin n) (Fin n) ℝ} :
    Z ∈ rowReach sub V ↔ ∀ p, ∀ v ∈ V (sub p), opE Z v p = 0 := by
  simp only [opE_apply]
  rfl

/-- **The identity is in the reach** if every vector of `V i` vanishes on the coordinates of `i`
(`𝒱_i^0 ⊆ ker Π_i`). -/
theorem one_mem_rowReach (hV : ∀ i, ∀ v ∈ V i, ∀ p, sub p = i → v p = 0) :
    (1 : Matrix (Fin n) (Fin n) ℝ) ∈ rowReach sub V := by
  rw [mem_rowReach]
  intro p v hv
  rw [opE_one, one_apply_eq_self]
  exact hV _ v hv p rfl

/-- The mask of a subsystem (the diagonal projection onto its coordinates) is in the reach if
every vector of `V i` vanishes on the coordinates of `i`. -/
theorem mask_mem_rowReach [DecidableEq κ] (hV : ∀ i, ∀ v ∈ V i, ∀ p, sub p = i → v p = 0)
    (s : κ) : diagonal (fun p => if sub p = s then (1 : ℝ) else 0) ∈ rowReach sub V := by
  rw [mem_rowReach]
  intro p v hv
  rw [opE_diagonal_apply, hV _ v hv p rfl, mul_zero]

/-- A matrix element `⟪x, Z y⟫` with `x` supported on subsystem `a` and `y ∈ V a` vanishes for
every `Z` in the reach. -/
theorem inner_opE_eq_zero_of_mem_rowReach {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : Z ∈ rowReach sub V) {a : κ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, sub p ≠ a → x p = 0) (hy : y ∈ V a) : ⟪x, opE Z y⟫ = 0 := by
  rw [inner_eq_sum]
  refine sum_eq_zero fun p _ => ?_
  by_cases hp : sub p = a
  · rw [mem_rowReach.1 hZ p y (by rw [hp]; exact hy), mul_zero]
  · rw [hx p hp, zero_mul]

/-- **The entries that no scheme changes**. For `e` supported on subsystem `a`
with `e ∈ V b`, and `e'` supported on subsystem `b` with `e' ∈ V a`:
`⟪e, sym (D + Z) e'⟫ = ⟪e, sym D e'⟫` for every `Z` in the reach. -/
theorem inner_sym_add_of_mem_rowReach (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ rowReach sub V) {a b : κ}
    {e e' : EuclideanSpace ℝ (Fin n)} (he : ∀ p, sub p ≠ a → e p = 0) (heV : e ∈ V b)
    (he' : ∀ p, sub p ≠ b → e' p = 0) (he'V : e' ∈ V a) :
    ⟪e, opE (sym (D + Z)) e'⟫ = ⟪e, opE (sym D) e'⟫ := by
  rw [inner_sym, inner_sym, inner_opE_add, inner_opE_add,
    inner_opE_eq_zero_of_mem_rowReach hZ he he'V, inner_opE_eq_zero_of_mem_rowReach hZ he' heV,
    add_zero, add_zero]

/-- **The norm is at least a fixed entry:** for unit `e`, `e'` as in
`inner_sym_add_of_mem_rowReach`, `|⟪e, sym D e'⟫| ≤ ‖sym (D + Z)‖` for every `Z` in the reach. -/
theorem abs_inner_sym_le_norm_of_mem_rowReach (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ rowReach sub V) {a b : κ}
    {e e' : EuclideanSpace ℝ (Fin n)} (he : ∀ p, sub p ≠ a → e p = 0) (heV : e ∈ V b)
    (he' : ∀ p, sub p ≠ b → e' p = 0) (he'V : e' ∈ V a) (hn : ‖e‖ = 1) (hn' : ‖e'‖ = 1) :
    |⟪e, opE (sym D) e'⟫| ≤ ‖opE (sym (D + Z))‖ := by
  rw [← inner_sym_add_of_mem_rowReach D hZ he heV he' he'V]
  have h := abs_inner_opE_le (sym (D + Z)) e e'
  rwa [hn, hn', mul_one, mul_one] at h

/-- **The spread is at least twice a fixed entry** (with Lemma 5.2): for subsystems `a ≠ b`
and unit `e`, `e'` as in `inner_sym_add_of_mem_rowReach`,
`2 |⟪e, sym D e'⟫| ≤ spr (sym (D + Z))` for every `Z` in the reach. -/
theorem two_mul_abs_inner_sym_le_spr_of_mem_rowReach (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ rowReach sub V) {a b : κ} (hab : a ≠ b)
    {e e' : EuclideanSpace ℝ (Fin n)} (he : ∀ p, sub p ≠ a → e p = 0) (heV : e ∈ V b)
    (he' : ∀ p, sub p ≠ b → e' p = 0) (he'V : e' ∈ V a) (hn : ‖e‖ = 1) (hn' : ‖e'‖ = 1) :
    2 * |⟪e, opE (sym D) e'⟫| ≤ spr (sym (D + Z)) := by
  rw [← inner_sym_add_of_mem_rowReach D hZ he heV he' he'V]
  have h := two_mul_abs_inner_le_spread
    ((opE (sym (D + Z)) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (isSymmetric_opE (isSymm_sym _)) (μ := lamMax (sym (D + Z))) (ι := -lamMin (sym (D + Z)))
    (fun x => by rw [neg_neg, ContinuousLinearMap.coe_coe]; exact lamMin_le_inner _ x)
    (fun x => by rw [ContinuousLinearMap.coe_coe]; exact inner_le_lamMax _ x) hn hn'
    (inner_eq_zero_of_support hab he he')
  rw [ContinuousLinearMap.coe_coe] at h
  rw [spr]
  linarith

/-- **The least norm and the least spread of the symmetric part over a subspace that contains the
identity** (`d_l` is attained, and `min_Z spr (sym (D + Z)) = 2 d_l`, attained). -/
theorem exists_isLeast_sym_of_one_mem (D : Matrix (Fin n) (Fin n) ℝ)
    {𝒵 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} (h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ 𝒵) :
    ∃ d, IsLeast {r | ∃ Z ∈ 𝒵, r = ‖opE (sym (D + Z))‖} d ∧
      IsLeast {r | ∃ Z ∈ 𝒵, r = spr (sym (D + Z))} (2 * d) := by
  let 𝓡 := 𝒵.map symL
  have h1' : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ 𝓡 :=
    Submodule.mem_map.2 ⟨1, h1, sym_of_isSymm isSymm_one⟩
  have hsym : ∀ R ∈ 𝓡, R.IsSymm := by
    intro R hR
    obtain ⟨Z, -, rfl⟩ := Submodule.mem_map.1 hR
    exact isSymm_sym Z
  obtain ⟨d, hd1, hd2⟩ := exists_isLeast_norm_isLeast_spr (isSymm_sym D) h1' hsym
  have e : ∀ Z, sym (D + Z) = sym D + symL Z := fun Z => sym_add D Z
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

/-- **The least value over the reach by rows**: if every vector of `V i`
vanishes on the coordinates of `i`, then `d_l = min_{Z ∈ 𝒵_l} ‖sym (D + Z)‖` is attained and the
least spread of `sym (D + Z)` over `𝒵_l` is `2 d_l`, attained. -/
theorem exists_isLeast_rowReach (D : Matrix (Fin n) (Fin n) ℝ)
    (hV : ∀ i, ∀ v ∈ V i, ∀ p, sub p = i → v p = 0) :
    ∃ d, IsLeast {r | ∃ Z ∈ rowReach sub V, r = ‖opE (sym (D + Z))‖} d ∧
      IsLeast {r | ∃ Z ∈ rowReach sub V, r = spr (sym (D + Z))} (2 * d) :=
  exists_isLeast_sym_of_one_mem D (one_mem_rowReach hV)

/-- **The least value is at least a fixed entry** (`2 d_l ≥ 2 |e^T sym (D_l) e'|`): for the
least value `d` of `‖sym (D + Z)‖` over the reach and unit `e`, `e'` as in
`inner_sym_add_of_mem_rowReach`, `|⟪e, sym D e'⟫| ≤ d`. -/
theorem abs_inner_sym_le_least_rowReach (D : Matrix (Fin n) (Fin n) ℝ) {d : ℝ}
    (hd : IsLeast {r | ∃ Z ∈ rowReach sub V, r = ‖opE (sym (D + Z))‖} d) {a b : κ}
    {e e' : EuclideanSpace ℝ (Fin n)} (he : ∀ p, sub p ≠ a → e p = 0) (heV : e ∈ V b)
    (he' : ∀ p, sub p ≠ b → e' p = 0) (he'V : e' ∈ V a) (hn : ‖e‖ = 1) (hn' : ‖e'‖ = 1) :
    |⟪e, opE (sym D) e'⟫| ≤ d := by
  obtain ⟨⟨Z, hZ, rfl⟩, -⟩ := hd
  exact abs_inner_sym_le_norm_of_mem_rowReach D hZ he heV he' he'V hn hn'

/-- **Every point of the half-plane, the matrices, over a subspace that contains the identity.**
Let `E` be a symmetric matrix in `𝒵` with `E p₀ p₀ = 1` and `E q₀ q₀ = 0`, and `d` the least value
of `‖sym (D + Z)‖` over `𝒵`. For all `a`, `b` with `a + b ≥ 2 d` there is `Z ∈ 𝒵` with
`λ_max (sym (D + Z)) = a` and `λ_min (sym (D + Z)) = -b`. -/
theorem exists_extremes_of_one_mem (D : Matrix (Fin n) (Fin n) ℝ)
    {𝒵 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} (h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ 𝒵)
    {E : Matrix (Fin n) (Fin n) ℝ} (hE : E ∈ 𝒵) (hEs : sym E = E) {p₀ q₀ : Fin n}
    (hEp : E p₀ p₀ = 1) (hEq : E q₀ q₀ = 0) {d : ℝ}
    (hd : IsLeast {r | ∃ Z ∈ 𝒵, r = ‖opE (sym (D + Z))‖} d) {a b : ℝ} (hab : 2 * d ≤ a + b) :
    ∃ Z ∈ 𝒵, lamMax (sym (D + Z)) = a ∧ lamMin (sym (D + Z)) = -b := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) p₀.isLt
  obtain ⟨⟨Z₀, hZ₀, hd₀⟩, -⟩ := hd
  obtain ⟨M, hMdef⟩ : ∃ M, M = sym (D + Z₀) := ⟨_, rfl⟩
  rw [← hMdef] at hd₀
  have hd0 : 0 ≤ d := by rw [hd₀]; exact norm_nonneg _
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
      hEp, smul_eq_mul, mul_one] at h1
    rw [inner_unitE_opE, norm_unitE, one_pow, mul_one, Matrix.add_apply, Matrix.smul_apply,
      hEq, smul_eq_mul, mul_zero, add_zero] at h2
    have h3 := abs_le.1 (hM p₀)
    have h4 := abs_le.1 (hM q₀)
    rw [hfdef]
    show a + b ≤ lamMax (M + (a + b + 2 * d) • E) - lamMin (M + (a + b + 2 * d) • E)
    linarith [h3.1, h4.2]
  -- the intermediate value
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hT hf.continuousOn ⟨hf0, hfT⟩
  refine ⟨Z₀ + t • E - (lamMax (M + t • E) - a) • 1, 𝒵.sub_mem
    (𝒵.add_mem hZ₀ (𝒵.smul_mem t hE)) (𝒵.smul_mem _ h1), ?_⟩
  have e : sym (D + (Z₀ + t • E - (lamMax (M + t • E) - a) • 1)) =
      M + t • E - (lamMax (M + t • E) - a) • 1 := by
    rw [show D + (Z₀ + t • E - (lamMax (M + t • E) - a) • 1) =
      (D + Z₀) + t • E - (lamMax (M + t • E) - a) • 1 by abel, sym_sub, sym_add,
      sym_smul, sym_smul, hEs, sym_of_isSymm isSymm_one, ← hMdef]
  rw [e, lamMax_sub_smul_one hn, lamMin_sub_smul_one hn]
  have ht' : lamMax (M + t • E) - lamMin (M + t • E) = a + b := by rw [← ht, hfdef]; rfl
  constructor <;> linarith

/-- **Every point of the half-plane, the matrices, over the reach by rows** (the
pairs `(ι, μ) = H^l (a, b) + O(H^{l+1})` with `a + b ≥ 2 d_l` are all attained, at the level of
the leading defects). If every vector of `V i` vanishes on the coordinates of `i`, two states lie
in different subsystems, and `d` is the least value of `‖sym (D + Z)‖` over the reach, then for
all `a`, `b` with `a + b ≥ 2 d` there is `Z` in the reach with `λ_max (sym (D + Z)) = a` and
`λ_min (sym (D + Z)) = -b`. -/
theorem exists_rowReach_extremes [DecidableEq κ] (D : Matrix (Fin n) (Fin n) ℝ)
    (hV : ∀ i, ∀ v ∈ V i, ∀ p, sub p = i → v p = 0) {p₀ q₀ : Fin n} (hpq : sub p₀ ≠ sub q₀)
    {d : ℝ} (hd : IsLeast {r | ∃ Z ∈ rowReach sub V, r = ‖opE (sym (D + Z))‖} d) {a b : ℝ}
    (hab : 2 * d ≤ a + b) :
    ∃ Z ∈ rowReach sub V, lamMax (sym (D + Z)) = a ∧ lamMin (sym (D + Z)) = -b := by
  refine exists_extremes_of_one_mem D (one_mem_rowReach hV) (mask_mem_rowReach hV (sub p₀))
    (sym_of_isSymm ?_) (p₀ := p₀) (q₀ := q₀) ?_ ?_ hd hab
  · rw [Matrix.IsSymm, diagonal_transpose]
  · rw [diagonal_apply_eq, ite_eq_left rfl]
  · rw [diagonal_apply_eq, ite_eq_right fun h => hpq h.symm]

end Rows

end CoSimFoundations
