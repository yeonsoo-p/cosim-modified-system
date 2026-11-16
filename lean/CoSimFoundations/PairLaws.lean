/-
The pair laws: what every scheme obeys between two directions.

`D` the defect, `U` the reference step, `X = D ∘ U`, on a real inner product space; `e₁`, `e₂`
orthonormal; `α = ‖D - 1‖`; largest stretch `‖D‖`. No structural zero of `X` is assumed.

* **Symmetric transfer, on the defect:**
  `|⟪e₁, (D - 1) e₂⟫ + ⟪e₂, (D - 1) e₁⟫| ≤ (‖D‖ - 1) + α`.
  (Quadratic form of `D - 1` on `e₁ ± e₂`: the two values differ by twice the symmetric pair, one is
  at most `2 (‖D‖ - 1)`, the other at least `-2 α`.)
* **Symmetric transfer, against the reference:** with
  `u_X = ⟪e₁, (U - X) e₂⟫ + ⟪e₂, (U - X) e₁⟫` and `η = ‖U e₁ - e₁‖ + ‖U e₂ - e₂‖`:
  `|u_X| ≤ (‖D‖ - 1) + α (1 + η)`.
  For a two-sided zero of `X` this is `link_tradeoff`; in general the class enters through `u_X`:
  what the scheme fails to move between the two directions, both ways together. If the two
  failures are opposite (`u_X = 0`: a forced numerical interconnection), nothing is forced.
* **Diagonal:** for a unit `e`: `(⟪e, X e⟫ - ⟪e, U e⟫) - α ‖U e - e‖ ≤ ‖D‖ - 1`.
  A scheme that leaves in a store more of its own state than the reference does (no local gain:
  the store's own decay instead of the coupled one) must let energy grow.
* **One-sided, sharp:** if `⟪e₂, (D - 1) e₁⟫ = 0` and `a = ⟪e₁, (D - 1) e₂⟫`, then
  `|a| / 2 - √(α (α - |a|)) ≤ ‖D‖ - 1` (and `|a| ≤ α`).
-/
import CoSimFoundations.TradeOff
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt

open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Symmetric transfer, on the defect.** -/
theorem abs_sym_pair_le (D : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) :
    |⟪e₁, (D - 1) e₂⟫ + ⟪e₂, (D - 1) e₁⟫| ≤ (‖D‖ - 1) + ‖D - 1‖ := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have qp := abs_le.1 (abs_inner_sub_one_self_le D (e₁ + e₂))
  have qm := abs_le.1 (abs_inner_sub_one_self_le D (e₁ - e₂))
  have dp := sq_add_inner_sub_one_le D (e₁ + e₂)
  have dm := sq_add_inner_sub_one_le D (e₁ - e₂)
  rw [hp] at qp dp
  rw [hm] at qm dm
  rw [inner_add_sub_one] at qp dp
  rw [inner_sub_sub_one] at qm dm
  rw [abs_le]
  constructor <;> linarith [qp.1, qm.1]

/-- **Symmetric transfer, against the reference** (`link_tradeoff` without its zero). -/
theorem pair_gain (D U : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) :
    |⟪e₁, U e₂ - D (U e₂)⟫ + ⟪e₂, U e₁ - D (U e₁)⟫| ≤
      (‖D‖ - 1) + ‖D - 1‖ * (1 + (‖U e₁ - e₁‖ + ‖U e₂ - e₂‖)) := by
  have hS := abs_le.1 (abs_sym_pair_le D h1 h2 h12)
  have r1 := abs_le.1 (abs_inner_sub_one_apply_le D h1 (U e₂ - e₂))
  have r2 := abs_le.1 (abs_inner_sub_one_apply_le D h2 (U e₁ - e₁))
  have k1 : ⟪e₁, U e₂ - D (U e₂)⟫ =
      -(⟪e₁, (D - 1) e₂⟫ + ⟪e₁, (D - 1) (U e₂ - e₂)⟫) := by
    have : (D - 1) (U e₂ - e₂) = D (U e₂) - U e₂ - (D - 1) e₂ := by simp [map_sub]
    rw [this]
    simp only [inner_sub_right]
    ring
  have k2 : ⟪e₂, U e₁ - D (U e₁)⟫ =
      -(⟪e₂, (D - 1) e₁⟫ + ⟪e₂, (D - 1) (U e₁ - e₁)⟫) := by
    have : (D - 1) (U e₁ - e₁) = D (U e₁) - U e₁ - (D - 1) e₁ := by simp [map_sub]
    rw [this]
    simp only [inner_sub_right]
    ring
  rw [k1, k2, abs_le]
  constructor <;> linarith [hS.1, hS.2, r1.1, r1.2, r2.1, r2.2]

/-- **Diagonal law.** -/
theorem diag_gain (D U : E →L[ℝ] E) {e : E} (he : ‖e‖ = 1) :
    (⟪e, D (U e)⟫ - ⟪e, U e⟫) - ‖D - 1‖ * ‖U e - e‖ ≤ ‖D‖ - 1 := by
  have h1 := sq_add_inner_sub_one_le D e
  rw [he] at h1
  have h2 := (abs_le.1 (abs_inner_sub_one_apply_le D he (U e - e))).2
  have h3 : ⟪e, (D - 1) (U e - e)⟫ = ⟪e, D (U e)⟫ - ⟪e, U e⟫ - ⟪e, (D - 1) e⟫ := by
    have : (D - 1) (U e - e) = D (U e) - U e - (D - 1) e := by simp [map_sub]
    rw [this, inner_sub_right, inner_sub_right]
  linarith

/-- The entry of the error between two orthonormal directions is at most `α`. -/
theorem abs_inner_sub_one_le (D : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) :
    |⟪e₁, (D - 1) e₂⟫| ≤ ‖D - 1‖ := by
  have h := abs_inner_sub_one_apply_le D h1 e₂
  rwa [h2, mul_one] at h

/-- Bessel's inequality for an orthonormal pair. -/
theorem inner_sq_add_inner_sq_le {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (w : E) : ⟪e₁, w⟫ ^ 2 + ⟪e₂, w⟫ ^ 2 ≤ ‖w‖ ^ 2 := by
  have hp : ‖⟪e₁, w⟫ • e₁ + ⟪e₂, w⟫ • e₂‖ ^ 2 = ⟪e₁, w⟫ ^ 2 + ⟪e₂, w⟫ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      h12, h1, h2, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs]
    ring
  have hw : ⟪w, ⟪e₁, w⟫ • e₁ + ⟪e₂, w⟫ • e₂⟫ = ⟪e₁, w⟫ ^ 2 + ⟪e₂, w⟫ ^ 2 := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm e₁ w,
      real_inner_comm e₂ w]
    ring
  have h := sq_nonneg ‖w - (⟪e₁, w⟫ • e₁ + ⟪e₂, w⟫ • e₂)‖
  rw [norm_sub_sq_real, hw, hp] at h
  linarith

/-- The compression of `D - 1` to `span {e₁, e₂}` is upper triangular when
`⟪e₂, (D - 1) e₁⟫ = 0`; its columns on `t e₁ + e₂` are bounded by `α`. -/
theorem sq_add_sq_compression_le (D : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (hb : ⟪e₂, (D - 1) e₁⟫ = 0) (t : ℝ) :
    (t * ⟪e₁, (D - 1) e₁⟫ + ⟪e₁, (D - 1) e₂⟫) ^ 2 + ⟪e₂, (D - 1) e₂⟫ ^ 2 ≤
      ‖D - 1‖ ^ 2 * (t ^ 2 + 1) := by
  have hv : ‖t • e₁ + e₂‖ ^ 2 = t ^ 2 + 1 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, h12, h1, h2, Real.norm_eq_abs,
      mul_one, sq_abs]
    ring
  have c1 : ⟪e₁, (D - 1) (t • e₁ + e₂)⟫ = t * ⟪e₁, (D - 1) e₁⟫ + ⟪e₁, (D - 1) e₂⟫ := by
    rw [map_add, map_smul, inner_add_right, real_inner_smul_right]
  have c2 : ⟪e₂, (D - 1) (t • e₁ + e₂)⟫ = ⟪e₂, (D - 1) e₂⟫ := by
    rw [map_add, map_smul, inner_add_right, real_inner_smul_right, hb, mul_zero, zero_add]
  have hB := inner_sq_add_inner_sq_le h1 h2 h12 ((D - 1) (t • e₁ + e₂))
  have hN : ‖(D - 1) (t • e₁ + e₂)‖ ^ 2 ≤ ‖D - 1‖ ^ 2 * ‖t • e₁ + e₂‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((D - 1).le_opNorm _) 2
  rw [c1, c2] at hB
  rw [hv] at hN
  linarith

/-- The 2x2 core: if `s² I - MᵀM` is positive semidefinite for `M = [[X, A], [0, Y]]`
(diagonal entries and determinant nonnegative), then `(X + Y)² ≤ 4 s (s - A)`. -/
theorem sq_add_le_of_det_nonneg {s X Y A : ℝ} (hs : 0 ≤ s) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h1 : X ^ 2 ≤ s ^ 2) (h2 : A ^ 2 + Y ^ 2 ≤ s ^ 2)
    (hdet : X ^ 2 * A ^ 2 ≤ (s ^ 2 - X ^ 2) * (s ^ 2 - A ^ 2 - Y ^ 2)) :
    (X + Y) ^ 2 ≤ 4 * s * (s - A) := by
  have hw0 : 0 ≤ s ^ 2 - X * Y := by nlinarith [sq_nonneg (X - Y), sq_nonneg A]
  have hw2 : (s * A) ^ 2 ≤ (s ^ 2 - X * Y) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg (X - Y))]
  have hw : s * A ≤ s ^ 2 - X * Y := by nlinarith
  have hv0 : 0 ≤ s ^ 2 + X * Y := add_nonneg (sq_nonneg s) (mul_nonneg hX hY)
  have hv : s ^ 2 + X * Y ≤ s * (2 * s - A) := by linarith
  have hv2 : s ^ 2 * ((X + Y) ^ 2 + A ^ 2) ≤ (s ^ 2 + X * Y) ^ 2 := by nlinarith
  have hv3 : (s ^ 2 + X * Y) ^ 2 ≤ (s * (2 * s - A)) ^ 2 := pow_le_pow_left₀ hv0 hv 2
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    nlinarith [sq_nonneg (X - Y), sq_nonneg A]
  · have h4 := le_trans hv2 hv3
    rw [mul_pow] at h4
    have h5 := le_of_mul_le_mul_left h4 (pow_pos hpos 2)
    nlinarith [h5]

/-- The one-sided law for real numbers: `x, y, a` the entries of an upper triangular 2x2 matrix
of norm at most `s`, `d` at least half of its symmetric quadratic form on `(1, ±1)`. -/
theorem one_sided_real {s x y a d : ℝ} (hs : 0 ≤ s) (hx : |x| ≤ s)
    (hq : ∀ t : ℝ, (t * x + a) ^ 2 + y ^ 2 ≤ s ^ 2 * (t ^ 2 + 1))
    (hp : x + y + a ≤ 2 * d) (hm : x + y - a ≤ 2 * d) :
    |a| / 2 - Real.sqrt (s * (s - |a|)) ≤ d := by
  have hdisc : discrim (s ^ 2 - x ^ 2) (-(2 * x * a)) (s ^ 2 - a ^ 2 - y ^ 2) ≤ 0 :=
    discrim_le_zero fun t => by nlinarith [hq t]
  rw [discrim] at hdisc
  have h0 := hq 0
  have hx2 : |x| ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hcore := sq_add_le_of_det_nonneg (A := |a|) hs (abs_nonneg x) (abs_nonneg y) hx2
    (by rw [sq_abs, sq_abs]; nlinarith [h0])
    (by rw [sq_abs, sq_abs, sq_abs]; nlinarith [hdisc])
  have hxy2 : (x + y) ^ 2 ≤ (|x| + |y|) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (x + y)) (abs_add_le x y) 2
    rwa [sq_abs] at h
  have hxy : ((x + y) / 2) ^ 2 ≤ s * (s - |a|) := by nlinarith [hxy2, hcore]
  have hsq := Real.neg_sqrt_le_of_sq_le hxy
  have ha : |a| ≤ 2 * d - (x + y) := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **One-sided law, sharp form.** -/
theorem one_sided_gain (D : E →L[ℝ] E) {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (h12 : ⟪e₁, e₂⟫ = 0) (hb : ⟪e₂, (D - 1) e₁⟫ = 0) :
    |⟪e₁, (D - 1) e₂⟫| / 2 -
        Real.sqrt (‖D - 1‖ * (‖D - 1‖ - |⟪e₁, (D - 1) e₂⟫|)) ≤ ‖D‖ - 1 := by
  obtain ⟨hp, hm⟩ := norm_add_sq_of_orthonormal h1 h2 h12
  have dp := sq_add_inner_sub_one_le D (e₁ + e₂)
  have dm := sq_add_inner_sub_one_le D (e₁ - e₂)
  rw [hp, inner_add_sub_one, hb] at dp
  rw [hm, inner_sub_sub_one, hb] at dm
  exact one_sided_real (norm_nonneg _) (abs_inner_sub_one_le D h1 h1)
    (sq_add_sq_compression_le D h1 h2 h12 hb) (by linarith) (by linarith)

end CoSimFoundations
