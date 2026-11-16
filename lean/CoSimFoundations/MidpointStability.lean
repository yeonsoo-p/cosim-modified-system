/-
The one-step map of the zero-order hold as the Cayley transform of a pencil (the paper,
Corollary `cor:stability`, eq. `eq:cayley`, with the midpoint form `eq:midpoint` of Lemma
`thm:half`).

**Abstract part** (namespace `MidpointStability`). Square matrices `E`, `A`, `X` over a field `K`,
`H : K`, and the midpoint form
  `hmid : E (X - 1) = (H/2) A (X + 1)`.
* `step`: `(E - (H/2) A) X = E + (H/2) A` (expand `hmid`).
* `eigen`: `X v = ξ v` implies `(H/2) (1 + ξ) A v = (ξ - 1) E v` (apply `hmid` to `v`).
  `eigen_of_eq`: the converse, if `E - (H/2) A` is invertible: by `step`,
  `(E - (H/2) A) (X v - ξ v) = (1 - ξ) E v + (H/2) (1 + ξ) A v = 0`. `eigen_iff`.
* `neg_one_imp`, `neg_one_of`, `neg_one_iff`: `X v = -v ↔ E v = 0`. The direction `→` uses
  `2 ≠ 0` in `K` and no invertibility (`ξ = -1` gives `0 = -2 E v`); the direction `←` uses the
  invertibility of `E - (H/2) A` and not `2 ≠ 0`.
* `pencil_of_eigen`: `X v = ξ v`, `ξ ≠ -1`, `H ≠ 0`, `2 ≠ 0` imply `A v = θ E v` with
  `θ = (2/H) (ξ - 1)/(ξ + 1)`. `eigen_of_pencil`: `A v = θ E v`, `1 - (H/2) θ ≠ 0` and
  `E - (H/2) A` invertible imply `X v = ξ v` with `ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`.
  `pencil_den_ne_zero`: for `v ≠ 0` the condition `1 - (H/2) θ ≠ 0` follows from the invertibility
  of `E - (H/2) A`. The two scalar maps are inverse to each other (`cayley_cayley_inv`,
  `cayley_inv_cayley`). `pencil_iff_of_left_inv`: if `E` is invertible, `A v = θ E v` says that
  `θ` is an eigenvalue of `E⁻¹ A`.
* Over `ℂ` with a real `H > 0` and `ξ ≠ -1`, `θ = (2/H) (ξ - 1)/(ξ + 1)`:
  `Re θ = (2/H) (|ξ|² - 1)/|ξ + 1|²` (`cayley_inv_re`), so `|ξ| < 1 ↔ Re θ < 0`
  (`norm_lt_one_iff_cayley_re_neg`) and `|ξ| = 1 ↔ Re θ = 0`
  (`norm_eq_one_iff_cayley_re_eq_zero`).
* `spectrum_iff` (complex matrices, real `H > 0`, `E - (H/2) A` invertible): every eigenvalue of
  `X` has modulus `< 1` if and only if `det E ≠ 0` and every eigenvalue `θ` of the pencil
  (`A v = θ E v`, `v ≠ 0`) has a negative real part.

**The zero-order hold** (namespace `HeldScheme`). `E = Ψ - (H/2) A_ς` (`midpointE`), `X` the
one-step map of `S.zoh A hA H`, `φ = φ₁(H A₀)` invertible (the hypothesis of
`zoh_midpoint_psi`; it holds for `‖H A₀‖ ≤ 1`, `isUnit_det_phiOne`).
* `phiOne_mul_midpointE_sub`: `φ (E - (H/2) A) = 1 - N`, `N = zohNew` the matrix of the new
  samples, because `A = A₀ + A_old + A_new`, `A_ς = A_new - A_old`, `N = H φ A_new`.
  `isUnit_det_midpointE_sub`: `E - (H/2) A` is invertible, because `N` is nilpotent by the
  stages. This is proved, not assumed.
* The statements of the abstract part for real vectors (`zoh_step`, `zoh_eigen_iff`,
  `zoh_neg_one_iff`, `zoh_neg_one_eigenvalue_iff`: `-1` is an eigenvalue of `X` iff `det E = 0`)
  and for complex eigenvalues of the complexified matrices (`zoh_eigen_iff_complex`,
  `zoh_pencil_of_eigen`, `zoh_eigen_of_pencil`, `zoh_spectrum_iff`, `zoh_spectrum_iff_inv`).

**What is not here.** The corollary says "asymptotically stable". `zoh_spectrum_iff_inv` states it
on the eigenvalues: all eigenvalues of `X` lie in the open unit disc iff `E` is invertible and all
eigenvalues of `E⁻¹ A` have a negative real part. That the powers of `X` tend to zero exactly
when its eigenvalues lie in the open unit disc is not formalised in this module.
-/
import CoSimFoundations.MidpointForm

open Matrix

namespace CoSimFoundations

namespace MidpointStability

/-! ### The Cayley transform of a scalar -/

section Scalar

variable {K : Type*} [Field K]

/-- For `ξ ≠ -1` and `θ = (2/H) (ξ - 1)/(ξ + 1)`: `1 - (H/2) θ = 2/(ξ + 1)` is not zero. -/
theorem cayley_inv_den_ne_zero [NeZero (2 : K)] {H xi : K} (hH : H ≠ 0) (hxi : xi ≠ -1) :
    1 - H / 2 * (2 / H * (xi - 1) / (xi + 1)) ≠ 0 := by
  have h1 : xi + 1 ≠ 0 := fun h => hxi (eq_neg_of_add_eq_zero_left h)
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have e : 1 - H / 2 * (2 / H * (xi - 1) / (xi + 1)) = 2 / (xi + 1) := by
    field_simp
    ring
  rw [e]
  exact div_ne_zero h2 h1

/-- **The two scalar maps are inverse to each other, first half:** for `ξ ≠ -1` and
`θ = (2/H) (ξ - 1)/(ξ + 1)`, `(1 + (H/2) θ)/(1 - (H/2) θ) = ξ`. -/
theorem cayley_cayley_inv [NeZero (2 : K)] {H xi : K} (hH : H ≠ 0) (hxi : xi ≠ -1) :
    (1 + H / 2 * (2 / H * (xi - 1) / (xi + 1))) / (1 - H / 2 * (2 / H * (xi - 1) / (xi + 1))) =
      xi := by
  have h1 : xi + 1 ≠ 0 := fun h => hxi (eq_neg_of_add_eq_zero_left h)
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have e1 : 1 - H / 2 * (2 / H * (xi - 1) / (xi + 1)) = 2 / (xi + 1) := by
    field_simp
    ring
  have e2 : 1 + H / 2 * (2 / H * (xi - 1) / (xi + 1)) = 2 * xi / (xi + 1) := by
    field_simp
    ring
  rw [e1, e2]
  field_simp

/-- For `1 - (H/2) θ ≠ 0` the Cayley transform `ξ = (1 + (H/2) θ)/(1 - (H/2) θ)` is not `-1`. -/
theorem cayley_ne_neg_one [NeZero (2 : K)] {H theta : K} (hθ : 1 - H / 2 * theta ≠ 0) :
    (1 + H / 2 * theta) / (1 - H / 2 * theta) ≠ -1 := by
  intro h
  rw [div_eq_iff hθ] at h
  have h2 : (2 : K) = 0 := by linear_combination h
  exact NeZero.ne 2 h2

/-- **The two scalar maps are inverse to each other, second half:** for `1 - (H/2) θ ≠ 0` and
`ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`, `(2/H) (ξ - 1)/(ξ + 1) = θ`. -/
theorem cayley_inv_cayley [NeZero (2 : K)] {H theta : K} (hH : H ≠ 0)
    (hθ : 1 - H / 2 * theta ≠ 0) :
    2 / H * ((1 + H / 2 * theta) / (1 - H / 2 * theta) - 1) /
      ((1 + H / 2 * theta) / (1 - H / 2 * theta) + 1) = theta := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have e1 : (1 + H / 2 * theta) / (1 - H / 2 * theta) - 1 =
      H * theta / (1 - H / 2 * theta) := by
    rw [div_sub_one hθ]
    congr 1
    field_simp
    ring
  have e2 : (1 + H / 2 * theta) / (1 - H / 2 * theta) + 1 = 2 / (1 - H / 2 * theta) := by
    rw [div_add_one hθ]
    congr 1
    ring
  rw [e1, e2, div_eq_iff (div_ne_zero h2 hθ), mul_div_assoc', mul_div_assoc']
  congr 1
  rw [show 2 / H * (H * theta) = H / H * (theta * 2) by ring, div_self hH, one_mul]

/-- **The real part of the inverse Cayley transform:** for a real `H` and a complex `ξ`,
`Re ((2/H) (ξ - 1)/(ξ + 1)) = (2/H) (|ξ|² - 1)/|ξ + 1|²`. -/
theorem cayley_inv_re (H : ℝ) (xi : ℂ) :
    (2 / (H : ℂ) * (xi - 1) / (xi + 1)).re =
      2 / H * ((Complex.normSq xi - 1) / Complex.normSq (xi + 1)) := by
  have e : 2 / (H : ℂ) * (xi - 1) / (xi + 1) = ((2 / H : ℝ) : ℂ) * ((xi - 1) / (xi + 1)) := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, Complex.div_re, ← add_div]
  congr 2
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, sub_zero, add_zero, Complex.normSq_apply]
  ring

/-- **The unit disc and the left half plane:** for a real `H > 0`, a complex `ξ ≠ -1` and
`θ = (2/H) (ξ - 1)/(ξ + 1)`: `|ξ| < 1` if and only if `Re θ < 0`. -/
theorem norm_lt_one_iff_cayley_re_neg {H : ℝ} (hH : 0 < H) {xi : ℂ} (hxi : xi ≠ -1) :
    ‖xi‖ < 1 ↔ (2 / (H : ℂ) * (xi - 1) / (xi + 1)).re < 0 := by
  have hd : 0 < Complex.normSq (xi + 1) :=
    Complex.normSq_pos.2 fun h => hxi (eq_neg_of_add_eq_zero_left h)
  have hc : 0 < 2 / H := div_pos two_pos hH
  rw [cayley_inv_re, ← sq_lt_one_iff₀ (norm_nonneg xi), ← Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg hc (div_neg_of_neg_of_pos (sub_neg.2 h) hd)
  · intro h
    by_contra hn
    exact absurd h (not_lt.2 (mul_nonneg hc.le (div_nonneg (sub_nonneg.2 (not_lt.1 hn)) hd.le)))

/-- **The unit circle and the imaginary axis:** for a real `H > 0`, a complex `ξ ≠ -1` and
`θ = (2/H) (ξ - 1)/(ξ + 1)`: `|ξ| = 1` if and only if `Re θ = 0`. -/
theorem norm_eq_one_iff_cayley_re_eq_zero {H : ℝ} (hH : 0 < H) {xi : ℂ} (hxi : xi ≠ -1) :
    ‖xi‖ = 1 ↔ (2 / (H : ℂ) * (xi - 1) / (xi + 1)).re = 0 := by
  have hd : 0 < Complex.normSq (xi + 1) :=
    Complex.normSq_pos.2 fun h => hxi (eq_neg_of_add_eq_zero_left h)
  have hc : 0 < 2 / H := div_pos two_pos hH
  rw [cayley_inv_re, ← pow_eq_one_iff_of_nonneg (norm_nonneg xi) two_ne_zero,
    ← Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    rw [h, sub_self, zero_div, mul_zero]
  · intro h
    have h1 := (mul_eq_zero.1 h).resolve_left hc.ne'
    exact sub_eq_zero.1 ((div_eq_zero_iff.1 h1).resolve_right hd.ne')

end Scalar

/-! ### The midpoint form of a one-step map -/

section Abstract

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
variable {E A X : Matrix ι ι K} {H : K}

/-- A matrix with an invertible determinant is injective on vectors. -/
theorem mulVec_left_cancel {M : Matrix ι ι K} (hM : IsUnit M.det) {u w : ι → K}
    (h : M *ᵥ u = M *ᵥ w) : u = w := by
  have h2 : M⁻¹ *ᵥ (M *ᵥ u) = M⁻¹ *ᵥ (M *ᵥ w) := by rw [h]
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM,
    Matrix.one_mulVec, Matrix.one_mulVec] at h2

/-- **The one-step map from the midpoint form:** `E (X - 1) = (H/2) A (X + 1)` implies
`(E - (H/2) A) X = E + (H/2) A`. -/
theorem step (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) :
    (E - (H / 2) • A) * X = E + (H / 2) • A := by
  rw [mul_sub, mul_add, mul_one, mul_one, smul_add, sub_eq_iff_eq_add] at hmid
  rw [sub_mul, smul_mul_assoc, hmid]
  abel

/-- The midpoint form on a vector: `E (X v - v) = (H/2) A (X v + v)`. -/
theorem midpoint_mulVec (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) (v : ι → K) :
    E *ᵥ (X *ᵥ v - v) = (H / 2) • (A *ᵥ (X *ᵥ v + v)) := by
  have h : (E * (X - 1)) *ᵥ v = ((H / 2) • (A * (X + 1))) *ᵥ v := by rw [hmid]
  rwa [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at h

/-- **An eigenvector of the one-step map:** if `E (X - 1) = (H/2) A (X + 1)` and `X v = ξ v`,
then `(H/2) (1 + ξ) A v = (ξ - 1) E v`. -/
theorem eigen (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) {v : ι → K} {xi : K}
    (hv : X *ᵥ v = xi • v) : (H / 2 * (1 + xi)) • (A *ᵥ v) = (xi - 1) • (E *ᵥ v) := by
  have h := midpoint_mulVec hmid v
  rw [hv, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at h
  rw [sub_smul, one_smul, h]
  module

/-- **The converse:** if `E (X - 1) = (H/2) A (X + 1)`, the matrix `E - (H/2) A` is invertible and
`(H/2) (1 + ξ) A v = (ξ - 1) E v`, then `X v = ξ v`. -/
theorem eigen_of_eq (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hdet : IsUnit (E - (H / 2) • A).det) {v : ι → K} {xi : K}
    (h : (H / 2 * (1 + xi)) • (A *ᵥ v) = (xi - 1) • (E *ᵥ v)) : X *ᵥ v = xi • v := by
  refine mulVec_left_cancel hdet ?_
  rw [Matrix.mulVec_mulVec, step hmid, Matrix.add_mulVec, Matrix.mulVec_smul,
    Matrix.sub_mulVec, Matrix.smul_mulVec, ← sub_eq_zero]
  have e : E *ᵥ v + (H / 2) • (A *ᵥ v) - xi • (E *ᵥ v - (H / 2) • (A *ᵥ v)) =
      (H / 2 * (1 + xi)) • (A *ᵥ v) - (xi - 1) • (E *ᵥ v) := by
    module
  rw [e, h, sub_self]

/-- **The eigenvectors of the one-step map:** if `E (X - 1) = (H/2) A (X + 1)` and
`E - (H/2) A` is invertible, `X v = ξ v` if and only if `(H/2) (1 + ξ) A v = (ξ - 1) E v`. -/
theorem eigen_iff (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hdet : IsUnit (E - (H / 2) • A).det) {v : ι → K} {xi : K} :
    X *ᵥ v = xi • v ↔ (H / 2 * (1 + xi)) • (A *ᵥ v) = (xi - 1) • (E *ᵥ v) :=
  ⟨eigen hmid, eigen_of_eq hmid hdet⟩

/-- **The eigenvalue `-1`, first direction** (no invertibility; `2 ≠ 0` in the field): if
`E (X - 1) = (H/2) A (X + 1)` and `X v = -v`, then `E v = 0`. -/
theorem neg_one_imp [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    {v : ι → K} (hv : X *ᵥ v = -v) : E *ᵥ v = 0 := by
  have h := eigen (xi := -1) hmid (by rw [neg_one_smul]; exact hv)
  rw [add_neg_cancel, mul_zero, zero_smul] at h
  have h2 : (-1 - 1 : K) ≠ 0 := by
    have e : (-1 - 1 : K) = -2 := by ring
    rw [e]
    exact neg_ne_zero.2 (NeZero.ne 2)
  exact (smul_eq_zero.1 h.symm).resolve_left h2

/-- **The eigenvalue `-1`, second direction:** if `E (X - 1) = (H/2) A (X + 1)`, the matrix
`E - (H/2) A` is invertible and `E v = 0`, then `X v = -v`. -/
theorem neg_one_of (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hdet : IsUnit (E - (H / 2) • A).det) {v : ι → K} (hE : E *ᵥ v = 0) : X *ᵥ v = -v := by
  have h := eigen_of_eq (xi := -1) (v := v) hmid hdet
    (by rw [hE, smul_zero, add_neg_cancel, mul_zero, zero_smul])
  rwa [neg_one_smul] at h

/-- **The eigenvalue `-1`:** if `E (X - 1) = (H/2) A (X + 1)` and `E - (H/2) A` is invertible,
`X v = -v` if and only if `E v = 0`. -/
theorem neg_one_iff [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hdet : IsUnit (E - (H / 2) • A).det) {v : ι → K} : X *ᵥ v = -v ↔ E *ᵥ v = 0 :=
  ⟨neg_one_imp hmid, neg_one_of hmid hdet⟩

/-- **From the one-step map to the pencil:** if `E (X - 1) = (H/2) A (X + 1)`, `H ≠ 0`,
`X v = ξ v` and `ξ ≠ -1`, then `A v = θ E v` with `θ = (2/H) (ξ - 1)/(ξ + 1)`. (No
invertibility, and `v` may be zero.) -/
theorem pencil_of_eigen [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hH : H ≠ 0) {v : ι → K} {xi : K} (hxi : xi ≠ -1) (hv : X *ᵥ v = xi • v) :
    A *ᵥ v = (2 / H * (xi - 1) / (xi + 1)) • (E *ᵥ v) := by
  have h := eigen hmid hv
  have h1 : 1 + xi ≠ 0 := fun h => hxi (eq_neg_of_add_eq_zero_right h)
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have h3 : H / 2 * (1 + xi) ≠ 0 := mul_ne_zero (div_ne_zero hH h2) h1
  have e : 2 / H * (xi - 1) / (xi + 1) = (H / 2 * (1 + xi))⁻¹ * (xi - 1) := by
    rw [add_comm xi 1]
    field_simp
  rw [e, mul_smul, ← h, smul_smul, inv_mul_cancel₀ h3, one_smul]

/-- **From the pencil to the one-step map:** if `E (X - 1) = (H/2) A (X + 1)`, the matrix
`E - (H/2) A` is invertible, `A v = θ E v` and `1 - (H/2) θ ≠ 0`, then `X v = ξ v` with
`ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`. -/
theorem eigen_of_pencil (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hdet : IsUnit (E - (H / 2) • A).det) {v : ι → K} {theta : K}
    (hθ : 1 - H / 2 * theta ≠ 0) (hv : A *ᵥ v = theta • (E *ᵥ v)) :
    X *ᵥ v = ((1 + H / 2 * theta) / (1 - H / 2 * theta)) • v := by
  refine eigen_of_eq hmid hdet ?_
  rw [hv, smul_smul]
  congr 1
  generalize H / 2 = c at hθ ⊢
  rw [one_add_div hθ, div_sub_one hθ, eq_div_iff hθ,
    show c * ((1 - c * theta + (1 + c * theta)) / (1 - c * theta)) * theta * (1 - c * theta) =
      c * (1 - c * theta + (1 + c * theta)) * theta * ((1 - c * theta) / (1 - c * theta)) by ring,
    div_self hθ]
  ring

/-- **The pencil has no eigenvalue `2/H`:** if `E - (H/2) A` is invertible, `v ≠ 0` and
`A v = θ E v`, then `1 - (H/2) θ ≠ 0`. -/
theorem pencil_den_ne_zero (hdet : IsUnit (E - (H / 2) • A).det) {v : ι → K} {theta : K}
    (hv0 : v ≠ 0) (hv : A *ᵥ v = theta • (E *ᵥ v)) : 1 - H / 2 * theta ≠ 0 := by
  intro h0
  apply hv0
  refine mulVec_left_cancel hdet ?_
  have e : E *ᵥ v - (H / 2 * theta) • (E *ᵥ v) = (1 - H / 2 * theta) • (E *ᵥ v) := by
    rw [sub_smul, one_smul]
  rw [Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_smul, e, h0, zero_smul]

/-- **The pencil and the matrix `E⁻¹ A`:** if `Ei E = 1`, then `A v = θ E v` if and only if
`(Ei A) v = θ v`. -/
theorem pencil_iff_of_left_inv {Ei : Matrix ι ι K} (hi : Ei * E = 1) {v : ι → K} {theta : K} :
    A *ᵥ v = theta • (E *ᵥ v) ↔ (Ei * A) *ᵥ v = theta • v := by
  have hi2 : E * Ei = 1 := mul_eq_one_comm.1 hi
  constructor
  · intro h
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hi,
      Matrix.one_mulVec]
  · intro h
    have h2 : E *ᵥ ((Ei * A) *ᵥ v) = E *ᵥ (theta • v) := by rw [h]
    rwa [Matrix.mulVec_mulVec, ← mul_assoc, hi2, one_mul, Matrix.mulVec_smul] at h2

/-- The midpoint form is kept by a homomorphism of fields applied to the entries. -/
theorem midpoint_map {L : Type*} [Field L] (f : K →+* L)
    (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) :
    E.map f * (X.map f - 1) = (f H / 2) • (A.map f * (X.map f + 1)) := by
  have hs : ∀ M : Matrix ι ι K, f.mapMatrix ((H / 2) • M) = (f H / 2) • f.mapMatrix M := by
    intro M
    ext i j
    simp [map_ofNat]
  have h := congrArg f.mapMatrix hmid
  rw [hs, map_mul, map_mul, map_sub, map_add, map_one] at h
  exact h

/-- The invertibility of `E - (H/2) A` is kept by a homomorphism of fields applied to the
entries. -/
theorem isUnit_det_map {L : Type*} [Field L] (f : K →+* L)
    (hdet : IsUnit (E - (H / 2) • A).det) : IsUnit (E.map f - (f H / 2) • A.map f).det := by
  have e : E.map f - (f H / 2) • A.map f = f.mapMatrix (E - (H / 2) • A) := by
    ext i j
    simp [map_ofNat]
  rw [e, ← RingHom.map_det]
  exact hdet.map f

end Abstract

/-! ### The eigenvalues of the one-step map and of the pencil -/

section Spectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Stability on the eigenvalues.** Complex matrices with `E (X - 1) = (H/2) A (X + 1)`, a real
`H > 0`, and `E - (H/2) A` invertible. Every eigenvalue of `X` has modulus less than one if and
only if `E` is invertible and every eigenvalue `θ` of the pencil (`A v = θ E v` with `v ≠ 0`) has
a negative real part. -/
theorem spectrum_iff {E A X : Matrix ι ι ℂ} {H : ℝ} (hH : 0 < H)
    (hmid : E * (X - 1) = ((H : ℂ) / 2) • (A * (X + 1)))
    (hdet : IsUnit (E - ((H : ℂ) / 2) • A).det) :
    (∀ (xi : ℂ) (v : ι → ℂ), v ≠ 0 → X *ᵥ v = xi • v → ‖xi‖ < 1) ↔
      E.det ≠ 0 ∧
        ∀ (theta : ℂ) (v : ι → ℂ), v ≠ 0 → A *ᵥ v = theta • (E *ᵥ v) → theta.re < 0 := by
  have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH.ne'
  constructor
  · intro h
    refine ⟨fun h0 => ?_, fun theta v hv0 hv => ?_⟩
    · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have h1 := h (-1) v hv0 (by rw [neg_one_smul]; exact neg_one_of hmid hdet hv)
      rw [norm_neg, norm_one] at h1
      exact lt_irrefl _ h1
    · have hθ := pencil_den_ne_zero hdet hv0 hv
      have h1 := h _ v hv0 (eigen_of_pencil hmid hdet hθ hv)
      have h2 := (norm_lt_one_iff_cayley_re_neg hH (cayley_ne_neg_one hθ)).1 h1
      rwa [cayley_inv_cayley hHc hθ] at h2
  · rintro ⟨hE, h⟩ xi v hv0 hv
    by_cases hxi : xi = -1
    · exfalso
      rw [hxi, neg_one_smul] at hv
      exact hE (Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, neg_one_imp hmid hv⟩)
    · exact (norm_lt_one_iff_cayley_re_neg hH hxi).2
        (h _ v hv0 (pencil_of_eigen hmid hHc hxi hv))

end Spectrum

end MidpointStability

/-! ### The zero-order hold -/

namespace HeldScheme

open MidpointStability

variable {n : ℕ} {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- The matrix `E = Ψ - (H/2) A_ς` of the midpoint form of the zero-order hold
(`Ψ = φ₁(H A₀)⁻¹ + (H/2) A₀`, `midpointPsi`). -/
noncomputable def midpointE (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  S.midpointPsi A H - (H / 2) • S.signedCoupling A

/-- The midpoint form of the zero-order hold with `E`: if `φ₁(H A₀)` is invertible,
`E (X - 1) = (H/2) A (X + 1)` (`zoh_midpoint_psi`). -/
theorem zoh_midpointE (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    S.midpointE A H * ((S.zoh A hA H).X - 1) = (H / 2) • (A * ((S.zoh A hA H).X + 1)) :=
  S.zoh_midpoint_psi A hA H hφ

/-- **`E - (H/2) A` by the new samples:** if `φ = φ₁(H A₀)` is invertible,
`φ (E - (H/2) A) = 1 - N` with `N = zohNew` the coefficient matrix of the new samples, that is
`E - (H/2) A = φ⁻¹ (1 - N)`. -/
theorem phiOne_mul_midpointE_sub (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    phiOne (H • S.blockDiag A) * (S.midpointE A H - (H / 2) • A) = 1 - S.zohNew A H := by
  have hA : (H / 2) • A =
      (H / 2) • (S.blockDiag A + (S.couplingOld A + S.couplingNew A)) := by
    rw [S.couplingOld_add_couplingNew, S.blockDiag_add_coupling]
  have e : S.midpointE A H - (H / 2) • A =
      (phiOne (H • S.blockDiag A))⁻¹ - H • S.couplingNew A := by
    rw [midpointE, midpointPsi, ← S.couplingNew_sub_couplingOld, hA]
    module
  rw [e, mul_sub, Matrix.mul_nonsing_inv _ hφ, S.zohNew_eq A H, zohKernel, mul_smul_comm,
    smul_mul_assoc]

/-- The coefficient matrix `N` of the new samples of the zero-order hold is nilpotent by the
stages, so `1 - N` is invertible. -/
theorem isUnit_det_one_sub_zohNew (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) :
    IsUnit (1 - S.zohNew A H).det := by
  have hN : S.zohNew A H ^ S.stageBound = 0 :=
    S.pow_stageBound_eq_zero fun p q h => by simp [zohNew, h]
  have h : IsUnit (1 - S.zohNew A H) := IsNilpotent.isUnit_one_sub ⟨_, hN⟩
  exact (Matrix.isUnit_iff_isUnit_det _).1 h

/-- **`E - (H/2) A` is invertible for the zero-order hold** (every assignment of stages), if
`φ₁(H A₀)` is invertible: `E - (H/2) A = φ₁(H A₀)⁻¹ (1 - N)` and `N` is nilpotent. -/
theorem isUnit_det_midpointE_sub (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    IsUnit (S.midpointE A H - (H / 2) • A).det := by
  have h := S.isUnit_det_one_sub_zohNew A H
  rw [← S.phiOne_mul_midpointE_sub A H hφ, Matrix.det_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- **The one-step map of the zero-order hold:** if `φ₁(H A₀)` is invertible,
`(E - (H/2) A) X = E + (H/2) A`. -/
theorem zoh_step (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (S.midpointE A H - (H / 2) • A) * (S.zoh A hA H).X = S.midpointE A H + (H / 2) • A :=
  step (S.zoh_midpointE A hA H hφ)

/-- **The real eigenvectors of the zero-order hold:** if `φ₁(H A₀)` is invertible, `X v = ξ v`
if and only if `(H/2) (1 + ξ) A v = (ξ - 1) E v`. -/
theorem zoh_eigen_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) {v : Fin n → ℝ} {xi : ℝ} :
    (S.zoh A hA H).X *ᵥ v = xi • v ↔
      (H / 2 * (1 + xi)) • (A *ᵥ v) = (xi - 1) • (S.midpointE A H *ᵥ v) :=
  eigen_iff (S.zoh_midpointE A hA H hφ) (S.isUnit_det_midpointE_sub A H hφ)

/-- **The step that changes the sign:** if `φ₁(H A₀)` is invertible, `X v = -v` if and only if
`E v = 0`. -/
theorem zoh_neg_one_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) {v : Fin n → ℝ} :
    (S.zoh A hA H).X *ᵥ v = -v ↔ S.midpointE A H *ᵥ v = 0 :=
  neg_one_iff (S.zoh_midpointE A hA H hφ) (S.isUnit_det_midpointE_sub A H hφ)

/-- **`-1` is an eigenvalue of the one-step map if and only if `E` is singular:** if `φ₁(H A₀)`
is invertible, there is a real `v ≠ 0` with `X v = -v` if and only if `det E = 0`. -/
theorem zoh_neg_one_eigenvalue_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (∃ v : Fin n → ℝ, v ≠ 0 ∧ (S.zoh A hA H).X *ᵥ v = -v) ↔ (S.midpointE A H).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact exists_congr fun v => and_congr_right fun _ => S.zoh_neg_one_iff A hA H hφ

/-- The midpoint form of the zero-order hold for the complexified matrices. -/
theorem zoh_midpointE_complex (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (S.midpointE A H).map (algebraMap ℝ ℂ) * ((S.zoh A hA H).X.map (algebraMap ℝ ℂ) - 1) =
      ((H : ℂ) / 2) •
        (A.map (algebraMap ℝ ℂ) * ((S.zoh A hA H).X.map (algebraMap ℝ ℂ) + 1)) :=
  midpoint_map (algebraMap ℝ ℂ) (S.zoh_midpointE A hA H hφ)

/-- `E - (H/2) A` of the zero-order hold is invertible as a complex matrix. -/
theorem isUnit_det_midpointE_sub_complex (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    IsUnit ((S.midpointE A H).map (algebraMap ℝ ℂ) -
      ((H : ℂ) / 2) • A.map (algebraMap ℝ ℂ)).det :=
  isUnit_det_map (algebraMap ℝ ℂ) (S.isUnit_det_midpointE_sub A H hφ)

/-- **The complex eigenvectors of the zero-order hold:** if `φ₁(H A₀)` is invertible, for a
complex vector `v` and a complex `ξ`, `X v = ξ v` if and only if
`(H/2) (1 + ξ) A v = (ξ - 1) E v`. -/
theorem zoh_eigen_iff_complex (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) {v : Fin n → ℂ} {xi : ℂ} :
    (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v ↔
      ((H : ℂ) / 2 * (1 + xi)) • (A.map (algebraMap ℝ ℂ) *ᵥ v) =
        (xi - 1) • ((S.midpointE A H).map (algebraMap ℝ ℂ) *ᵥ v) :=
  eigen_iff (S.zoh_midpointE_complex A hA H hφ) (S.isUnit_det_midpointE_sub_complex A H hφ)

/-- **An eigenvalue of the zero-order hold gives an eigenvalue of the pencil, and the unit disc
is the left half plane.** If `H > 0`, `φ₁(H A₀)` is invertible, `X v = ξ v` for a complex `v`
and `ξ ≠ -1`, then `A v = θ E v` with `θ = (2/H) (ξ - 1)/(ξ + 1)`, and `|ξ| < 1 ↔ Re θ < 0`,
`|ξ| = 1 ↔ Re θ = 0`. -/
theorem zoh_pencil_of_eigen (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 < H) (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) {v : Fin n → ℂ} {xi : ℂ}
    (hxi : xi ≠ -1) (hv : (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v) :
    A.map (algebraMap ℝ ℂ) *ᵥ v =
        (2 / (H : ℂ) * (xi - 1) / (xi + 1)) • ((S.midpointE A H).map (algebraMap ℝ ℂ) *ᵥ v) ∧
      (‖xi‖ < 1 ↔ (2 / (H : ℂ) * (xi - 1) / (xi + 1)).re < 0) ∧
      (‖xi‖ = 1 ↔ (2 / (H : ℂ) * (xi - 1) / (xi + 1)).re = 0) :=
  ⟨pencil_of_eigen (S.zoh_midpointE_complex A hA H hφ) (Complex.ofReal_ne_zero.2 hH.ne') hxi hv,
    norm_lt_one_iff_cayley_re_neg hH hxi, norm_eq_one_iff_cayley_re_eq_zero hH hxi⟩

/-- **An eigenvalue of the pencil gives an eigenvalue of the zero-order hold.** If `φ₁(H A₀)` is
invertible and `A v = θ E v` for a complex `v ≠ 0`, then `1 - (H/2) θ ≠ 0` and `X v = ξ v` with
`ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`. -/
theorem zoh_eigen_of_pencil (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) {v : Fin n → ℂ} {theta : ℂ} (hv0 : v ≠ 0)
    (hv : A.map (algebraMap ℝ ℂ) *ᵥ v =
      theta • ((S.midpointE A H).map (algebraMap ℝ ℂ) *ᵥ v)) :
    1 - (H : ℂ) / 2 * theta ≠ 0 ∧
      (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v =
        ((1 + (H : ℂ) / 2 * theta) / (1 - (H : ℂ) / 2 * theta)) • v :=
  ⟨pencil_den_ne_zero (S.isUnit_det_midpointE_sub_complex A H hφ) hv0 hv,
    eigen_of_pencil (S.zoh_midpointE_complex A hA H hφ)
      (S.isUnit_det_midpointE_sub_complex A H hφ)
      (pencil_den_ne_zero (S.isUnit_det_midpointE_sub_complex A H hφ) hv0 hv) hv⟩

/-- **Stability of the zero-order hold on the eigenvalues, with the pencil.** If `H > 0` and
`φ₁(H A₀)` is invertible: every complex eigenvalue of the one-step map `X` has modulus less than
one if and only if `det E ≠ 0` and every eigenvalue `θ` of the pencil (`A v = θ E v` with a
complex `v ≠ 0`) has a negative real part. -/
theorem zoh_spectrum_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 < H) (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (∀ (xi : ℂ) (v : Fin n → ℂ), v ≠ 0 →
        (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v → ‖xi‖ < 1) ↔
      (S.midpointE A H).det ≠ 0 ∧
        ∀ (theta : ℂ) (v : Fin n → ℂ), v ≠ 0 →
          A.map (algebraMap ℝ ℂ) *ᵥ v =
            theta • ((S.midpointE A H).map (algebraMap ℝ ℂ) *ᵥ v) → theta.re < 0 := by
  have e : ((S.midpointE A H).map (algebraMap ℝ ℂ)).det =
      algebraMap ℝ ℂ (S.midpointE A H).det := (RingHom.map_det _ _).symm
  rw [spectrum_iff hH (S.zoh_midpointE_complex A hA H hφ)
    (S.isUnit_det_midpointE_sub_complex A H hφ), e, map_ne_zero]

/-- **Stability of the zero-order hold on the eigenvalues** (Corollary `cor:stability`, with
"asymptotically stable" read as "every eigenvalue of `X` lies in the open unit disc"). If
`H > 0` and `φ₁(H A₀)` is invertible: every complex eigenvalue of the one-step map `X` has
modulus less than one if and only if `E` is invertible and every complex eigenvalue of `E⁻¹ A`
has a negative real part. -/
theorem zoh_spectrum_iff_inv (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : 0 < H) (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (∀ (xi : ℂ) (v : Fin n → ℂ), v ≠ 0 →
        (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v → ‖xi‖ < 1) ↔
      IsUnit (S.midpointE A H).det ∧
        ∀ (theta : ℂ) (v : Fin n → ℂ), v ≠ 0 →
          ((S.midpointE A H)⁻¹ * A).map (algebraMap ℝ ℂ) *ᵥ v = theta • v → theta.re < 0 := by
  rw [S.zoh_spectrum_iff A hA hH hφ, isUnit_iff_ne_zero]
  refine and_congr_right fun hE => ?_
  have hi : ((S.midpointE A H)⁻¹).map (algebraMap ℝ ℂ) * (S.midpointE A H).map (algebraMap ℝ ℂ) =
      1 := by
    have h := congrArg (algebraMap ℝ ℂ).mapMatrix
      (Matrix.nonsing_inv_mul (S.midpointE A H) (isUnit_iff_ne_zero.2 hE))
    rwa [map_mul, map_one] at h
  have hm : ((S.midpointE A H)⁻¹ * A).map (algebraMap ℝ ℂ) =
      ((S.midpointE A H)⁻¹).map (algebraMap ℝ ℂ) * A.map (algebraMap ℝ ℂ) :=
    map_mul (algebraMap ℝ ℂ).mapMatrix _ _
  rw [hm]
  exact forall_congr' fun theta => forall_congr' fun v => imp_congr_right fun _ =>
    imp_congr_left (pencil_iff_of_left_inv hi)

end HeldScheme

end CoSimFoundations
