/-
The one-step map as the Cayley transform of `M = Ê⁻¹ Â` (the paper, stability corollary
`cor:stability`, the part that is not about eigenvalues).

**Paper.** For invertible `Ê` the one-step map is a function of `Ê⁻¹ Â`,
`X = (1 - (H/2) M)⁻¹ (1 + (H/2) M)`, `M = Ê⁻¹ Â`, so that the stability of `X` is that of `M`.

**Setting** (`MidpointStability`, section `Abstract`): square matrices `E`, `A`, `X` over a field
with `2 ≠ 0` and the midpoint form `E (X - 1) = (H/2) A (X + 1)`; `E` invertible. For a scheme
with one held sample the midpoint form is `pencil_midpoint` (`SchemePencil`), `E = pencilE`,
`A = pencilA H`.

**Statements** (`M = E⁻¹ A`):
* `one_sub_mul_step`: `(1 - (H/2) M) X = 1 + (H/2) M`.
* `one_sub_mul_add_one`: `(1 - (H/2) M) (X + 1) = 2`; hence `1 - (H/2) M` and `X + 1` are
  invertible (`isUnit_det_one_sub`, `isUnit_det_add_one`): no eigenvalue `-1`, and no hypothesis
  on `E - (H/2) A`.
* `step_eq_cayley`: `X = (1 - (H/2) M)⁻¹ (1 + (H/2) M)`.
* `commute_step`: `X M = M X`.
* `mul_add_one_eq`, `eq_inv_cayley`: `M (X + 1) = (2/H) (X - 1)` and
  `M = (2/H) (X - 1) (X + 1)⁻¹` for `H ≠ 0`: the inverse Cayley map.
* `conj_step`: the relation is carried by every change of basis: for invertible `P`,
  `(1 - (H/2) M') X' = 1 + (H/2) M'` with `M' = P⁻¹ M P`, `X' = P⁻¹ X P`. In a basis in which
  `M` has block form, `X` has the block form whose blocks are the Cayley transforms of the
  blocks of `M`.
* For a scheme with one held sample and invertible `Ê` (`HeldScheme.pencil_step_eq_cayley`,
  `HeldScheme.pencil_commute_step`, `HeldScheme.pencil_eq_inv_cayley`,
  `HeldScheme.isUnit_det_X_add_one`).

**What is not formalised.** The conclusion of the paper, that `X` is power-bounded exactly if
`exp (t M)` is bounded for `t ≥ 0`. It follows from the statements here and the Jordan form of
`M` (a Jordan block of `M` to `θ` gives a block of `X` to `ξ = (1 + Hθ/2)/(1 - Hθ/2)` of the
same size, and `|ξ| ≤ 1` iff `Re θ ≤ 0`, `norm_lt_one_iff_cayley_re_neg` and
`norm_eq_one_iff_cayley_re_eq_zero` of `MidpointStability`); the Jordan form is not in the
library.
-/
import CoSimFoundations.SchemePencil

open Matrix

namespace CoSimFoundations

namespace CayleyStep

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
variable {E A X : Matrix ι ι K} {H : K}

/-- **The one-step map and `M = E⁻¹ A`:** the midpoint form `E (X - 1) = (H/2) A (X + 1)` with
invertible `E` gives `(1 - (H/2) M) X = 1 + (H/2) M`. -/
theorem one_sub_mul_step (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) (hE : IsUnit E.det) :
    (1 - (H / 2) • (E⁻¹ * A)) * X = 1 + (H / 2) • (E⁻¹ * A) := by
  have hs := MidpointStability.step hmid
  have h1 : E⁻¹ * (E - (H / 2) • A) = 1 - (H / 2) • (E⁻¹ * A) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hE, Matrix.mul_smul]
  have h2 : E⁻¹ * (E + (H / 2) • A) = 1 + (H / 2) • (E⁻¹ * A) := by
    rw [Matrix.mul_add, Matrix.nonsing_inv_mul _ hE, Matrix.mul_smul]
  rw [← h1, Matrix.mul_assoc, hs, h2]

/-- `(1 - (H/2) M) (X + 1) = 2`. -/
theorem one_sub_mul_add_one (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hE : IsUnit E.det) :
    (1 - (H / 2) • (E⁻¹ * A)) * (X + 1) = (2 : K) • (1 : Matrix ι ι K) := by
  rw [Matrix.mul_add, Matrix.mul_one, one_sub_mul_step hmid hE, two_smul]
  abel

/-- `1 - (H/2) M` is invertible. -/
theorem isUnit_det_one_sub [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hE : IsUnit E.det) : IsUnit (1 - (H / 2) • (E⁻¹ * A)).det := by
  have h := congrArg Matrix.det (one_sub_mul_add_one hmid hE)
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h
  have h2 : (1 - (H / 2) • (E⁻¹ * A)).det * (X + 1).det ≠ 0 := by
    rw [h]
    exact pow_ne_zero _ (NeZero.ne 2)
  exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul h2)

/-- **The one-step map does not have the eigenvalue `-1` if `E` is invertible:** `X + 1` is
invertible. -/
theorem isUnit_det_add_one [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hE : IsUnit E.det) : IsUnit (X + 1).det := by
  have h := congrArg Matrix.det (one_sub_mul_add_one hmid hE)
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h
  have h2 : (1 - (H / 2) • (E⁻¹ * A)).det * (X + 1).det ≠ 0 := by
    rw [h]
    exact pow_ne_zero _ (NeZero.ne 2)
  exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h2)

/-- **The one-step map is the Cayley transform of `M = E⁻¹ A`** (the paper, `cor:stability`):
`X = (1 - (H/2) M)⁻¹ (1 + (H/2) M)`. -/
theorem step_eq_cayley [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hE : IsUnit E.det) :
    X = (1 - (H / 2) • (E⁻¹ * A))⁻¹ * (1 + (H / 2) • (E⁻¹ * A)) := by
  rw [← one_sub_mul_step hmid hE, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_one_sub hmid hE), Matrix.one_mul]

/-- A matrix `X` with `(1 - c M) X = 1 + c M` and invertible `1 - c M` commutes with `M`. -/
theorem commute_of_one_sub_mul {c : K} {M X : Matrix ι ι K}
    (h1 : (1 - c • M) * X = 1 + c • M) (hu : IsUnit (1 - c • M).det) : X * M = M * X := by
  have hc : (1 - c • M) * M = M * (1 - c • M) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  have key : (1 - c • M) * (X * M) = (1 - c • M) * (M * X) := by
    rw [← Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, h1, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  have h2 := congrArg (fun T => (1 - c • M)⁻¹ * T) key
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at h2
  exact h2

/-- **The one-step map commutes with `M = E⁻¹ A`.** -/
theorem commute_step [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hE : IsUnit E.det) : X * (E⁻¹ * A) = E⁻¹ * A * X :=
  commute_of_one_sub_mul (one_sub_mul_step hmid hE) (isUnit_det_one_sub hmid hE)

/-- `M (X + 1) = (2/H) (X - 1)` for `H ≠ 0`. -/
theorem mul_add_one_eq [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hE : IsUnit E.det) (hH : H ≠ 0) : E⁻¹ * A * (X + 1) = (2 / H) • (X - 1) := by
  have h1 : X - 1 = (H / 2) • (E⁻¹ * A * (X + 1)) := by
    have h2 := congrArg (fun T => E⁻¹ * T) hmid
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hE, Matrix.one_mul,
      Matrix.mul_smul] at h2
    exact h2
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  rw [h1, smul_smul]
  have h3 : 2 / H * (H / 2) = 1 := by
    field_simp
  rw [h3, one_smul]

/-- **The inverse Cayley map:** `M = (2/H) (X - 1) (X + 1)⁻¹` for `H ≠ 0`. -/
theorem eq_inv_cayley [NeZero (2 : K)] (hmid : E * (X - 1) = (H / 2) • (A * (X + 1)))
    (hE : IsUnit E.det) (hH : H ≠ 0) : E⁻¹ * A = (2 / H) • ((X - 1) * (X + 1)⁻¹) := by
  have h1 := mul_add_one_eq hmid hE hH
  have hu := isUnit_det_add_one hmid hE
  have h2 := congrArg (fun T => T * (X + 1)⁻¹) h1
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    Matrix.smul_mul] at h2
  exact h2

/-- The relation `(1 - c M) X = 1 + c M` in another basis: it holds for `P⁻¹ M P` and
`P⁻¹ X P`. -/
theorem conj_of_one_sub_mul {c : K} {M X P : Matrix ι ι K}
    (h1 : (1 - c • M) * X = 1 + c • M) (hP : IsUnit P.det) :
    (1 - c • (P⁻¹ * M * P)) * (P⁻¹ * X * P) = 1 + c • (P⁻¹ * M * P) := by
  have e1 : P⁻¹ * (1 - c • M) * P = 1 - c • (P⁻¹ * M * P) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP,
      Matrix.mul_smul, Matrix.smul_mul]
  have e2 : P⁻¹ * (1 + c • M) * P = 1 + c • (P⁻¹ * M * P) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [← e1, ← e2, ← h1]
  calc P⁻¹ * (1 - c • M) * P * (P⁻¹ * X * P)
      = P⁻¹ * (1 - c • M) * (P * P⁻¹) * X * P := by simp only [Matrix.mul_assoc]
    _ = P⁻¹ * ((1 - c • M) * X) * P := by
        rw [Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, Matrix.mul_assoc P⁻¹]

/-- **The relation in another basis:** for invertible `P`, with `M' = P⁻¹ M P` and
`X' = P⁻¹ X P`, `(1 - (H/2) M') X' = 1 + (H/2) M'`. -/
theorem conj_step (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) (hE : IsUnit E.det)
    {P : Matrix ι ι K} (hP : IsUnit P.det) :
    (1 - (H / 2) • (P⁻¹ * (E⁻¹ * A) * P)) * (P⁻¹ * X * P) =
      1 + (H / 2) • (P⁻¹ * (E⁻¹ * A) * P) :=
  conj_of_one_sub_mul (one_sub_mul_step hmid hE) hP

end CayleyStep

namespace HeldScheme

variable {n : ℕ} {κ : Type*} (S : HeldScheme n κ)

/-- **The one-step map of a scheme with one held sample is the Cayley transform of `Ê⁻¹ Â`**
(the paper, `cor:stability`): for `H ≠ 0` and invertible `Ê`,
`X = (1 - (H/2) M)⁻¹ (1 + (H/2) M)`, `M = Ê⁻¹ Â`. -/
theorem pencil_step_eq_cayley {H : ℝ} (hH : H ≠ 0) (hE : IsUnit S.pencilE.det) :
    S.X = (1 - (H / 2) • (S.pencilE⁻¹ * S.pencilA H))⁻¹ *
      (1 + (H / 2) • (S.pencilE⁻¹ * S.pencilA H)) :=
  CayleyStep.step_eq_cayley (S.pencil_midpoint hH) hE

/-- The one-step map of a scheme with invertible `Ê` commutes with `M = Ê⁻¹ Â`. -/
theorem pencil_commute_step {H : ℝ} (hH : H ≠ 0) (hE : IsUnit S.pencilE.det) :
    S.X * (S.pencilE⁻¹ * S.pencilA H) = S.pencilE⁻¹ * S.pencilA H * S.X :=
  CayleyStep.commute_step (S.pencil_midpoint hH) hE

/-- A scheme with invertible `Ê` does not have the eigenvalue `-1`: `X + 1` is invertible. -/
theorem isUnit_det_X_add_one (hE : IsUnit S.pencilE.det) : IsUnit (S.X + 1).det :=
  CayleyStep.isUnit_det_add_one (S.pencil_midpoint one_ne_zero) hE

/-- **`Ê⁻¹ Â` from the one-step map:** for `H ≠ 0` and invertible `Ê`,
`Ê⁻¹ Â = (2/H) (X - 1) (X + 1)⁻¹`. -/
theorem pencil_eq_inv_cayley {H : ℝ} (hH : H ≠ 0) (hE : IsUnit S.pencilE.det) :
    S.pencilE⁻¹ * S.pencilA H = (2 / H) • ((S.X - 1) * (S.X + 1)⁻¹) :=
  CayleyStep.eq_inv_cayley (S.pencil_midpoint hH) hE hH

end HeldScheme

end CoSimFoundations
