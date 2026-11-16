/-
The pencil `(Â, Ê)` of every scheme with one held sample, and the stability corollary for every
such scheme (the paper, Lemma `thm:half`, eq. `eq:pair`, and Corollary `cor:stability`,
eq. `eq:cayley`).

**Setting.** A `HeldScheme` `S`: local maps `F`, old samples `M = G^old C`, new samples
`N = G^new C`, one-step map `X = F + M + N X`. For a macro step `H`,
  `H Â = F - 1 + M + N` (`pencilHA`),   `Â = (F - 1 + M + N)/H` (`pencilA S H`),
  `Ê = ½ (1 + F) - ½ (N - M)` (`pencilE`).
`Ê` and `H Â` do not contain `H`; the statements with `Â` are those of the paper and need `H ≠ 0`
(the division), the statements with `H Â` need nothing.

**Statements.**
* (i) `pencil_midpoint_one`: `Ê (X - 1) = ½ (H Â) (X + 1)`; `pencil_midpoint`:
  `Ê (X - 1) = (H/2) Â (X + 1)` for `H ≠ 0`; `pencil_pair`: on a state,
  `Ê (x' - x)/H = Â (x' + x)/2` with `x' = X x` (eq. `eq:pair`). Proof: `held_midpoint_ring`.
* (ii) `pencilE_sub_one`, `pencilE_sub`: `Ê - ½ (H Â) = Ê - (H/2) Â = 1 - N`, so its determinant
  is `1` (`det_pencilE_sub`, from `det_one_sub_N` of `StoredEnergy`: new samples come only from
  earlier stages) and it is invertible. `pencil_step`: `(1 - N) X = Ê + (H/2) Â`.
* (iii) The statements of `MidpointStability` with `E := Ê`, `A := Â`, `H := H` (the paper's
  scaling; `pencil_neg_one_iff` uses `A := H Â`, `H := 1`, and so has no `H`):
  `pencil_neg_one_iff` (`X v = -v ↔ Ê v = 0`), `pencil_neg_one_eigenvalue_iff`,
  `pencil_eigen_iff` (real), `pencil_eigen_iff_complex`, `pencil_cayley_iff`
  (`X v = ξ v ↔ Â v = θ Ê v` for `ξ ≠ -1`, `θ = (2/H) (ξ - 1)/(ξ + 1)`, with
  `|ξ| < 1 ↔ Re θ < 0`), `pencil_eigen_of_pencil` (`ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`),
  `pencil_spectrum_iff` and `pencil_spectrum_iff_inv`: for `H > 0`, every complex eigenvalue of
  `X` has modulus `< 1` if and only if `Ê` is invertible and every complex eigenvalue of `Ê⁻¹ Â`
  has a negative real part.
* The zero-order hold `S.zoh A hA H`: `H Â = H φ A` (`zoh_pencilHA`), `Â = φ A` for `H ≠ 0`
  (`zoh_pencilA`), `Ê = 1 + (H/2) φ A₀ - (H/2) φ A_ς` (`zoh_pencilE_eq`) `= φ E` if
  `φ = φ₁(H A₀)` is invertible (`zoh_pencilE`), `E = midpointE` of `MidpointStability`.

The abstract statements `SchemePencil.cayley_iff`, `SchemePencil.real_spectrum_iff` and
`SchemePencil.real_spectrum_iff_inv` put the theorems of `MidpointStability` in the form that is
instantiated here (real matrices, complex eigenvalues).

**What is not here.** As in `MidpointStability`, "asymptotically stable" is stated on the
eigenvalues: all complex eigenvalues of `X` lie in the open unit disc. That the powers of `X` tend
to zero exactly then is not formalised in this module.
-/
import CoSimFoundations.MidpointStability
import CoSimFoundations.StoredEnergy

open Matrix

namespace CoSimFoundations

/-! ### The abstract statements in the form used below -/

namespace SchemePencil

open MidpointStability

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- **The Cayley transform of the pencil, on one vector.** If `E (X - 1) = (H/2) A (X + 1)`,
`E - (H/2) A` is invertible, `H ≠ 0`, `2 ≠ 0` and `ξ ≠ -1`, then `X v = ξ v` if and only if
`A v = θ E v` with `θ = (2/H) (ξ - 1)/(ξ + 1)`, that is `ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`. -/
theorem cayley_iff [NeZero (2 : K)] {E A X : Matrix ι ι K} {H : K}
    (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) (hdet : IsUnit (E - (H / 2) • A).det)
    (hH : H ≠ 0) {v : ι → K} {xi : K} (hxi : xi ≠ -1) :
    X *ᵥ v = xi • v ↔ A *ᵥ v = (2 / H * (xi - 1) / (xi + 1)) • (E *ᵥ v) := by
  refine ⟨pencil_of_eigen hmid hH hxi, fun h => ?_⟩
  have h2 := eigen_of_pencil hmid hdet (cayley_inv_den_ne_zero hH hxi) h
  rwa [cayley_cayley_inv hH hxi] at h2

/-- **Stability on the complex eigenvalues, for real matrices.** Real matrices with
`E (X - 1) = (H/2) A (X + 1)`, `H > 0` and `E - (H/2) A` invertible: every complex eigenvalue of
`X` has modulus less than one if and only if `det E ≠ 0` and every complex eigenvalue `θ` of the
pencil (`A v = θ E v`, `v ≠ 0`) has a negative real part. -/
theorem real_spectrum_iff {E A X : Matrix ι ι ℝ} {H : ℝ} (hH : 0 < H)
    (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) (hdet : IsUnit (E - (H / 2) • A).det) :
    (∀ (xi : ℂ) (v : ι → ℂ), v ≠ 0 → X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v → ‖xi‖ < 1) ↔
      E.det ≠ 0 ∧
        ∀ (theta : ℂ) (v : ι → ℂ), v ≠ 0 →
          A.map (algebraMap ℝ ℂ) *ᵥ v = theta • (E.map (algebraMap ℝ ℂ) *ᵥ v) →
            theta.re < 0 := by
  have e : (E.map (algebraMap ℝ ℂ)).det = algebraMap ℝ ℂ E.det := (RingHom.map_det _ _).symm
  rw [spectrum_iff hH (midpoint_map (algebraMap ℝ ℂ) hmid)
    (isUnit_det_map (algebraMap ℝ ℂ) hdet), e, map_ne_zero]

/-- **Stability on the complex eigenvalues, with `E⁻¹ A`.** Real matrices with
`E (X - 1) = (H/2) A (X + 1)`, `H > 0` and `E - (H/2) A` invertible: every complex eigenvalue of
`X` has modulus less than one if and only if `E` is invertible and every complex eigenvalue of
`E⁻¹ A` has a negative real part. -/
theorem real_spectrum_iff_inv {E A X : Matrix ι ι ℝ} {H : ℝ} (hH : 0 < H)
    (hmid : E * (X - 1) = (H / 2) • (A * (X + 1))) (hdet : IsUnit (E - (H / 2) • A).det) :
    (∀ (xi : ℂ) (v : ι → ℂ), v ≠ 0 → X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v → ‖xi‖ < 1) ↔
      IsUnit E.det ∧
        ∀ (theta : ℂ) (v : ι → ℂ), v ≠ 0 →
          (E⁻¹ * A).map (algebraMap ℝ ℂ) *ᵥ v = theta • v → theta.re < 0 := by
  rw [real_spectrum_iff hH hmid hdet, isUnit_iff_ne_zero]
  refine and_congr_right fun hE => ?_
  have hi : (E⁻¹).map (algebraMap ℝ ℂ) * E.map (algebraMap ℝ ℂ) = 1 := by
    have h := congrArg (algebraMap ℝ ℂ).mapMatrix
      (Matrix.nonsing_inv_mul E (isUnit_iff_ne_zero.2 hE))
    rwa [map_mul, map_one] at h
  have hm : (E⁻¹ * A).map (algebraMap ℝ ℂ) =
      (E⁻¹).map (algebraMap ℝ ℂ) * A.map (algebraMap ℝ ℂ) :=
    map_mul (algebraMap ℝ ℂ).mapMatrix _ _
  rw [hm]
  exact forall_congr' fun theta => forall_congr' fun v => imp_congr_right fun _ =>
    imp_congr_left (pencil_iff_of_left_inv hi)

end SchemePencil

namespace HeldScheme

open MidpointStability

variable {n : ℕ}

section Pencil

variable {κ : Type*} (S : HeldScheme n κ)

/-! ### The pencil of a scheme -/

/-- `H Â = F - 1 + GC = F - 1 + M + N`: what the scheme integrates, times the macro step. -/
def pencilHA : Matrix (Fin n) (Fin n) ℝ := S.F - 1 + S.M + S.N

/-- `Â = (F - 1 + GC)/H`, the matrix that the scheme integrates (eq. `eq:pair`). -/
noncomputable def pencilA (H : ℝ) : Matrix (Fin n) (Fin n) ℝ := H⁻¹ • S.pencilHA

/-- `Ê = ½ (1 + F) - ½ (G^new - G^old) C = ½ (1 + F) - ½ (N - M)` (eq. `eq:pair`). -/
noncomputable def pencilE : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (1 + S.F) - (1 / 2 : ℝ) • (S.N - S.M)

/-- `(H/2) Â = ½ (H Â)` for `H ≠ 0`. -/
theorem half_smul_pencilA {H : ℝ} (hH : H ≠ 0) :
    (H / 2) • S.pencilA H = (1 / 2 : ℝ) • S.pencilHA := by
  rw [pencilA, smul_smul]
  congr 1
  field_simp

/-! ### (i) The midpoint identity -/

/-- **(i) The midpoint identity of every scheme with one held sample, without a division:**
`Ê (X - 1) = ½ (H Â) (X + 1)` with `H Â = F - 1 + M + N`. -/
theorem pencil_midpoint_one :
    S.pencilE * (S.X - 1) = ((1 : ℝ) / 2) • (S.pencilHA * (S.X + 1)) := by
  rw [pencilE, pencilHA, ← smul_sub, smul_mul_assoc, held_midpoint_ring S.hX]

/-- **(i) The midpoint identity of every scheme with one held sample** (eq. `eq:pair` as a matrix
identity): for `H ≠ 0`, `Ê (X - 1) = (H/2) Â (X + 1)`. -/
theorem pencil_midpoint {H : ℝ} (hH : H ≠ 0) :
    S.pencilE * (S.X - 1) = (H / 2) • (S.pencilA H * (S.X + 1)) := by
  rw [← smul_mul_assoc, S.half_smul_pencilA hH, smul_mul_assoc]
  exact S.pencil_midpoint_one

/-- **(i) Eq. `eq:pair` on a state:** for `H ≠ 0` and `x' = X x`,
`Ê (x' - x)/H = Â (x' + x)/2`. -/
theorem pencil_pair {H : ℝ} (hH : H ≠ 0) (x : Fin n → ℝ) :
    S.pencilE *ᵥ (H⁻¹ • (S.X *ᵥ x - x)) = S.pencilA H *ᵥ ((1 / 2 : ℝ) • (S.X *ᵥ x + x)) := by
  have h := midpoint_mulVec (S.pencil_midpoint hH) x
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, h, smul_smul]
  congr 1
  field_simp

/-! ### (ii) `Ê - (H/2) Â = 1 - N` -/

/-- **(ii) without a division:** `Ê - ½ (H Â) = 1 - N`. -/
theorem pencilE_sub_one : S.pencilE - (1 / 2 : ℝ) • S.pencilHA = 1 - S.N := by
  rw [pencilE, pencilHA]
  module

/-- **(ii)** For `H ≠ 0`, `Ê - (H/2) Â = 1 - N = 1 - G^new C`. -/
theorem pencilE_sub {H : ℝ} (hH : H ≠ 0) : S.pencilE - (H / 2) • S.pencilA H = 1 - S.N := by
  rw [S.half_smul_pencilA hH, S.pencilE_sub_one]

/-- **(ii)** `det (Ê - ½ (H Â)) = 1`: new samples come only from earlier stages. -/
theorem det_pencilE_sub_one : (S.pencilE - (1 / 2 : ℝ) • S.pencilHA).det = 1 := by
  rw [S.pencilE_sub_one, S.det_one_sub_N]

/-- **(ii)** For `H ≠ 0`, `det (Ê - (H/2) Â) = 1`. -/
theorem det_pencilE_sub {H : ℝ} (hH : H ≠ 0) : (S.pencilE - (H / 2) • S.pencilA H).det = 1 := by
  rw [S.pencilE_sub hH, S.det_one_sub_N]

/-- **(ii)** `Ê - ½ (H Â)` is invertible, for every scheme with one held sample. -/
theorem isUnit_det_pencilE_sub_one : IsUnit (S.pencilE - (1 / 2 : ℝ) • S.pencilHA).det := by
  rw [S.det_pencilE_sub_one]
  exact isUnit_one

/-- **(ii)** For `H ≠ 0`, `Ê - (H/2) Â` is invertible, for every scheme with one held sample. -/
theorem isUnit_det_pencilE_sub {H : ℝ} (hH : H ≠ 0) :
    IsUnit (S.pencilE - (H / 2) • S.pencilA H).det := by
  rw [S.det_pencilE_sub hH]
  exact isUnit_one

/-- **The one-step map from the pencil:** for `H ≠ 0`, `(1 - N) X = Ê + (H/2) Â`. -/
theorem pencil_step {H : ℝ} (hH : H ≠ 0) :
    (1 - S.N) * S.X = S.pencilE + (H / 2) • S.pencilA H := by
  rw [← S.pencilE_sub hH]
  exact step (S.pencil_midpoint hH)

/-! ### (iii) The eigenvalues of the one-step map and of the pencil -/

/-- **(iii) The step that changes the sign, for every scheme with one held sample:** `X v = -v`
if and only if `Ê v = 0`. -/
theorem pencil_neg_one_iff {v : Fin n → ℝ} : S.X *ᵥ v = -v ↔ S.pencilE *ᵥ v = 0 :=
  neg_one_iff S.pencil_midpoint_one S.isUnit_det_pencilE_sub_one

/-- **(iii) `-1` is an eigenvalue of the one-step map if and only if `Ê` is singular.** -/
theorem pencil_neg_one_eigenvalue_iff :
    (∃ v : Fin n → ℝ, v ≠ 0 ∧ S.X *ᵥ v = -v) ↔ S.pencilE.det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact exists_congr fun v => and_congr_right fun _ => S.pencil_neg_one_iff

/-- **(iii) The real eigenvectors of the one-step map:** for `H ≠ 0`, `X v = ξ v` if and only if
`(H/2) (1 + ξ) Â v = (ξ - 1) Ê v`. -/
theorem pencil_eigen_iff {H : ℝ} (hH : H ≠ 0) {v : Fin n → ℝ} {xi : ℝ} :
    S.X *ᵥ v = xi • v ↔
      (H / 2 * (1 + xi)) • (S.pencilA H *ᵥ v) = (xi - 1) • (S.pencilE *ᵥ v) :=
  eigen_iff (S.pencil_midpoint hH) (S.isUnit_det_pencilE_sub hH)

/-- The midpoint identity for the complexified matrices. -/
theorem pencil_midpoint_complex {H : ℝ} (hH : H ≠ 0) :
    S.pencilE.map (algebraMap ℝ ℂ) * (S.X.map (algebraMap ℝ ℂ) - 1) =
      ((H : ℂ) / 2) • ((S.pencilA H).map (algebraMap ℝ ℂ) * (S.X.map (algebraMap ℝ ℂ) + 1)) :=
  midpoint_map (algebraMap ℝ ℂ) (S.pencil_midpoint hH)

/-- `Ê - (H/2) Â` is invertible as a complex matrix. -/
theorem isUnit_det_pencilE_sub_complex {H : ℝ} (hH : H ≠ 0) :
    IsUnit (S.pencilE.map (algebraMap ℝ ℂ) -
      ((H : ℂ) / 2) • (S.pencilA H).map (algebraMap ℝ ℂ)).det :=
  isUnit_det_map (algebraMap ℝ ℂ) (S.isUnit_det_pencilE_sub hH)

/-- **(iii) The step that changes the sign, complex vectors:** `X v = -v` if and only if
`Ê v = 0`. -/
theorem pencil_neg_one_iff_complex {v : Fin n → ℂ} :
    S.X.map (algebraMap ℝ ℂ) *ᵥ v = -v ↔ S.pencilE.map (algebraMap ℝ ℂ) *ᵥ v = 0 :=
  neg_one_iff (midpoint_map (algebraMap ℝ ℂ) S.pencil_midpoint_one)
    (isUnit_det_map (algebraMap ℝ ℂ) S.isUnit_det_pencilE_sub_one)

/-- **(iii) The complex eigenvectors of the one-step map:** for `H ≠ 0`, a complex vector `v`
and a complex `ξ`, `X v = ξ v` if and only if `(H/2) (1 + ξ) Â v = (ξ - 1) Ê v`. -/
theorem pencil_eigen_iff_complex {H : ℝ} (hH : H ≠ 0) {v : Fin n → ℂ} {xi : ℂ} :
    S.X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v ↔
      ((H : ℂ) / 2 * (1 + xi)) • ((S.pencilA H).map (algebraMap ℝ ℂ) *ᵥ v) =
        (xi - 1) • (S.pencilE.map (algebraMap ℝ ℂ) *ᵥ v) :=
  eigen_iff (S.pencil_midpoint_complex hH) (S.isUnit_det_pencilE_sub_complex hH)

/-- **(iii) The one-step map of every scheme with one held sample is the Cayley transform of the
pencil `(Â, Ê)`** (eq. `eq:cayley`). For `H > 0`, a complex vector `v` and a complex `ξ ≠ -1`:
`X v = ξ v` if and only if `Â v = θ Ê v` with `θ = (2/H) (ξ - 1)/(ξ + 1)` (that is
`ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`), and `|ξ| < 1 ↔ Re θ < 0`, `|ξ| = 1 ↔ Re θ = 0`. The case
`ξ = -1` is `pencil_neg_one_iff_complex`. -/
theorem pencil_cayley_iff {H : ℝ} (hH : 0 < H) {v : Fin n → ℂ} {xi : ℂ} (hxi : xi ≠ -1) :
    (S.X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v ↔
        (S.pencilA H).map (algebraMap ℝ ℂ) *ᵥ v =
          (2 / (H : ℂ) * (xi - 1) / (xi + 1)) • (S.pencilE.map (algebraMap ℝ ℂ) *ᵥ v)) ∧
      (‖xi‖ < 1 ↔ (2 / (H : ℂ) * (xi - 1) / (xi + 1)).re < 0) ∧
      (‖xi‖ = 1 ↔ (2 / (H : ℂ) * (xi - 1) / (xi + 1)).re = 0) :=
  ⟨SchemePencil.cayley_iff (S.pencil_midpoint_complex hH.ne')
      (S.isUnit_det_pencilE_sub_complex hH.ne') (Complex.ofReal_ne_zero.2 hH.ne') hxi,
    norm_lt_one_iff_cayley_re_neg hH hxi, norm_eq_one_iff_cayley_re_eq_zero hH hxi⟩

/-- **(iii) An eigenvalue of the pencil gives an eigenvalue of the one-step map.** If `H ≠ 0`
and `Â v = θ Ê v` for a complex `v ≠ 0`, then `1 - (H/2) θ ≠ 0` and `X v = ξ v` with
`ξ = (1 + (H/2) θ)/(1 - (H/2) θ)`. -/
theorem pencil_eigen_of_pencil {H : ℝ} (hH : H ≠ 0) {v : Fin n → ℂ} {theta : ℂ} (hv0 : v ≠ 0)
    (hv : (S.pencilA H).map (algebraMap ℝ ℂ) *ᵥ v =
      theta • (S.pencilE.map (algebraMap ℝ ℂ) *ᵥ v)) :
    1 - (H : ℂ) / 2 * theta ≠ 0 ∧
      S.X.map (algebraMap ℝ ℂ) *ᵥ v =
        ((1 + (H : ℂ) / 2 * theta) / (1 - (H : ℂ) / 2 * theta)) • v :=
  ⟨pencil_den_ne_zero (S.isUnit_det_pencilE_sub_complex hH) hv0 hv,
    eigen_of_pencil (S.pencil_midpoint_complex hH) (S.isUnit_det_pencilE_sub_complex hH)
      (pencil_den_ne_zero (S.isUnit_det_pencilE_sub_complex hH) hv0 hv) hv⟩

/-- **(iii) Stability of every scheme with one held sample on the eigenvalues, with the
pencil.** For `H > 0`: every complex eigenvalue of the one-step map `X` has modulus less than one
if and only if `det Ê ≠ 0` and every eigenvalue `θ` of the pencil (`Â v = θ Ê v` with a complex
`v ≠ 0`) has a negative real part. -/
theorem pencil_spectrum_iff {H : ℝ} (hH : 0 < H) :
    (∀ (xi : ℂ) (v : Fin n → ℂ), v ≠ 0 →
        S.X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v → ‖xi‖ < 1) ↔
      S.pencilE.det ≠ 0 ∧
        ∀ (theta : ℂ) (v : Fin n → ℂ), v ≠ 0 →
          (S.pencilA H).map (algebraMap ℝ ℂ) *ᵥ v =
            theta • (S.pencilE.map (algebraMap ℝ ℂ) *ᵥ v) → theta.re < 0 :=
  SchemePencil.real_spectrum_iff hH (S.pencil_midpoint hH.ne') (S.isUnit_det_pencilE_sub hH.ne')

/-- **(iii) Stability of every scheme with one held sample on the eigenvalues** (Corollary
`cor:stability`, with "asymptotically stable" read as "every eigenvalue of `X` lies in the open
unit disc"). For `H > 0`: every complex eigenvalue of the one-step map `X` has modulus less than
one if and only if `Ê` is invertible and every complex eigenvalue of `Ê⁻¹ Â` has a negative real
part. -/
theorem pencil_spectrum_iff_inv {H : ℝ} (hH : 0 < H) :
    (∀ (xi : ℂ) (v : Fin n → ℂ), v ≠ 0 →
        S.X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v → ‖xi‖ < 1) ↔
      IsUnit S.pencilE.det ∧
        ∀ (theta : ℂ) (v : Fin n → ℂ), v ≠ 0 →
          (S.pencilE⁻¹ * S.pencilA H).map (algebraMap ℝ ℂ) *ᵥ v = theta • v → theta.re < 0 :=
  SchemePencil.real_spectrum_iff_inv hH (S.pencil_midpoint hH.ne')
    (S.isUnit_det_pencilE_sub hH.ne')

end Pencil

/-! ### The pencil of the zero-order hold -/

section ZOH

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- **`H Â` of the zero-order hold:** `F - 1 + M + N = H φ A`, `φ = φ₁(H A₀)`. -/
theorem zoh_pencilHA (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (S.zoh A hA H).pencilHA = H • (phiOne (H • S.blockDiag A) * A) := by
  have hF : NormedSpace.exp (H • S.blockDiag A) =
      1 + H • (phiOne (H • S.blockDiag A) * S.blockDiag A) := by
    rw [exp_eq_one_add_phiOne_mul, mul_smul_comm]
  have hN : S.zohNew A H = H • (phiOne (H • S.blockDiag A) * S.couplingNew A) := by
    rw [S.zohNew_eq, zohKernel, smul_mul_assoc]
  have hM : S.zohOld A H = H • (phiOne (H • S.blockDiag A) * S.couplingOld A) := by
    rw [S.zohOld_eq, zohKernel, smul_mul_assoc]
  have hA' : phiOne (H • S.blockDiag A) * A =
      phiOne (H • S.blockDiag A) * S.blockDiag A +
        (phiOne (H • S.blockDiag A) * S.couplingOld A +
          phiOne (H • S.blockDiag A) * S.couplingNew A) := by
    rw [← mul_add, ← mul_add, S.couplingOld_add_couplingNew, S.blockDiag_add_coupling]
  change NormedSpace.exp (H • S.blockDiag A) - 1 + S.zohOld A H + S.zohNew A H = _
  rw [hF, hN, hM, hA']
  module

/-- **`Â` of the zero-order hold:** for `H ≠ 0`, `Â = φ A`, `φ = φ₁(H A₀)`. -/
theorem zoh_pencilA (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : H ≠ 0) : (S.zoh A hA H).pencilA H = phiOne (H • S.blockDiag A) * A := by
  rw [pencilA, S.zoh_pencilHA A hA H, smul_smul, inv_mul_cancel₀ hH, one_smul]

/-- **`Ê` of the zero-order hold, without an inverse:**
`Ê = 1 + (H/2) φ A₀ - (H/2) φ A_ς`, `φ = φ₁(H A₀)`. -/
theorem zoh_pencilE_eq (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (S.zoh A hA H).pencilE =
      1 + (H / 2) • (phiOne (H • S.blockDiag A) * S.blockDiag A) -
        (H / 2) • (phiOne (H • S.blockDiag A) * S.signedCoupling A) := by
  have hF : NormedSpace.exp (H • S.blockDiag A) =
      1 + H • (phiOne (H • S.blockDiag A) * S.blockDiag A) := by
    rw [exp_eq_one_add_phiOne_mul, mul_smul_comm]
  have hN : S.zohNew A H = H • (phiOne (H • S.blockDiag A) * S.couplingNew A) := by
    rw [S.zohNew_eq, zohKernel, smul_mul_assoc]
  have hM : S.zohOld A H = H • (phiOne (H • S.blockDiag A) * S.couplingOld A) := by
    rw [S.zohOld_eq, zohKernel, smul_mul_assoc]
  have hς : phiOne (H • S.blockDiag A) * S.signedCoupling A =
      phiOne (H • S.blockDiag A) * S.couplingNew A -
        phiOne (H • S.blockDiag A) * S.couplingOld A := by
    rw [← mul_sub, S.couplingNew_sub_couplingOld]
  change (1 / 2 : ℝ) • (1 + NormedSpace.exp (H • S.blockDiag A)) -
    (1 / 2 : ℝ) • (S.zohNew A H - S.zohOld A H) = _
  rw [hF, hN, hM, hς]
  module

/-- **`Ê` of the zero-order hold:** if `φ = φ₁(H A₀)` is invertible, `Ê = φ E` with
`E = Ψ - (H/2) A_ς` (`midpointE`), the matrix of eq. `eq:midpoint`. -/
theorem zoh_pencilE (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ)
    (hφ : IsUnit (phiOne (H • S.blockDiag A)).det) :
    (S.zoh A hA H).pencilE = phiOne (H • S.blockDiag A) * S.midpointE A H := by
  rw [S.zoh_pencilE_eq A hA H, midpointE, midpointPsi, mul_sub, mul_add,
    Matrix.mul_nonsing_inv _ hφ, mul_smul_comm, mul_smul_comm]

end ZOH

end HeldScheme

end CoSimFoundations
