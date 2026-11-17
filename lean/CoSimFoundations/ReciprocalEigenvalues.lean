/-
Reciprocal eigenvalues (the paper, Corollary `cor:stability` and the paragraph after equation
`eq:tree`): the eigenvalues `θ` of the pencil `(Â, Ê)` of a
scheme, written as `1/θ`.

**(a) Every scheme with one held sample** (`reciprocal_cayley_inv`,
`smul_eq_smul_iff_reciprocal`, `HeldScheme.pencil_reciprocal_iff_complex`,
`HeldScheme.pencil_reciprocal_iff`, `HeldScheme.pencil_cayley_reciprocal`). For `ξ ≠ ±1` and
`θ = (2/H) (ξ - 1)/(ξ + 1)`: `1/θ = H/2 + H/(ξ - 1)`. On the vectors: for `ξ ≠ 1`,
  `X v = ξ v`   if and only if   `Ê v = (H/2 + H/(ξ - 1)) Â v`
(from `pencil_eigen_iff`, `(H/2) (1 + ξ) Â v = (ξ - 1) Ê v`); for `ξ = -1` the factor is zero and
this is `Ê v = 0`.

**(b) The zero-order hold in a Jacobi scheme** (`HeldScheme.zoh_X_sub_one_of_jacobi`,
`HeldScheme.zoh_jacobi_eigen_iff_complex`, `HeldScheme.zoh_jacobi_reciprocal`). If all
subsystems run at the same stage, `X - 1 = H φ A`, `φ = φ₁(H A₀)`: no sample is new, and
`F - 1 + M = H φ A` (`zoh_pencilHA`). Hence `X v = ξ v` if and only if `φ A v = ((ξ - 1)/H) v`,
and for an eigenvalue `λ̂ ≠ 0` of `φ A` with eigenvector `v`: `Ê v = (H/2 + 1/λ̂) Â v`.

**(c) A stage offset and subsystems without dynamics** (`HeldScheme.det_sq_sub_X_one_of_offset`,
`HeldScheme.exists_eigenvector_X_sq_iff_of_offset_one`, `HeldScheme.zoh_eigen_sq_iff_of_offset`,
`reciprocal_sq_eq`, `HeldScheme.zoh_reciprocal_sq_of_offset`). If `F = 1` and the stages have a
stage offset (`Offsets`), then for `s ≠ 0` in a field `𝕜 ⊇ ℝ`
  `det(s² - X) = sⁿ det((s - 1/s) - (N + M))`,
so `s²` is an eigenvalue of `X` if and only if `s - 1/s` is an eigenvalue of `G C = N + M`. For
the zero-order hold with `A₀ = 0`, `N + M = H A`: `s²` is an eigenvalue of `X` if and only if
`λ = (s - 1/s)/H` is an eigenvalue of `A`. The scalar identity: if `H λ = s - 1/s`, `s ≠ 0`,
`s² ≠ ±1` and `θ = (2/H) (s² - 1)/(s² + 1)`, then `1/θ² = 1/λ² + (H/2)²`.
-/
import CoSimFoundations.SchemePencil
import CoSimFoundations.GraphOrder
import CoSimFoundations.Offsets

open Matrix

namespace CoSimFoundations

/-! ### Scalars and vectors -/

section Scalar

variable {K : Type*} [Field K]

/-- **The reciprocal of the Cayley parameter:** for `H ≠ 0`, `ξ ≠ 1`, `ξ ≠ -1` and
`θ = (2/H) (ξ - 1)/(ξ + 1)`: `1/θ = H/2 + H/(ξ - 1)`. -/
theorem reciprocal_cayley_inv [NeZero (2 : K)] {H xi : K} (hH : H ≠ 0) (hxi1 : xi ≠ 1)
    (hxi : xi ≠ -1) : (2 / H * (xi - 1) / (xi + 1))⁻¹ = H / 2 + H / (xi - 1) := by
  have h1 : xi + 1 ≠ 0 := fun h => hxi (eq_neg_of_add_eq_zero_left h)
  have h2 : xi - 1 ≠ 0 := sub_ne_zero.2 hxi1
  have h3 : (2 : K) ≠ 0 := NeZero.ne 2
  field_simp
  ring

/-- **The pencil relation in reciprocal form:** for `ξ ≠ 1`,
`(H/2) (1 + ξ) u = (ξ - 1) w` if and only if `w = (H/2 + H/(ξ - 1)) u`. -/
theorem smul_eq_smul_iff_reciprocal [NeZero (2 : K)] {ι : Type*} {u w : ι → K} {H xi : K}
    (hxi : xi ≠ 1) :
    (H / 2 * (1 + xi)) • u = (xi - 1) • w ↔ w = (H / 2 + H / (xi - 1)) • u := by
  have h2 : xi - 1 ≠ 0 := sub_ne_zero.2 hxi
  have h3 : (2 : K) ≠ 0 := NeZero.ne 2
  have e : H / 2 + H / (xi - 1) = (xi - 1)⁻¹ * (H / 2 * (1 + xi)) := by
    field_simp
    ring
  constructor
  · intro h
    rw [e, mul_smul, h, smul_smul, inv_mul_cancel₀ h2, one_smul]
  · intro h
    rw [h, smul_smul, e, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- **The scalar identity of the reciprocal squares:** if `H λ = s - 1/s` with `H ≠ 0`, `s ≠ 0`,
`s² ≠ 1`, `s² ≠ -1`, and `θ = (2/H) (s² - 1)/(s² + 1)` (the Cayley parameter of `ξ = s²`), then
`1/θ² = 1/λ² + (H/2)²`. -/
theorem reciprocal_sq_eq [NeZero (2 : K)] {H s lam : K} (hH : H ≠ 0) (hs : s ≠ 0)
    (hs1 : s ^ 2 ≠ 1) (hs2 : s ^ 2 ≠ -1) (hlam : H * lam = s - s⁻¹) :
    ((2 / H * (s ^ 2 - 1) / (s ^ 2 + 1)) ^ 2)⁻¹ = (lam ^ 2)⁻¹ + (H / 2) ^ 2 := by
  have h1 : s ^ 2 + 1 ≠ 0 := fun h => hs2 (eq_neg_of_add_eq_zero_left h)
  have h2 : s ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hs1
  have h3 : (2 : K) ≠ 0 := NeZero.ne 2
  have h4 : lam * (s * H) = s ^ 2 - 1 := by
    have h := congrArg (fun t => s * t) hlam
    simp only [mul_sub, mul_inv_cancel₀ hs] at h
    linear_combination h
  rw [eq_div_of_mul_eq (mul_ne_zero hs hH) h4]
  field_simp
  ring

/-- A scalar `t` is an eigenvalue of a matrix `M` over a field if and only if
`det(t - M) = 0`. -/
theorem exists_eigenvector_iff_det_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (t : K) :
    (∃ v : ι → K, v ≠ 0 ∧ M *ᵥ v = t • v) ↔ (t • (1 : Matrix ι ι K) - M).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]

end Scalar

namespace HeldScheme

variable {n : ℕ} {κ : Type*} (S : HeldScheme n κ)

/-! ### (a) Every scheme with one held sample -/

/-- **The pencil in reciprocal form, complex vectors:** for `H ≠ 0`, a complex vector `v` and a
complex `ξ ≠ 1`, `X v = ξ v` if and only if `Ê v = (H/2 + H/(ξ - 1)) Â v`. -/
theorem pencil_reciprocal_iff_complex {H : ℝ} (hH : H ≠ 0) {v : Fin n → ℂ} {xi : ℂ}
    (hxi : xi ≠ 1) :
    S.X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v ↔
      S.pencilE.map (algebraMap ℝ ℂ) *ᵥ v =
        ((H : ℂ) / 2 + (H : ℂ) / (xi - 1)) • ((S.pencilA H).map (algebraMap ℝ ℂ) *ᵥ v) :=
  (S.pencil_eigen_iff_complex hH).trans (smul_eq_smul_iff_reciprocal hxi)

/-- **The pencil in reciprocal form, real vectors:** for `H ≠ 0` and a real `ξ ≠ 1`,
`X v = ξ v` if and only if `Ê v = (H/2 + H/(ξ - 1)) Â v`. -/
theorem pencil_reciprocal_iff {H : ℝ} (hH : H ≠ 0) {v : Fin n → ℝ} {xi : ℝ} (hxi : xi ≠ 1) :
    S.X *ᵥ v = xi • v ↔
      S.pencilE *ᵥ v = (H / 2 + H / (xi - 1)) • (S.pencilA H *ᵥ v) :=
  (S.pencil_eigen_iff hH).trans (smul_eq_smul_iff_reciprocal hxi)

/-- **Reciprocal eigenvalues of every scheme with one held sample:** for `H > 0` and an
eigenpair `X v = ξ v` with `ξ ≠ 1`, `ξ ≠ -1`, the Cayley parameter
`θ = (2/H) (ξ - 1)/(ξ + 1)` obeys `Â v = θ Ê v` and `1/θ = H/2 + H/(ξ - 1)`. -/
theorem pencil_cayley_reciprocal {H : ℝ} (hH : 0 < H) {v : Fin n → ℂ} {xi : ℂ} (hxi1 : xi ≠ 1)
    (hxi : xi ≠ -1) (hv : S.X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v) :
    (S.pencilA H).map (algebraMap ℝ ℂ) *ᵥ v =
        (2 / (H : ℂ) * (xi - 1) / (xi + 1)) • (S.pencilE.map (algebraMap ℝ ℂ) *ᵥ v) ∧
      (2 / (H : ℂ) * (xi - 1) / (xi + 1))⁻¹ = (H : ℂ) / 2 + (H : ℂ) / (xi - 1) :=
  ⟨((S.pencil_cayley_iff hH hxi).1).1 hv,
    reciprocal_cayley_inv (Complex.ofReal_ne_zero.2 hH.ne') hxi1 hxi⟩

/-! ### (c) A stage offset and subsystems without dynamics -/

section Field

variable {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜]

/-- **The eigenvalue equation for `F = 1` with a stage offset:** for `s ≠ 0` in a field
`𝕜 ⊇ ℝ`, `det(s² - X) = sⁿ det((s - 1/s) - (N + M))`. -/
theorem det_sq_sub_X_one_of_offset {p : κ → ℤ} (hp : S.IsStageOffset p) (hF : S.F = 1) {s : 𝕜}
    (hs : s ≠ 0) :
    (s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.X.map (algebraMap ℝ 𝕜)).det =
      s ^ n * ((s - s⁻¹) • (1 : Matrix (Fin n) (Fin n) 𝕜) -
        (S.N + S.M).map (algebraMap ℝ 𝕜)).det := by
  have h := S.det_sq_sub_X_of_offset (𝕜 := 𝕜) hp s
  have e : s ^ 2 • (1 : Matrix (Fin n) (Fin n) 𝕜) - S.F.map (algebraMap ℝ 𝕜) -
      s • (S.N + S.M).map (algebraMap ℝ 𝕜) =
      s • ((s - s⁻¹) • (1 : Matrix (Fin n) (Fin n) 𝕜) - (S.N + S.M).map (algebraMap ℝ 𝕜)) := by
    have h1 : s * (s - s⁻¹) = s ^ 2 - 1 := by
      field_simp
    rw [hF, Matrix.map_one _ (map_zero _) (map_one _), smul_sub, smul_smul, h1, sub_smul,
      one_smul]
  rw [h, e, det_smul, Fintype.card_fin]

/-- **`s²` is an eigenvalue of `X` if and only if `s - 1/s` is an eigenvalue of `G C`:** for a
scheme with `F = 1` and a stage offset, and `s ≠ 0` in a field `𝕜 ⊇ ℝ`. -/
theorem exists_eigenvector_X_sq_iff_of_offset_one {p : κ → ℤ} (hp : S.IsStageOffset p)
    (hF : S.F = 1) {s : 𝕜} (hs : s ≠ 0) :
    (∃ v : Fin n → 𝕜, v ≠ 0 ∧ S.X.map (algebraMap ℝ 𝕜) *ᵥ v = s ^ 2 • v) ↔
      ∃ v : Fin n → 𝕜, v ≠ 0 ∧ (S.N + S.M).map (algebraMap ℝ 𝕜) *ᵥ v = (s - s⁻¹) • v := by
  rw [exists_eigenvector_iff_det_eq_zero, exists_eigenvector_iff_det_eq_zero,
    S.det_sq_sub_X_one_of_offset hp hF hs, mul_eq_zero]
  exact or_iff_right (pow_ne_zero n hs)

end Field

variable [DecidableEq κ]

/-! ### (b) The zero-order hold in a Jacobi scheme -/

/-- **The zero-order hold in a Jacobi scheme:** if all subsystems run at the same stage,
`X - 1 = H φ A` with `φ = φ₁(H A₀)`. -/
theorem zoh_X_sub_one_of_jacobi (hJ : ∀ s t, S.stage s = S.stage t)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (S.zoh A hA H).X - 1 = H • (phiOne (H • S.blockDiag A) * A) := by
  have hN : (S.zoh A hA H).N = 0 := N_eq_zero_of_jacobi (S := S.zoh A hA H) hJ
  have hX := (S.zoh A hA H).hX
  rw [hN, zero_mul, add_zero] at hX
  rw [← S.zoh_pencilHA A hA H, pencilHA, hN, add_zero, hX]
  abel

/-- The complexified one-step map of the zero-order hold in a Jacobi scheme. -/
theorem zoh_X_map_of_jacobi (hJ : ∀ s t, S.stage s = S.stage t)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) (H : ℝ) :
    (S.zoh A hA H).X.map (algebraMap ℝ ℂ) =
      1 + (H : ℂ) • (phiOne (H • S.blockDiag A) * A).map (algebraMap ℝ ℂ) := by
  have h : (S.zoh A hA H).X = 1 + H • (phiOne (H • S.blockDiag A) * A) :=
    eq_add_of_sub_eq' (S.zoh_X_sub_one_of_jacobi hJ A hA H)
  have hs : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      (algebraMap ℝ ℂ).mapMatrix (H • M) = (H : ℂ) • (algebraMap ℝ ℂ).mapMatrix M := by
    intro M
    ext i j
    simp
  have h2 := congrArg (algebraMap ℝ ℂ).mapMatrix h
  rw [map_add, map_one, hs] at h2
  exact h2

/-- **The eigenvalues of the zero-order hold in a Jacobi scheme:** for `H ≠ 0`, a complex `v`
and a complex `ξ`, `X v = ξ v` if and only if `φ A v = ((ξ - 1)/H) v`: `ξ - 1 = H λ̂` for an
eigenvalue `λ̂` of `φ A`. -/
theorem zoh_jacobi_eigen_iff_complex (hJ : ∀ s t, S.stage s = S.stage t)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : H ≠ 0) {v : Fin n → ℂ} {xi : ℂ} :
    (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = xi • v ↔
      (phiOne (H • S.blockDiag A) * A).map (algebraMap ℝ ℂ) *ᵥ v = ((xi - 1) / (H : ℂ)) • v := by
  have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH
  rw [S.zoh_X_map_of_jacobi hJ A hA H, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  constructor
  · intro h
    have h1 : (H : ℂ) • ((phiOne (H • S.blockDiag A) * A).map (algebraMap ℝ ℂ) *ᵥ v) =
        (xi - 1) • v := by
      rw [sub_smul, one_smul, ← h, add_sub_cancel_left]
    rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hHc, one_smul]
  · intro h
    rw [h, smul_smul, mul_div_cancel₀ _ hHc, sub_smul, one_smul, add_sub_cancel]

/-- **Reciprocal eigenvalues of the zero-order hold in a Jacobi scheme:** for `H ≠ 0` and an
eigenvalue `λ̂ ≠ 0` of `φ A` with a complex eigenvector `v`, `Ê v = (H/2 + 1/λ̂) Â v`: the
eigenvalue `θ` of the pencil has `1/θ = 1/λ̂ + H/2`. -/
theorem zoh_jacobi_reciprocal (hJ : ∀ s t, S.stage s = S.stage t)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0) {H : ℝ}
    (hH : H ≠ 0) {v : Fin n → ℂ} {lam : ℂ} (hlam : lam ≠ 0)
    (hv : (phiOne (H • S.blockDiag A) * A).map (algebraMap ℝ ℂ) *ᵥ v = lam • v) :
    (S.zoh A hA H).pencilE.map (algebraMap ℝ ℂ) *ᵥ v =
      ((H : ℂ) / 2 + 1 / lam) •
        (((S.zoh A hA H).pencilA H).map (algebraMap ℝ ℂ) *ᵥ v) := by
  have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH
  have hxi : 1 + (H : ℂ) * lam ≠ 1 := fun h =>
    mul_ne_zero hHc hlam (by linear_combination h)
  have h1 : (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = (1 + (H : ℂ) * lam) • v := by
    rw [S.zoh_jacobi_eigen_iff_complex hJ A hA hH, add_sub_cancel_left,
      mul_div_cancel_left₀ _ hHc]
    exact hv
  have h2 := ((S.zoh A hA H).pencil_reciprocal_iff_complex hH hxi).1 h1
  have e : (H : ℂ) / (1 + (H : ℂ) * lam - 1) = 1 / lam := by
    rw [add_sub_cancel_left]
    field_simp
  rw [e] at h2
  exact h2

/-! ### (c) The zero-order hold of subsystems without dynamics -/

/-- For subsystems without dynamics of their own, `A₀ = 0`, the coefficients of the samples of
the zero-order hold add up to `H A`. -/
theorem zoh_N_add_M_of_blockDiag_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hA0 : S.blockDiag A = 0) (H : ℝ) :
    (S.zoh A hA H).N + (S.zoh A hA H).M = H • A := by
  rw [add_comm, S.zoh_M_add_N]
  show S.zohKernel A H * S.coupling A = H • A
  rw [zohKernel, coupling, hA0, smul_zero, phiOne_zero_eq_one, sub_zero, smul_mul_assoc,
    one_mul]

/-- **Subsystems without dynamics, with a stage offset:** for the zero-order hold with `A₀ = 0`,
`H ≠ 0` and a complex `s ≠ 0`, `s²` is an eigenvalue of the one-step map if and only if
`λ = (s - 1/s)/H` is an eigenvalue of `A`. -/
theorem zoh_eigen_sq_iff_of_offset {p : κ → ℤ} (hp : S.IsStageOffset p)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hA0 : S.blockDiag A = 0) {H : ℝ} (hH : H ≠ 0) {s : ℂ} (hs : s ≠ 0) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = s ^ 2 • v) ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = ((s - s⁻¹) / (H : ℂ)) • v := by
  have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH
  have hF : (S.zoh A hA H).F = 1 := by
    show NormedSpace.exp (H • S.blockDiag A) = 1
    rw [hA0, smul_zero, NormedSpace.exp_zero]
  have hs' : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      (H • M).map (algebraMap ℝ ℂ) = (H : ℂ) • M.map (algebraMap ℝ ℂ) := by
    intro M
    ext i j
    simp
  rw [(S.zoh A hA H).exists_eigenvector_X_sq_iff_of_offset_one (𝕜 := ℂ) hp hF hs,
    S.zoh_N_add_M_of_blockDiag_eq_zero hA hA0 H, hs']
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.smul_mulVec]
  constructor
  · intro h
    rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hHc, one_smul]
  · intro h
    rw [h, smul_smul, mul_div_cancel₀ _ hHc]

/-- **Reciprocal squares for subsystems without dynamics** (the paper, after equation `eq:tree`).
For the zero-order hold with `A₀ = 0` in an order with a stage offset, `H ≠ 0`: if `ξ = s²` is an
eigenvalue of the one-step map with `s ≠ 0`, `s² ≠ 1`, `s² ≠ -1`, there is an eigenvalue `λ` of
`A` with `H λ = s - 1/s`, and the Cayley parameter `θ = (2/H) (ξ - 1)/(ξ + 1)` obeys
`1/θ² = 1/λ² + (H/2)²`. -/
theorem zoh_reciprocal_sq_of_offset {p : κ → ℤ} (hp : S.IsStageOffset p)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hA0 : S.blockDiag A = 0) {H : ℝ} (hH : H ≠ 0) {s : ℂ} (hs : s ≠ 0) (hs1 : s ^ 2 ≠ 1)
    (hs2 : s ^ 2 ≠ -1)
    (hX : ∃ v : Fin n → ℂ, v ≠ 0 ∧ (S.zoh A hA H).X.map (algebraMap ℝ ℂ) *ᵥ v = s ^ 2 • v) :
    ∃ lam : ℂ, (∃ w : Fin n → ℂ, w ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ w = lam • w) ∧
      (H : ℂ) * lam = s - s⁻¹ ∧
      ((2 / (H : ℂ) * (s ^ 2 - 1) / (s ^ 2 + 1)) ^ 2)⁻¹ = (lam ^ 2)⁻¹ + ((H : ℂ) / 2) ^ 2 := by
  have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH
  have hlam : (H : ℂ) * ((s - s⁻¹) / (H : ℂ)) = s - s⁻¹ := mul_div_cancel₀ _ hHc
  exact ⟨(s - s⁻¹) / (H : ℂ), (S.zoh_eigen_sq_iff_of_offset hp hA hA0 hH hs).1 hX, hlam,
    reciprocal_sq_eq hHc hs hs1 hs2 hlam⟩

end HeldScheme

end CoSimFoundations
