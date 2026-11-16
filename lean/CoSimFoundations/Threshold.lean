/-
The angle form of the reference step of two stores and the thresholds (the paper, eq. (13),
Prop 7.3), underdamped case.

Two stores `A = !![-r₁, -ω; ω, -r₂]`, `ω > 0`, with the asymmetry of the dissipation written as an
angle, `(r₁ - r₂)/2 = ω cos φ`, `0 < φ < π` (underdamped), and `μ = ω sin φ · H`:

  `exp (H • A) = (e^{-(r₁+r₂)H/2} / sin φ) • !![sin (φ - μ), -sin μ; sin μ, sin (φ + μ)]`.

For `0 < μ ≤ π` (at most half a turn of the pair in one macro step):

* `0 < U 0 0 ↔ μ < φ`, `0 < U 1 1 ↔ μ < π - φ`;
* a Jacobi scheme of two coupled scalar stores has the step `U` for some gains and weights iff
  `μ < φ` and `μ < π - φ` (for `φ ≤ π/2`, store `0` the more damped one: iff `μ < φ`);
* a Gauss–Seidel scheme (store `0` first) iff `μ < φ` (store `0` the less damped one, `φ ≥ π/2`:
  the paper's `μ < π - φ'` with `φ' = π - φ`).

The restriction `μ ≤ π` matters: beyond a full turn the diagonal of `U` is positive again.
-/
import CoSimFoundations.TwoStoreStep
import CoSimFoundations.DetExp
import CoSimFoundations.FloorMatrix
import CoSimFoundations.GaussSeidelTwo

open NormedSpace Matrix

namespace CoSimFoundations

/-- **Angle form of the reference step of two stores.** -/
theorem exp_twoStore_angle {r₁ r₂ ω φ : ℝ} (hω : 0 < ω) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hd : (r₁ - r₂) / 2 = ω * Real.cos φ) (H : ℝ) :
    exp (H • !![-r₁, -ω; ω, -r₂]) =
      (Real.exp (-((r₁ + r₂) / 2) * H) / Real.sin φ) •
        !![Real.sin (φ - ω * Real.sin φ * H), -Real.sin (ω * Real.sin φ * H);
           Real.sin (ω * Real.sin φ * H), Real.sin (φ + ω * Real.sin φ * H)] := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ
  have hs' : Real.sin φ ≠ 0 := hs.ne'
  have hω' : ω ≠ 0 := hω.ne'
  have hν : ω * Real.sin φ ≠ 0 := mul_ne_zero hω' hs'
  have hν2 : (ω * Real.sin φ) ^ 2 = ω ^ 2 - ((r₁ - r₂) / 2) ^ 2 := by
    rw [hd]
    linear_combination ω ^ 2 * Real.sin_sq_add_cos_sq φ
  rw [exp_twoStore hν hν2 H, hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.sin_sub, Real.sin_add] <;> field_simp

section Signs

variable {r₁ r₂ ω φ H : ℝ}

/-- The first store keeps its sign iff `μ < φ`. -/
theorem twoStore_zero_pos_iff (hω : 0 < ω) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hd : (r₁ - r₂) / 2 = ω * Real.cos φ) (hμ0 : 0 ≤ ω * Real.sin φ * H)
    (hμ : ω * Real.sin φ * H ≤ Real.pi) :
    0 < (exp (H • !![-r₁, -ω; ω, -r₂])) 0 0 ↔ ω * Real.sin φ * H < φ := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ
  have hc : 0 < Real.exp (-((r₁ + r₂) / 2) * H) / Real.sin φ := div_pos (Real.exp_pos _) hs
  rw [exp_twoStore_angle hω hφ0 hφ hd H]
  simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, smul_eq_mul]
  rw [mul_pos_iff_of_pos_left hc]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := φ - ω * Real.sin φ * H)
      (by linarith) (by linarith)
    linarith
  · intro h
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- The second store keeps its sign iff `μ < π - φ`. -/
theorem twoStore_one_pos_iff (hω : 0 < ω) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hd : (r₁ - r₂) / 2 = ω * Real.cos φ) (hμ0 : 0 ≤ ω * Real.sin φ * H)
    (hμ : ω * Real.sin φ * H ≤ Real.pi) :
    0 < (exp (H • !![-r₁, -ω; ω, -r₂])) 1 1 ↔ ω * Real.sin φ * H < Real.pi - φ := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ
  have hc : 0 < Real.exp (-((r₁ + r₂) / 2) * H) / Real.sin φ := div_pos (Real.exp_pos _) hs
  rw [exp_twoStore_angle hω hφ0 hφ hd H]
  simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    smul_eq_mul]
  rw [mul_pos_iff_of_pos_left hc]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have h1 := Real.sin_nonneg_of_nonneg_of_le_pi (x := φ + ω * Real.sin φ * H - Real.pi)
      (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h1
    linarith
  · intro h
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

end Signs

/-- The determinant of a reference step is positive. -/
theorem det_exp_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : 0 < (exp A).det := by
  rw [det_exp]
  exact Real.exp_pos _

/-- **The Jacobi threshold of two coupled stores (Prop 7.3).** For at most half a turn of the pair
in one macro step, the Jacobi class contains a scheme that reproduces the reference iff
`μ < φ` and `μ < π - φ`. -/
theorem ScalarNet.jacobi_threshold (N : ScalarNet 2) (hfull : ∀ i j, i ≠ j → N.partner i j)
    {r₁ r₂ ω φ H : ℝ} (hH : 0 < H) (hω : 0 < ω) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hd : (r₁ - r₂) / 2 = ω * Real.cos φ) (hμ : ω * Real.sin φ * H ≤ Real.pi) :
    (∃ k w, (∀ i j, ¬ N.partner i j → w i j = 0) ∧
        exp (H • !![-r₁, -ω; ω, -r₂]) = N.jacobiStep H k w) ↔
      ω * Real.sin φ * H < φ ∧ ω * Real.sin φ * H < Real.pi - φ := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ
  have hμ0 : 0 ≤ ω * Real.sin φ * H := (mul_pos (mul_pos hω hs) hH).le
  rw [N.exists_exact_iff_of_fullyCoupled hH hfull, Fin.forall_fin_two,
    twoStore_zero_pos_iff hω hφ0 hφ hd hμ0 hμ, twoStore_one_pos_iff hω hφ0 hφ hd hμ0 hμ]

/-- The Jacobi threshold when store `0` is the more damped one (`φ ≤ π/2`): `μ < φ`. -/
theorem ScalarNet.jacobi_threshold_of_le (N : ScalarNet 2)
    (hfull : ∀ i j, i ≠ j → N.partner i j)
    {r₁ r₂ ω φ H : ℝ} (hH : 0 < H) (hω : 0 < ω) (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi / 2)
    (hd : (r₁ - r₂) / 2 = ω * Real.cos φ) (hμ : ω * Real.sin φ * H ≤ Real.pi) :
    (∃ k w, (∀ i j, ¬ N.partner i j → w i j = 0) ∧
        exp (H • !![-r₁, -ω; ω, -r₂]) = N.jacobiStep H k w) ↔ ω * Real.sin φ * H < φ := by
  have hπ := Real.pi_pos
  rw [N.jacobi_threshold hfull hH hω hφ0 (by linarith) hd hμ]
  exact ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩

/-- **The Gauss–Seidel threshold of two stores (Prop 7.3).** With store `0` first, the
Gauss–Seidel class contains a scheme that reproduces the reference iff `μ < φ`. -/
theorem ScalarNet.gs_threshold (N : ScalarNet 2)
    {r₁ r₂ ω φ H : ℝ} (hH : 0 < H) (hω : 0 < ω) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hd : (r₁ - r₂) / 2 = ω * Real.cos φ) (hμ : ω * Real.sin φ * H ≤ Real.pi) :
    (∃ k w, exp (H • !![-r₁, -ω; ω, -r₂]) = N.gsStep H k w) ↔ ω * Real.sin φ * H < φ := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ
  have hμ0 : 0 ≤ ω * Real.sin φ * H := (mul_pos (mul_pos hω hs) hH).le
  rw [N.exists_exact_gs_two_iff hH _ (det_exp_pos _),
    twoStore_zero_pos_iff hω hφ0 hφ hd hμ0 hμ]

end CoSimFoundations
