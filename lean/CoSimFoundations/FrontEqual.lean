/-
The front of the Jacobi class for a pair with equal dissipation (the paper, Thm 7.4 with
`ϑ = 0`, Cor 7.5, Cor 7.6): the geometry in the row plane.

Frame of the binding wall. The defect of a two-store scheme is a pair `(z, w)` of complex numbers
(`RowCoords`: `x ↦ z x + w x̄`), with rows `z + w` and `z - w`, largest stretch `‖z‖ + ‖w‖`,
determinant `‖z‖² - ‖w‖²` and accuracy `‖z - e‖ + ‖w‖`, where `e = e^{iψ}` is the exact point and
`0 < ψ ≤ π/2` the overshoot. For equal dissipation both walls are the real axis: the closure of the
Jacobi class is `Im (z + w) ≤ 0`, `Im (z - w) ≤ 0`.

Statements:
* on the wall, `‖s - e‖² = s² - 2 s cos ψ + 1`; it is `sin ψ` at `s = cos ψ` (the sine of the
  overshoot) and `2 sin (ψ/2)` at `s = 1` (the chord), and it increases with `s ≥ cos ψ`;
* **domination**: every defect of the closure with positive determinant is weakly dominated, in
  accuracy, in `|ε| = |s₊² - 1|` and in `|H δ̄| = |log s̄|`, by a stick of zero height `z = s`,
  `w = 0` with `cos ψ ≤ s ≤ 1`. With the monotonicity, these sticks are the front, they add no
  energy (`s ≤ 1`), and on them `sin ψ ≤ α ≤ 2 sin (ψ/2)`.

Plan of proof of the domination: `s = min (max (‖z‖ + ‖w‖) (cos ψ)) 1`. Since `Im z ≤ 0` and
`cos ψ ≥ 0`, `Re (z * conj e) ≤ ‖z‖ cos ψ`, so `‖z - e‖ ≥ ‖‖z‖ - e‖`; the triangle inequality gives
`‖(‖z‖ + ‖w‖) - e‖ ≤ ‖z - e‖ + ‖w‖`; and on the real axis the distance to `e` is least at `cos ψ`
and increases beyond it.
-/
import CoSimFoundations.RowCoords
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Complex

namespace CoSimFoundations

/-- The exact point in the frame of the binding wall. -/
noncomputable def exactPt (ψ : ℝ) : ℂ := Complex.exp (ψ * Complex.I)

theorem exactPt_re (ψ : ℝ) : (exactPt ψ).re = Real.cos ψ := exp_ofReal_mul_I_re ψ

theorem exactPt_im (ψ : ℝ) : (exactPt ψ).im = Real.sin ψ := exp_ofReal_mul_I_im ψ

theorem norm_exactPt (ψ : ℝ) : ‖exactPt ψ‖ = 1 := norm_exp_ofReal_mul_I ψ

theorem exactPt_neg_mul_exactPt (ψ : ℝ) : exactPt (-ψ) * exactPt ψ = 1 := by
  rw [exactPt, exactPt, ← Complex.exp_add, ofReal_neg, neg_mul, neg_add_cancel, Complex.exp_zero]

/-- Distance from a point of the wall to the exact point. -/
theorem norm_ofReal_sub_exactPt_sq (s ψ : ℝ) :
    ‖(s : ℂ) - exactPt ψ‖ ^ 2 = s ^ 2 - 2 * s * Real.cos ψ + 1 := by
  rw [Complex.sq_norm, normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, exactPt_re,
    exactPt_im]
  linear_combination Real.sin_sq_add_cos_sq ψ

/-- At the corner the accuracy is the sine of the overshoot. -/
theorem norm_cos_sub_exactPt {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ Real.pi) :
    ‖((Real.cos ψ : ℝ) : ℂ) - exactPt ψ‖ = Real.sin ψ := by
  have hs : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi h0 h1
  rw [← sq_eq_sq₀ (norm_nonneg _) hs, norm_ofReal_sub_exactPt_sq]
  linear_combination -(Real.sin_sq_add_cos_sq ψ)

/-- At the energy-neutral end the accuracy is the chord of the overshoot. -/
theorem norm_one_sub_exactPt {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ 2 * Real.pi) :
    ‖(1 : ℂ) - exactPt ψ‖ = 2 * Real.sin (ψ / 2) := by
  have hs : 0 ≤ Real.sin (ψ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have h2 : Real.cos ψ = 2 * Real.cos (ψ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    congr 1
    ring
  have h3 := norm_ofReal_sub_exactPt_sq 1 ψ
  rw [ofReal_one] at h3
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), h3, h2]
  linear_combination -4 * Real.sin_sq_add_cos_sq (ψ / 2)

/-- Along the wall beyond the corner the accuracy gets worse as the foot moves out. -/
theorem norm_sub_exactPt_mono {ψ s t : ℝ} (hs : Real.cos ψ ≤ s) (hst : s ≤ t) :
    ‖(s : ℂ) - exactPt ψ‖ ≤ ‖(t : ℂ) - exactPt ψ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_ofReal_sub_exactPt_sq,
    norm_ofReal_sub_exactPt_sq]
  nlinarith [mul_nonneg (sub_nonneg.2 hst) (by linarith : (0 : ℝ) ≤ t + s - 2 * Real.cos ψ)]

/-- On the wall the corner `cos ψ` is the point nearest to the exact point. -/
theorem norm_cos_sub_exactPt_le (ψ x : ℝ) :
    ‖((Real.cos ψ : ℝ) : ℂ) - exactPt ψ‖ ≤ ‖(x : ℂ) - exactPt ψ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_ofReal_sub_exactPt_sq,
    norm_ofReal_sub_exactPt_sq]
  nlinarith [sq_nonneg (x - Real.cos ψ)]

/-- Below the wall, turning `z` onto the wall (to `‖z‖`) brings it no farther from `e`. -/
theorem norm_ofReal_norm_sub_exactPt_le {ψ : ℝ} (hc : 0 ≤ Real.cos ψ) (hsn : 0 ≤ Real.sin ψ)
    {z : ℂ} (hz : z.im ≤ 0) : ‖((‖z‖ : ℝ) : ℂ) - exactPt ψ‖ ≤ ‖z - exactPt ψ‖ := by
  have h1 := norm_ofReal_sub_exactPt_sq ‖z‖ ψ
  have h2 : ‖z - exactPt ψ‖ ^ 2 =
      ‖z‖ ^ 2 - 2 * (z.re * Real.cos ψ + z.im * Real.sin ψ) + 1 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply, sub_re, sub_im, exactPt_re,
      exactPt_im]
    linear_combination Real.sin_sq_add_cos_sq ψ
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h1, h2]
  linarith [mul_le_mul_of_nonneg_right (re_le_norm z) hc, mul_nonpos_of_nonpos_of_nonneg hz hsn]

theorem abs_log_le_abs_log_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    |Real.log b| ≤ |Real.log a| := by
  have h1 : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have h2 : Real.log b ≤ 0 := Real.log_nonpos (ha.le.trans hab) hb
  rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
  linarith

/-- **Domination by the sticks of zero height.** -/
theorem front_equal_dominates {ψ : ℝ} (h0 : 0 < ψ) (h1 : ψ ≤ Real.pi / 2) {z w : ℂ}
    (hr1 : (z + w).im ≤ 0) (hr2 : (z - w).im ≤ 0) (hdet : ‖w‖ < ‖z‖) :
    ∃ s : ℝ, Real.cos ψ ≤ s ∧ s ≤ 1 ∧
      ‖(s : ℂ) - exactPt ψ‖ ≤ ‖z - exactPt ψ‖ + ‖w‖ ∧
      |s ^ 2 - 1| ≤ |(‖z‖ + ‖w‖) ^ 2 - 1| ∧
      |Real.log s| ≤ |Real.log (Real.sqrt (‖z‖ ^ 2 - ‖w‖ ^ 2))| := by
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ Real.cos ψ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  have hc1 : Real.cos ψ ≤ 1 := Real.cos_le_one ψ
  have hsn : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi h0.le (by linarith)
  have hzim : z.im ≤ 0 := by
    rw [add_im] at hr1
    rw [sub_im] at hr2
    linarith
  have hq := norm_nonneg w
  have hρ : 0 < ‖z‖ := hq.trans_lt hdet
  -- (a) and (b): the foot `‖z‖ + ‖w‖` on the wall is no less accurate than `(z, w)`
  have hA := norm_ofReal_norm_sub_exactPt_le hc0 hsn hzim
  have hB : ‖((‖z‖ + ‖w‖ : ℝ) : ℂ) - exactPt ψ‖ ≤ ‖z - exactPt ψ‖ + ‖w‖ := by
    have h : ((‖z‖ + ‖w‖ : ℝ) : ℂ) - exactPt ψ =
        (((‖z‖ : ℝ) : ℂ) - exactPt ψ) + ((‖w‖ : ℝ) : ℂ) := by
      rw [ofReal_add]
      ring
    rw [h]
    calc ‖(((‖z‖ : ℝ) : ℂ) - exactPt ψ) + ((‖w‖ : ℝ) : ℂ)‖
        ≤ ‖((‖z‖ : ℝ) : ℂ) - exactPt ψ‖ + ‖((‖w‖ : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖z - exactPt ψ‖ + ‖w‖ := by
        rw [Complex.norm_of_nonneg hq]
        linarith
  -- the energy bound: `0 < √(‖z‖² - ‖w‖²) ≤ ‖z‖`
  have hD : 0 < ‖z‖ ^ 2 - ‖w‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hdet) (by linarith : (0 : ℝ) < ‖z‖ + ‖w‖)]
  have hsq0 : 0 < Real.sqrt (‖z‖ ^ 2 - ‖w‖ ^ 2) := Real.sqrt_pos.2 hD
  have hsq1 : Real.sqrt (‖z‖ ^ 2 - ‖w‖ ^ 2) ≤ ‖z‖ :=
    (Real.sqrt_le_left hρ.le).2 (by linarith [sq_nonneg ‖w‖])
  -- (c): `s = min (max (‖z‖ + ‖w‖) (cos ψ)) 1`, case by case
  by_cases hS1 : 1 ≤ ‖z‖ + ‖w‖
  · refine ⟨1, hc1, le_rfl, (norm_sub_exactPt_mono hc1 hS1).trans hB, ?_, ?_⟩
    · rw [one_pow, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [Real.log_one, abs_zero]
      exact abs_nonneg _
  · replace hS1 := not_le.mp hS1
    by_cases hcS : Real.cos ψ ≤ ‖z‖ + ‖w‖
    · exact ⟨‖z‖ + ‖w‖, hcS, hS1.le, hB, le_rfl,
        abs_log_le_abs_log_of_le hsq0 (by linarith) hS1.le⟩
    · replace hcS := not_le.mp hcS
      refine ⟨Real.cos ψ, le_rfl, hc1, ?_, ?_, abs_log_le_abs_log_of_le hsq0 (by linarith) hc1⟩
      · calc ‖((Real.cos ψ : ℝ) : ℂ) - exactPt ψ‖ ≤ ‖((‖z‖ : ℝ) : ℂ) - exactPt ψ‖ :=
            norm_cos_sub_exactPt_le ψ ‖z‖
          _ ≤ ‖z - exactPt ψ‖ := hA
          _ ≤ ‖z - exactPt ψ‖ + ‖w‖ := le_add_of_nonneg_right hq
      · have hS0 : 0 ≤ ‖z‖ + ‖w‖ := by positivity
        have ha : Real.cos ψ ^ 2 - 1 ≤ 0 := by nlinarith [mul_nonneg hc0 (sub_nonneg.2 hc1)]
        have hb : (‖z‖ + ‖w‖) ^ 2 - 1 ≤ 0 := by
          nlinarith [mul_nonneg hS0 (by linarith : (0 : ℝ) ≤ 1 - (‖z‖ + ‖w‖))]
        rw [abs_of_nonpos ha, abs_of_nonpos hb]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.cos ψ - (‖z‖ + ‖w‖))
          (by linarith : (0 : ℝ) ≤ Real.cos ψ + (‖z‖ + ‖w‖))]

/-- **The same in the original frame, for the maps of `RowCoords`** (exact point `1`, wall turned
by `-ψ`): a defect `rowMap z w` whose rows `z ± w` lie in the closed half-plane
`Im (ξ e^{iψ}) ≤ 0` and whose determinant is positive is weakly dominated by
`rowMap (s e^{-iψ}) 0` for some `cos ψ ≤ s ≤ 1`. -/
theorem front_equal_rowMap {ψ : ℝ} (h0 : 0 < ψ) (h1 : ψ ≤ Real.pi / 2) {z w : ℂ}
    (hr1 : ((z + w) * exactPt ψ).im ≤ 0) (hr2 : ((z - w) * exactPt ψ).im ≤ 0)
    (hdet : ‖w‖ < ‖z‖) :
    ∃ s : ℝ, Real.cos ψ ≤ s ∧ s ≤ 1 ∧
      ‖rowMap ((s : ℂ) * exactPt (-ψ)) 0 - 1‖ ≤ ‖rowMap z w - 1‖ ∧
      |‖rowMap ((s : ℂ) * exactPt (-ψ)) 0‖ ^ 2 - 1| ≤ |‖rowMap z w‖ ^ 2 - 1| ∧
      |Real.log s| ≤ |Real.log (Real.sqrt (‖z‖ ^ 2 - ‖w‖ ^ 2))| := by
  have he := norm_exactPt ψ
  have hz : ‖z * exactPt ψ‖ = ‖z‖ := by rw [norm_mul, he, mul_one]
  have hw : ‖w * exactPt ψ‖ = ‖w‖ := by rw [norm_mul, he, mul_one]
  obtain ⟨s, hs0, hs1, hacc, hen, hlog⟩ :=
    front_equal_dominates h0 h1 (z := z * exactPt ψ) (w := w * exactPt ψ)
      (by rw [← add_mul]; exact hr1) (by rw [← sub_mul]; exact hr2) (by rw [hz, hw]; exact hdet)
  rw [hz, hw] at hen hlog
  refine ⟨s, hs0, hs1, ?_, ?_, hlog⟩
  · have h2 : (s : ℂ) * exactPt (-ψ) - 1 = ((s : ℂ) - exactPt ψ) * exactPt (-ψ) := by
      linear_combination exactPt_neg_mul_exactPt ψ
    have h3 : z * exactPt ψ - exactPt ψ = (z - 1) * exactPt ψ := by ring
    rw [hw, h3, norm_mul, he, mul_one] at hacc
    rw [norm_rowMap_sub_one, norm_rowMap_sub_one, norm_zero, add_zero, h2, norm_mul,
      norm_exactPt, mul_one]
    exact hacc
  · rw [opNorm_rowMap, opNorm_rowMap, norm_zero, add_zero, norm_mul, norm_exactPt, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact hen

end CoSimFoundations
