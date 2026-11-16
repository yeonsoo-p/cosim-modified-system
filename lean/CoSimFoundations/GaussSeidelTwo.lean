/-
Two scalar stores in Gauss–Seidel mode (the paper, Prop 7.2 and Thm 7.3, Gauss–Seidel part).

With store `0` running first, the step matrices of the class are exactly the matrices with
`X 0 0 > 0` and `det X > 0`. Hence the class contains a scheme whose step matrix is the reference
step `U` if and only if `U 0 0 > 0` and `det U > 0`: only the store that runs first has to be
turned by less than a right angle.
-/
import CoSimFoundations.GaussSeidel

open Real Matrix

namespace CoSimFoundations

namespace ScalarNet

variable {n : ℕ} (N : ScalarNet n)

/-- A local gain realises any positive local exponential. -/
theorem exists_gain {H : ℝ} (hH : 0 < H) (i : Fin n) {y : ℝ} (hy : 0 < y) :
    ∃ κ : ℝ, exp ((N.a i + N.b i * κ * N.c i) * H) = y := by
  have hb : N.b i ≠ 0 := left_ne_zero_of_mul (N.hbc i)
  have hc : N.c i ≠ 0 := right_ne_zero_of_mul (N.hbc i)
  have hH' := hH.ne'
  refine ⟨(log y / H - N.a i) / (N.b i * N.c i), ?_⟩
  have h1 : (N.a i + N.b i * ((log y / H - N.a i) / (N.b i * N.c i)) * N.c i) * H = log y := by
    field_simp
    ring
  rw [h1, exp_log hy]

theorem inGain_ne_zero {H : ℝ} (hH : 0 < H) (k : Fin n → ℝ) (i : Fin n) : N.inGain H k i ≠ 0 :=
  mul_ne_zero (holdGain_pos hH).ne' (left_ne_zero_of_mul (N.hbc i))

end ScalarNet

/-- **The Gauss–Seidel class of two stores** (store `0` first): its step matrices are exactly those
with `X 0 0 > 0` and `det X > 0`. -/
theorem ScalarNet.range_gsStep_two (N : ScalarNet 2) {H : ℝ} (hH : 0 < H)
    (U : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ k w, U = N.gsStep H k w) ↔ 0 < U 0 0 ∧ 0 < U.det := by
  constructor
  · rintro ⟨k, w, rfl⟩
    refine ⟨?_, ?_⟩
    · have h := congrFun (congrFun (N.gsLo_mul_gsStep H k w) 0) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, ScalarNet.gsLo, ScalarNet.gsR] at h
      simp at h
      rw [h]; exact exp_pos _
    · rw [N.det_gsStep]; exact Finset.prod_pos fun i _ => exp_pos _
  · rintro ⟨h00, hdet⟩
    have hdet' : 0 < U.det / U 0 0 := div_pos hdet h00
    obtain ⟨κ0, hκ0⟩ := N.exists_gain hH 0 h00
    obtain ⟨κ1, hκ1⟩ := N.exists_gain hH 1 hdet'
    let k : Fin 2 → ℝ := fun i => if i = 0 then κ0 else κ1
    have hr0 : exp (N.rate k 0 * H) = U 0 0 := by simpa [ScalarNet.rate, k] using hκ0
    have hr1 : exp (N.rate k 1 * H) = U.det / U 0 0 := by simpa [ScalarNet.rate, k] using hκ1
    have hg0 := N.inGain_ne_zero hH k 0
    have hg1 := N.inGain_ne_zero hH k 1
    have hc0 : N.c 0 ≠ 0 := right_ne_zero_of_mul (N.hbc 0)
    have hc1 : N.c 1 ≠ 0 := right_ne_zero_of_mul (N.hbc 1)
    let w : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      if i = 0 then U 0 1 / (N.inGain H k 0 * N.c 1) else U 1 0 / (N.inGain H k 1 * N.c 0 * U 0 0)
    refine ⟨k, w, ?_⟩
    have hfac : N.gsLo H k w * U = N.gsR H k w := by
      have h00' := h00.ne'
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, ScalarNet.gsLo, ScalarNet.gsR, hr0]
      · simp [Matrix.mul_apply, ScalarNet.gsLo, ScalarNet.gsR, w]
        field_simp
      · simp [Matrix.mul_apply, Fin.sum_univ_two, ScalarNet.gsLo, ScalarNet.gsR, w]
        field_simp
        ring
      · simp [Matrix.mul_apply, Fin.sum_univ_two, ScalarNet.gsLo, ScalarNet.gsR, w, hr1,
          Matrix.det_fin_two]
        field_simp
        ring
    have hu : IsUnit (N.gsLo H k w).det := by rw [N.det_gsLo]; exact isUnit_one
    rw [ScalarNet.gsStep, ← hfac, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-- **The threshold in Gauss–Seidel mode (Thm 7.3).** The class contains a scheme whose step matrix
is `U` if and only if `U 0 0 > 0` and `det U > 0`; for a reference step `det U > 0` always, so only
the store that runs first matters. -/
theorem ScalarNet.exists_exact_gs_two_iff (N : ScalarNet 2) {H : ℝ} (hH : 0 < H)
    (U : Matrix (Fin 2) (Fin 2) ℝ) (hdet : 0 < U.det) :
    (∃ k w, U = N.gsStep H k w) ↔ 0 < U 0 0 := by
  rw [N.range_gsStep_two hH]
  exact ⟨fun h => h.1, fun h => ⟨h, hdet⟩⟩

end CoSimFoundations
