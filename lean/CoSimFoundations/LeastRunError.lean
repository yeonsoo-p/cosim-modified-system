/-
The least error over a run with one held sample (the paper, Section 4, the display `eq:leastrun`
after Theorem "order barrier").

**Paper.** For a co-simulation started from the initial state, `x⁰ = x₀`, with one held sample,
`ε_K = max_{k ≤ K} ‖X^k - U^k‖` over the `K = ⌊T/H⌋` macro steps in `[0, T]`, `T = 1/(2‖A‖)`:
every consistent scheme has `ε_K ≥ H g - O(H²)` and some scheme has `ε_K ≤ H g + O(H²)`, where
  `g = min_{Z ∈ 𝒵} max_{0 ≤ t ≤ T} ‖Φ_t(½ A_ς A + Z)‖`,  `Φ_t(M) = ∫₀ᵗ e^{(t-s)A} M e^{sA} ds`.

**What is formalised.** In a Banach algebra with `‖1‖ ≤ 1` (applied to the operators `opE` of the
matrices):
* `runPhi a m t = ∫₀ᵗ e^{(t-s)a} m e^{sa} ds` with the semigroup law
  `Φ_{t+h} = e^{ha} Φ_t + Φ_h e^{ta}` (`runPhi_add`), the bounds `‖Φ_t‖ ≤ t e^{t‖a‖} ‖m‖`,
  `‖Φ_h - h m‖ ≤ h ‖m‖ (e^{h‖a‖} - 1)` (`norm_runPhi_le`, `norm_runPhi_sub_smul_le`), linearity in
  `m` (`runPhi_sub`), continuity in `t` (`norm_runPhi_add_sub_le`) and coercivity
  `‖Φ_T(m)‖ ≥ T (2 - e^{T‖a‖}) ‖m‖` (`norm_runPhi_ge`).
* **The run** (`norm_run_sub_runPhi_le`): if `‖x‖ ≤ ρ` (`ρ ≥ 1`), `‖x - e^{Ha}‖ ≤ c H²` and
  `‖x - e^{Ha} - H² m‖ ≤ C₁ H³`, then for `k H ≤ T`
    `‖x^k - e^{kHa} - H Φ_{kH}(m)‖ ≤ T e^{T‖a‖} (ρ^k (c T ‖m‖ + C₁) + ‖m‖ ‖a‖ e^{H‖a‖}) H²`.
  The proof is a pair of recursions, `x^{k+1} - u^{k+1} = x (x^k - u^k) + (x - u) u^k` for the run
  (`run_recursion`) and `Φ_{(k+1)H} = u Φ_{kH} + Φ_H u^k` for the integral against the discrete
  sum `runSum` (`norm_runPhi_sub_runSum_le`); no Riemann sum is needed.
* **The maximum over `[0, T]`** (`runMax`, `runMax_le_gridMax`, `gridMax_le_runMax`,
  `abs_runErr_sub_runMax_le`): `G(m) = sup_{0 ≤ t ≤ T} ‖Φ_t(m)‖` is within
  `H e^{T‖a‖} ‖m‖ (1 + T‖a‖)` of the maximum over the grid `k H`, `k ≤ ⌊T/H⌋`, and
  `|ε_K - H G(m)| ≤ runConst … H²`. `G` is Lipschitz and coercive in `m` (`runMax_le_add`,
  `runMax_ge`).
* **A minimiser exists** (`exists_forall_le_of_coercive`, `exists_least_run`): a function that is
  Lipschitz and coercive on a subspace of matrices attains its least value (finite dimension); for
  `0 < T`, `T ‖A‖ ≤ 1/2`, `Z ↦ G(½ A_ς A + Z)` attains its least value `g` on the reach.
* **Every scheme** (`HeldScheme.Consistent.least_run_le`): for a consistent scheme whose coupling
  and coefficients act through the outputs, `0 < H`, `0 ≤ T`, and every `g ≤ G(½ A_ς A + Z)` on the
  reach: `ε_K ≥ H g - runConst T ‖A‖ e^{bT} c C₁ (c + C₁ H) H · H²`, `C₁ = √(card κ) C₃`.
* **Some scheme** (`HeldScheme.least_run_attained`): the scheme `reachScheme` of the minimiser has
  `ε_K ≤ H g + runConst T ‖A‖ e^{9βT} ((6 + 27σ) β²) (reachK σ β) ‖½ A_ς A + Z₀‖ H · H²`.

The paper's `T = 1/(2‖A‖)` satisfies `T ‖A‖ ≤ 1/2`; here `T` is any such time. The constants do
not depend on `H` except through `e^{H‖A‖}` and `C₃`, which are bounded for small `H`.
-/
import CoSimFoundations.LeastOneStep
import CoSimFoundations.ReversedOrder

open intervalIntegral MeasureTheory

namespace CoSimFoundations

section RunAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `s ↦ e^{s a}` is continuous. -/
theorem continuous_exp_smul_const (a : 𝔸) :
    Continuous fun s : ℝ => NormedSpace.exp (s • a) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

/-- `e^{(s + t) a} = e^{s a} e^{t a}`. -/
theorem exp_add_smul_const (a : 𝔸) (s t : ℝ) :
    NormedSpace.exp ((s + t) • a) = NormedSpace.exp (s • a) * NormedSpace.exp (t • a) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl a).smul_left s).smul_right t)

/-- `e^{(k h) a} = (e^{h a})^k`. -/
theorem exp_natCast_mul_smul (a : 𝔸) (h : ℝ) (k : ℕ) :
    NormedSpace.exp (((k : ℝ) * h) • a) = NormedSpace.exp (h • a) ^ k := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [mul_smul, Nat.cast_smul_eq_nsmul, NormedSpace.exp_nsmul]

/-- The integrand `s ↦ e^{(t-s)a} m e^{sa}` is continuous. -/
theorem continuous_runIntegrand (a m : 𝔸) (t : ℝ) :
    Continuous fun s : ℝ => NormedSpace.exp ((t - s) • a) * m * NormedSpace.exp (s • a) :=
  (((continuous_exp_smul_const a).comp (continuous_const.sub continuous_id)).mul
    continuous_const).mul (continuous_exp_smul_const a)

/-- **The accumulated half step** `Φ_t(m) = ∫₀ᵗ e^{(t-s)a} m e^{sa} ds` (the paper, eq.
`eq:leastrun`). -/
noncomputable def runPhi (a m : 𝔸) (t : ℝ) : 𝔸 :=
  ∫ s in (0 : ℝ)..t, NormedSpace.exp ((t - s) • a) * m * NormedSpace.exp (s • a)

/-- **The semigroup law** `Φ_{t+h} = e^{ha} Φ_t + Φ_h e^{ta}`. -/
theorem runPhi_add (a m : 𝔸) (t h : ℝ) :
    runPhi a m (t + h) =
      NormedSpace.exp (h • a) * runPhi a m t + runPhi a m h * NormedSpace.exp (t • a) := by
  unfold runPhi
  have hi : ∀ u v : ℝ, IntervalIntegrable
      (fun s : ℝ => NormedSpace.exp ((t + h - s) • a) * m * NormedSpace.exp (s • a)) volume u v :=
    fun u v => (continuous_runIntegrand a m (t + h)).intervalIntegrable u v
  rw [← integral_add_adjacent_intervals (hi 0 t) (hi t (t + h))]
  congr 1
  · have e : ∀ s : ℝ, NormedSpace.exp ((t + h - s) • a) * m * NormedSpace.exp (s • a) =
        NormedSpace.exp (h • a) *
          (NormedSpace.exp ((t - s) • a) * m * NormedSpace.exp (s • a)) := by
      intro s
      rw [show t + h - s = h + (t - s) by ring, exp_add_smul_const, mul_assoc, mul_assoc,
        mul_assoc]
    rw [integral_congr fun s _ => e s]
    have h1 := (ContinuousLinearMap.mul ℝ 𝔸 (NormedSpace.exp (h • a))).intervalIntegral_comp_comm
      ((continuous_runIntegrand a m t).intervalIntegrable (μ := volume) 0 t)
    simpa only [ContinuousLinearMap.mul_apply'] using h1
  · have e2 := integral_comp_add_right
      (fun s : ℝ => NormedSpace.exp ((t + h - s) • a) * m * NormedSpace.exp (s • a)) t
      (a := 0) (b := h)
    rw [zero_add, add_comm h t] at e2
    rw [← e2]
    have e3 : ∀ u : ℝ, NormedSpace.exp ((t + h - (u + t)) • a) * m *
        NormedSpace.exp ((u + t) • a) =
        NormedSpace.exp ((h - u) • a) * m * NormedSpace.exp (u • a) *
          NormedSpace.exp (t • a) := by
      intro u
      rw [show t + h - (u + t) = h - u by ring, exp_add_smul_const, ← mul_assoc]
    rw [integral_congr fun u _ => e3 u]
    have h1 := ((ContinuousLinearMap.mul ℝ 𝔸).flip
      (NormedSpace.exp (t • a))).intervalIntegral_comp_comm
      ((continuous_runIntegrand a m h).intervalIntegrable (μ := volume) 0 h)
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h1

/-- `Φ_0 = 0`. -/
theorem runPhi_zero (a m : 𝔸) : runPhi a m 0 = 0 := by
  simp [runPhi]

/-- `Φ` is additive in `m`: `Φ_t(m - m') = Φ_t(m) - Φ_t(m')`. -/
theorem runPhi_sub (a m m' : 𝔸) (t : ℝ) :
    runPhi a (m - m') t = runPhi a m t - runPhi a m' t := by
  unfold runPhi
  rw [← integral_sub ((continuous_runIntegrand a m t).intervalIntegrable 0 t)
    ((continuous_runIntegrand a m' t).intervalIntegrable 0 t)]
  refine integral_congr fun s _ => ?_
  simp only [mul_sub, sub_mul]

variable (h1 : ‖(1 : 𝔸)‖ ≤ 1)
include h1

/-- `‖e^{s a}‖ ≤ e^{s ‖a‖}` for `s ≥ 0`. -/
theorem norm_exp_smul_le' (a : 𝔸) {s : ℝ} (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • a)‖ ≤ Real.exp (s * ‖a‖) :=
  norm_exp_smul_le_of_norm_one_le h1 a hs

/-- `‖e^{s a} - 1‖ ≤ e^{s ‖a‖} - 1` for `s ≥ 0`. -/
theorem norm_exp_smul_sub_one_le' (a : 𝔸) {s : ℝ} (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • a) - 1‖ ≤ Real.exp (s * ‖a‖) - 1 := by
  have h := norm_exp_sub_one_le_exp_norm (s • a)
  rwa [norm_smul, Real.norm_of_nonneg hs] at h

/-- The integrand is at most `e^{t ‖a‖} ‖m‖` on `[0, t]`. -/
theorem norm_runIntegrand_le (a m : 𝔸) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖NormedSpace.exp ((t - s) • a) * m * NormedSpace.exp (s • a)‖ ≤ Real.exp (t * ‖a‖) * ‖m‖ := by
  have e1 := norm_exp_smul_le' h1 a (sub_nonneg.2 hst)
  have e2 := norm_exp_smul_le' h1 a hs
  calc ‖NormedSpace.exp ((t - s) • a) * m * NormedSpace.exp (s • a)‖
      ≤ ‖NormedSpace.exp ((t - s) • a)‖ * ‖m‖ * ‖NormedSpace.exp (s • a)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp ((t - s) * ‖a‖) * ‖m‖ * Real.exp (s * ‖a‖) := by gcongr
    _ = Real.exp (t * ‖a‖) * ‖m‖ := by
        rw [mul_right_comm, ← Real.exp_add]
        ring_nf

/-- `‖Φ_t(m)‖ ≤ t e^{t ‖a‖} ‖m‖` for `t ≥ 0`. -/
theorem norm_runPhi_le (a m : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖runPhi a m t‖ ≤ t * Real.exp (t * ‖a‖) * ‖m‖ := by
  have h := norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s : ℝ => NormedSpace.exp ((t - s) • a) * m * NormedSpace.exp (s • a))
    (C := Real.exp (t * ‖a‖) * ‖m‖) fun s hs => by
      rw [Set.uIoc_of_le ht] at hs
      exact norm_runIntegrand_le h1 a m hs.1.le hs.2
  rw [sub_zero, abs_of_nonneg ht] at h
  unfold runPhi
  exact h.trans_eq (by ring)

/-- **The accumulated half step over a short interval:** `‖Φ_h(m) - h m‖ ≤ h ‖m‖ (e^{h‖a‖} - 1)`
for `h ≥ 0`. -/
theorem norm_runPhi_sub_smul_le (a m : 𝔸) {h : ℝ} (hh : 0 ≤ h) :
    ‖runPhi a m h - h • m‖ ≤ h * ‖m‖ * (Real.exp (h * ‖a‖) - 1) := by
  have e : runPhi a m h - h • m =
      ∫ s in (0 : ℝ)..h, (NormedSpace.exp ((h - s) • a) * m * NormedSpace.exp (s • a) - m) := by
    rw [integral_sub ((continuous_runIntegrand a m h).intervalIntegrable 0 h)
      intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, runPhi]
  rw [e]
  have hb := norm_integral_le_of_norm_le_const (a := 0) (b := h)
    (f := fun s : ℝ => NormedSpace.exp ((h - s) • a) * m * NormedSpace.exp (s • a) - m)
    (C := ‖m‖ * (Real.exp (h * ‖a‖) - 1)) fun s hs => by
      rw [Set.uIoc_of_le hh] at hs
      have hs0 : 0 ≤ s := hs.1.le
      have hsh : 0 ≤ h - s := sub_nonneg.2 hs.2
      have d : NormedSpace.exp ((h - s) • a) * m * NormedSpace.exp (s • a) - m =
          (NormedSpace.exp ((h - s) • a) - 1) * m * NormedSpace.exp (s • a) +
            m * (NormedSpace.exp (s • a) - 1) := by noncomm_ring
      rw [d]
      have k1 := norm_exp_smul_sub_one_le' h1 a hsh
      have k2 := norm_exp_smul_sub_one_le' h1 a hs0
      have k3 := norm_exp_smul_le' h1 a hs0
      have n1 : ‖(NormedSpace.exp ((h - s) • a) - 1) * m * NormedSpace.exp (s • a)‖ ≤
          (Real.exp ((h - s) * ‖a‖) - 1) * ‖m‖ * Real.exp (s * ‖a‖) :=
        (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right k1 (norm_nonneg _))) k3 (norm_nonneg _)
          (mul_nonneg ((norm_nonneg _).trans k1) (norm_nonneg _)))
      have n2 : ‖m * (NormedSpace.exp (s • a) - 1)‖ ≤ ‖m‖ * (Real.exp (s * ‖a‖) - 1) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left k2 (norm_nonneg _))
      have e4 : Real.exp ((h - s) * ‖a‖) * Real.exp (s * ‖a‖) = Real.exp (h * ‖a‖) := by
        rw [← Real.exp_add]
        ring_nf
      refine (norm_add_le _ _).trans ?_
      nlinarith [Real.exp_pos (s * ‖a‖), norm_nonneg m]
  rw [sub_zero, abs_of_nonneg hh] at hb
  exact hb.trans_eq (by ring)

/-- **Continuity in `t`:** for `t, h ≥ 0`,
`‖Φ_{t+h}(m) - Φ_t(m)‖ ≤ h e^{(h + t) ‖a‖} ‖m‖ (1 + t ‖a‖)`. -/
theorem norm_runPhi_add_sub_le (a m : 𝔸) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    ‖runPhi a m (t + h) - runPhi a m t‖ ≤
      h * Real.exp ((h + t) * ‖a‖) * ‖m‖ * (1 + t * ‖a‖) := by
  rw [runPhi_add]
  have e : NormedSpace.exp (h • a) * runPhi a m t + runPhi a m h * NormedSpace.exp (t • a) -
      runPhi a m t = (NormedSpace.exp (h • a) - 1) * runPhi a m t +
        runPhi a m h * NormedSpace.exp (t • a) := by noncomm_ring
  rw [e]
  have k1 := norm_exp_smul_sub_one_le' h1 a hh
  have k2 := norm_runPhi_le h1 a m ht
  have k3 := norm_runPhi_le h1 a m hh
  have k4 := norm_exp_smul_le' h1 a ht
  have hexp : Real.exp (h * ‖a‖) - 1 ≤ h * ‖a‖ * Real.exp (h * ‖a‖) := by
    have := Real.add_one_le_exp (-(h * ‖a‖))
    have h5 : Real.exp (-(h * ‖a‖)) * Real.exp (h * ‖a‖) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (h * ‖a‖), Real.exp_pos (-(h * ‖a‖))]
  have n1 : ‖(NormedSpace.exp (h • a) - 1) * runPhi a m t‖ ≤
      h * ‖a‖ * Real.exp (h * ‖a‖) * (t * Real.exp (t * ‖a‖) * ‖m‖) :=
    (norm_mul_le _ _).trans (mul_le_mul (k1.trans hexp) k2 (norm_nonneg _)
      (by have := Real.exp_pos (h * ‖a‖); positivity))
  have n2 : ‖runPhi a m h * NormedSpace.exp (t • a)‖ ≤
      h * Real.exp (h * ‖a‖) * ‖m‖ * Real.exp (t * ‖a‖) :=
    (norm_mul_le _ _).trans (mul_le_mul k3 k4 (norm_nonneg _)
      (by have := Real.exp_pos (h * ‖a‖); positivity))
  have e5 : Real.exp ((h + t) * ‖a‖) = Real.exp (h * ‖a‖) * Real.exp (t * ‖a‖) := by
    rw [← Real.exp_add]
    ring_nf
  refine (norm_add_le _ _).trans ?_
  rw [e5]
  nlinarith [n1, n2]

/-- **Coercivity:** `‖Φ_T(m)‖ ≥ T (2 - e^{T ‖a‖}) ‖m‖` for `T ≥ 0`. -/
theorem norm_runPhi_ge (a m : 𝔸) {T : ℝ} (hT : 0 ≤ T) :
    T * (2 - Real.exp (T * ‖a‖)) * ‖m‖ ≤ ‖runPhi a m T‖ := by
  have h := norm_runPhi_sub_smul_le h1 a m hT
  have h2 := norm_sub_norm_le (T • m) (T • m - runPhi a m T)
  rw [sub_sub_cancel, norm_sub_rev, norm_smul, Real.norm_of_nonneg hT] at h2
  nlinarith

end RunAlgebra

section RunDiscrete

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The discrete accumulation** `S_k = H Σ_{j<k} u^{k-1-j} m u^j`, by its recursion
`S_0 = 0`, `S_{k+1} = u S_k + H m u^k`. -/
noncomputable def runSum (u m : 𝔸) (H : ℝ) : ℕ → 𝔸
  | 0 => 0
  | k + 1 => u * runSum u m H k + H • (m * u ^ k)

theorem runSum_zero (u m : 𝔸) (H : ℝ) : runSum u m H 0 = 0 := rfl

theorem runSum_succ (u m : 𝔸) (H : ℝ) (k : ℕ) :
    runSum u m H (k + 1) = u * runSum u m H k + H • (m * u ^ k) := rfl

/-- **The recursion of the run.** With `F_k = (x^k - u^k) - H S_k`:
`F_{k+1} = x F_k + (x - u) (H S_k) + (x - u - H² m) u^k`. -/
theorem run_recursion (x u m : 𝔸) (H : ℝ) (k : ℕ) :
    x ^ (k + 1) - u ^ (k + 1) - H • runSum u m H (k + 1) =
      x * (x ^ k - u ^ k - H • runSum u m H k) + (x - u) * (H • runSum u m H k) +
        (x - u - H ^ 2 • m) * u ^ k := by
  rw [runSum_succ, pow_succ', pow_succ', smul_add, smul_smul, ← sq, mul_sub, mul_sub, sub_mul,
    sub_mul, sub_mul, mul_smul_comm, mul_smul_comm]
  simp only [smul_mul_assoc]
  abel

variable (h1 : ‖(1 : 𝔸)‖ ≤ 1)
include h1

/-- `‖(e^{Ha})^k‖ ≤ e^{k H ‖a‖}` for `H ≥ 0`. -/
theorem norm_exp_pow_le (a : 𝔸) {H : ℝ} (hH : 0 ≤ H) (k : ℕ) :
    ‖NormedSpace.exp (H • a) ^ k‖ ≤ Real.exp (k * H * ‖a‖) := by
  rw [← exp_natCast_mul_smul]
  exact norm_exp_smul_le' h1 a (by positivity)

/-- `‖S_k‖ ≤ k H e^{k H ‖a‖} ‖m‖` for `u = e^{Ha}`, `H ≥ 0`. -/
theorem norm_runSum_le (a m : 𝔸) {H : ℝ} (hH : 0 ≤ H) (k : ℕ) :
    ‖runSum (NormedSpace.exp (H • a)) m H k‖ ≤ k * H * Real.exp (k * H * ‖a‖) * ‖m‖ := by
  induction k with
  | zero => simp [runSum_zero]
  | succ k ih =>
    rw [runSum_succ]
    have hu := norm_exp_smul_le' h1 a hH
    have hp := norm_exp_pow_le h1 a hH k
    have e : Real.exp (((k + 1 : ℕ) : ℝ) * H * ‖a‖) =
        Real.exp (H * ‖a‖) * Real.exp (k * H * ‖a‖) := by
      rw [← Real.exp_add]
      push_cast
      ring_nf
    have hE1 : 1 ≤ Real.exp (H * ‖a‖) := Real.one_le_exp (by positivity)
    have hEk := Real.exp_pos (k * H * ‖a‖)
    have n1 : ‖NormedSpace.exp (H • a) * runSum (NormedSpace.exp (H • a)) m H k‖ ≤
        Real.exp (H * ‖a‖) * (k * H * Real.exp (k * H * ‖a‖) * ‖m‖) :=
      (norm_mul_le _ _).trans (mul_le_mul hu ih (norm_nonneg _) (Real.exp_pos _).le)
    have n2 : ‖H • (m * NormedSpace.exp (H • a) ^ k)‖ ≤ H * (‖m‖ * Real.exp (k * H * ‖a‖)) := by
      rw [norm_smul, Real.norm_of_nonneg hH]
      exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left hp (norm_nonneg _))) hH
    have n3 : H * (‖m‖ * Real.exp (k * H * ‖a‖)) ≤
        H * (‖m‖ * (Real.exp (H * ‖a‖) * Real.exp (k * H * ‖a‖))) := by
      gcongr
      exact le_mul_of_one_le_left hEk.le hE1
    refine (norm_add_le _ _).trans ?_
    rw [e]
    push_cast
    nlinarith [norm_nonneg m]

/-- **The integral against the discrete accumulation:**
`‖Φ_{kH}(m) - S_k‖ ≤ k e^{k H ‖a‖} H ‖m‖ (e^{H‖a‖} - 1)` for `u = e^{Ha}`, `H ≥ 0`. -/
theorem norm_runPhi_sub_runSum_le (a m : 𝔸) {H : ℝ} (hH : 0 ≤ H) (k : ℕ) :
    ‖runPhi a m (k * H) - runSum (NormedSpace.exp (H • a)) m H k‖ ≤
      k * Real.exp (k * H * ‖a‖) * (H * ‖m‖ * (Real.exp (H * ‖a‖) - 1)) := by
  induction k with
  | zero => simp [runSum_zero, runPhi_zero]
  | succ k ih =>
    have e1 : runPhi a m (((k + 1 : ℕ) : ℝ) * H) =
        NormedSpace.exp (H • a) * runPhi a m (k * H) +
          runPhi a m H * NormedSpace.exp (H • a) ^ k := by
      rw [show ((k + 1 : ℕ) : ℝ) * H = k * H + H by push_cast; ring, runPhi_add,
        exp_natCast_mul_smul]
    have e2 : runPhi a m (((k + 1 : ℕ) : ℝ) * H) -
        runSum (NormedSpace.exp (H • a)) m H (k + 1) =
        NormedSpace.exp (H • a) *
          (runPhi a m (k * H) - runSum (NormedSpace.exp (H • a)) m H k) +
          (runPhi a m H - H • m) * NormedSpace.exp (H • a) ^ k := by
      rw [e1, runSum_succ, mul_sub, sub_mul, smul_mul_assoc]
      abel
    rw [e2]
    have hu := norm_exp_smul_le' h1 a hH
    have hp := norm_exp_pow_le h1 a hH k
    have hd := norm_runPhi_sub_smul_le h1 a m hH
    have hE1 : 1 ≤ Real.exp (H * ‖a‖) := Real.one_le_exp (by positivity)
    have hδ : 0 ≤ H * ‖m‖ * (Real.exp (H * ‖a‖) - 1) := by
      have := norm_nonneg m
      have : 0 ≤ Real.exp (H * ‖a‖) - 1 := by linarith
      positivity
    have e : Real.exp (((k + 1 : ℕ) : ℝ) * H * ‖a‖) =
        Real.exp (H * ‖a‖) * Real.exp (k * H * ‖a‖) := by
      rw [← Real.exp_add]
      push_cast
      ring_nf
    have hEk := Real.exp_pos (k * H * ‖a‖)
    have n1 := (norm_mul_le (NormedSpace.exp (H • a))
      (runPhi a m (k * H) - runSum (NormedSpace.exp (H • a)) m H k)).trans
      (mul_le_mul hu ih (norm_nonneg _) (Real.exp_pos _).le)
    have n2 := (norm_mul_le (runPhi a m H - H • m) (NormedSpace.exp (H • a) ^ k)).trans
      (mul_le_mul hd hp (norm_nonneg _) hδ)
    have n3 : H * ‖m‖ * (Real.exp (H * ‖a‖) - 1) * Real.exp (k * H * ‖a‖) ≤
        H * ‖m‖ * (Real.exp (H * ‖a‖) - 1) * (Real.exp (H * ‖a‖) * Real.exp (k * H * ‖a‖)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hEk.le hE1) hδ
    refine (norm_add_le _ _).trans ?_
    rw [e]
    push_cast
    nlinarith

/-- **The run against its accumulation**. Let `u = e^{Ha}`, `H ≥ 0`, `‖x‖ ≤ ρ`, `1 ≤ ρ`,
`‖x - u‖ ≤ c H²`, `‖x - u - H² m‖ ≤ C₁ H³`, `c, C₁ ≥ 0`. Then for `k H ≤ T`:
`‖(x^k - u^k) - H S_k‖ ≤ k ρ^k H³ e^{T‖a‖} (c T ‖m‖ + C₁)`. -/
theorem norm_runF_le (a m x : 𝔸) {H T ρ c C₁ : ℝ} (hH : 0 ≤ H) (hρ : 1 ≤ ρ)
    (hc0 : 0 ≤ c) (hC0 : 0 ≤ C₁) (hx : ‖x‖ ≤ ρ)
    (hc : ‖x - NormedSpace.exp (H • a)‖ ≤ c * H ^ 2)
    (hC : ‖x - NormedSpace.exp (H • a) - H ^ 2 • m‖ ≤ C₁ * H ^ 3) :
    ∀ k : ℕ, (k : ℝ) * H ≤ T →
      ‖x ^ k - NormedSpace.exp (H • a) ^ k - H • runSum (NormedSpace.exp (H • a)) m H k‖ ≤
        k * ρ ^ k * (H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁)) := by
  intro k
  induction k with
  | zero => intro _; simp [runSum_zero]
  | succ k ih =>
    intro hk
    have hk' : (k : ℝ) * H ≤ T := le_trans (by push_cast; nlinarith) hk
    have hT : 0 ≤ T := le_trans (by positivity) hk'
    have ihk := ih hk'
    rw [run_recursion]
    have hS := norm_runSum_le h1 a m hH k
    have hp := norm_exp_pow_le h1 a hH k
    have hEk : Real.exp (k * H * ‖a‖) ≤ Real.exp (T * ‖a‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hk' (norm_nonneg _))
    have hm := norm_nonneg m
    have hδ : 0 ≤ H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁) :=
      mul_nonneg (mul_nonneg (pow_nonneg hH 3) (Real.exp_pos _).le)
        (add_nonneg (mul_nonneg (mul_nonneg hc0 hT) hm) hC0)
    have hρk : 1 ≤ ρ ^ k := one_le_pow₀ hρ
    have n1 : ‖x * (x ^ k - NormedSpace.exp (H • a) ^ k -
        H • runSum (NormedSpace.exp (H • a)) m H k)‖ ≤
        ρ * (k * ρ ^ k * (H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁))) :=
      (norm_mul_le _ _).trans (mul_le_mul hx ihk (norm_nonneg _) (by linarith))
    have h2 : H * ‖runSum (NormedSpace.exp (H • a)) m H k‖ ≤
        H * (T * Real.exp (T * ‖a‖) * ‖m‖) := by
      refine mul_le_mul_of_nonneg_left (hS.trans ?_) hH
      have := Real.exp_pos (k * H * ‖a‖)
      gcongr
    have n2 : ‖(x - NormedSpace.exp (H • a)) * (H • runSum (NormedSpace.exp (H • a)) m H k)‖ ≤
        c * H ^ 2 * (H * (T * Real.exp (T * ‖a‖) * ‖m‖)) := by
      refine (norm_mul_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hH]
      exact mul_le_mul hc h2 (by positivity) (by positivity)
    have n3 : ‖(x - NormedSpace.exp (H • a) - H ^ 2 • m) * NormedSpace.exp (H • a) ^ k‖ ≤
        C₁ * H ^ 3 * Real.exp (T * ‖a‖) :=
      (norm_mul_le _ _).trans (mul_le_mul hC (hp.trans hEk) (norm_nonneg _) (by positivity))
    have h3 : H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁) ≤
        ρ ^ (k + 1) * (H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁)) :=
      le_mul_of_one_le_left hδ (one_le_pow₀ hρ)
    refine (norm_add₃_le).trans ?_
    have e : ρ * (k * ρ ^ k * (H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁))) =
        k * ρ ^ (k + 1) * (H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁)) := by
      rw [pow_succ]
      ring
    have e2 : c * H ^ 2 * (H * (T * Real.exp (T * ‖a‖) * ‖m‖)) +
        C₁ * H ^ 3 * Real.exp (T * ‖a‖) = H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁) := by
      ring
    push_cast
    nlinarith

/-- **The run against the accumulated half step** (main estimate). Under the hypotheses of
`norm_runF_le`, for `0 < H` and `k H ≤ T`:
`‖x^k - u^k - H Φ_{kH}(m)‖ ≤ T e^{T‖a‖} (ρ^k (c T ‖m‖ + C₁) + ‖m‖ ‖a‖ e^{H‖a‖}) H²`. -/
theorem norm_run_sub_runPhi_le (a m x : 𝔸) {H T ρ c C₁ : ℝ} (hH : 0 < H) (hρ : 1 ≤ ρ)
    (hc0 : 0 ≤ c) (hC0 : 0 ≤ C₁) (hx : ‖x‖ ≤ ρ)
    (hc : ‖x - NormedSpace.exp (H • a)‖ ≤ c * H ^ 2)
    (hC : ‖x - NormedSpace.exp (H • a) - H ^ 2 • m‖ ≤ C₁ * H ^ 3) (k : ℕ)
    (hk : (k : ℝ) * H ≤ T) :
    ‖x ^ k - NormedSpace.exp (H • a) ^ k - H • runPhi a m (k * H)‖ ≤
      T * Real.exp (T * ‖a‖) * (ρ ^ k * (c * T * ‖m‖ + C₁) +
        ‖m‖ * ‖a‖ * Real.exp (H * ‖a‖)) * H ^ 2 := by
  have hT : 0 ≤ T := le_trans (by positivity) hk
  have hTe : 0 ≤ T * Real.exp (T * ‖a‖) := mul_nonneg hT (Real.exp_pos _).le
  have hF := norm_runF_le h1 a m x hH.le hρ hc0 hC0 hx hc hC k hk
  have hD := norm_runPhi_sub_runSum_le h1 a m hH.le k
  have e : x ^ k - NormedSpace.exp (H • a) ^ k - H • runPhi a m (k * H) =
      (x ^ k - NormedSpace.exp (H • a) ^ k - H • runSum (NormedSpace.exp (H • a)) m H k) -
        H • (runPhi a m (k * H) - runSum (NormedSpace.exp (H • a)) m H k) := by
    rw [smul_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hH.le]
  have hEk : Real.exp (k * H * ‖a‖) ≤ Real.exp (T * ‖a‖) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
  have hexp : Real.exp (H * ‖a‖) - 1 ≤ H * ‖a‖ * Real.exp (H * ‖a‖) := by
    have := Real.add_one_le_exp (-(H * ‖a‖))
    have h5 : Real.exp (-(H * ‖a‖)) * Real.exp (H * ‖a‖) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (H * ‖a‖), Real.exp_pos (-(H * ‖a‖))]
  have hm := norm_nonneg m
  have hρk : 0 ≤ ρ ^ k := by positivity
  have hE1 : 1 ≤ Real.exp (H * ‖a‖) := Real.one_le_exp (by positivity)
  have t1 : (k : ℝ) * ρ ^ k * (H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁)) ≤
      T * Real.exp (T * ‖a‖) * (ρ ^ k * (c * T * ‖m‖ + C₁)) * H ^ 2 := by
    have h2 : (k : ℝ) * H * (ρ ^ k * (H ^ 2 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁))) ≤
        T * (ρ ^ k * (H ^ 2 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁))) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    calc (k : ℝ) * ρ ^ k * (H ^ 3 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁))
        = (k : ℝ) * H * (ρ ^ k * (H ^ 2 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁))) := by ring
      _ ≤ T * (ρ ^ k * (H ^ 2 * Real.exp (T * ‖a‖) * (c * T * ‖m‖ + C₁))) := h2
      _ = T * Real.exp (T * ‖a‖) * (ρ ^ k * (c * T * ‖m‖ + C₁)) * H ^ 2 := by ring
  have t2 : H * ((k : ℝ) * Real.exp (k * H * ‖a‖) * (H * ‖m‖ * (Real.exp (H * ‖a‖) - 1))) ≤
      T * Real.exp (T * ‖a‖) * (‖m‖ * ‖a‖ * Real.exp (H * ‖a‖)) * H ^ 2 := by
    have h4 : 0 ≤ Real.exp (H * ‖a‖) - 1 := by linarith
    calc H * ((k : ℝ) * Real.exp (k * H * ‖a‖) * (H * ‖m‖ * (Real.exp (H * ‖a‖) - 1)))
        = ((k : ℝ) * H) * Real.exp (k * H * ‖a‖) * (H * ‖m‖ * (Real.exp (H * ‖a‖) - 1)) := by
          ring
      _ ≤ T * Real.exp (T * ‖a‖) * (H * ‖m‖ * (H * ‖a‖ * Real.exp (H * ‖a‖))) := by
          gcongr
      _ = T * Real.exp (T * ‖a‖) * (‖m‖ * ‖a‖ * Real.exp (H * ‖a‖)) * H ^ 2 := by ring
  have t3 := mul_le_mul_of_nonneg_left hD hH.le
  nlinarith

end RunDiscrete

section RunMax

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The largest accumulated half step over `[0, T]`**, `G(m) = sup_{0 ≤ t ≤ T} ‖Φ_t(m)‖`. -/
noncomputable def runMax (a m : 𝔸) (T : ℝ) : ℝ := ⨆ t : Set.Icc (0 : ℝ) T, ‖runPhi a m t‖

/-- The largest accumulated half step over the grid `k H`, `k ≤ K`. -/
noncomputable def gridMax (a m : 𝔸) (H : ℝ) (K : ℕ) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => ‖runPhi a m (k * H)‖

/-- **The error over a run** `ε_K = max_{k ≤ K} ‖x^k - u^k‖`. -/
noncomputable def runErr (x u : 𝔸) (K : ℕ) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => ‖x ^ k - u ^ k‖

/-- The constant of the run: `T e^{Tα} (B (c T M + C₁) + M α e^{Hα}) + e^{Tα} M (1 + T α)`. -/
noncomputable def runConst (T α B c C₁ M H : ℝ) : ℝ :=
  T * Real.exp (T * α) * (B * (c * T * M + C₁) + M * α * Real.exp (H * α)) +
    Real.exp (T * α) * M * (1 + T * α)

/-- The constant of the run is monotone in `B` and `M`. -/
theorem runConst_mono {T α B B' c C₁ M M' H : ℝ} (hT : 0 ≤ T) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hC : 0 ≤ C₁) (hM : 0 ≤ M) (hB : 0 ≤ B) (hBB : B ≤ B') (hMM : M ≤ M') :
    runConst T α B c C₁ M H ≤ runConst T α B' c C₁ M' H := by
  unfold runConst
  have hM' : 0 ≤ M' := hM.trans hMM
  have hB' : 0 ≤ B' := hB.trans hBB
  gcongr

variable (h1 : ‖(1 : 𝔸)‖ ≤ 1)
include h1

theorem bddAbove_runPhi (a m : 𝔸) (T : ℝ) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => ‖runPhi a m t‖) := by
  refine ⟨T * Real.exp (T * ‖a‖) * ‖m‖, ?_⟩
  rintro _ ⟨⟨t, ht0, htT⟩, rfl⟩
  refine (norm_runPhi_le h1 a m ht0).trans ?_
  have := norm_nonneg m
  have := Real.exp_pos (t * ‖a‖)
  have hT : 0 ≤ T := ht0.trans htT
  gcongr

theorem le_runMax (a m : 𝔸) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖runPhi a m t‖ ≤ runMax a m T :=
  le_ciSup (f := fun t : Set.Icc (0 : ℝ) T => ‖runPhi a m t‖) (bddAbove_runPhi h1 a m T)
    ⟨t, ht0, htT⟩

omit h1 in
theorem runMax_le (a m : 𝔸) {T B : ℝ} (hT : 0 ≤ T)
    (h : ∀ t, 0 ≤ t → t ≤ T → ‖runPhi a m t‖ ≤ B) : runMax a m T ≤ B := by
  have : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_refl _, hT⟩⟩
  exact ciSup_le fun t => h t t.2.1 t.2.2

/-- **`G` is Lipschitz in `m`:** `G(m) ≤ G(m') + T e^{T‖a‖} ‖m - m'‖` for `T ≥ 0`. -/
theorem runMax_le_add (a m m' : 𝔸) {T : ℝ} (hT : 0 ≤ T) :
    runMax a m T ≤ runMax a m' T + T * Real.exp (T * ‖a‖) * ‖m - m'‖ := by
  refine runMax_le a m hT fun t ht0 htT => ?_
  have e : runPhi a m t = runPhi a m' t + runPhi a (m - m') t := by rw [runPhi_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (le_runMax h1 a m' ht0 htT) ?_)
  refine (norm_runPhi_le h1 a (m - m') ht0).trans ?_
  have := norm_nonneg (m - m')
  have := Real.exp_pos (t * ‖a‖)
  gcongr

/-- **`G` is coercive:** `T (2 - e^{T‖a‖}) ‖m‖ ≤ G(m)` for `T ≥ 0`. -/
theorem runMax_ge (a m : 𝔸) {T : ℝ} (hT : 0 ≤ T) :
    T * (2 - Real.exp (T * ‖a‖)) * ‖m‖ ≤ runMax a m T :=
  (norm_runPhi_ge h1 a m hT).trans (le_runMax h1 a m hT le_rfl)

/-- The grid lies in `[0, T]`: `max_{k ≤ K} ‖Φ_{kH}‖ ≤ G(m)` for `H ≥ 0`, `K H ≤ T`. -/
theorem gridMax_le_runMax (a m : 𝔸) {H T : ℝ} (hH : 0 ≤ H) {K : ℕ} (hK : (K : ℝ) * H ≤ T) :
    gridMax a m H K ≤ runMax a m T := by
  refine Finset.sup'_le _ _ fun k hk => le_runMax h1 a m (by positivity) ?_
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  exact le_trans (mul_le_mul_of_nonneg_right hk' hH) hK

/-- **The grid is fine:** for `0 < H`, `0 ≤ T` and `K = ⌊T/H⌋`,
`G(m) ≤ max_{k ≤ K} ‖Φ_{kH}(m)‖ + H e^{T‖a‖} ‖m‖ (1 + T‖a‖)`. -/
theorem runMax_le_gridMax (a m : 𝔸) {H T : ℝ} (hH : 0 < H) (hT : 0 ≤ T) :
    runMax a m T ≤ gridMax a m H ⌊T / H⌋₊ +
      H * (Real.exp (T * ‖a‖) * ‖m‖ * (1 + T * ‖a‖)) := by
  refine runMax_le a m hT fun t ht0 htT => ?_
  set k := ⌊t / H⌋₊
  have hk1 : (k : ℝ) * H ≤ t := by
    have := Nat.floor_le (div_nonneg ht0 hH.le)
    rwa [le_div_iff₀ hH] at this
  have hk2 : t < ((k : ℝ) + 1) * H := by
    have := Nat.lt_floor_add_one (t / H)
    rwa [div_lt_iff₀ hH] at this
  have hkK : k ≤ ⌊T / H⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_right htT hH.le)
  have hk0 : 0 ≤ (k : ℝ) * H := by positivity
  have e : t = (k : ℝ) * H + (t - k * H) := by ring
  have h2 := norm_runPhi_add_sub_le h1 a m hk0 (sub_nonneg.2 hk1)
  rw [← e] at h2
  have h3 : ‖runPhi a m (k * H)‖ ≤ gridMax a m H ⌊T / H⌋₊ :=
    Finset.le_sup' (fun k : ℕ => ‖runPhi a m (k * H)‖)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hkK))
  have h4 : (t - k * H) * Real.exp ((t - k * H + k * H) * ‖a‖) * ‖m‖ * (1 + k * H * ‖a‖) ≤
      H * (Real.exp (T * ‖a‖) * ‖m‖ * (1 + T * ‖a‖)) := by
    rw [sub_add_cancel]
    have h5 : t - k * H ≤ H := by linarith
    have := norm_nonneg m
    have := norm_nonneg a
    have h6 : (k : ℝ) * H ≤ T := hk1.trans htT
    calc (t - k * H) * Real.exp (t * ‖a‖) * ‖m‖ * (1 + k * H * ‖a‖)
        ≤ H * Real.exp (T * ‖a‖) * ‖m‖ * (1 + T * ‖a‖) := by
          gcongr
      _ = H * (Real.exp (T * ‖a‖) * ‖m‖ * (1 + T * ‖a‖)) := by ring
  have h7 := norm_sub_norm_le (runPhi a m t) (runPhi a m (k * H))
  linarith

/-- **The error over a run and the accumulated half step** (`ε_K = H G(m) + O(H²)`). Let
`u = e^{Ha}`, `0 < H`, `0 ≤ T`, `K = ⌊T/H⌋`, `‖x‖ ≤ ρ`, `1 ≤ ρ`, `‖x - u‖ ≤ c H²`,
`‖x - u - H² m‖ ≤ C₁ H³`, `c, C₁ ≥ 0`. Then
`|ε_K - H G(m)| ≤ runConst T ‖a‖ ρ^K c C₁ ‖m‖ H · H²`. -/
theorem abs_runErr_sub_runMax_le (a m x : 𝔸) {H T ρ c C₁ : ℝ} (hH : 0 < H) (hT : 0 ≤ T)
    (hρ : 1 ≤ ρ) (hc0 : 0 ≤ c) (hC0 : 0 ≤ C₁) (hx : ‖x‖ ≤ ρ)
    (hc : ‖x - NormedSpace.exp (H • a)‖ ≤ c * H ^ 2)
    (hC : ‖x - NormedSpace.exp (H • a) - H ^ 2 • m‖ ≤ C₁ * H ^ 3) :
    |runErr x (NormedSpace.exp (H • a)) ⌊T / H⌋₊ - H * runMax a m T| ≤
      runConst T ‖a‖ (ρ ^ ⌊T / H⌋₊) c C₁ ‖m‖ H * H ^ 2 := by
  set K := ⌊T / H⌋₊
  have hKT : (K : ℝ) * H ≤ T := by
    have := Nat.floor_le (div_nonneg hT hH.le)
    rwa [le_div_iff₀ hH] at this
  set E := T * Real.exp (T * ‖a‖) * (ρ ^ K * (c * T * ‖m‖ + C₁) +
    ‖m‖ * ‖a‖ * Real.exp (H * ‖a‖)) * H ^ 2
  have hm := norm_nonneg m
  -- each step of the grid
  have hstep : ∀ k ∈ Finset.range (K + 1),
      |‖x ^ k - NormedSpace.exp (H • a) ^ k‖ - H * ‖runPhi a m (k * H)‖| ≤ E := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hk : (k : ℝ) * H ≤ T :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkK) hH.le) hKT
    have h2 := norm_run_sub_runPhi_le h1 a m x hH hρ hc0 hC0 hx hc hC k hk
    have h3 := abs_norm_sub_norm_le (x ^ k - NormedSpace.exp (H • a) ^ k)
      (H • runPhi a m (k * H))
    rw [norm_smul, Real.norm_of_nonneg hH.le] at h3
    refine h3.trans (h2.trans ?_)
    have hρk : ρ ^ k ≤ ρ ^ K := pow_le_pow_right₀ hρ hkK
    have := Real.exp_pos (T * ‖a‖)
    have := Real.exp_pos (H * ‖a‖)
    have hTe : 0 ≤ T * Real.exp (T * ‖a‖) := by positivity
    have hcm : 0 ≤ c * T * ‖m‖ + C₁ := by positivity
    have h5 : T * Real.exp (T * ‖a‖) * (ρ ^ k * (c * T * ‖m‖ + C₁) +
        ‖m‖ * ‖a‖ * Real.exp (H * ‖a‖)) * H ^ 2 ≤ T * Real.exp (T * ‖a‖) *
        (ρ ^ K * (c * T * ‖m‖ + C₁) + ‖m‖ * ‖a‖ * Real.exp (H * ‖a‖)) * H ^ 2 := by
      gcongr
    exact h5
  -- the two sides
  have hup : runErr x (NormedSpace.exp (H • a)) K ≤ H * gridMax a m H K + E := by
    refine Finset.sup'_le _ _ fun k hk => ?_
    have h2 := (abs_le.1 (hstep k hk)).2
    have h3 : ‖runPhi a m (k * H)‖ ≤ gridMax a m H K :=
      Finset.le_sup' (fun k : ℕ => ‖runPhi a m (k * H)‖) hk
    nlinarith
  have hlo : H * gridMax a m H K ≤ runErr x (NormedSpace.exp (H • a)) K + E := by
    have h4 : gridMax a m H K ≤ (runErr x (NormedSpace.exp (H • a)) K + E) / H := by
      refine Finset.sup'_le _ _ fun k hk => ?_
      rw [le_div_iff₀ hH]
      have h2 := (abs_le.1 (hstep k hk)).1
      have h3 : ‖x ^ k - NormedSpace.exp (H • a) ^ k‖ ≤ runErr x (NormedSpace.exp (H • a)) K :=
        Finset.le_sup' (fun k : ℕ => ‖x ^ k - NormedSpace.exp (H • a) ^ k‖) hk
      linarith
    rw [le_div_iff₀ hH] at h4
    linarith
  have hg1 := gridMax_le_runMax h1 a m hH.le hKT
  have hg2 := runMax_le_gridMax h1 a m hH hT
  have e : runConst T ‖a‖ (ρ ^ K) c C₁ ‖m‖ H * H ^ 2 =
      E + H * (H * (Real.exp (T * ‖a‖) * ‖m‖ * (1 + T * ‖a‖))) := by
    simp only [E, runConst]
    ring
  rw [e, abs_le]
  constructor
  · nlinarith
  · nlinarith

end RunMax

/-! ### The least value is attained -/

section Minimiser

variable {n : ℕ}

/-- **A Lipschitz and coercive function attains its least value on a subspace** (finite
dimension). If `f Z ≤ f Z' + L ‖Z - Z'‖` and `f Z ≥ c ‖Z‖ - d` on `𝓡` with `c > 0` (spectral
norms), then `f` has a least value on `𝓡`. -/
theorem exists_forall_le_of_coercive {𝓡 : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    {f : Matrix (Fin n) (Fin n) ℝ → ℝ} {L c d : ℝ}
    (hf : ∀ Z Z', f Z ≤ f Z' + L * ‖opE (Z - Z')‖) (hc : 0 < c)
    (hcoer : ∀ Z ∈ 𝓡, c * ‖opE Z‖ - d ≤ f Z) :
    ∃ Z₀ ∈ 𝓡, ∀ Z ∈ 𝓡, f Z₀ ≤ f Z := by
  have : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearMap.finiteDimensional
  let Lm : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    { toFun := opE
      map_add' := OneStep.opE_add
      map_smul' := fun c A => OneStep.opE_smul c A }
  let V := 𝓡.map Lm
  have hV : IsClosed (V : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
    V.closed_of_finiteDimensional
  let e := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
  let g : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) → ℝ := fun T => f (e.symm T)
  have hopE : ∀ T, opE (e.symm T) = T := fun T => e.apply_symm_apply T
  have hL : 0 ≤ L ∨ ∀ Z Z' : Matrix (Fin n) (Fin n) ℝ, f Z ≤ f Z' := by
    by_cases h : 0 ≤ L
    · exact Or.inl h
    · refine Or.inr fun Z Z' => (hf Z Z').trans ?_
      have := norm_nonneg (opE (Z - Z'))
      nlinarith
  have hg : Continuous g := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) fun T T' => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]
    have h1 := hf (e.symm T) (e.symm T')
    have h2 := hf (e.symm T') (e.symm T)
    have n1 : ‖opE (e.symm T - e.symm T')‖ = ‖T - T'‖ := by rw [OneStep.opE_sub, hopE, hopE]
    have n2 : ‖opE (e.symm T' - e.symm T)‖ = ‖T - T'‖ := by
      rw [OneStep.opE_sub, hopE, hopE, norm_sub_rev]
    rw [n1] at h1
    rw [n2] at h2
    have h3 : L * ‖T - T'‖ ≤ Real.toNNReal L * ‖T - T'‖ :=
      mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _)
    rw [abs_le]
    constructor <;> linarith
  have hf0 : c * ‖opE (0 : Matrix (Fin n) (Fin n) ℝ)‖ - d ≤ f 0 := hcoer 0 𝓡.zero_mem
  rw [show opE (0 : Matrix (Fin n) (Fin n) ℝ) = 0 from map_zero _, norm_zero, mul_zero,
    zero_sub] at hf0
  set R := (f 0 + d) / c
  have hR : 0 ≤ R := div_nonneg (by linarith) hc.le
  have hK : IsCompact ((V : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∩
      Metric.closedBall 0 R) :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) R).inter_left hV
  have hne : ((V : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∩
      Metric.closedBall 0 R).Nonempty := ⟨0, V.zero_mem, Metric.mem_closedBall_self hR⟩
  obtain ⟨T₀, ⟨hT₀V, -⟩, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
  obtain ⟨Z₀, hZ₀, hT₀⟩ := Submodule.mem_map.1 hT₀V
  have hgZ : ∀ Z, g (opE Z) = f Z := fun Z => by
    show f (e.symm (e Z)) = f Z
    rw [e.symm_apply_apply]
  have hg0 : g T₀ = f Z₀ := by rw [← hT₀]; exact hgZ Z₀
  refine ⟨Z₀, hZ₀, fun Z hZ => ?_⟩
  rw [← hg0]
  by_cases hZR : ‖opE Z‖ ≤ R
  · have h := hmin ⟨Submodule.mem_map_of_mem (f := Lm) hZ, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hZR⟩
    rwa [Set.mem_ofPred_eq, show Lm Z = opE Z from rfl, hgZ] at h
  · have h := hmin ⟨V.zero_mem, Metric.mem_closedBall_self hR⟩
    rw [Set.mem_ofPred_eq, show (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      opE 0 from (map_zero _).symm, hgZ] at h
    have h2 := hcoer Z hZ
    have h3 : c * R < c * ‖opE Z‖ := mul_lt_mul_of_pos_left (lt_of_not_ge hZR) hc
    have h4 : c * R = f 0 + d := by simp only [R]; field_simp
    linarith

end Minimiser

/-! ### Schemes -/

section Schemes

variable {n : ℕ}

/-- `‖1‖ ≤ 1` for the operators on Euclidean space. -/
theorem norm_one_opE_le :
    ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 1 :=
  ContinuousLinearMap.norm_id_le

/-- `e^{1/2} < 2`. -/
theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2)]

/-- `(1 + b H)^K ≤ e^{b T}` for `b H ≥ 0`, `H > 0`, `K H ≤ T`. -/
theorem one_add_pow_le_exp {b H T : ℝ} (hH : 0 < H) (hb : 0 ≤ b * H) {K : ℕ}
    (hK : (K : ℝ) * H ≤ T) : (1 + b * H) ^ K ≤ Real.exp (b * T) := by
  have hb0 : 0 ≤ b := (mul_nonneg_iff_of_pos_right hH).1 hb
  have h1 : 1 + b * H ≤ Real.exp (b * H) := by
    have := Real.add_one_le_exp (b * H)
    linarith
  calc (1 + b * H) ^ K ≤ Real.exp (b * H) ^ K := pow_le_pow_left₀ (by linarith) h1 K
    _ = Real.exp (K * (b * H)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (b * T) := Real.exp_le_exp.2 (by nlinarith)

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] {S : HeldScheme n κ}

/-- **The least error over a run, every scheme** (the paper, eq. `eq:leastrun`, lower bound). For
a consistent scheme whose coupling and coefficients act through the outputs, started from the
initial state, `0 < H`, `0 ≤ T`, `K = ⌊T/H⌋`, and every `g` with
`g ≤ max_{0 ≤ t ≤ T} ‖Φ_t(½ A_ς A + Z)‖` for all `Z` in the reach:
`ε_K ≥ H g - runConst T ‖A‖ e^{bT} c C₁ (c + C₁ H) H · H²`, `C₁ = √(card κ) C₃`,
`C₃ = reactionC a b c ‖A‖ H`, `ε_K = max_{k ≤ K} ‖X^k - e^{kHA}‖`. -/
theorem Consistent.least_run_le [Fintype κ] {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hH : 0 < H) {Θ : Matrix (Fin n) (Fin n) ℝ}
    (hΘ : ∀ p q, S.sub p ≠ S.sub q → Θ p q = 0) (hAΘ : S.coupling A * Θ = 0)
    (hGΘ : (S.M + S.N) * Θ = 0) {T : ℝ} (hT : 0 ≤ T) {g : ℝ}
    (hg : ∀ Z ∈ S.reach Θ, g ≤ runMax (opE A) (opE (S.halfStepTerm A + Z)) T) :
    H * g - runConst T ‖opE A‖ (Real.exp (b * T)) c
        (Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H)
        (c + Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H * H) H * H ^ 2 ≤
      runErr (opE S.X) (NormedSpace.exp (H • opE A)) ⌊T / H⌋₊ := by
  set C₁ := Real.sqrt (Fintype.card κ) * reactionC a b c ‖opE A‖ H
  set m := opE (S.halfStepTerm A + S.reachLead A H)
  have hm : ‖m‖ ≤ c + C₁ * H := (h.norm_reachLead_le hH).1
  have hbH : 0 ≤ b * H := (norm_nonneg _).trans h.hb
  have hc0 : 0 ≤ c := (mul_nonneg_iff_of_pos_right (by positivity : (0 : ℝ) < H ^ 2)).1
    ((norm_nonneg _).trans h.hc)
  have hC0 : 0 ≤ C₁ := by
    have h3 := h.reaction_bound_nonneg
    have : 0 ≤ reactionC a b c ‖opE A‖ H :=
      (mul_nonneg_iff_of_pos_right (by positivity : (0 : ℝ) < H ^ 3)).1 h3
    exact mul_nonneg (Real.sqrt_nonneg _) this
  have hx : ‖opE S.X‖ ≤ 1 + b * H := by
    have e : opE S.X = opE (S.X - 1) + 1 := by rw [OneStep.opE_sub, OneStep.opE_one]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    linarith [h.hb, norm_one_opE_le (n := n)]
  have hU : opE U = NormedSpace.exp (H • opE A) := by
    rw [h.hU, OneStep.opE_exp, OneStep.opE_smul]
  have hc : ‖opE S.X - NormedSpace.exp (H • opE A)‖ ≤ c * H ^ 2 := by
    rw [← hU, ← OneStep.opE_sub]
    exact h.hc
  have hC : ‖opE S.X - NormedSpace.exp (H • opE A) - H ^ 2 • m‖ ≤ C₁ * H ^ 3 := by
    rw [← hU, ← OneStep.opE_sub, ← OneStep.opE_smul, ← OneStep.opE_sub]
    exact h.norm_sub_reachLead_le hH.ne'
  have hρ : 1 ≤ 1 + b * H := by linarith
  have habs := abs_runErr_sub_runMax_le norm_one_opE_le (opE A) m (opE S.X) hH hT hρ hc0 hC0 hx
    hc hC
  have hKT : (⌊T / H⌋₊ : ℝ) * H ≤ T := by
    have := Nat.floor_le (div_nonneg hT hH.le)
    rwa [le_div_iff₀ hH] at this
  have hmono := runConst_mono (H := H) hT (norm_nonneg (opE A)) hc0 hC0 (norm_nonneg m)
    (by positivity) (one_add_pow_le_exp hH hbH hKT) hm
  have hgZ := hg _ (h.reachLead_mem hΘ hAΘ hGΘ)
  have h2 := mul_le_mul_of_nonneg_left hgZ hH.le
  have h3 := mul_le_mul_of_nonneg_right hmono (sq_nonneg H)
  have h4 := (abs_le.1 habs).1
  linarith

/-- **The least value of the run is attained over the reach** (`G` is convex and coercive,
so a minimiser exists). For `0 < T` with `T ‖A‖ ≤ 1/2` there is `Z₀` in the reach with
`G(½ A_ς A + Z₀) ≤ G(½ A_ς A + Z)` for all `Z` in the reach, `G(m) = max_{0 ≤ t ≤ T} ‖Φ_t(m)‖`. -/
theorem exists_least_run (A : Matrix (Fin n) (Fin n) ℝ) (Θ : Matrix (Fin n) (Fin n) ℝ)
    {T : ℝ} (hT : 0 < T) (hTA : T * ‖opE A‖ ≤ 1 / 2) :
    ∃ Z₀ ∈ S.reach Θ, ∀ Z ∈ S.reach Θ,
      runMax (opE A) (opE (S.halfStepTerm A + Z₀)) T ≤
        runMax (opE A) (opE (S.halfStepTerm A + Z)) T := by
  have he : Real.exp (T * ‖opE A‖) < 2 :=
    lt_of_le_of_lt (Real.exp_le_exp.2 hTA) exp_half_lt_two
  have hc : 0 < T * (2 - Real.exp (T * ‖opE A‖)) := mul_pos hT (by linarith)
  refine exists_forall_le_of_coercive (L := T * Real.exp (T * ‖opE A‖))
    (c := T * (2 - Real.exp (T * ‖opE A‖)))
    (d := T * (2 - Real.exp (T * ‖opE A‖)) * ‖opE (S.halfStepTerm A)‖) (fun Z Z' => ?_) hc
    (fun Z _ => ?_)
  · have h := runMax_le_add norm_one_opE_le (opE A) (opE (S.halfStepTerm A + Z))
      (opE (S.halfStepTerm A + Z')) hT.le
    rwa [← OneStep.opE_sub, add_sub_add_left_eq_sub] at h
  · have h := runMax_ge norm_one_opE_le (opE A) (opE (S.halfStepTerm A + Z)) hT.le
    have h2 : ‖opE Z‖ ≤ ‖opE (S.halfStepTerm A + Z)‖ + ‖opE (S.halfStepTerm A)‖ := by
      have e : opE Z = opE (S.halfStepTerm A + Z) - opE (S.halfStepTerm A) := by
        rw [OneStep.opE_add]; abel
      rw [e]
      exact norm_sub_le _ _
    have h3 := mul_le_mul_of_nonneg_left h2 hc.le
    linarith

/-- **The least error over a run is attained** (the paper, eq. `eq:leastrun`, upper bound). For `A`
without blocks between subsystems that are not partners and with `A_c Θ = 0`, `0 < T`,
`T ‖A‖ ≤ 1/2`: there is a minimiser `Z₀` of `G(½ A_ς A + Z)` over the reach such that, for `0 < H`,
`‖A‖ ≤ β`, `‖Z₀‖ ≤ β²`, `H β ≤ 1/4`, `σ H β ≤ 1/6`, the scheme `reachScheme` of `Z₀` (consistent;
its coefficients act through the outputs), started from the initial state, has
`ε_K ≤ H G(½ A_ς A + Z₀) + runConst T ‖A‖ e^{9βT} ((6 + 27σ) β²) (reachK σ β) ‖½ A_ς A + Z₀‖ H`
`· H²`,
`K = ⌊T/H⌋`. -/
theorem least_run_attained [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    {Θ : Matrix (Fin n) (Fin n) ℝ} (hAΘ : S.coupling A * Θ = 0) {T : ℝ} (hT : 0 < T)
    (hTA : T * ‖opE A‖ ≤ 1 / 2) :
    ∃ Z₀, ∃ hZ₀ : Z₀ ∈ S.reach Θ,
      (∀ Z ∈ S.reach Θ, runMax (opE A) (opE (S.halfStepTerm A + Z₀)) T ≤
        runMax (opE A) (opE (S.halfStepTerm A + Z)) T) ∧
      ∀ {H β : ℝ}, 0 < H → ‖opE A‖ ≤ β → ‖opE Z₀‖ ≤ β ^ 2 → H * β ≤ 1 / 4 →
        Real.sqrt (Fintype.card κ) * (H * β) ≤ 1 / 6 →
        ((S.reachScheme A hA Z₀ hZ₀.1 H).M + (S.reachScheme A hA Z₀ hZ₀.1 H).N) * Θ = 0 ∧
        runErr (opE (S.reachScheme A hA Z₀ hZ₀.1 H).X) (NormedSpace.exp (H • opE A))
            ⌊T / H⌋₊ ≤
          H * runMax (opE A) (opE (S.halfStepTerm A + Z₀)) T +
            runConst T ‖opE A‖ (Real.exp (9 * β * T))
              ((6 + 27 * Real.sqrt (Fintype.card κ)) * β ^ 2)
              (reachK (Real.sqrt (Fintype.card κ)) β) ‖opE (S.halfStepTerm A + Z₀)‖ H *
              H ^ 2 := by
  obtain ⟨Z₀, hZ₀, hmin⟩ := exists_least_run (S := S) A Θ hT hTA
  refine ⟨Z₀, hZ₀, hmin, fun {H β} hH hAβ hZβ hβH hσ => ⟨reachScheme_samples_mul_eq_zero hAΘ hZ₀.2,
    ?_⟩⟩
  have hc := reachScheme_consistent (hA := hA) (hZ := hZ₀.1) hH.le hAβ hZβ hβH hσ
  have hR := norm_reachScheme_sub_le (hA := hA) (hZ := hZ₀.1) hH.le hAβ hZβ hβH hσ
  set R := S.reachScheme A hA Z₀ hZ₀.1 H
  set σ := Real.sqrt (Fintype.card κ)
  set m := opE (S.halfStepTerm A + Z₀)
  have hβ : 0 ≤ β := (norm_nonneg _).trans hAβ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hc0 : 0 ≤ (6 + 27 * σ) * β ^ 2 := by positivity
  have hC0 : 0 ≤ reachK σ β := by unfold reachK; positivity
  have hx : ‖opE R.X‖ ≤ 1 + 9 * β * H := by
    have e : opE R.X = opE (R.X - 1) + 1 := by rw [OneStep.opE_sub, OneStep.opE_one]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    linarith [hc.hb, norm_one_opE_le (n := n)]
  have hU : opE (NormedSpace.exp (H • A)) = NormedSpace.exp (H • opE A) := by
    rw [OneStep.opE_exp, OneStep.opE_smul]
  have hcx : ‖opE R.X - NormedSpace.exp (H • opE A)‖ ≤ (6 + 27 * σ) * β ^ 2 * H ^ 2 := by
    rw [← hU, ← OneStep.opE_sub]
    exact hc.hc
  have hCx : ‖opE R.X - NormedSpace.exp (H • opE A) - H ^ 2 • m‖ ≤ reachK σ β * H ^ 3 := by
    rw [← hU, ← OneStep.opE_sub, ← OneStep.opE_smul, ← OneStep.opE_sub]
    exact hR
  have hρ : 1 ≤ 1 + 9 * β * H := by nlinarith
  have habs := abs_runErr_sub_runMax_le norm_one_opE_le (opE A) m (opE R.X) hH hT.le hρ hc0 hC0
    hx hcx hCx
  have hKT : (⌊T / H⌋₊ : ℝ) * H ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hH.le)
    rwa [le_div_iff₀ hH] at this
  have hpow : (1 + 9 * β * H) ^ ⌊T / H⌋₊ ≤ Real.exp (9 * β * T) :=
    one_add_pow_le_exp hH (by positivity) hKT
  have hmono := runConst_mono (H := H) hT.le (norm_nonneg (opE A)) hc0 hC0 (norm_nonneg m)
    (by positivity) hpow le_rfl
  have h3 := mul_le_mul_of_nonneg_right hmono (sq_nonneg H)
  have h4 := (abs_le.1 habs).2
  linarith

end HeldScheme

end Schemes

end CoSimFoundations
