/-
The largest order of convergence with `l` held samples is `l` (the paper, the paragraph after
Theorem `cor:barrier`: "Polynomial extrapolation of degree `l-1` reaches this order: its local
defect is of the order `H^{l+1}`, and its past samples enter with coefficients of the order `H`,
so that its recursion perturbs by `O(H)` one whose powers are bounded. The largest order of
convergence is therefore `l`").

**Setting**, that of `RunOrder`: a scheme with `l` held samples in any order of execution is the
recursion `(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` on the state space `E` (a Banach space),
`U = exp (H • A)`, the local defect `T = (1 - N) U - Σ_{r<l} M r U^{-r}` (`runDefect`), and the
starting values are exact, `x^k = U^k x_0` for `k < l`.

**Convergence** (`run_error_le`, `run_convergence`). If the new samples and the past samples
enter with coefficients of the order `H` and the current step is the identity up to `O(H)`,

  `‖N‖ ≤ b H`,   `‖M 0 - 1‖ ≤ b H`,   `‖M r‖ ≤ b H` (`1 ≤ r < l`),   `b H ≤ 1/2`,

(the recursion is `C_0 + O(H)` with `C_0` the shift `x^{k+1} = x^k`, whose powers are bounded),
then the error `e_k = x^k - U^k x_0` satisfies, for `k ≤ K`,

  `‖e_k‖ ≤ 2 ‖T‖ e^{K H ‖A‖} ‖x_0‖ k (1 + 2 (l + 1) b H)^k`.

Proof: `(1 - N) e_{k+1} = Σ_r M r e_{k-r} - T U^k x_0` (`runDefect_smul_pow`), so
`(1 - b H) ‖e_{k+1}‖ ≤ (1 + l b H) max_{j ≤ k} ‖e_j‖ + ‖T‖ ‖U^k x_0‖`, and
`(1 + l b H)/(1 - b H) ≤ 1 + 2 (l + 1) b H` for `b H ≤ 1/2`; induction on `k`. With
`‖T‖ ≤ D H^{l+1}` and `K H ≤ T₀` (`run_convergence`):

  `‖x^k - U^k x_0‖ ≤ 2 D T₀ e^{(‖A‖ + 2 (l + 1) b) T₀} H^l ‖x_0‖`,  `k ≤ K`:

order `l` over an interval of the length `T₀`.

**A scheme of order `l`** (`exists_jacobi_rule`, `exists_jacobi_order`). For a state space split
into subsystems (`Pr i : E → Es i`, `Em i : Es i → E`, `Σ_i Em i Pr i = 1`), each driven through
its own state and the outputs `C i` of its partners, `Pr i A = Ai i Pr i + L i C i` (`E` a
finite-dimensional inner product space, `Es i`, `Gs i` finite-dimensional), the Jacobi scheme
with `l` old samples (`jacobiM`: `N = 0`,
`M r = [r = 0] Σ_i Em i Fi i Pr i + Σ_i Em i g i r C i`) whose rule of every subsystem is the rule
of `MemoryReached` (`exists_rule_nodeDefect_le` with the ages `0, …, l-1`; it integrates the
Taylor polynomial of the own state through divided differences, as polynomial extrapolation does
to this order) satisfies the hypotheses above with constants that do not depend on `H`: its local
defect is `Σ_i Em i 𝒯_i` (`runDefect_jacobiM`). Its run from exact starting values
(`schemeRun`) has, over `K H ≤ T₀`, the error `‖x^k - U^k x_0‖ ≤ C H^l ‖x_0‖` for
`0 < H ≤ H₀`. The rule is not literally polynomial extrapolation (which integrates the subsystem
exactly on the interpolating polynomial); it is a rule of the same class, with bounded weights
and a local defect of the same order `H^{l+1}`.

**The largest order** (`jacobi_order_exact`). With moreover `Pr i Em i = 1`, `Pr i Em j = 0`
for `i ≠ j`, `‖Pr i‖ ≤ 1` and `A ≠ 0`, the row of subsystem `i` of this scheme is its rule, so
the order barrier `run_order_lead` (Theorem `cor:barrier` (ii), all samples old, bounded weights)
applies to it: over the interval of the length `1/(2‖A‖)` the error is at most `C H^l` and at
least `(γ_l c_i H^l - κ_i H^{l+1}) / ((212/7 + 100/7 b H l (l-1)) ‖A‖)` for every subsystem `i`.
Where some `c_i > 0` the order of this scheme is exactly `l`; `run_order_lead` (bounded weights)
and `order_barrier_all` (independent maps) exclude an order above `l` for every other rule.

Not covered: sequential schemes (new samples) are in the convergence theorem (`N ≠ 0` is allowed)
but no sequential scheme of order `l` is constructed here; nor is polynomial extrapolation itself.
-/
import CoSimFoundations.MemoryReached

open NormedSpace Finset

namespace CoSimFoundations

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `‖U^k x‖ ≤ e^{k H ‖A‖} ‖x‖`. -/
theorem norm_exp_smul_pow_apply_le (A : E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H) (k : ℕ) (x : E) :
    ‖(exp (H • A) ^ k) x‖ ≤ Real.exp (k * (H * ‖A‖)) * ‖x‖ := by
  have h1 := norm_exp_smul_pow_sub_one_le A hH k
  have h2 : (exp (H • A) ^ k) x = x + (exp (H • A) ^ k - 1) x := by
    rw [_root_.sub_apply, one_apply_eq_self]
    abel
  rw [h2]
  calc ‖x + (exp (H • A) ^ k - 1) x‖ ≤ ‖x‖ + ‖exp (H • A) ^ k - 1‖ * ‖x‖ :=
        (norm_add_le _ _).trans (add_le_add_right ((exp (H • A) ^ k - 1).le_opNorm x) _)
    _ ≤ ‖x‖ + (Real.exp (k * (H * ‖A‖)) - 1) * ‖x‖ := by gcongr
    _ = Real.exp (k * (H * ‖A‖)) * ‖x‖ := by ring

/-- The arithmetic of one step: `(1 + l y)/(1 - y) ≤ 1 + 2 (l + 1) y` for `0 ≤ y ≤ 1/2`. -/
theorem one_add_mul_div_le {y : ℝ} (l : ℝ) (hl : 0 ≤ l) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    1 + l * y ≤ (1 + 2 * (l + 1) * y) * (1 - y) := by
  nlinarith [mul_nonneg hl hy0, mul_nonneg (mul_nonneg hl hy0) hy0, mul_nonneg hy0 hy0]

/-- **Convergence of a scheme with `l` held samples** (zero-stability and consistency). Let
`‖N‖ ≤ b H`, `‖M 0 - 1‖ ≤ b H`, `‖M r‖ ≤ b H` for `1 ≤ r < l`, `b H ≤ 1/2`, `‖T‖ ≤ D`, exact
starting values `x^k = U^k x_0` for `k < l`, and the recursion
`(1 - N) x^{k+1} = Σ_{r<l} M r x^{k-r}` for `l - 1 ≤ k < K`. Then for `k ≤ K`,
`‖x^k - U^k x_0‖ ≤ 2 (D e^{K H ‖A‖} ‖x_0‖) k (1 + 2 (l + 1) b H)^k`. -/
theorem run_error_le (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H b D : ℝ} (hH : 0 ≤ H)
    (hb : 0 ≤ b) (hbH : b * H ≤ 1 / 2) {l K : ℕ} (hl : 1 ≤ l) (hN : ‖N‖ ≤ b * H)
    (hM0 : ‖M 0 - 1‖ ≤ b * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (hT : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤ D) (x0 : E) (x : ℕ → E)
    (hstart : ∀ k < l, x k = (exp (H • A) ^ k) x0)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) (x (k + 1)) = ∑ r ∈ range l, M r (x (k - r))) :
    ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0‖ ≤
      2 * (D * Real.exp (K * (H * ‖A‖)) * ‖x0‖) * k * (1 + 2 * (l + 1) * b * H) ^ k := by
  set U := exp (H • A) with hU
  set c : ℝ := 1 + 2 * (l + 1) * b * H with hc
  set τ : ℝ := D * Real.exp (K * (H * ‖A‖)) * ‖x0‖ with hτ
  have hbH0 : 0 ≤ b * H := mul_nonneg hb hH
  have hc1 : 1 ≤ c := by
    have : 0 ≤ 2 * (l + 1) * b * H := by positivity
    linarith
  have hD : 0 ≤ D := (norm_nonneg _).trans hT
  have hτ0 : 0 ≤ τ := by positivity
  -- the bound `φ k = 2 τ k c^k` increases with `k`
  have hφmono : ∀ i j : ℕ, i ≤ j → 2 * τ * i * c ^ i ≤ 2 * τ * j * c ^ j := by
    intro i j hij
    have h1 : (i : ℝ) ≤ j := by exact_mod_cast hij
    have h2 : c ^ i ≤ c ^ j := pow_le_pow_right₀ hc1 hij
    have h3 : 0 ≤ c ^ i := by positivity
    have h4 : 0 ≤ (j : ℝ) := by positivity
    have := mul_le_mul h1 h2 h3 h4
    nlinarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases lt_or_ge k l with hkl | hkl
    · rw [hstart k hkl, sub_self, norm_zero]
      have := pow_nonneg (zero_le_one.trans hc1) k
      positivity
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : l - 1 ≤ j := by omega
      have hjK : j < K := by omega
      have hIH : ∀ i ≤ j, ‖x i - (U ^ i) x0‖ ≤ 2 * τ * j * c ^ j := fun i hi =>
        (ih i (by omega) (by omega)).trans (hφmono i j hi)
      -- the error equation
      have hrec := runDefect_smul_pow (V := E) (exp_neg_mul_exp (H • A)) hj x0 x (hx j hj hjK)
      rw [← hU] at hrec
      set e : ℕ → E := fun i => x i - (U ^ i) x0 with he
      have hrec' : e (j + 1) = N (e (j + 1)) + e j + (M 0 - 1) (e j) +
          ∑ r ∈ Ico 1 l, M r (e (j - r)) -
            runDefect N M U (exp (-(H • A))) l ((U ^ j) x0) := by
        have h1 : runDefect N M U (exp (-(H • A))) l ((U ^ j) x0) =
            ∑ r ∈ range l, M r (e (j - r)) - (e (j + 1) - N (e (j + 1))) := by
          have h := hrec
          simp only [ContinuousLinearMap.smul_def] at h
          rw [h]
          simp only [he, _root_.sub_apply, one_apply_eq_self]
        rw [h1, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < l)]
        simp only [_root_.sub_apply, one_apply_eq_self, Nat.sub_zero]
        abel
      -- the norms
      have hT' : ‖runDefect N M U (exp (-(H • A))) l ((U ^ j) x0)‖ ≤ τ := by
        refine ((runDefect N M U _ l).le_opNorm _).trans ?_
        have h1 := norm_exp_smul_pow_apply_le A hH j x0
        have h2 : Real.exp (j * (H * ‖A‖)) ≤ Real.exp (K * (H * ‖A‖)) := by
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (by positivity))
          exact_mod_cast hjK.le
        calc ‖runDefect N M U (exp (-(H • A))) l‖ * ‖(U ^ j) x0‖
            ≤ D * (Real.exp (K * (H * ‖A‖)) * ‖x0‖) := by
              gcongr
              exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
          _ = τ := by rw [hτ]; ring
      have hsum : ‖∑ r ∈ Ico 1 l, M r (e (j - r))‖ ≤ ((l : ℝ) - 1) * (b * H) *
          (2 * τ * j * c ^ j) := by
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∀ r ∈ Ico 1 l, ‖M r (e (j - r))‖ ≤ b * H * (2 * τ * j * c ^ j) := by
          intro r hr
          have hr' := mem_Ico.1 hr
          refine ((M r).le_opNorm _).trans ?_
          exact mul_le_mul (hM r hr'.1 hr'.2) (hIH (j - r) (by omega)) (norm_nonneg _) hbH0
        refine (sum_le_sum h1).trans (le_of_eq ?_)
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hl]
        push_cast
        ring
      have hNe : ‖N (e (j + 1))‖ ≤ b * H * ‖e (j + 1)‖ :=
        (N.le_opNorm _).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
      have hM0e : ‖(M 0 - 1) (e j)‖ ≤ b * H * (2 * τ * j * c ^ j) :=
        ((M 0 - 1).le_opNorm _).trans (mul_le_mul hM0 (hIH j le_rfl) (norm_nonneg _) hbH0)
      have hej := hIH j le_rfl
      have htri : ‖e (j + 1)‖ ≤ b * H * ‖e (j + 1)‖ + 2 * τ * j * c ^ j +
          b * H * (2 * τ * j * c ^ j) + ((l : ℝ) - 1) * (b * H) * (2 * τ * j * c ^ j) + τ := by
        have h := norm_sub_le (N (e (j + 1)) + e j + (M 0 - 1) (e j) +
          ∑ r ∈ Ico 1 l, M r (e (j - r))) (runDefect N M U (exp (-(H • A))) l ((U ^ j) x0))
        have h2 := norm_add₃_le (a := N (e (j + 1)) + e j) (b := (M 0 - 1) (e j))
          (c := ∑ r ∈ Ico 1 l, M r (e (j - r)))
        have h3 := norm_add_le (N (e (j + 1))) (e j)
        rw [← hrec'] at h
        linarith
      -- solve for the new error
      have hl0 : (0 : ℝ) ≤ l := by positivity
      have hstep := one_add_mul_div_le (l : ℝ) hl0 hbH0 hbH
      set φ := 2 * τ * j * c ^ j with hφ
      have hφ0 : 0 ≤ φ := by
        have := pow_nonneg (zero_le_one.trans hc1) j
        positivity
      have h1 : (1 - b * H) * ‖e (j + 1)‖ ≤ (1 + l * (b * H)) * φ + τ := by linarith
      have hpos : 0 < 1 - b * H := by linarith
      have h2 : (1 - b * H) * ‖e (j + 1)‖ ≤ (1 - b * H) * (c * φ + 2 * τ) := by
        have h3 : (1 + l * (b * H)) * φ ≤ (c * (1 - b * H)) * φ := by
          refine mul_le_mul_of_nonneg_right ?_ hφ0
          rw [hc]
          linarith
        nlinarith
      have h4 : ‖e (j + 1)‖ ≤ c * φ + 2 * τ := le_of_mul_le_mul_left h2 hpos
      have h5 : c * φ + 2 * τ ≤ 2 * τ * ((j + 1 : ℕ) : ℝ) * c ^ (j + 1) := by
        have hcj : 1 ≤ c ^ (j + 1) := one_le_pow₀ hc1
        have e1 : c * φ = 2 * τ * j * c ^ (j + 1) := by
          rw [hφ, pow_succ]
          ring
        rw [e1]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hcj (by positivity : (0 : ℝ) ≤ 2 * τ)]
      exact h4.trans h5

/-- **Order `l` over an interval of the length `T₀`:** under the hypotheses of `run_error_le`
with `‖T‖ ≤ D H^{l+1}` and `K H ≤ T₀`, `0 < H`,
`‖x^k - U^k x_0‖ ≤ 2 D T₀ e^{(‖A‖ + 2 (l + 1) b) T₀} H^l ‖x_0‖` for every `k ≤ K`. -/
theorem run_convergence (A N : E →L[ℝ] E) (M : ℕ → E →L[ℝ] E) {H b D T₀ : ℝ} (hH : 0 < H)
    (hb : 0 ≤ b) (hbH : b * H ≤ 1 / 2) {l K : ℕ} (hl : 1 ≤ l) (hKT : K * H ≤ T₀)
    (hN : ‖N‖ ≤ b * H) (hM0 : ‖M 0 - 1‖ ≤ b * H) (hM : ∀ r, 1 ≤ r → r < l → ‖M r‖ ≤ b * H)
    (hT : ‖runDefect N M (exp (H • A)) (exp (-(H • A))) l‖ ≤ D * H ^ (l + 1)) (x0 : E)
    (x : ℕ → E) (hstart : ∀ k < l, x k = (exp (H • A) ^ k) x0)
    (hx : ∀ k, l - 1 ≤ k → k < K → (1 - N) (x (k + 1)) = ∑ r ∈ range l, M r (x (k - r))) :
    ∀ k ≤ K, ‖x k - (exp (H • A) ^ k) x0‖ ≤
      2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) * H ^ l * ‖x0‖ := by
  intro k hk
  have h := run_error_le A N M hH.le hb hbH hl hN hM0 hM hT x0 x hstart hx k hk
  have hD : 0 ≤ D * H ^ (l + 1) := (norm_nonneg _).trans hT
  have hD' : 0 ≤ D := by
    have : 0 < H ^ (l + 1) := by positivity
    exact nonneg_of_mul_nonneg_left hD this
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hkH : (k : ℝ) * H ≤ T₀ := (mul_le_mul_of_nonneg_right hkK hH.le).trans hKT
  have hKH' : (K : ℝ) * (H * ‖A‖) ≤ T₀ * ‖A‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hKT (norm_nonneg A)
  have hc : (1 + 2 * (l + 1) * b * H) ^ k ≤ Real.exp (2 * (l + 1) * b * T₀) := by
    have h1 : 1 + 2 * (l + 1) * b * H ≤ Real.exp (2 * (l + 1) * b * H) := by
      have := Real.add_one_le_exp (2 * (l + 1) * b * H)
      linarith
    have h2 : 0 ≤ 1 + 2 * (l + 1) * b * H := by positivity
    calc (1 + 2 * (l + 1) * b * H) ^ k ≤ Real.exp (2 * (l + 1) * b * H) ^ k :=
          pow_le_pow_left₀ h2 h1 k
      _ = Real.exp (k * (2 * (l + 1) * b * H)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * (l + 1) * b * T₀) := by
          refine Real.exp_le_exp.2 ?_
          have : (k : ℝ) * (2 * (l + 1) * b * H) = 2 * (l + 1) * b * (k * H) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hkH (by positivity)
  have hexp : Real.exp (K * (H * ‖A‖)) * Real.exp (2 * (l + 1) * b * T₀) ≤
      Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  refine h.trans ?_
  have hx0 := norm_nonneg x0
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have e1 : 2 * (D * H ^ (l + 1) * Real.exp (K * (H * ‖A‖)) * ‖x0‖) * k *
      (1 + 2 * (l + 1) * b * H) ^ k =
      2 * D * ((k : ℝ) * H) * (Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k) *
        H ^ l * ‖x0‖ := by ring
  rw [e1]
  have hHl : 0 ≤ H ^ l := by positivity
  have h3 : Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k ≤
      Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) :=
    (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le).trans hexp
  have h4 : 0 ≤ Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k := by positivity
  have hT0 : 0 ≤ T₀ := (by positivity : (0 : ℝ) ≤ k * H).trans hkH
  calc 2 * D * ((k : ℝ) * H) * (Real.exp (K * (H * ‖A‖)) * (1 + 2 * (l + 1) * b * H) ^ k) *
        H ^ l * ‖x0‖
      ≤ 2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) * H ^ l * ‖x0‖ := by
        gcongr

end Convergence

section Run

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The run of a scheme without new samples, `x^{k+1} = Σ_{r<l} M r x^{k-r}`, from the exact
starting values `x^k = U^k x_0`, `k < l`. -/
noncomputable def schemeRun (M : ℕ → E →L[ℝ] E) (U : E →L[ℝ] E) (l : ℕ) (x0 : E) : ℕ → E
  | k => if h : k < l then (U ^ k) x0 else
      ∑ r ∈ (range l).attach, M r (schemeRun M U l x0 (k - 1 - r))
decreasing_by
  have := mem_range.1 r.2
  omega

/-- The starting values of the run are exact. -/
theorem schemeRun_of_lt (M : ℕ → E →L[ℝ] E) (U : E →L[ℝ] E) (l : ℕ) (x0 : E) {k : ℕ}
    (hk : k < l) : schemeRun M U l x0 k = (U ^ k) x0 := by
  rw [schemeRun]
  simp [hk]

/-- The run satisfies the recursion of the scheme. -/
theorem schemeRun_succ (M : ℕ → E →L[ℝ] E) (U : E →L[ℝ] E) {l : ℕ} (x0 : E) {k : ℕ}
    (hk : l - 1 ≤ k) (hl : 1 ≤ l) :
    schemeRun M U l x0 (k + 1) = ∑ r ∈ range l, M r (schemeRun M U l x0 (k - r)) := by
  rw [schemeRun]
  simp only [show ¬ k + 1 < l by omega, ↓reduceDIte, Nat.add_sub_cancel]
  exact sum_attach (range l) (fun r => M r (schemeRun M U l x0 (k - r)))

end Run

section Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  {Gs : ι → Type*} [∀ i, NormedAddCommGroup (Gs i)] [∀ i, NormedSpace ℝ (Gs i)]

/-- **The Jacobi scheme with `l` held samples assembled from the rules of the subsystems:**
`M r = [r = 0] Σ_i Em i Fi i Pr i + Σ_i Em i g i r C i`; subsystem `i` advances on its own state
(coefficient `Fi i`) and on the samples of the outputs `C i` of its partners of the ages
`r < l` (coefficients `g i r`); no sample is new (`N = 0`). -/
noncomputable def jacobiM (Pr : ∀ i, E →L[ℝ] Es i) (Em : ∀ i, Es i →L[ℝ] E)
    (C : ∀ i, E →L[ℝ] Gs i) (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i)
    (r : ℕ) : E →L[ℝ] E :=
  (if r = 0 then ∑ i, Em i ∘L (Fi i ∘L Pr i) else 0) + ∑ i, Em i ∘L (g i r ∘L C i)

variable {Pr : ∀ i, E →L[ℝ] Es i} {Em : ∀ i, Es i →L[ℝ] E} {C : ∀ i, E →L[ℝ] Gs i}

/-- **The local defect of the Jacobi scheme is made of those of the rules:**
`T = Σ_i Em i 𝒯_i` if `Σ_i Em i Pr i = 1`. -/
theorem runDefect_jacobiM (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i) (A : E →L[ℝ] E) (H : ℝ)
    {l : ℕ} (hl : 1 ≤ l) :
    runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l =
      ∑ i, Em i ∘L localDefect (Pr i) (Fi i) (g i) (C i) A H l := by
  have hU : ∀ w : E, ∑ i, Em i (Pr i w) = w := fun w => by
    have h := congrArg (fun T : E →L[ℝ] E => T w) hdec
    simpa using h
  ext v
  simp only [runDefect, sub_zero, one_mul, jacobiM, localDefect, _root_.sub_apply,
    _root_.sum_apply, _root_.add_apply, mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply, map_sub, map_sum]
  have h0 : ∑ r ∈ range l, (if r = 0 then ∑ i, Em i ∘L (Fi i ∘L Pr i) else 0)
      ((exp (-(H • A)) ^ r) v) = ∑ i, Em i (Fi i (Pr i v)) := by
    rw [sum_eq_single_of_mem 0 (mem_range.2 (by omega)) fun r _ hr => by simp [hr]]
    simp
  simp only [sum_add_distrib, sum_sub_distrib, h0, hU]
  rw [sum_comm (s := range l)]
  abel

/-- The norm of the defect of the Jacobi scheme: `‖T‖ ≤ Σ_i ‖Em i‖ ‖𝒯_i‖`. -/
theorem norm_runDefect_jacobiM_le (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i) (A : E →L[ℝ] E) (H : ℝ)
    {l : ℕ} (hl : 1 ≤ l) :
    ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l‖ ≤
      ∑ i, ‖Em i‖ * ‖localDefect (Pr i) (Fi i) (g i) (C i) A H l‖ := by
  rw [runDefect_jacobiM hdec Fi g A H hl]
  exact norm_sum_le_of_le _ fun i _ => ContinuousLinearMap.opNorm_comp_le _ _

/-- `M 0 - 1 = Σ_i Em i ((Fi i - 1) Pr i + g i 0 C i)`, bounded by the coefficients. -/
theorem norm_jacobiM_zero_sub_one_le (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i) :
    ‖jacobiM Pr Em C Fi g 0 - 1‖ ≤
      ∑ i, ‖Em i‖ * (‖Fi i - 1‖ * ‖Pr i‖ + ‖g i 0 ∘L C i‖) := by
  have hU : ∀ w : E, ∑ i, Em i (Pr i w) = w := fun w => by
    have h := congrArg (fun T : E →L[ℝ] E => T w) hdec
    simpa using h
  have e : jacobiM Pr Em C Fi g 0 - 1 =
      ∑ i, Em i ∘L ((Fi i - 1) ∘L Pr i + g i 0 ∘L C i) := by
    ext v
    simp only [jacobiM, ite_true, _root_.sub_apply, _root_.add_apply, _root_.sum_apply,
      ContinuousLinearMap.comp_apply, one_apply_eq_self, map_add, map_sub, sum_add_distrib,
      sum_sub_distrib, hU]
    abel
  rw [e]
  refine norm_sum_le_of_le _ fun i _ => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
  exact add_le_add_left (ContinuousLinearMap.opNorm_comp_le _ _) _

/-- `‖M r‖ ≤ Σ_i ‖Em i‖ ‖g i r C i‖` for `r ≥ 1`. -/
theorem norm_jacobiM_le (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i) {r : ℕ}
    (hr : 1 ≤ r) : ‖jacobiM Pr Em C Fi g r‖ ≤ ∑ i, ‖Em i‖ * ‖g i r ∘L C i‖ := by
  rw [jacobiM, ite_eq_right (by omega), zero_add]
  exact norm_sum_le_of_le _ fun i _ => ContinuousLinearMap.opNorm_comp_le _ _

end Jacobi

section Order

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {Es : ι → Type*} [∀ i, NormedAddCommGroup (Es i)] [∀ i, NormedSpace ℝ (Es i)]
  [∀ i, FiniteDimensional ℝ (Es i)]
  {Gs : ι → Type*} [∀ i, NormedAddCommGroup (Gs i)] [∀ i, NormedSpace ℝ (Gs i)]
  [∀ i, FiniteDimensional ℝ (Gs i)]
  {Pr : ∀ i, E →L[ℝ] Es i} {Em : ∀ i, Es i →L[ℝ] E} {C : ∀ i, E →L[ℝ] Gs i}
  {A : E →L[ℝ] E} {Ai : ∀ i, Es i →L[ℝ] Es i} {L : ∀ i, Gs i →L[ℝ] Es i}

/-- **A Jacobi scheme with `l` held samples in the run class with the hypotheses of
`run_convergence`.** With the rules of `MemoryReached` (ages `0, …, l-1`) for every subsystem,
there are `w, b, D ≥ 0` and `H₀ > 0` such that for every `0 < H ≤ H₀`: bounded weights
`‖g i r ∘ C i‖ ≤ w H` for all `r < l`, `‖M 0 - 1‖ ≤ b H`, `‖M r‖ ≤ b H` for `1 ≤ r < l`,
`b H ≤ 1/2`, and the local defect `‖T‖ ≤ D H^{l+1}`. -/
theorem exists_jacobi_rule (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) {l : ℕ} (hl : 1 ≤ l) :
    ∃ w b D H₀ : ℝ, 0 ≤ w ∧ 0 ≤ b ∧ 0 ≤ D ∧ 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
      H ≤ 1 ∧ H * ‖A‖ ≤ 1 ∧ b * H ≤ 1 / 2 ∧
      ∃ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
        (∀ i, ∀ r < l, ‖g i r ∘L C i‖ ≤ w * H) ∧
        ‖jacobiM Pr Em C Fi g 0 - 1‖ ≤ b * H ∧
        (∀ r, 1 ≤ r → r < l → ‖jacobiM Pr Em C Fi g r‖ ≤ b * H) ∧
        ‖runDefect 0 (jacobiM Pr Em C Fi g) (exp (H • A)) (exp (-(H • A))) l‖ ≤
          D * H ^ (l + 1) := by
  have hrule := fun i => exists_rule_nodeDefect_le (hA i) (leadNodes l)
  choose w K hw0 hK0 hrule using hrule
  choose Fi g hFi hg hT using hrule
  set c : ι → ℝ := fun i => |nodeGamma (leadNodes l)| *
    ‖(Pr i ∘L (A ^ (l + 1))) ∘L (unseen (Pr i) (C i) A l).subtypeL‖
    + K i with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    have := hK0 i
    positivity
  set W := ∑ i, w i with hW
  have hwW : ∀ i, w i ≤ W := fun i => single_le_sum (fun j _ => hw0 j) (mem_univ i)
  have hW0 : 0 ≤ W := sum_nonneg fun i _ => hw0 i
  set b := ∑ i, ‖Em i‖ * (W * ‖Pr i‖ + W) with hb
  have hb0 : 0 ≤ b := sum_nonneg fun i _ => by positivity
  set D := ∑ i, ‖Em i‖ * c i with hD
  have hD0 : 0 ≤ D := sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hc0 i)
  refine ⟨W, b, D, 1 / (1 + ‖A‖ + 2 * b), hW0, hb0, hD0, by positivity, fun H hH hH₀ => ?_⟩
  have hden : 0 < 1 + ‖A‖ + 2 * b := by positivity
  have hHd : H * (1 + ‖A‖ + 2 * b) ≤ 1 := by
    rw [le_div_iff₀ hden] at hH₀
    linarith
  have hA0 := norm_nonneg A
  have hH1 : H ≤ 1 := by nlinarith
  have hx1 : H * ‖A‖ ≤ 1 := by nlinarith
  have hbH : b * H ≤ 1 / 2 := by nlinarith
  refine ⟨hH1, hx1, hbH, fun i => Fi i H hH.le hH1 hx1, fun i n => g i H hH.le hH1 hx1 n,
    fun i r hr => ?_, ?_, fun r hr1 hrl => ?_, ?_⟩
  · -- the weights
    have h := hg i H hH.le hH1 hx1 r (mem_map.2 ⟨r, mem_range.2 hr, rfl⟩)
    exact h.trans (mul_le_mul_of_nonneg_right (hwW i) hH.le)
  · -- the current step
    refine (norm_jacobiM_zero_sub_one_le hdec _ _).trans ?_
    rw [hb, sum_mul]
    refine sum_le_sum fun i _ => ?_
    have h1 := (hFi i H hH.le hH1 hx1).trans (mul_le_mul_of_nonneg_right (hwW i) hH.le)
    have h2 : ‖g i H hH.le hH1 hx1 ((0 : ℕ) : ℤ) ∘L C i‖ ≤ W * H :=
      (hg i H hH.le hH1 hx1 _ (mem_map.2 ⟨0, mem_range.2 (by omega), rfl⟩)).trans
      (mul_le_mul_of_nonneg_right (hwW i) hH.le)
    have h3 : ‖Fi i H hH.le hH1 hx1 - 1‖ * ‖Pr i‖ ≤ W * H * ‖Pr i‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    calc ‖Em i‖ * (‖Fi i H hH.le hH1 hx1 - 1‖ * ‖Pr i‖ +
          ‖g i H hH.le hH1 hx1 ((0 : ℕ) : ℤ) ∘L C i‖)
        ≤ ‖Em i‖ * (W * H * ‖Pr i‖ + W * H) := by gcongr
      _ = ‖Em i‖ * (W * ‖Pr i‖ + W) * H := by ring
  · -- the past samples
    refine (norm_jacobiM_le _ _ hr1).trans ?_
    rw [hb, sum_mul]
    refine sum_le_sum fun i _ => ?_
    have h2 := (hg i H hH.le hH1 hx1 r (mem_map.2 ⟨r, mem_range.2 hrl, rfl⟩)).trans
      (mul_le_mul_of_nonneg_right (hwW i) hH.le)
    have hP := norm_nonneg (Pr i)
    calc ‖Em i‖ * ‖g i H hH.le hH1 hx1 (r : ℤ) ∘L C i‖ ≤ ‖Em i‖ * (W * H) := by gcongr
      _ ≤ ‖Em i‖ * (W * ‖Pr i‖ + W) * H := by
        have : 0 ≤ ‖Em i‖ * (W * ‖Pr i‖) * H := by positivity
        nlinarith
  · -- the local defect
    refine (norm_runDefect_jacobiM_le hdec _ _ A H hl).trans ?_
    rw [hD, sum_mul]
    refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _) |>.trans
      (le_of_eq (mul_assoc _ _ _).symm)
    have e : localDefect (Pr i) (Fi i H hH.le hH1 hx1) (fun n => g i H hH.le hH1 hx1 n) (C i) A
        H l = nodeDefect (Pr i) (Fi i H hH.le hH1 hx1) (g i H hH.le hH1 hx1) (C i) A H
          (leadNodes l) := by
      rw [← nodeDefect_leadNodes]
      unfold nodeDefect
      rw [sum_leadNodes, sum_leadNodes]
      simp only [Int.toNat_natCast]
    rw [e]
    have hT' := hT i H hH.le hH1 hx1
    rw [card_leadNodes] at hT'
    have hH2 : H ^ (l + 2) ≤ H ^ (l + 1) := pow_le_pow_of_le_one hH.le hH1 (by omega)
    refine hT'.trans ?_
    calc |nodeGamma (leadNodes l)| *
          ‖(Pr i ∘L (A ^ (l + 1))) ∘L (unseen (Pr i) (C i) A l).subtypeL‖ * H ^ (l + 1) +
          K i * H ^ (l + 2)
        ≤ |nodeGamma (leadNodes l)| *
          ‖(Pr i ∘L (A ^ (l + 1))) ∘L (unseen (Pr i) (C i) A l).subtypeL‖ * H ^ (l + 1) +
          K i * H ^ (l + 1) := by
          have := hK0 i
          gcongr
      _ = c i * H ^ (l + 1) := by
          rw [hc]
          ring

/-- **Polynomial-extrapolation order is reached**: for a state space split into
subsystems driven through their own states and the outputs of their partners, the Jacobi scheme
with `l` held samples and the rules of `MemoryReached` has, for every `T₀`, an error
`‖x^k - U^k x_0‖ ≤ C H^l ‖x_0‖` for all `k ≤ K`, `K H ≤ T₀`, with exact starting values, for
`0 < H ≤ H₀`; its weights are bounded, `‖g i r ∘ C i‖ ≤ w H`. -/
theorem exists_jacobi_order (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) {l : ℕ} (hl : 1 ≤ l) (T₀ : ℝ) :
    ∃ w Cr H₀ : ℝ, 0 ≤ w ∧ 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
      ∃ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
        (∀ i, ∀ r < l, ‖g i r ∘L C i‖ ≤ w * H) ∧
        ∀ K : ℕ, K * H ≤ T₀ → ∀ (x0 : E), ∀ k ≤ K,
          ‖schemeRun (jacobiM Pr Em C Fi g) (exp (H • A)) l x0 k - (exp (H • A) ^ k) x0‖ ≤
            Cr * H ^ l * ‖x0‖ := by
  obtain ⟨w, b, D, H₀, hw, hb, hD, hH₀, h⟩ := exists_jacobi_rule hdec hA hl (Em := Em)
  refine ⟨w, 2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀), H₀, hw, hH₀,
    fun H hH hHH₀ => ?_⟩
  obtain ⟨-, -, hbH, Fi, g, hg, hM0, hM, hT⟩ := h H hH hHH₀
  refine ⟨Fi, g, hg, fun K hKT x0 k hk => ?_⟩
  have hx : ∀ k, l - 1 ≤ k → k < K →
      (1 - (0 : E →L[ℝ] E)) (schemeRun (jacobiM Pr Em C Fi g) (exp (H • A)) l x0 (k + 1)) =
        ∑ r ∈ range l, jacobiM Pr Em C Fi g r
          (schemeRun (jacobiM Pr Em C Fi g) (exp (H • A)) l x0 (k - r)) := by
    intro k hk _
    rw [sub_zero, one_apply_eq_self, schemeRun_succ _ _ x0 hk hl]
  have h1 := run_convergence A 0 (jacobiM Pr Em C Fi g) hH hb hbH hl hKT
    (by rw [norm_zero]; positivity) hM0 hM hT x0 _
    (fun k hk => schemeRun_of_lt _ _ l x0 hk) hx k hk
  exact h1

/-- **The largest order of convergence is `l`, for this scheme** (Theorem `cor:barrier` with its
attainment). Let moreover `Pr i Em i = 1`, `Pr i Em j = 0` for `i ≠ j`, `‖Pr i‖ ≤ 1`, `A ≠ 0`.
There are constants such that for `0 < H ≤ H₀` the Jacobi scheme of `exists_jacobi_rule` has
over the interval of the length `1/(2‖A‖)` (`K H ‖A‖ ≤ 1/2`) an error at most `C H^l ‖x_0‖`, and
for every subsystem `i`, if moreover `2 l H ‖A‖ ≤ 1` and `1/2 < (K + 1) H ‖A‖`, the order barrier
`run_order_lead` gives
`(γ_l c_i H^l - κ_i H^{l+1}) / ((212/7 + 100/7 b H l (l - 1)) ‖A‖) ≤ C H^l`, `c_i = unseenRate`.
Where some `c_i > 0` the error is exactly of the order `H^l`; with `run_order_lead` and
`order_barrier_all` for all other rules, `l` is the largest order of convergence. -/
theorem jacobi_order_exact [Nontrivial E] (hdec : ∑ i, Em i ∘L Pr i = ContinuousLinearMap.id ℝ E)
    (hPEi : ∀ i, Pr i ∘L Em i = ContinuousLinearMap.id ℝ (Es i))
    (hPE : ∀ i j, i ≠ j → Pr i ∘L Em j = 0)
    (hA : ∀ i, Pr i ∘L A = Ai i ∘L Pr i + L i ∘L C i) (hP : ∀ i, ‖Pr i‖ ≤ 1)
    (hA0 : A ≠ 0) {l : ℕ} (hl : 1 ≤ l) :
    ∃ w b Cr H₀ : ℝ, 0 ≤ w ∧ 0 ≤ b ∧ 0 < H₀ ∧ ∀ H : ℝ, 0 < H → H ≤ H₀ →
      ∃ (Fi : ∀ i, Es i →L[ℝ] Es i) (g : ∀ i, ℕ → Gs i →L[ℝ] Es i),
        (∀ i, ∀ r < l, ‖g i r ∘L C i‖ ≤ w * H) ∧
        (∀ K : ℕ, K * H * ‖A‖ ≤ 1 / 2 → ∀ (x0 : E), ∀ k ≤ K,
          ‖schemeRun (jacobiM Pr Em C Fi g) (exp (H • A)) l x0 k - (exp (H • A) ^ k) x0‖ ≤
            Cr * H ^ l * ‖x0‖) ∧
        ∀ i, 2 * l * (H * ‖A‖) ≤ 1 → ∀ K : ℕ, K * H * ‖A‖ ≤ 1 / 2 →
          1 / 2 < (K + 1) * H * ‖A‖ →
          (adamsGamma l * unseenRate (Pr i) (C i) A l * H ^ l -
              (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) +
                adamsGamma l * unseenRate (Pr i) (C i) A l *
                  (2 * l + memB l + ((l : ℝ) - 1) / 3) * ‖A‖) * H ^ (l + 1)) /
            ((212 / 7 * (1 + 0) + 100 / 7 * (b * H * ((l : ℝ) * (l - 1)))) * ‖A‖) ≤
            Cr * H ^ l := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.2 hA0
  obtain ⟨w, b, D, H₀, hw, hb, hD, hH₀, h⟩ := exists_jacobi_rule hdec hA hl (Em := Em)
  set T₀ := 1 / (2 * ‖A‖) with hT₀
  set Cr := 2 * D * T₀ * Real.exp ((‖A‖ + 2 * (l + 1) * b) * T₀) with hCr
  refine ⟨w, b, Cr, H₀, hw, hb, hH₀, fun H hH hHH₀ => ?_⟩
  obtain ⟨-, -, hbH, Fi, g, hg, hM0, hM, hT⟩ := h H hH hHH₀
  set M := jacobiM Pr Em C Fi g with hMdef
  have hx : ∀ x0 : E, ∀ k, l - 1 ≤ k →
      (1 - (0 : E →L[ℝ] E)) (schemeRun M (exp (H • A)) l x0 (k + 1)) =
        ∑ r ∈ range l, M r (schemeRun M (exp (H • A)) l x0 (k - r)) := by
    intro x0 k hk
    rw [sub_zero, one_apply_eq_self, schemeRun_succ _ _ x0 hk hl]
  have herr : ∀ K : ℕ, K * H * ‖A‖ ≤ 1 / 2 → ∀ (x0 : E), ∀ k ≤ K,
      ‖schemeRun M (exp (H • A)) l x0 k - (exp (H • A) ^ k) x0‖ ≤ Cr * H ^ l * ‖x0‖ := by
    intro K hK x0 k hk
    have hKT : (K : ℝ) * H ≤ T₀ := by
      rw [hT₀, le_div_iff₀ (by positivity)]
      linarith
    exact run_convergence A 0 M hH hb hbH hl hKT (by rw [norm_zero]; positivity) hM0 hM hT x0
      _ (fun k hk => schemeRun_of_lt _ _ l x0 hk) (fun k hk _ => hx x0 k hk) k hk
  refine ⟨Fi, g, hg, herr, fun i hlx K hKH hK1 => ?_⟩
  -- the row of subsystem `i` is its rule
  have hrow : ∀ r, Pr i ∘L M r =
      (if r = 0 then Fi i ∘L Pr i else 0) + g i r ∘L C i := by
    intro r
    have hsum : ∀ X : ∀ j, E →L[ℝ] Es j,
        Pr i ∘L ∑ j, Em j ∘L X j = X i := by
      intro X
      rw [ContinuousLinearMap.comp_finsetSum, sum_eq_single i]
      · rw [← ContinuousLinearMap.comp_assoc, hPEi, ContinuousLinearMap.id_comp]
      · intro j _ hji
        rw [← ContinuousLinearMap.comp_assoc, hPE i j (Ne.symm hji),
          ContinuousLinearMap.zero_comp]
      · intro hi
        exact absurd (mem_univ i) hi
    rw [hMdef, jacobiM, ContinuousLinearMap.comp_add]
    split_ifs with hr
    · rw [hsum (fun j => Fi j ∘L Pr j), hsum (fun j => g j r ∘L C j)]
    · rw [ContinuousLinearMap.comp_zero, hsum (fun j => g j r ∘L C j)]
  have hrow0 : Pr i ∘L M 0 = Fi i ∘L Pr i + g i 0 ∘L C i := by
    rw [hrow 0, ite_eq_left rfl]
  have hrowr : ∀ r, 1 ≤ r → r < l → Pr i ∘L M r = g i r ∘L C i := by
    intro r hr _
    rw [hrow r, ite_eq_right (by omega), zero_add]
  have hδ : ∀ x0 : E, x0 ≠ 0 → ∀ k ≤ K,
      ‖schemeRun M (exp (H • A)) l x0 k - (exp (H • A) ^ k) x0‖ ≤ Cr * H ^ l * ‖x0‖ :=
    fun x0 _ k hk => herr K hKH x0 k hk
  exact run_order_lead (P := Pr i) (C := C i) (L := L i) 0 M (hA i) (hP i) (Fi i) (g i) hH.le hw
    hl (ContinuousLinearMap.comp_zero _) hrow0 hrowr
    (fun r hr hrl => hg i r hrl) hlx hKH hK1 (by rw [norm_zero]) hM
    (fun x0 => schemeRun M (exp (H • A)) l x0) (fun x0 _ k hk _ => hx x0 k hk) hδ

end Order

end CoSimFoundations
