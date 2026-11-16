/-
From a scheme to its step matrix: networks of scalar stores, Jacobi mode, one held sample
(the paper, Prop 2.1 for this class and the first statement of Thm 6.2).

A scalar store `ẋ = a x + b u`, `y = c x`, driven during one macro step by `u = v + k y` with a
constant `v` (the held samples of its partners, weighted) and a local gain `k`, obeys
`ẋ = λ x + b v`, `λ = a + b k c`, and after the step `x(H) = e^{λH} x(0) + g(λ, H) · b v` with
`g(λ, H) = (e^{λH} - 1)/λ` (`= H` for `λ = 0`). Hence the step matrix of a Jacobi scheme with weights
`w` and gains `k`:

  `X i i = e^{λ_i H}`,   `X i j = g(λ_i, H) · b_i · w i j · c_j`  (`j ≠ i`).

As the gains and the weights vary (weights supported on the coupling graph), `X` ranges exactly over
the matrices with positive diagonal and zeros outside the graph: the class `𝒳` of Thm 6.2.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Matrix.Basic

open Real

namespace CoSimFoundations

/-- The response of a scalar store to a unit constant input over a step: `(e^{λH} - 1)/λ`. -/
noncomputable def holdGain (lam H : ℝ) : ℝ := if lam = 0 then H else (exp (lam * H) - 1) / lam

theorem holdGain_pos {lam H : ℝ} (hH : 0 < H) : 0 < holdGain lam H := by
  unfold holdGain
  split_ifs with h
  · exact hH
  · rcases lt_or_gt_of_ne h with hneg | hpos
    · have h1 : exp (lam * H) < 1 := by
        have := Real.exp_lt_exp.2 (mul_neg_of_neg_of_pos hneg hH)
        rwa [Real.exp_zero] at this
      exact div_pos_of_neg_of_neg (by linarith) hneg
    · have h1 : 1 < exp (lam * H) := by
        have := Real.exp_lt_exp.2 (mul_pos hpos hH)
        rwa [Real.exp_zero] at this
      exact div_pos (by linarith) hpos

theorem hasDerivAt_holdGain (lam t : ℝ) :
    HasDerivAt (holdGain lam) (lam * holdGain lam t + 1) t := by
  unfold holdGain
  by_cases h : lam = 0
  · simp only [h, ↓reduceIte, zero_mul, zero_add]
    exact hasDerivAt_id t
  · simp only [h, ↓reduceIte]
    have h1 : HasDerivAt (fun s => exp (lam * s)) (exp (lam * t) * lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).exp
    have h2 := (h1.sub_const 1).div_const lam
    convert h2 using 1
    field_simp
    ring

/-- **One step of a scalar store under a constant input.** If `x' = λ x + β` on `ℝ`, then
`x(H) = e^{λH} x(0) + g(λ, H) β`. -/
theorem scalar_step {lam β : ℝ} {x : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (lam * x t + β) t) (H : ℝ) :
    x H = exp (lam * H) * x 0 + holdGain lam H * β := by
  -- the difference `d` from the claimed solution satisfies `d' = λ d`, `d 0 = 0`
  set d : ℝ → ℝ := fun t => x t - (exp (lam * t) * x 0 + holdGain lam t * β) with hd
  have hexp : ∀ t, HasDerivAt (fun s => exp (lam * s)) (lam * exp (lam * t)) t := by
    intro t
    have h0 : HasDerivAt (fun s => exp (lam * s)) (exp (lam * t) * lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).exp
    rwa [mul_comm] at h0
  have hd' : ∀ t, HasDerivAt d (lam * d t) t := by
    intro t
    have h1 := ((hexp t).mul_const (x 0)).add ((hasDerivAt_holdGain lam t).mul_const β)
    have h2 := (hx t).sub h1
    convert h2 using 1
    simp only [hd]
    ring
  -- so `e^{-λ t} d t` is constant
  have hconst : ∀ t, HasDerivAt (fun s => exp (-(lam * s)) * d s) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s => exp (-(lam * s))) (exp (-(lam * t)) * -lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).neg.exp
    have h2 := h1.mul (hd' t)
    convert h2 using 1
    ring
  have hzero : ∀ t, exp (-(lam * t)) * d t = exp (-(lam * 0)) * d 0 :=
    fun t => is_const_of_deriv_eq_zero (fun s => (hconst s).differentiableAt)
      (fun s => (hconst s).deriv) t 0
  have hd0 : d 0 = 0 := by simp [hd, holdGain]
  have hdH : d H = 0 := by
    have := hzero H
    rw [hd0, mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (exp_pos _).ne'
  have : x H - (exp (lam * H) * x 0 + holdGain lam H * β) = 0 := hdH
  linarith

variable {n : ℕ}

/-- A network of scalar stores `ẋ_i = a_i x_i + b_i u_i`, `y_i = c_i x_i` with a coupling graph. -/
structure ScalarNet (n : ℕ) where
  /-- local rates -/
  a : Fin n → ℝ
  /-- input gains -/
  b : Fin n → ℝ
  /-- output gains -/
  c : Fin n → ℝ
  /-- `partner i j`: store `j` is a partner of store `i` -/
  partner : Fin n → Fin n → Prop
  hbc : ∀ i, b i * c i ≠ 0

namespace ScalarNet

variable (N : ScalarNet n)

/-- The local rate of store `i` closed by its gain. -/
def rate (k : Fin n → ℝ) (i : Fin n) : ℝ := N.a i + N.b i * k i * N.c i

/-- The step matrix of the Jacobi scheme with weights `w` and gains `k` at the macro step `H`. -/
noncomputable def jacobiStep (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then exp (N.rate k i * H) else holdGain (N.rate k i) H * N.b i * w i j * N.c j

/-- **The step matrix is the step.** If during one macro step every store obeys
`ẋ_i = a_i x_i + b_i (Σ_{j ≠ i} w i j c_j x_j(0) + k_i c_i x_i)`, then `x(H) = X x(0)`. -/
theorem step_eq (H : ℝ) (k : Fin n → ℝ) (w : Matrix (Fin n) (Fin n) ℝ) {x : Fin n → ℝ → ℝ}
    (hx : ∀ i t, HasDerivAt (x i)
      (N.a i * x i t + N.b i * ((∑ j ∈ Finset.univ.erase i, w i j * (N.c j * x j 0)) +
        k i * (N.c i * x i t))) t) (i : Fin n) :
    x i H = ∑ j, N.jacobiStep H k w i j * x j 0 := by
  have h := scalar_step (lam := N.rate k i)
    (β := N.b i * ∑ j ∈ Finset.univ.erase i, w i j * (N.c j * x j 0)) (x := x i) (fun t => by
      convert hx i t using 1
      simp only [rate]; ring) H
  rw [h, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [jacobiStep]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    simp only [jacobiStep, hji, ↓reduceIte]
    ring

/-- The class `𝒳`: positive diagonal, zeros between stores that are not partners. -/
def classX : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | (∀ i, 0 < X i i) ∧ ∀ i j, i ≠ j → ¬ N.partner i j → X i j = 0}

/-- **The one-step maps of the class are exactly `𝒳`.** As the gains and the weights (supported on
the coupling graph) vary, the Jacobi step matrix ranges over all of `𝒳`, for every `H > 0`. -/
theorem range_jacobiStep {H : ℝ} (hH : 0 < H) :
    {X | ∃ k w, (∀ i j, ¬ N.partner i j → w i j = 0) ∧ X = N.jacobiStep H k w} = N.classX := by
  ext X
  constructor
  · rintro ⟨k, w, hw, rfl⟩
    refine ⟨fun i => by simp [jacobiStep, exp_pos], fun i j hij hp => ?_⟩
    simp [jacobiStep, hij, hw i j hp]
  · rintro ⟨hdiag, hzero⟩
    have hb : ∀ i, N.b i ≠ 0 := fun i => left_ne_zero_of_mul (N.hbc i)
    have hc : ∀ i, N.c i ≠ 0 := fun i => right_ne_zero_of_mul (N.hbc i)
    -- gains: `e^{λ_i H} = X i i`
    let k : Fin n → ℝ := fun i => (log (X i i) / H - N.a i) / (N.b i * N.c i)
    have hrate : ∀ i, N.rate k i * H = log (X i i) := by
      intro i
      have hbi := hb i
      have hci := hc i
      have hH' := hH.ne'
      have h1 : N.b i * k i * N.c i = log (X i i) / H - N.a i := by
        simp only [k]; field_simp
      rw [rate, h1]
      field_simp
      ring
    -- weights: `g · b_i · w i j · c_j = X i j`
    let w : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => if i = j then 0 else X i j / (holdGain (N.rate k i) H * N.b i * N.c j)
    refine ⟨k, w, fun i j hp => ?_, ?_⟩
    · by_cases hij : i = j
      · simp [w, hij]
      · simp [w, hij, hzero i j hij hp]
    · ext i j
      by_cases hij : i = j
      · subst hij
        simp [jacobiStep, hrate, exp_log (hdiag i)]
      · have hg : holdGain (N.rate k i) H ≠ 0 := (holdGain_pos hH).ne'
        have hbi := hb i
        have hcj := hc j
        simp only [jacobiStep, hij, ↓reduceIte, w]
        field_simp

end ScalarNet

end CoSimFoundations
