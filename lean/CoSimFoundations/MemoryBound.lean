/-
The memory bound (the paper, Corollary 4.8 `cor:memory`, inequality (21) `eq:memorybound`).

**The step and its inverse.** In a normed ring with `‖1‖ = 1` let `U` have the inverse `V`, let
`α = ‖D - 1‖ < 1` and `P = D * U` (reference step, defect, step of the scheme). If `D'` is the
inverse of `D` (it exists in a complete ring: Neumann series), then `P' = V * D'` is the inverse of
`P`, and

  `‖D'‖ ≤ 1 / (1 - α)`,                     `‖D' - 1‖ ≤ α / (1 - α)`,
  `‖P'‖ ≤ ‖V‖ / (1 - α)`,                   `‖P' - V‖ ≤ ‖V‖ α / (1 - α)`,
  `‖P' ^ r - V ^ r‖ ≤ r ‖V‖ ^ r α / (1 - α) ^ r`   for every `r`.

Proofs: `D' = 1 - (D - 1) D'` gives `‖D'‖ ≤ 1 + α ‖D'‖`; `D' - 1 = -(D - 1) D'`;
`P' - V = V (D' - 1)`; and `a ^ (r+1) - b ^ (r+1) = a ^ r (a - b) + (a ^ r - b ^ r) b` with
`‖a‖, ‖b‖ ≤ q = ‖V‖ / (1 - α)` and `‖a - b‖ ≤ q α` gives `‖a ^ r - b ^ r‖ ≤ r q ^ r α` by
induction (the telescoping sum of the paper).

**The memory bound.** In the setting of `VisibilityFloor.lean`, for a Jacobi scheme with held
samples: the piece of information `k` has age `r k`, the scheme uses the sample
`C k ∘ P' ^ r k` of the state `r k` steps ago, the reference would provide `C k ∘ V ^ r k`, and the
rule of subsystem `i` is `Pr ∘ P = F ∘ Pr + Σ_k G k ∘ C k ∘ P' ^ r k`. Then, with `‖Pr‖ ≤ 1`,

  `‖Pr ∘ U - F ∘ Pr - Σ_k G k ∘ C k ∘ V ^ r k‖ ≤ α (‖U‖ + ϱ)`,
  `ϱ = Σ_k r k · (‖V‖ / (1 - α)) ^ r k · ‖G k ∘ C k‖`.

The left side is at least the visibility bound `f` of the subsystem, so `f ≤ α (‖U‖ + ϱ)`, that
is, `α ≥ f / (‖U‖ + ϱ)`. Current samples (`r k = 0`) do not enter `ϱ`.

**Against the printed (21).** The paper prints `ϱ` with an additional prefactor `1 / (1 - α)`.
The proof of the paper (and this file) gives the constant without it; since `1 / (1 - α) ≥ 1` the
printed inequality is true but weaker than what is proved. Both are stated:
`memory_bound` (sharp), `memory_bound_printed` (as printed).

Proof: `visibility_bound` with the pieces `G k ∘ C k` and `P' ^ r k` against `V ^ r k`, the power
estimate above, and `‖Pr ∘ (P - U)‖ ≤ ‖Pr‖ α ‖U‖`.
-/
import Mathlib.Analysis.SpecificLimits.Normed
import CoSimFoundations.VisibilityFloor

namespace CoSimFoundations

section Ring

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- A right inverse of an element at distance `α < 1` from `1` has norm at most `1 / (1 - α)`. -/
theorem norm_le_of_mul_eq_one {D D' : 𝔸} (h : D * D' = 1) (hα : ‖D - 1‖ < 1) :
    ‖D'‖ ≤ 1 / (1 - ‖D - 1‖) := by
  have e : D' = 1 - (D - 1) * D' := by
    rw [sub_mul, one_mul, h, sub_sub_cancel]
  have h1 : ‖D'‖ ≤ 1 + ‖D - 1‖ * ‖D'‖ :=
    calc ‖D'‖ = ‖1 - (D - 1) * D'‖ := congrArg norm e
      _ ≤ ‖(1 : 𝔸)‖ + ‖(D - 1) * D'‖ := norm_sub_le _ _
      _ ≤ 1 + ‖D - 1‖ * ‖D'‖ := by
          rw [norm_one]
          exact add_le_add le_rfl (norm_mul_le _ _)
  rw [le_div_iff₀ (sub_pos.2 hα)]
  linarith

/-- A right inverse of an element at distance `α < 1` from `1` is at distance at most
`α / (1 - α)` from `1`. -/
theorem norm_sub_one_le_of_mul_eq_one {D D' : 𝔸} (h : D * D' = 1) (hα : ‖D - 1‖ < 1) :
    ‖D' - 1‖ ≤ ‖D - 1‖ / (1 - ‖D - 1‖) := by
  have e : D' - 1 = -((D - 1) * D') := by
    rw [sub_mul, one_mul, h, neg_sub]
  calc ‖D' - 1‖ = ‖(D - 1) * D'‖ := by rw [e, norm_neg]
    _ ≤ ‖D - 1‖ * ‖D'‖ := norm_mul_le _ _
    _ ≤ ‖D - 1‖ * (1 / (1 - ‖D - 1‖)) :=
        mul_le_mul_of_nonneg_left (norm_le_of_mul_eq_one h hα) (norm_nonneg _)
    _ = ‖D - 1‖ / (1 - ‖D - 1‖) := by rw [mul_one_div]

/-- The inverse of the step: `‖V * D'‖ ≤ ‖V‖ / (1 - α)`. -/
theorem norm_mul_inv_le {D D' : 𝔸} (V : 𝔸) (h : D * D' = 1) (hα : ‖D - 1‖ < 1) :
    ‖V * D'‖ ≤ ‖V‖ / (1 - ‖D - 1‖) :=
  calc ‖V * D'‖ ≤ ‖V‖ * ‖D'‖ := norm_mul_le _ _
    _ ≤ ‖V‖ * (1 / (1 - ‖D - 1‖)) :=
        mul_le_mul_of_nonneg_left (norm_le_of_mul_eq_one h hα) (norm_nonneg _)
    _ = ‖V‖ / (1 - ‖D - 1‖) := by rw [mul_one_div]

/-- The inverse of the step against that of the reference: `‖V * D' - V‖ ≤ ‖V‖ α / (1 - α)`. -/
theorem norm_mul_inv_sub_le {D D' : 𝔸} (V : 𝔸) (h : D * D' = 1) (hα : ‖D - 1‖ < 1) :
    ‖V * D' - V‖ ≤ ‖V‖ * ‖D - 1‖ / (1 - ‖D - 1‖) :=
  calc ‖V * D' - V‖ = ‖V * (D' - 1)‖ := by rw [mul_sub, mul_one]
    _ ≤ ‖V‖ * ‖D' - 1‖ := norm_mul_le _ _
    _ ≤ ‖V‖ * (‖D - 1‖ / (1 - ‖D - 1‖)) :=
        mul_le_mul_of_nonneg_left (norm_sub_one_le_of_mul_eq_one h hα) (norm_nonneg _)
    _ = ‖V‖ * ‖D - 1‖ / (1 - ‖D - 1‖) := by rw [mul_div_assoc]

/-- **Telescoping.** If `‖a‖ ≤ q`, `‖b‖ ≤ q` and `‖a - b‖ ≤ q ε`, then
`‖a ^ r - b ^ r‖ ≤ r q ^ r ε`. -/
theorem norm_pow_sub_pow_le_mul {a b : 𝔸} {q ε : ℝ} (ha : ‖a‖ ≤ q) (hb : ‖b‖ ≤ q)
    (hab : ‖a - b‖ ≤ q * ε) (r : ℕ) : ‖a ^ r - b ^ r‖ ≤ r * q ^ r * ε := by
  have hq : 0 ≤ q := (norm_nonneg a).trans ha
  induction r with
  | zero => simp
  | succ r ih =>
    have e : a ^ (r + 1) - b ^ (r + 1) = a ^ r * (a - b) + (a ^ r - b ^ r) * b := by
      rw [pow_succ, pow_succ, mul_sub, sub_mul]
      abel
    have h1 : ‖a ^ r * (a - b)‖ ≤ q ^ r * (q * ε) :=
      (norm_mul_le _ _).trans
        (mul_le_mul ((norm_pow_le a r).trans (pow_le_pow_left₀ (norm_nonneg a) ha r)) hab
          (norm_nonneg _) (pow_nonneg hq r))
    have h2 : ‖(a ^ r - b ^ r) * b‖ ≤ (r * q ^ r * ε) * q :=
      (norm_mul_le _ _).trans
        (mul_le_mul ih hb (norm_nonneg _) ((norm_nonneg _).trans ih))
    calc ‖a ^ (r + 1) - b ^ (r + 1)‖
        ≤ ‖a ^ r * (a - b)‖ + ‖(a ^ r - b ^ r) * b‖ := by rw [e]; exact norm_add_le _ _
      _ ≤ q ^ r * (q * ε) + (r * q ^ r * ε) * q := add_le_add h1 h2
      _ = ((r + 1 : ℕ) : ℝ) * q ^ (r + 1) * ε := by push_cast; ring

/-- **Powers of the inverse step against those of the reference:**
`‖(V * D') ^ r - V ^ r‖ ≤ r ‖V‖ ^ r α / (1 - α) ^ r`. -/
theorem norm_pow_mul_inv_sub_pow_le {D D' : 𝔸} (V : 𝔸) (h : D * D' = 1) (hα : ‖D - 1‖ < 1)
    (r : ℕ) :
    ‖(V * D') ^ r - V ^ r‖ ≤ r * ‖V‖ ^ r * ‖D - 1‖ / (1 - ‖D - 1‖) ^ r := by
  have hpos : 0 < 1 - ‖D - 1‖ := sub_pos.2 hα
  have hb : ‖V‖ ≤ ‖V‖ / (1 - ‖D - 1‖) := by
    rw [le_div_iff₀ hpos]
    nlinarith [norm_nonneg V, norm_nonneg (D - 1)]
  have hab : ‖V * D' - V‖ ≤ ‖V‖ / (1 - ‖D - 1‖) * ‖D - 1‖ :=
    (norm_mul_inv_sub_le V h hα).trans (le_of_eq (by ring))
  have hmain := norm_pow_sub_pow_le_mul (norm_mul_inv_le V h hα) hb hab r
  refine hmain.trans (le_of_eq ?_)
  rw [div_pow]
  ring

/-- The inverse of the step is `V * D'`: any right inverse `P'` of `D * U` equals it. -/
theorem eq_mul_inv_of_step_mul_eq_one {D D' U V P' : 𝔸} (hD' : D' * D = 1) (hVU : V * U = 1)
    (hP' : D * U * P' = 1) : P' = V * D' := by
  have h1 : V * D' * (D * U) = 1 := by
    rw [mul_assoc, ← mul_assoc D', hD', one_mul, hVU]
  calc P' = V * D' * (D * U) * P' := by rw [h1, one_mul]
    _ = V * D' := by rw [mul_assoc, hP', mul_one]

variable [CompleteSpace 𝔸]

/-- An element at distance less than `1` from `1` has an inverse (Neumann series). -/
theorem exists_inverse_of_norm_sub_one_lt {D : 𝔸} (hα : ‖D - 1‖ < 1) :
    ∃ D' : 𝔸, D * D' = 1 ∧ D' * D = 1 := by
  have h : ‖1 - D‖ < 1 := by rwa [norm_sub_rev]
  refine ⟨∑' i : ℕ, (1 - D) ^ i, ?_, ?_⟩
  · have h1 := mul_neg_geom_series (1 - D) h
    rwa [sub_sub_cancel] at h1
  · have h1 := geom_series_mul_neg (1 - D) h
    rwa [sub_sub_cancel] at h1

/-- **Corollary 4.8, the step is invertible.** If `U` has the inverse `V` and `‖D - 1‖ < 1`, then
`P = D * U` has an inverse `P'`. -/
theorem exists_step_inverse {D U V : 𝔸} (hUV : U * V = 1) (hVU : V * U = 1)
    (hα : ‖D - 1‖ < 1) : ∃ P' : 𝔸, D * U * P' = 1 ∧ P' * (D * U) = 1 := by
  obtain ⟨D', h1, h2⟩ := exists_inverse_of_norm_sub_one_lt hα
  refine ⟨V * D', ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc U, hUV, one_mul, h1]
  · rw [mul_assoc, ← mul_assoc D', h2, one_mul, hVU]

/-- **Corollary 4.8, the bounds on the inverse step.** If `V` is a left inverse of `U`,
`α = ‖D - 1‖ < 1` and `P'` is a right inverse of `P = D * U`, then `P'` is also a left inverse,
`‖P'‖ ≤ ‖V‖ / (1 - α)`, `‖P' - V‖ ≤ ‖V‖ α / (1 - α)` and, for every `r`,
`‖P' ^ r - V ^ r‖ ≤ r ‖V‖ ^ r α / (1 - α) ^ r`. -/
theorem step_inverse_bounds {D U V P' : 𝔸} (hVU : V * U = 1) (hα : ‖D - 1‖ < 1)
    (hP' : D * U * P' = 1) :
    P' * (D * U) = 1 ∧ ‖P'‖ ≤ ‖V‖ / (1 - ‖D - 1‖) ∧
      ‖P' - V‖ ≤ ‖V‖ * ‖D - 1‖ / (1 - ‖D - 1‖) ∧
      ∀ r : ℕ, ‖P' ^ r - V ^ r‖ ≤ r * ‖V‖ ^ r * ‖D - 1‖ / (1 - ‖D - 1‖) ^ r := by
  obtain ⟨D', h1, h2⟩ := exists_inverse_of_norm_sub_one_lt hα
  rw [eq_mul_inv_of_step_mul_eq_one h2 hVU hP']
  refine ⟨?_, norm_mul_inv_le V h1 hα, norm_mul_inv_sub_le V h1 hα,
    norm_pow_mul_inv_sub_pow_le V h1 hα⟩
  rw [mul_assoc, ← mul_assoc D', h2, one_mul, hVU]

end Ring

section Visibility

variable {E Ei : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Ei] [NormedSpace ℝ Ei]
  {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ k, NormedAddCommGroup (Y k)]
  [∀ k, NormedSpace ℝ (Y k)]

/-- The constant `ϱ = Σ_k r k (‖V‖ / (1 - α)) ^ r k ‖G k ∘ C k‖` of the memory bound is
nonnegative for `α = ‖D - 1‖ < 1`. -/
theorem memory_sum_nonneg (D V : E →L[ℝ] E) (hα : ‖D - 1‖ < 1) (G : ∀ k, Y k →L[ℝ] Ei)
    (C : ∀ k, E →L[ℝ] Y k) (r : ι → ℕ) :
    0 ≤ ∑ k, (r k : ℝ) * (‖V‖ / (1 - ‖D - 1‖)) ^ r k * ‖(G k).comp (C k)‖ := by
  have hpos : 0 < 1 - ‖D - 1‖ := sub_pos.2 hα
  exact Finset.sum_nonneg fun k _ => by positivity

/-- **Corollary 4.8 (memory), the bound for the rule at hand.** A Jacobi scheme with held
samples: `U` the reference step with left inverse `V`, `P = D * U` the step of the scheme with
`α = ‖D - 1‖ < 1` and right inverse `P'`; the piece of information `k` is the sample
`C k ∘ P' ^ r k` of age `r k`, used with the coefficient `G k`. Then the distance of the
reference's block row from the rule built on the reference's own samples is at most
`α (‖U‖ + ϱ)` with `ϱ = Σ_k r k (‖V‖ / (1 - α)) ^ r k ‖G k ∘ C k‖`. -/
theorem memory_visibility_bound (Pr : E →L[ℝ] Ei) (hPr : ‖Pr‖ ≤ 1) (D U V P' : E →L[ℝ] E)
    (hVU : V * U = 1) (hα : ‖D - 1‖ < 1) (hP' : D * U * P' = 1) (F : Ei →L[ℝ] Ei)
    (G : ∀ k, Y k →L[ℝ] Ei) (C : ∀ k, E →L[ℝ] Y k) (r : ι → ℕ)
    (hstep : Pr.comp (D * U) = F.comp Pr + ∑ k, (G k).comp ((C k).comp (P' ^ r k))) :
    ‖Pr.comp U - F.comp Pr - ∑ k, (G k).comp ((C k).comp (V ^ r k))‖ ≤
      ‖D - 1‖ * (‖U‖ +
        ∑ k, (r k : ℝ) * (‖V‖ / (1 - ‖D - 1‖)) ^ r k * ‖(G k).comp (C k)‖) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- on the trivial space everything vanishes
    have h0 : Pr.comp U - F.comp Pr - ∑ k, (G k).comp ((C k).comp (V ^ r k)) = 0 :=
      Subsingleton.elim _ _
    rw [h0, norm_zero]
    exact mul_nonneg (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (memory_sum_nonneg D V hα G C r))
  · have hstep' : Pr.comp (D * U) =
        F.comp Pr + ∑ k, ((G k).comp (C k)).comp (P' ^ r k) := hstep
    have hb := visibility_bound (Y := fun _ => E) Pr (D * U) U F
      (fun k => (G k).comp (C k)) (fun k => P' ^ r k) (fun k => V ^ r k) hstep'
    obtain ⟨-, -, -, hpow⟩ := step_inverse_bounds hVU hα hP'
    have h1 : ‖Pr.comp (D * U - U)‖ ≤ ‖D - 1‖ * ‖U‖ :=
      (norm_comp_step_sub_le Pr D U).trans
        (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hPr)
    have h2 : ∀ k, ‖(G k).comp (C k)‖ * ‖P' ^ r k - V ^ r k‖ ≤
        ‖D - 1‖ * ((r k : ℝ) * (‖V‖ / (1 - ‖D - 1‖)) ^ r k * ‖(G k).comp (C k)‖) := by
      intro k
      refine (mul_le_mul_of_nonneg_left (hpow (r k)) (norm_nonneg _)).trans (le_of_eq ?_)
      rw [div_pow]
      ring
    refine hb.trans ?_
    rw [mul_add, Finset.mul_sum]
    exact add_le_add h1 (Finset.sum_le_sum fun k _ => h2 k)

/-- **Corollary 4.8 (memory), inequality (21) with the constant that the proof gives.** If `f` is
a lower bound for the distance of the reference's block row from the rule built on the reference's
own samples (the visibility bound of the subsystem for these samples), then
`f ≤ α (‖U‖ + ϱ)` with `ϱ = Σ_k r k (‖V‖ / (1 - α)) ^ r k ‖G k ∘ C k‖`. Current samples
(`r k = 0`) do not enter `ϱ`. -/
theorem memory_bound (Pr : E →L[ℝ] Ei) (hPr : ‖Pr‖ ≤ 1) (D U V P' : E →L[ℝ] E)
    (hVU : V * U = 1) (hα : ‖D - 1‖ < 1) (hP' : D * U * P' = 1) (F : Ei →L[ℝ] Ei)
    (G : ∀ k, Y k →L[ℝ] Ei) (C : ∀ k, E →L[ℝ] Y k) (r : ι → ℕ)
    (hstep : Pr.comp (D * U) = F.comp Pr + ∑ k, (G k).comp ((C k).comp (P' ^ r k)))
    {f : ℝ} (hf : f ≤ ‖Pr.comp U - F.comp Pr - ∑ k, (G k).comp ((C k).comp (V ^ r k))‖) :
    f ≤ ‖D - 1‖ * (‖U‖ +
      ∑ k, (r k : ℝ) * (‖V‖ / (1 - ‖D - 1‖)) ^ r k * ‖(G k).comp (C k)‖) :=
  hf.trans (memory_visibility_bound Pr hPr D U V P' hVU hα hP' F G C r hstep)

/-- **Inequality (21) as a bound on the one-step error:** `α ≥ f / (‖U‖ + ϱ)`. -/
theorem memory_bound_div (Pr : E →L[ℝ] Ei) (hPr : ‖Pr‖ ≤ 1) (D U V P' : E →L[ℝ] E)
    (hVU : V * U = 1) (hα : ‖D - 1‖ < 1) (hP' : D * U * P' = 1) (F : Ei →L[ℝ] Ei)
    (G : ∀ k, Y k →L[ℝ] Ei) (C : ∀ k, E →L[ℝ] Y k) (r : ι → ℕ)
    (hstep : Pr.comp (D * U) = F.comp Pr + ∑ k, (G k).comp ((C k).comp (P' ^ r k)))
    {f : ℝ} (hf : f ≤ ‖Pr.comp U - F.comp Pr - ∑ k, (G k).comp ((C k).comp (V ^ r k))‖) :
    f / (‖U‖ + ∑ k, (r k : ℝ) * (‖V‖ / (1 - ‖D - 1‖)) ^ r k * ‖(G k).comp (C k)‖) ≤
      ‖D - 1‖ := by
  exact div_le_of_le_mul₀ (add_nonneg (norm_nonneg _) (memory_sum_nonneg D V hα G C r))
    (norm_nonneg _)
    (memory_bound Pr hPr D U V P' hVU hα hP' F G C r hstep hf)

/-- **Inequality (21) as printed,** with the prefactor `1 / (1 - α)` in `ϱ`:
`f ≤ α (‖U‖ + (1 - α)⁻¹ Σ_k r k (‖V‖ / (1 - α)) ^ r k ‖G k ∘ C k‖)`. It is weaker than
`memory_bound`, because `(1 - α)⁻¹ ≥ 1`. -/
theorem memory_bound_printed (Pr : E →L[ℝ] Ei) (hPr : ‖Pr‖ ≤ 1) (D U V P' : E →L[ℝ] E)
    (hVU : V * U = 1) (hα : ‖D - 1‖ < 1) (hP' : D * U * P' = 1) (F : Ei →L[ℝ] Ei)
    (G : ∀ k, Y k →L[ℝ] Ei) (C : ∀ k, E →L[ℝ] Y k) (r : ι → ℕ)
    (hstep : Pr.comp (D * U) = F.comp Pr + ∑ k, (G k).comp ((C k).comp (P' ^ r k)))
    {f : ℝ} (hf : f ≤ ‖Pr.comp U - F.comp Pr - ∑ k, (G k).comp ((C k).comp (V ^ r k))‖) :
    f ≤ ‖D - 1‖ * (‖U‖ + (1 - ‖D - 1‖)⁻¹ *
      ∑ k, (r k : ℝ) * (‖V‖ / (1 - ‖D - 1‖)) ^ r k * ‖(G k).comp (C k)‖) := by
  have hinv : 1 ≤ (1 - ‖D - 1‖)⁻¹ :=
    (one_le_inv₀ (sub_pos.2 hα)).2 (by linarith [norm_nonneg (D - 1)])
  refine (memory_bound Pr hPr D U V P' hVU hα hP' F G C r hstep hf).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (norm_nonneg _)
  exact le_mul_of_one_le_left (memory_sum_nonneg D V hα G C r) hinv

end Visibility

end CoSimFoundations
