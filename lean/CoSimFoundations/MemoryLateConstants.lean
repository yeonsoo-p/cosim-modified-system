/-
Constants for the bound with `l` held samples at arbitrary sample ages (the paper, Section 4,
the sentence after Theorem 4.11 on a subsystem that runs after all of its partners;
"bounded weights" with the nodes `1, 0, …, -(l-2)`; used by
`MemoryLate.lean`).

A sample of the age `r ∈ ℤ` is the sample of `t_{k-r}`: the age `0` is the current sample, the
ages `r ≥ 1` are past samples, the age `-1` is the new sample of `t_{k+1}`.

1. **Node polynomial of a finite set `S` of ages.** `nodePoly S = ∏_{r ∈ S} (s + r)`, with the
   coefficients `nodeCoeff S m`. It is monic of degree `#S` and vanishes at `s = -r`, `r ∈ S`:
   `(-r)^{#S} = -Σ_{m < #S} nodeCoeff S m (-r)ᵐ`. Recursion for the coefficients when an age is
   added (`nodeCoeff_insert_zero`, `nodeCoeff_insert_succ`).

2. **The error constant.** `nodeGamma S = (1/l!) Σ_{m≤l} nodeCoeff S m / (m+1)
   = (1/l!) ∫₀¹ ∏_{r ∈ S} (s + r) ds`, `l = #S` (`nodeGamma_eq_integral`), and
   `nodeGamma S · h = h/(l+1)! + Σ_{m<l} (nodeCoeff S m · m!/l!) h/(m+1)!` (`nodeGamma_mul`).

3. **The two sets of ages of the paper.** `leadNodes l = {0, …, l-1}` (a subsystem that runs
   before all of its partners): its node polynomial is the rising factorial, `nodeGamma` is the
   Adams–Bashforth constant `adamsGamma l`. `lateNodes l = {-1, 0, …, l-2}` (a subsystem that runs
   after all of its partners): `lateGamma l = (1/l!) ∫₀¹ (s - 1) ∏_{k<l-1} (s + k) ds`, the error
   constant of the Adams–Moulton method with `l` nodes,
   `lateGamma 1, …, lateGamma 4 = -1/2, -1/12, -1/24, -19/720`.

4. **The constants of the bound.** `β_m = |nodeCoeff S m| m!/l!` (`nodeBeta`), `b = Σ_{m<l} β_m`
   (`nodeB`), `C_1 = ε_l + Σ_{m<l} β_m ε_m`, `ε_m = Σ_{p≥m+2} 1/p!` (`nodeC1`),
   `C_2 = ς_l + Σ_{m<l} β_m ς_m`, `ς_m = Σ_{r ∈ S} Σ_{p≥m+1} |r|ᵖ/p!` (`nodeC2`), and the remainder
   `e_m = Σ_{p≥m+2} xᵖ/p! + w H Σ_{r ∈ S} Σ_{p≥m+1} (|r| x)ᵖ/p!` (`nodeE`). For the late ages:
   `lateB 1, …, lateB 4 = 1, 1/2, 1/6, 2/3`; `lateC1 1 = 2e - 9/2`, `lateC2 1 = 2e - 3`;
   `lateC1 2 = 3e/2 - 47/12`, `lateC2 2 = 3e/2 - 7/2`; `lateC1 3 = 7e/6 - 25/8`,
   `lateC2 3 = 7e/3 - 6`; `lateC1 4 = 5e/3 - 3241/720`, `lateC2 4 = 5e²/3 + 10e/3 - 59/3`
   (numerically `0.937, 2.437; 0.161, 0.577; 0.046, 0.343; 0.029, 1.709`).
-/
import CoSimFoundations.AdamsConstants

open Finset
open scoped Nat

namespace CoSimFoundations

section NodePolynomial

/-- The node polynomial `∏_{r ∈ S} (s + r)` of a finite set `S` of sample ages. -/
noncomputable def nodePoly (S : Finset ℤ) : Polynomial ℝ :=
  ∏ r ∈ S, (Polynomial.X + Polynomial.C (r : ℝ))

/-- The coefficient of `sᵐ` in the node polynomial `∏_{r ∈ S} (s + r)`. -/
noncomputable def nodeCoeff (S : Finset ℤ) (m : ℕ) : ℝ :=
  (nodePoly S).coeff m

/-- The node polynomial at `s` is `∏_{r ∈ S} (s + r)`. -/
theorem nodePoly_eval (S : Finset ℤ) (s : ℝ) : (nodePoly S).eval s = ∏ r ∈ S, (s + r) := by
  simp [nodePoly, Polynomial.eval_prod]

/-- The node polynomial has the degree `#S`. -/
theorem nodePoly_natDegree (S : Finset ℤ) : (nodePoly S).natDegree = S.card := by
  unfold nodePoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun r _ => Polynomial.monic_X_add_C _]
  simp only [Polynomial.natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]

/-- The node polynomial is monic: its coefficient of `s^{#S}` is `1`. -/
theorem nodeCoeff_card (S : Finset ℤ) : nodeCoeff S S.card = 1 := by
  have h := (Polynomial.monic_prod_of_monic S (fun r : ℤ => Polynomial.X + Polynomial.C (r : ℝ))
    fun r _ => Polynomial.monic_X_add_C _).coeff_natDegree
  rwa [← nodePoly, nodePoly_natDegree] at h

/-- The node polynomial in terms of its coefficients:
`Σ_{m ≤ #S} nodeCoeff S m sᵐ = ∏_{r ∈ S} (s + r)`. -/
theorem sum_nodeCoeff_mul_pow (S : Finset ℤ) (s : ℝ) :
    ∑ m ∈ range (S.card + 1), nodeCoeff S m * s ^ m = ∏ r ∈ S, (s + r) := by
  rw [← nodePoly_eval, Polynomial.eval_eq_sum_range, nodePoly_natDegree]
  rfl

/-- The node polynomial vanishes at the ages: `Σ_{m ≤ #S} nodeCoeff S m (-r)ᵐ = 0`, `r ∈ S`. -/
theorem sum_nodeCoeff_mul_neg_pow {S : Finset ℤ} {r : ℤ} (hr : r ∈ S) :
    ∑ m ∈ range (S.card + 1), nodeCoeff S m * (-(r : ℝ)) ^ m = 0 := by
  rw [sum_nodeCoeff_mul_pow]
  exact prod_eq_zero hr (neg_add_cancel _)

/-- **The relation between the powers of the ages:**
`(-r)^{#S} = -Σ_{m < #S} nodeCoeff S m (-r)ᵐ` for every age `r ∈ S`. -/
theorem neg_pow_card_eq_neg_sum {S : Finset ℤ} {r : ℤ} (hr : r ∈ S) :
    (-(r : ℝ)) ^ S.card = -∑ m ∈ range S.card, nodeCoeff S m * (-(r : ℝ)) ^ m := by
  have h := sum_nodeCoeff_mul_neg_pow hr
  rw [sum_range_succ, nodeCoeff_card, one_mul] at h
  linarith

/-- The node polynomial of no sample is `1`. -/
theorem nodeCoeff_empty_zero : nodeCoeff ∅ 0 = 1 := by
  simp [nodeCoeff, nodePoly]

/-- The node polynomial of no sample is `1`: no higher coefficients. -/
theorem nodeCoeff_empty_succ (m : ℕ) : nodeCoeff ∅ (m + 1) = 0 := by
  simp [nodeCoeff, nodePoly, Polynomial.coeff_one]

/-- Adding an age `r` multiplies the node polynomial by `s + r`. -/
theorem nodePoly_insert {S : Finset ℤ} {r : ℤ} (hr : r ∉ S) :
    nodePoly (insert r S) = (Polynomial.X + Polynomial.C (r : ℝ)) * nodePoly S :=
  prod_insert hr

/-- Recursion for the constant coefficient when an age `r` is added. -/
theorem nodeCoeff_insert_zero {S : Finset ℤ} {r : ℤ} (hr : r ∉ S) :
    nodeCoeff (insert r S) 0 = r * nodeCoeff S 0 := by
  unfold nodeCoeff
  rw [nodePoly_insert hr, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul_zero,
    Polynomial.coeff_C_mul, zero_add]

/-- Recursion for the coefficients when an age `r` is added. -/
theorem nodeCoeff_insert_succ {S : Finset ℤ} {r : ℤ} (hr : r ∉ S) (m : ℕ) :
    nodeCoeff (insert r S) (m + 1) = nodeCoeff S m + r * nodeCoeff S (m + 1) := by
  unfold nodeCoeff
  rw [nodePoly_insert hr, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]

/-- The error constant of the set `S` of ages, `γ = (1/l!) Σ_{m≤l} nodeCoeff S m / (m+1)` with
`l = #S`, which is `(1/l!) ∫₀¹ ∏_{r ∈ S} (s + r) ds` (`nodeGamma_eq_integral`). -/
noncomputable def nodeGamma (S : Finset ℤ) : ℝ :=
  ((S.card ! : ℝ))⁻¹ * ∑ m ∈ range (S.card + 1), nodeCoeff S m / ((m : ℝ) + 1)

/-- **The constant as an integral:** `nodeGamma S = (1/l!) ∫₀¹ ∏_{r ∈ S} (s + r) ds`, `l = #S`. -/
theorem nodeGamma_eq_integral (S : Finset ℤ) :
    nodeGamma S = ((S.card ! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1, ∏ r ∈ S, (s + r) := by
  simp_rw [← sum_nodeCoeff_mul_pow]
  rw [integral_sum_mul_pow]
  rfl

/-- The constant in terms of the coefficients of the node polynomial, in the form used in the
proof: `γ h = h/(l+1)! + Σ_{m<l} (nodeCoeff S m · m!/l!) h/(m+1)!`, `l = #S`. -/
theorem nodeGamma_mul (S : Finset ℤ) (h : ℝ) :
    nodeGamma S * h = h / ((S.card + 1)! : ℝ) +
      ∑ m ∈ range S.card,
        nodeCoeff S m * (m ! : ℝ) / (S.card ! : ℝ) * (h / ((m + 1)! : ℝ)) := by
  have hl' : (S.card ! : ℝ) ≠ 0 := by positivity
  have hsum : ∑ m ∈ range S.card,
        nodeCoeff S m * (m ! : ℝ) / (S.card ! : ℝ) * (h / ((m + 1)! : ℝ)) =
      (S.card ! : ℝ)⁻¹ * h * ∑ m ∈ range S.card, nodeCoeff S m / ((m : ℝ) + 1) := by
    rw [mul_sum]
    exact sum_congr rfl fun m _ => mul_factorial_div_mul_div _ h S.card m
  have hl1 : (S.card : ℝ) + 1 ≠ 0 := by positivity
  unfold nodeGamma
  rw [hsum, sum_range_succ, nodeCoeff_card, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end NodePolynomial

section NodeSets

/-- The ages `0, …, l-1` of the samples of a subsystem that runs before all of its partners. -/
def leadNodes (l : ℕ) : Finset ℤ :=
  (range l).map Nat.castEmbedding

/-- The ages `-1, 0, …, l-2` of the `l ≥ 1` samples of a subsystem that runs after all of its
partners: the new sample (age `-1`) and the samples of the ages `0, …, l-2`. -/
def lateNodes (l : ℕ) : Finset ℤ :=
  insert (-1) (leadNodes (l - 1))

/-- There are `l` ages `0, …, l-1`. -/
theorem card_leadNodes (l : ℕ) : (leadNodes l).card = l := by
  simp [leadNodes]

/-- The age of the new sample is not among the ages `0, …, l-1`. -/
theorem neg_one_notMem_leadNodes (l : ℕ) : (-1 : ℤ) ∉ leadNodes l := by
  intro h
  obtain ⟨k, -, hk⟩ := mem_map.1 h
  have hk' : (k : ℤ) = -1 := hk
  omega

/-- There are `l` ages `-1, 0, …, l-2` (`l ≥ 1`). -/
theorem card_lateNodes {l : ℕ} (hl : 1 ≤ l) : (lateNodes l).card = l := by
  rw [lateNodes, card_insert_of_notMem (neg_one_notMem_leadNodes _), card_leadNodes]
  omega

/-- A sum over the ages `0, …, l-1`. -/
theorem sum_leadNodes {M : Type*} [AddCommMonoid M] (f : ℤ → M) (l : ℕ) :
    ∑ r ∈ leadNodes l, f r = ∑ k ∈ range l, f (k : ℤ) := by
  rw [leadNodes, sum_map]
  rfl

/-- A sum over the ages `-1, 0, …, l-2`: the new sample and the samples `0, …, l-2`. -/
theorem sum_lateNodes {M : Type*} [AddCommMonoid M] (f : ℤ → M) (l : ℕ) :
    ∑ r ∈ lateNodes l, f r = f (-1) + ∑ k ∈ range (l - 1), f (k : ℤ) := by
  rw [lateNodes, sum_insert (neg_one_notMem_leadNodes _), sum_leadNodes]

/-- The node polynomial of the ages `0, …, l-1` is the rising factorial. -/
theorem nodePoly_leadNodes (l : ℕ) : nodePoly (leadNodes l) = ascPochhammer ℝ l := by
  have h : nodePoly (leadNodes l) = ∏ k ∈ range l, (Polynomial.X + (k : Polynomial ℝ)) := by
    unfold nodePoly leadNodes
    rw [prod_map]
    refine prod_congr rfl fun k _ => ?_
    simp
  have hp : ∀ n : ℕ, ∏ k ∈ range n, (Polynomial.X + (k : Polynomial ℝ)) = ascPochhammer ℝ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [prod_range_succ, ih, ascPochhammer_succ_right]
  rw [h, hp]

/-- The coefficients of the node polynomial of the ages `0, …, l-1` are those of
`AdamsConstants.lean`. -/
theorem nodeCoeff_leadNodes (l m : ℕ) : nodeCoeff (leadNodes l) m = adamsCoeff l m := by
  unfold nodeCoeff adamsCoeff
  rw [nodePoly_leadNodes]

/-- For the ages `0, …, l-1` the error constant is the Adams–Bashforth constant `γ_l`. -/
theorem nodeGamma_leadNodes (l : ℕ) : nodeGamma (leadNodes l) = adamsGamma l := by
  unfold nodeGamma adamsGamma
  rw [card_leadNodes]
  simp only [nodeCoeff_leadNodes]

/-- The constant coefficient of the node polynomial `(s - 1) ∏_{k<l-1} (s + k)` of the ages
`-1, 0, …, l-2`. -/
theorem nodeCoeff_lateNodes_zero (l : ℕ) :
    nodeCoeff (lateNodes l) 0 = -adamsCoeff (l - 1) 0 := by
  rw [lateNodes, nodeCoeff_insert_zero (neg_one_notMem_leadNodes _), nodeCoeff_leadNodes]
  push_cast
  ring

/-- The coefficients of the node polynomial `(s - 1) ∏_{k<l-1} (s + k)` of the ages
`-1, 0, …, l-2`. -/
theorem nodeCoeff_lateNodes_succ (l m : ℕ) :
    nodeCoeff (lateNodes l) (m + 1) = adamsCoeff (l - 1) m - adamsCoeff (l - 1) (m + 1) := by
  rw [lateNodes, nodeCoeff_insert_succ (neg_one_notMem_leadNodes _), nodeCoeff_leadNodes,
    nodeCoeff_leadNodes]
  push_cast
  ring

/-- The error constant of the ages `-1, 0, …, l-2`: `γ'_l = (1/l!) ∫₀¹ (s-1) ∏_{k<l-1} (s+k) ds`
(`lateGamma_eq_integral`), the error constant of the Adams–Moulton method with `l` nodes. -/
noncomputable def lateGamma (l : ℕ) : ℝ :=
  nodeGamma (lateNodes l)

/-- The constant of the late ages in terms of the coefficients of the node polynomial. -/
theorem lateGamma_eq {l : ℕ} (hl : 1 ≤ l) :
    lateGamma l =
      ((l ! : ℝ))⁻¹ * ∑ m ∈ range (l + 1), nodeCoeff (lateNodes l) m / ((m : ℝ) + 1) := by
  unfold lateGamma nodeGamma
  rw [card_lateNodes hl]

/-- **The constant of the paper for a subsystem that runs after all of its partners:**
`γ'_l = (1/l!) ∫₀¹ (s - 1) ∏_{k<l-1} (s + k) ds`, the product over the ages `-1, 0, …, l-2`. -/
theorem lateGamma_eq_integral {l : ℕ} (hl : 1 ≤ l) :
    lateGamma l = ((l ! : ℝ))⁻¹ * ∫ s in (0 : ℝ)..1, (s - 1) * ∏ k ∈ range (l - 1), (s + k) := by
  have h : ∀ s : ℝ, ∏ r ∈ lateNodes l, (s + r) = (s - 1) * ∏ k ∈ range (l - 1), (s + k) := by
    intro s
    rw [lateNodes, prod_insert (neg_one_notMem_leadNodes _), leadNodes, prod_map]
    simp [sub_eq_add_neg]
  unfold lateGamma
  rw [nodeGamma_eq_integral, card_lateNodes hl]
  simp_rw [h]

/-- `γ'_1 = -1/2`. -/
theorem lateGamma_one : lateGamma 1 = -1 / 2 := by
  rw [lateGamma_eq le_rfl]
  simp [sum_range_succ, nodeCoeff_lateNodes_zero, nodeCoeff_lateNodes_succ,
    adamsCoeff_zero_zero, adamsCoeff_zero_succ, Nat.factorial]
  norm_num

end NodeSets

section BoundConstants

/-- `β_m = |nodeCoeff S m| m!/l!`, `l = #S`: the weight of the `m`-th moment in the `l`-th. -/
noncomputable def nodeBeta (S : Finset ℤ) (m : ℕ) : ℝ :=
  |nodeCoeff S m| * (m ! : ℝ) / (S.card ! : ℝ)

/-- `β_m ≥ 0`. -/
theorem nodeBeta_nonneg (S : Finset ℤ) (m : ℕ) : 0 ≤ nodeBeta S m := by
  unfold nodeBeta
  positivity

/-- `β_m` is the absolute value of the coefficient in Step 2. -/
theorem abs_nodeCoeff_mul_div (S : Finset ℤ) (m : ℕ) :
    |nodeCoeff S m * (m ! : ℝ) / (S.card ! : ℝ)| = nodeBeta S m := by
  unfold nodeBeta
  rw [abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]

/-- The constant `b = Σ_{m<l} β_m` of the bound, `l = #S`. -/
noncomputable def nodeB (S : Finset ℤ) : ℝ :=
  ∑ m ∈ range S.card, nodeBeta S m

/-- The constant `C_1 = ε_l + Σ_{m<l} β_m ε_m`, `ε_m = Σ_{p≥m+2} 1/p!`, of the bound. -/
noncomputable def nodeC1 (S : Finset ℤ) : ℝ :=
  expTail (S.card + 2) 1 + ∑ m ∈ range S.card, nodeBeta S m * expTail (m + 2) 1

/-- The constant `C_2 = ς_l + Σ_{m<l} β_m ς_m`, `ς_m = Σ_{r ∈ S} Σ_{p≥m+1} |r|ᵖ/p!`, of the
bound. -/
noncomputable def nodeC2 (S : Finset ℤ) : ℝ :=
  ∑ r ∈ S, expTail (S.card + 1) |(r : ℝ)| +
    ∑ m ∈ range S.card, nodeBeta S m * ∑ r ∈ S, expTail (m + 1) |(r : ℝ)|

/-- `b ≥ 0`. -/
theorem nodeB_nonneg (S : Finset ℤ) : 0 ≤ nodeB S :=
  sum_nonneg fun m _ => nodeBeta_nonneg S m

/-- `C_1 ≥ 0`. -/
theorem nodeC1_nonneg (S : Finset ℤ) : 0 ≤ nodeC1 S :=
  add_nonneg (expTail_nonneg _ zero_le_one) (sum_nonneg fun m _ =>
    mul_nonneg (nodeBeta_nonneg S m) (expTail_nonneg _ zero_le_one))

/-- `C_2 ≥ 0`. -/
theorem nodeC2_nonneg (S : Finset ℤ) : 0 ≤ nodeC2 S :=
  add_nonneg (sum_nonneg fun _ _ => expTail_nonneg _ (abs_nonneg _))
    (sum_nonneg fun m _ => mul_nonneg (nodeBeta_nonneg S m)
      (sum_nonneg fun _ _ => expTail_nonneg _ (abs_nonneg _)))

/-- The remainder of Step 1 for the ages `S`:
`e_m = Σ_{p≥m+2} xᵖ/p! + w H Σ_{r ∈ S} Σ_{p≥m+1} (|r| x)ᵖ/p!`. -/
noncomputable def nodeE (S : Finset ℤ) (m : ℕ) (w H x : ℝ) : ℝ :=
  expTail (m + 2) x + w * H * ∑ r ∈ S, expTail (m + 1) (|(r : ℝ)| * x)

/-- The remainder of Step 1 is nonnegative. -/
theorem nodeE_nonneg (S : Finset ℤ) (m : ℕ) {w H x : ℝ} (hw : 0 ≤ w) (hH : 0 ≤ H)
    (hx : 0 ≤ x) : 0 ≤ nodeE S m w H x :=
  add_nonneg (expTail_nonneg _ hx) (mul_nonneg (mul_nonneg hw hH)
    (sum_nonneg fun _ _ => expTail_nonneg _ (mul_nonneg (abs_nonneg _) hx)))

/-- The remainder of Step 1 for `x ≤ 1`: `e_m ≤ ε_m x^{m+2} + w H ς_m x^{m+1}`. -/
theorem nodeE_le (S : Finset ℤ) (m : ℕ) {w H x : ℝ} (hw : 0 ≤ w) (hH : 0 ≤ H) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    nodeE S m w H x ≤ expTail (m + 2) 1 * x ^ (m + 2) +
      w * H * (∑ r ∈ S, expTail (m + 1) |(r : ℝ)|) * x ^ (m + 1) := by
  have h1 := expTail_le_mul_pow (m + 2) hx0 hx1
  have h2 : ∑ r ∈ S, expTail (m + 1) (|(r : ℝ)| * x) ≤
      (∑ r ∈ S, expTail (m + 1) |(r : ℝ)|) * x ^ (m + 1) := by
    rw [sum_mul]
    refine sum_le_sum fun r _ => ?_
    have h := expTail_mul_le (m + 1) (abs_nonneg (r : ℝ)) hx0 hx1
    rwa [mul_comm (x ^ (m + 1))] at h
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hw hH)
  unfold nodeE
  linarith

/-- The constant `b'_l` of the bound for a subsystem that runs after all of its partners. -/
noncomputable def lateB (l : ℕ) : ℝ :=
  nodeB (lateNodes l)

/-- The constant `C'_1` of the bound for a subsystem that runs after all of its partners. -/
noncomputable def lateC1 (l : ℕ) : ℝ :=
  nodeC1 (lateNodes l)

/-- The constant `C'_2` of the bound for a subsystem that runs after all of its partners. -/
noncomputable def lateC2 (l : ℕ) : ℝ :=
  nodeC2 (lateNodes l)

/-- `b'_l ≥ 0`. -/
theorem lateB_nonneg (l : ℕ) : 0 ≤ lateB l :=
  nodeB_nonneg _

/-- `C'_1 ≥ 0`. -/
theorem lateC1_nonneg (l : ℕ) : 0 ≤ lateC1 l :=
  nodeC1_nonneg _

/-- `C'_2 ≥ 0`. -/
theorem lateC2_nonneg (l : ℕ) : 0 ≤ lateC2 l :=
  nodeC2_nonneg _

/-- `b'_l = Σ_{m<l} |nodeCoeff m| m!/l!` for the ages `-1, 0, …, l-2`. -/
theorem lateB_eq {l : ℕ} (hl : 1 ≤ l) :
    lateB l = ∑ m ∈ range l, |nodeCoeff (lateNodes l) m| * (m ! : ℝ) / (l ! : ℝ) := by
  unfold lateB nodeB nodeBeta
  rw [card_lateNodes hl]

/-- `C'_1 = ε_l + Σ_{m<l} β_m ε_m` for the ages `-1, 0, …, l-2`. -/
theorem lateC1_eq {l : ℕ} (hl : 1 ≤ l) :
    lateC1 l = expTail (l + 2) 1 + ∑ m ∈ range l,
      |nodeCoeff (lateNodes l) m| * (m ! : ℝ) / (l ! : ℝ) * expTail (m + 2) 1 := by
  unfold lateC1 nodeC1 nodeBeta
  rw [card_lateNodes hl]

/-- `C'_2 = ς_l + Σ_{m<l} β_m ς_m` for the ages `-1, 0, …, l-2`, with
`ς_m = Σ_{p≥m+1} 1/p! + Σ_{k<l-1} Σ_{p≥m+1} kᵖ/p!`. -/
theorem lateC2_eq {l : ℕ} (hl : 1 ≤ l) :
    lateC2 l = expTail (l + 1) 1 + ∑ k ∈ range (l - 1), expTail (l + 1) k +
      ∑ m ∈ range l, |nodeCoeff (lateNodes l) m| * (m ! : ℝ) / (l ! : ℝ) *
        (expTail (m + 1) 1 + ∑ k ∈ range (l - 1), expTail (m + 1) k) := by
  unfold lateC2 nodeC2 nodeBeta
  rw [card_lateNodes hl]
  simp [sum_lateNodes]

/-- `expTail 1 1 = e - 1`. -/
theorem expTail_one_one : expTail 1 1 = Real.exp 1 - 1 := by
  simp [expTail]

/-- `b'_1 = 1`. -/
theorem lateB_one : lateB 1 = 1 := by
  rw [lateB_eq le_rfl]
  simp [nodeCoeff_lateNodes_zero, adamsCoeff_zero_zero]

/-- `C'_1 = 2e - 9/2` for one sample, the new one. -/
theorem lateC1_one : lateC1 1 = 2 * Real.exp 1 - 9 / 2 := by
  rw [lateC1_eq le_rfl]
  simp [nodeCoeff_lateNodes_zero, adamsCoeff_zero_zero, expTail_two_one, expTail_three_one]
  ring

/-- `C'_2 = 2e - 3` for one sample, the new one. -/
theorem lateC2_one : lateC2 1 = 2 * Real.exp 1 - 3 := by
  rw [lateC2_eq le_rfl]
  simp [nodeCoeff_lateNodes_zero, adamsCoeff_zero_zero, expTail_two_one, expTail_one_one]
  ring

/-- The constants `γ'_l` and `b'_l` for `l = 2, 3, 4` samples, from the recursion for the
coefficients of the node polynomial: `γ'_2, γ'_3, γ'_4 = -1/12, -1/24, -19/720` and
`b'_2, b'_3, b'_4 = 1/2, 1/6, 2/3`. -/
theorem lateGamma_lateB_two_to_four :
    (lateGamma 2 = -1 / 12 ∧ lateGamma 3 = -1 / 24 ∧ lateGamma 4 = -19 / 720) ∧
      lateB 2 = 1 / 2 ∧ lateB 3 = 1 / 6 ∧ lateB 4 = 2 / 3 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    (first | rw [lateGamma_eq (by norm_num)] | rw [lateB_eq (by norm_num)]) <;>
    simp [sum_range_succ, nodeCoeff_lateNodes_zero, nodeCoeff_lateNodes_succ,
      adamsCoeff_succ_succ, adamsCoeff_succ_zero, adamsCoeff_zero_zero, adamsCoeff_zero_succ,
      Nat.factorial] <;>
    norm_num

/-- `γ'_2 = -1/12`. -/
theorem lateGamma_two : lateGamma 2 = -1 / 12 :=
  lateGamma_lateB_two_to_four.1.1

/-- `γ'_3 = -1/24`. -/
theorem lateGamma_three : lateGamma 3 = -1 / 24 :=
  lateGamma_lateB_two_to_four.1.2.1

/-- `γ'_4 = -19/720`. -/
theorem lateGamma_four : lateGamma 4 = -19 / 720 :=
  lateGamma_lateB_two_to_four.1.2.2

/-- `b'_2 = 1/2`. -/
theorem lateB_two : lateB 2 = 1 / 2 :=
  lateGamma_lateB_two_to_four.2.1

/-- `b'_3 = 1/6`. -/
theorem lateB_three : lateB 3 = 1 / 6 :=
  lateGamma_lateB_two_to_four.2.2.1

/-- `b'_4 = 2/3`. -/
theorem lateB_four : lateB 4 = 2 / 3 :=
  lateGamma_lateB_two_to_four.2.2.2

/-- `expTail 5 1 = e - 65/24`. -/
theorem expTail_five_one : expTail 5 1 = Real.exp 1 - 65 / 24 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- `expTail 6 1 = e - 163/60`. -/
theorem expTail_six_one : expTail 6 1 = Real.exp 1 - 163 / 60 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- `expTail 2 2 = e² - 3`. -/
theorem expTail_two_two : expTail 2 2 = Real.exp 2 - 3 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- `expTail 3 2 = e² - 5`. -/
theorem expTail_three_two : expTail 3 2 = Real.exp 2 - 5 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- `expTail 4 2 = e² - 19/3`. -/
theorem expTail_four_two : expTail 4 2 = Real.exp 2 - 19 / 3 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- `expTail 5 2 = e² - 7`. -/
theorem expTail_five_two : expTail 5 2 = Real.exp 2 - 7 := by
  simp [expTail, sum_range_succ, Nat.factorial]
  norm_num

/-- The constants `C'_1` for `l = 2, 3, 4` samples: `3e/2 - 47/12`, `7e/6 - 25/8` and
`5e/3 - 3241/720`. -/
theorem lateC1_two_to_four :
    lateC1 2 = 3 / 2 * Real.exp 1 - 47 / 12 ∧ lateC1 3 = 7 / 6 * Real.exp 1 - 25 / 8 ∧
      lateC1 4 = 5 / 3 * Real.exp 1 - 3241 / 720 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [lateC1_eq (by norm_num)]
    simp [sum_range_succ, nodeCoeff_lateNodes_zero, nodeCoeff_lateNodes_succ,
      adamsCoeff_succ_succ, adamsCoeff_succ_zero, adamsCoeff_zero_zero, adamsCoeff_zero_succ,
      Nat.factorial, expTail_three_one, expTail_four_one, expTail_five_one, expTail_six_one]
    ring

/-- `C'_1 = 3e/2 - 47/12` for the new and the current sample. -/
theorem lateC1_two : lateC1 2 = 3 / 2 * Real.exp 1 - 47 / 12 :=
  lateC1_two_to_four.1

/-- `C'_1 = 7e/6 - 25/8` for three samples (ages `-1, 0, 1`). -/
theorem lateC1_three : lateC1 3 = 7 / 6 * Real.exp 1 - 25 / 8 :=
  lateC1_two_to_four.2.1

/-- `C'_1 = 5e/3 - 3241/720` for four samples (ages `-1, 0, 1, 2`). -/
theorem lateC1_four : lateC1 4 = 5 / 3 * Real.exp 1 - 3241 / 720 :=
  lateC1_two_to_four.2.2

/-- The constants `C'_2` for `l = 2, 3, 4` samples: `3e/2 - 7/2`, `7e/3 - 6` and
`5e²/3 + 10e/3 - 59/3`. -/
theorem lateC2_two_to_four :
    lateC2 2 = 3 / 2 * Real.exp 1 - 7 / 2 ∧ lateC2 3 = 7 / 3 * Real.exp 1 - 6 ∧
      lateC2 4 = 5 / 3 * Real.exp 2 + 10 / 3 * Real.exp 1 - 59 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [lateC2_eq (by norm_num)]
    simp [sum_range_succ, nodeCoeff_lateNodes_zero, nodeCoeff_lateNodes_succ,
      adamsCoeff_succ_succ, adamsCoeff_succ_zero, adamsCoeff_zero_zero, adamsCoeff_zero_succ,
      Nat.factorial, expTail_zero, expTail_two_one, expTail_three_one, expTail_four_one,
      expTail_five_one, expTail_two_two, expTail_three_two, expTail_four_two, expTail_five_two]
    ring

/-- `C'_2 = 3e/2 - 7/2` for the new and the current sample. -/
theorem lateC2_two : lateC2 2 = 3 / 2 * Real.exp 1 - 7 / 2 :=
  lateC2_two_to_four.1

/-- `C'_2 = 7e/3 - 6` for three samples (ages `-1, 0, 1`). -/
theorem lateC2_three : lateC2 3 = 7 / 3 * Real.exp 1 - 6 :=
  lateC2_two_to_four.2.1

/-- `C'_2 = 5e²/3 + 10e/3 - 59/3` for four samples (ages `-1, 0, 1, 2`). -/
theorem lateC2_four :
    lateC2 4 = 5 / 3 * Real.exp 2 + 10 / 3 * Real.exp 1 - 59 / 3 :=
  lateC2_two_to_four.2.2

end BoundConstants

end CoSimFoundations
