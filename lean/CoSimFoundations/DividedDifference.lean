/-
Samples at `l` nodes and derivatives up to the order `l - 1` (the paper, Theorem `thm:memory`
(i), proof: "the maps `C_j U^{σ_ij - q}`, `q < l`, have the same common kernel as their divided
differences, which are `C_j A^p + O(H)`").

**Setting.** `A : E → E` bounded, `U^s = exp (s H A)`, `C : E → Y` an output map, nodes
`x : Fin l → ℝ` (the paper's `σ - q`), and a matrix `W` with `W · V = 1`, `V = (x_q^p)` the
Vandermonde matrix of the nodes (`W = V⁻¹`, which exists iff the nodes are distinct).

**Combinations of the samples.** `ddComb p = Σ_q W p q U^{x_q}`. From the exponential series and
`Σ_q W p q x_q^n = δ_{pn}` for `n < l`,

  `ddComb p = H^p A^p / p! + ddRem l p`                                    (`ddComb_eq_low`),
  `ddComb p = H^p A^p / p! + β_p H^l A^l / l! + ddRem (l+1) p`             (`ddComb_eq_top`),

with `β_p = Σ_q W p q x_q^l` (`ddBeta`; `s^l - Σ_p β_p s^p` is the node polynomial
`∏_q (s - x_q)`) and remainders `‖ddRem b p‖ ≤ (H ‖A‖)^b ω_p^b` for `H ‖A‖ ≤ 1`,
`ω_p^b = Σ_q |W p q| Σ_{n≥b} |x_q|^n / n!` (`ddOmega`, `norm_ddRem_le`).

**Statements.**
* `forall_ddComb_eq_zero_iff`: the samples `C U^{x_q} v`, `q < l`, all vanish iff the
  combinations `C (ddComb p v)`, `p < l`, all vanish.
* `norm_ddiff_sub_le`: the divided difference `(p!/H^p) C ∘ ddComb p` (`ddiff`) is
  `C A^p` up to `p! ‖C‖ ω_p^l ‖A‖^l H^{l-p}`.
* For a state `v` all of whose samples vanish:
  `dd_low_order`: `(H^p/p!) C A^p v = -β_p (H^l/l!) C A^l v - C (ddRem (l+1) p v)`;
  `norm_pow_smul_le`: `‖H^p C A^p v‖ ≤ p! ‖C‖ (|β_p|/l! + ω_p^{l+1}) (H ‖A‖)^l ‖v‖`;
  `dd_mean`: `Σ_{m≤l} H^{m+1}/(m+1)! C A^m v = γ H^{l+1} C A^l v - Σ_{p<l} H/(p+1) C (ddRem
  (l+1) p v)` with `γ = (1/l!) (1/(l+1) - Σ_p β_p/(p+1))` (`ddGamma`), which is
  `(1/l!) ∫₀¹ ∏_q (s - x_q) ds` (`LeadingConstant`): the mean over the macro step of a signal
  whose samples vanish is `γ H^l` times its `l`-th derivative to leading order;
  `norm_dd_mean_le`: the remainder of `dd_mean` is at most
  `(Σ_p ω_p^{l+1}/(p+1)) ‖C‖ H (H ‖A‖)^{l+1} ‖v‖`.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CoSimFoundations.AdamsConstants

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Moments

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {l : ℕ}

/-- `β_p = Σ_q W p q x_q^l`: the coefficient of `s^p` in the polynomial of degree below `l`
that agrees with `s^l` at the nodes. -/
def ddBeta (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ) (p : Fin l) : ℝ :=
  ∑ q, W p q * x q ^ l

/-- `ω_p^b = Σ_q |W p q| Σ_{n≥b} |x_q|^n / n!`, the constant of the remainder of order `b`. -/
noncomputable def ddOmega (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ) (b : ℕ) (p : Fin l) : ℝ :=
  ∑ q, |W p q| * expTail b |x q|

/-- The constant of the remainder is not negative. -/
theorem ddOmega_nonneg (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ) (b : ℕ) (p : Fin l) :
    0 ≤ ddOmega x W b p :=
  sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (expTail_nonneg b (abs_nonneg _))

/-- `γ = (1/l!) (1/(l+1) - Σ_{p<l} β_p/(p+1))`, the error constant of the nodes. -/
noncomputable def ddGamma (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ) : ℝ :=
  ((l ! : ℝ))⁻¹ * (1 / ((l : ℝ) + 1) - ∑ p : Fin l, ddBeta x W p / ((p : ℝ) + 1))

variable {x : Fin l → ℝ} {W : Matrix (Fin l) (Fin l) ℝ}

/-- The columns of `W` are dual to the powers at the nodes: `Σ_p x_q^p W p q' = δ_{qq'}`. -/
theorem sum_pow_mul_eq (hW : W * Matrix.vandermonde x = 1) (q q' : Fin l) :
    ∑ p : Fin l, x q ^ (p : ℕ) * W p q' = if q = q' then 1 else 0 := by
  have hV : Matrix.vandermonde x * W = 1 := mul_eq_one_comm.1 hW
  have h2 := congrFun (congrFun hV q) q'
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  exact h2

/-- The rows of `W` are dual to the powers at the nodes: `Σ_q W p q x_q^n = δ_{pn}`, `n < l`. -/
theorem sum_mul_pow_eq (hW : W * Matrix.vandermonde x = 1) (p n : Fin l) :
    ∑ q, W p q * x q ^ (n : ℕ) = if p = n then 1 else 0 := by
  have h := congrFun (congrFun hW p) n
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

/-- **Moments of order below `l`:** `Σ_q W p q Σ_{n<l} x_q^n f_n = f_p`. -/
theorem sum_vandermonde_low (hW : W * Matrix.vandermonde x = 1) (f : ℕ → M) (p : Fin l) :
    ∑ q, W p q • ∑ n ∈ range l, x q ^ n • f n = f p := by
  calc ∑ q, W p q • ∑ n ∈ range l, x q ^ n • f n
      = ∑ q, ∑ n : Fin l, (W p q * x q ^ (n : ℕ)) • f n := by
        refine sum_congr rfl fun q _ => ?_
        rw [← Fin.sum_univ_eq_sum_range (fun n => x q ^ n • f n) l, smul_sum]
        exact sum_congr rfl fun n _ => by rw [smul_smul]
    _ = ∑ n : Fin l, (∑ q, W p q * x q ^ (n : ℕ)) • f n := by
        rw [sum_comm]
        exact sum_congr rfl fun n _ => by rw [sum_smul]
    _ = ∑ n : Fin l, (if p = n then (1 : ℝ) else 0) • f n :=
        sum_congr rfl fun n _ => by rw [sum_mul_pow_eq hW]
    _ = f p := by simp

/-- **Moments up to the order `l`:** `Σ_q W p q Σ_{n≤l} x_q^n f_n = f_p + β_p f_l`. -/
theorem sum_vandermonde_top (hW : W * Matrix.vandermonde x = 1) (f : ℕ → M) (p : Fin l) :
    ∑ q, W p q • ∑ n ∈ range (l + 1), x q ^ n • f n = f p + ddBeta x W p • f l := by
  have h : ∀ q, W p q • ∑ n ∈ range (l + 1), x q ^ n • f n =
      W p q • ∑ n ∈ range l, x q ^ n • f n + (W p q * x q ^ l) • f l := fun q => by
    rw [sum_range_succ, smul_add, smul_smul]
  rw [sum_congr rfl fun q _ => h q, sum_add_distrib, sum_vandermonde_low hW, ← sum_smul]
  rfl

end Moments

section Exp

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {l : ℕ}

/-- The remainder of the exponential series after `b` terms. -/
noncomputable def expRem (b : ℕ) (Z : E →L[ℝ] E) : E →L[ℝ] E :=
  exp Z - ∑ n ∈ range b, ((n ! : ℝ)⁻¹) • Z ^ n

/-- The remainder is bounded by the tail of the series of norms. -/
theorem norm_expRem_le (Z : E →L[ℝ] E) {b : ℕ} (hb : 0 < b) : ‖expRem b Z‖ ≤ expTail b ‖Z‖ :=
  norm_exp_sub_sum_le_expTail Z hb

/-- The term of order `n` of the series of `exp (H A)`: `H^n A^n / n!`. -/
noncomputable def taylorTerm (A : E →L[ℝ] E) (H : ℝ) (n : ℕ) : E →L[ℝ] E :=
  ((n ! : ℝ)⁻¹ * H ^ n) • A ^ n

/-- The flow at the node `c`: `exp (c H A) = Σ_{n<b} c^n H^n A^n / n! + ` remainder. -/
theorem exp_node_eq (A : E →L[ℝ] E) (H c : ℝ) (b : ℕ) :
    exp ((c * H) • A) = ∑ n ∈ range b, c ^ n • taylorTerm A H n + expRem b ((c * H) • A) := by
  have h : ∀ n : ℕ, c ^ n • taylorTerm A H n = ((n ! : ℝ)⁻¹) • ((c * H) • A) ^ n := fun n => by
    unfold taylorTerm
    rw [smul_pow, mul_pow, smul_smul, smul_smul]
    congr 1
    ring
  rw [sum_congr rfl fun n _ => h n]
  unfold expRem
  exact (add_sub_cancel _ _).symm

/-- The combination `Σ_q W p q U^{x_q}` of the flows at the nodes. -/
noncomputable def ddComb (A : E →L[ℝ] E) (H : ℝ) (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ)
    (p : Fin l) : E →L[ℝ] E :=
  ∑ q, W p q • exp ((x q * H) • A)

/-- The same combination of the remainders of order `b`. -/
noncomputable def ddRem (A : E →L[ℝ] E) (H : ℝ) (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ)
    (b : ℕ) (p : Fin l) : E →L[ℝ] E :=
  ∑ q, W p q • expRem b ((x q * H) • A)

variable {x : Fin l → ℝ} {W : Matrix (Fin l) (Fin l) ℝ}

/-- The combination applied to a state. -/
theorem ddComb_apply (A : E →L[ℝ] E) (H : ℝ) (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ)
    (p : Fin l) (v : E) : ddComb A H x W p v = ∑ q, W p q • exp ((x q * H) • A) v := by
  simp [ddComb]

/-- **The combination to the order `l`:** `Σ_q W p q U^{x_q} = H^p A^p / p! + ` remainder. -/
theorem ddComb_eq_low (hW : W * Matrix.vandermonde x = 1) (A : E →L[ℝ] E) (H : ℝ) (p : Fin l) :
    ddComb A H x W p = taylorTerm A H p + ddRem A H x W l p := by
  have h : ∀ q, W p q • exp ((x q * H) • A) =
      W p q • ∑ n ∈ range l, x q ^ n • taylorTerm A H n +
        W p q • expRem l ((x q * H) • A) := fun q => by
    rw [← smul_add, ← exp_node_eq]
  unfold ddComb ddRem
  rw [sum_congr rfl fun q _ => h q, sum_add_distrib, sum_vandermonde_low hW]

/-- **The combination to the order `l + 1`:**
`Σ_q W p q U^{x_q} = H^p A^p / p! + β_p H^l A^l / l! + ` remainder. -/
theorem ddComb_eq_top (hW : W * Matrix.vandermonde x = 1) (A : E →L[ℝ] E) (H : ℝ) (p : Fin l) :
    ddComb A H x W p =
      taylorTerm A H p + ddBeta x W p • taylorTerm A H l + ddRem A H x W (l + 1) p := by
  have h : ∀ q, W p q • exp ((x q * H) • A) =
      W p q • ∑ n ∈ range (l + 1), x q ^ n • taylorTerm A H n +
        W p q • expRem (l + 1) ((x q * H) • A) := fun q => by
    rw [← smul_add, ← exp_node_eq]
  unfold ddComb ddRem
  rw [sum_congr rfl fun q _ => h q, sum_add_distrib, sum_vandermonde_top hW]

/-- **The remainder of the combination:** `‖ddRem b p‖ ≤ (H ‖A‖)^b ω_p^b` for `H ‖A‖ ≤ 1`. -/
theorem norm_ddRem_le (A : E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H) (hHA : H * ‖A‖ ≤ 1)
    (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ) {b : ℕ} (hb : 0 < b) (p : Fin l) :
    ‖ddRem A H x W b p‖ ≤ (H * ‖A‖) ^ b * ddOmega x W b p := by
  unfold ddRem ddOmega
  rw [mul_sum]
  refine norm_sum_le_of_le _ fun q _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : ‖expRem b ((x q * H) • A)‖ ≤ expTail b (|x q| * (H * ‖A‖)) := by
    have h := norm_expRem_le ((x q * H) • A) hb
    rwa [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hH, mul_assoc] at h
  have h2 := expTail_mul_le b (abs_nonneg (x q)) (mul_nonneg hH (norm_nonneg A)) hHA
  calc |W p q| * ‖expRem b ((x q * H) • A)‖
      ≤ |W p q| * ((H * ‖A‖) ^ b * expTail b |x q|) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
    _ = (H * ‖A‖) ^ b * (|W p q| * expTail b |x q|) := by ring

/-- `‖A^n v‖ ≤ ‖A‖^n ‖v‖`. -/
theorem norm_pow_apply_le (A : E →L[ℝ] E) (n : ℕ) (v : E) : ‖(A ^ n) v‖ ≤ ‖A‖ ^ n * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (A ^ (n + 1)) v = A ((A ^ n) v) := by
      rw [pow_succ']
      rfl
    rw [h, pow_succ', mul_assoc]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg A))

/-- The flow at a node is a combination of the combinations `ddComb`:
`exp (x_q H A) v = Σ_p x_q^p ddComb p v`. -/
theorem exp_node_apply_eq_sum (hW : W * Matrix.vandermonde x = 1) (A : E →L[ℝ] E) (H : ℝ)
    (q : Fin l) (v : E) :
    exp ((x q * H) • A) v = ∑ p : Fin l, x q ^ (p : ℕ) • ddComb A H x W p v := by
  calc exp ((x q * H) • A) v
      = ∑ q' : Fin l, (if q = q' then (1 : ℝ) else 0) • exp ((x q' * H) • A) v := by simp
    _ = ∑ q' : Fin l, (∑ p : Fin l, x q ^ (p : ℕ) * W p q') • exp ((x q' * H) • A) v :=
        sum_congr rfl fun q' _ => by rw [sum_pow_mul_eq hW]
    _ = ∑ p : Fin l, ∑ q' : Fin l, (x q ^ (p : ℕ) * W p q') • exp ((x q' * H) • A) v := by
        rw [sum_comm]
        exact sum_congr rfl fun q' _ => by rw [sum_smul]
    _ = ∑ p : Fin l, x q ^ (p : ℕ) • ddComb A H x W p v :=
        sum_congr rfl fun p _ => by
          rw [ddComb_apply, smul_sum]
          exact sum_congr rfl fun q' _ => by rw [smul_smul]

/-- **The samples and their combinations have the same common kernel:** `C U^{x_q} v = 0` for
all `q < l` iff `C (Σ_q W p q U^{x_q} v) = 0` for all `p < l`. -/
theorem forall_ddComb_eq_zero_iff (hW : W * Matrix.vandermonde x = 1) (C : E →L[ℝ] Y)
    (A : E →L[ℝ] E) (H : ℝ) (v : E) :
    (∀ p, C (ddComb A H x W p v) = 0) ↔ ∀ q, C (exp ((x q * H) • A) v) = 0 := by
  constructor
  · intro h q
    rw [exp_node_apply_eq_sum hW, map_sum]
    exact sum_eq_zero fun p _ => by rw [map_smul, h p, smul_zero]
  · intro h p
    rw [ddComb_apply, map_sum]
    exact sum_eq_zero fun q _ => by rw [map_smul, h q, smul_zero]

/-- The divided difference of order `p` of the samples of the output `C` at the nodes:
`(p!/H^p) C ∘ Σ_q W p q U^{x_q}`. -/
noncomputable def ddiff (C : E →L[ℝ] Y) (A : E →L[ℝ] E) (H : ℝ) (x : Fin l → ℝ)
    (W : Matrix (Fin l) (Fin l) ℝ) (p : Fin l) : E →L[ℝ] Y :=
  ((p ! : ℝ) / H ^ (p : ℕ)) • (C ∘L ddComb A H x W p)

/-- For a positive macro step the divided difference vanishes where the combination does. -/
theorem ddiff_apply_eq_zero_iff (C : E →L[ℝ] Y) (A : E →L[ℝ] E) {H : ℝ} (hH : 0 < H)
    (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ) (p : Fin l) (v : E) :
    ddiff C A H x W p v = 0 ↔ C (ddComb A H x W p v) = 0 := by
  have hc : (p ! : ℝ) / H ^ (p : ℕ) ≠ 0 := by positivity
  unfold ddiff
  rw [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_zero]
  exact ⟨fun h => h.resolve_left hc, fun h => Or.inr h⟩

/-- **The divided differences of the samples are the derivatives up to `O(H)`** (the paper, proof of
Theorem `thm:memory` (i)): `‖(p!/H^p) C Σ_q W p q U^{x_q} - C A^p‖ ≤ p! ‖C‖ ω_p^l ‖A‖^l H^{l-p}`
for `0 < H`, `H ‖A‖ ≤ 1`, `l ≥ 1`. -/
theorem norm_ddiff_sub_le (hW : W * Matrix.vandermonde x = 1) (C : E →L[ℝ] Y) (A : E →L[ℝ] E)
    {H : ℝ} (hH : 0 < H) (hHA : H * ‖A‖ ≤ 1) (p : Fin l) :
    ‖ddiff C A H x W p - C ∘L (A ^ (p : ℕ))‖ ≤
      (p ! : ℝ) * ‖C‖ * ddOmega x W l p * ‖A‖ ^ l * H ^ (l - (p : ℕ)) := by
  have hl : 0 < l := lt_of_le_of_lt (Nat.zero_le _) p.2
  have hp : (p : ℕ) ≤ l := p.2.le
  have hHp : H ^ (p : ℕ) ≠ 0 := by positivity
  have hfac : (p ! : ℝ) ≠ 0 := by positivity
  have h1 : ddiff C A H x W p - C ∘L (A ^ (p : ℕ)) =
      ((p ! : ℝ) / H ^ (p : ℕ)) • (C ∘L ddRem A H x W l p) := by
    unfold ddiff
    rw [ddComb_eq_low hW, ContinuousLinearMap.comp_add, smul_add]
    unfold taylorTerm
    rw [ContinuousLinearMap.comp_smul, smul_smul]
    have h2 : (p ! : ℝ) / H ^ (p : ℕ) * ((p ! : ℝ)⁻¹ * H ^ (p : ℕ)) = 1 := by
      field_simp
    rw [h2, one_smul, add_sub_cancel_left]
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 : ‖C ∘L ddRem A H x W l p‖ ≤ ‖C‖ * ((H * ‖A‖) ^ l * ddOmega x W l p) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_ddRem_le A hH.le hHA x W hl p) (norm_nonneg C))
  have h4 : H ^ l = H ^ (p : ℕ) * H ^ (l - (p : ℕ)) := by
    rw [← pow_add, Nat.add_sub_cancel' hp]
  calc (p ! : ℝ) / H ^ (p : ℕ) * ‖C ∘L ddRem A H x W l p‖
      ≤ (p ! : ℝ) / H ^ (p : ℕ) * (‖C‖ * ((H * ‖A‖) ^ l * ddOmega x W l p)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (p ! : ℝ) * ‖C‖ * ddOmega x W l p * ‖A‖ ^ l * H ^ (l - (p : ℕ)) := by
        rw [mul_pow, h4]
        field_simp

end Exp

section Vanishing

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {l : ℕ}
  {x : Fin l → ℝ} {W : Matrix (Fin l) (Fin l) ℝ}

/-- **A state whose samples vanish, the derivative of order `p < l`:**
`(H^p/p!) C A^p v = -β_p (H^l/l!) C A^l v - C (ddRem (l+1) p v)`. -/
theorem dd_low_order (hW : W * Matrix.vandermonde x = 1) (C : E →L[ℝ] Y) (A : E →L[ℝ] E)
    (H : ℝ) {v : E} (hv : ∀ q, C (exp ((x q * H) • A) v) = 0) (p : Fin l) :
    ((p ! : ℝ)⁻¹ * H ^ (p : ℕ)) • C ((A ^ (p : ℕ)) v) =
      -((ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l)) • C ((A ^ l) v)) -
        C (ddRem A H x W (l + 1) p v) := by
  have h0 : C (ddComb A H x W p v) = 0 := (forall_ddComb_eq_zero_iff hW C A H v).2 hv p
  have h1 : ddComb A H x W p v = ((p ! : ℝ)⁻¹ * H ^ (p : ℕ)) • (A ^ (p : ℕ)) v +
      (ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l)) • (A ^ l) v + ddRem A H x W (l + 1) p v := by
    rw [ddComb_eq_top hW]
    simp only [taylorTerm, _root_.add_apply, _root_.smul_apply, smul_smul]
  rw [h1, map_add, map_add, map_smul, map_smul] at h0
  rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, add_right_comm]
  exact h0

/-- **A state whose samples vanish, the size of the derivative of order `p < l`:**
`‖H^p C A^p v‖ ≤ p! ‖C‖ (|β_p|/l! + ω_p^{l+1}) (H ‖A‖)^l ‖v‖` for `H ‖A‖ ≤ 1`. -/
theorem norm_pow_smul_le (hW : W * Matrix.vandermonde x = 1) (C : E →L[ℝ] Y) (A : E →L[ℝ] E)
    {H : ℝ} (hH : 0 ≤ H) (hHA : H * ‖A‖ ≤ 1) {v : E}
    (hv : ∀ q, C (exp ((x q * H) • A) v) = 0) (p : Fin l) :
    ‖H ^ (p : ℕ) • C ((A ^ (p : ℕ)) v)‖ ≤
      (p ! : ℝ) * ‖C‖ * (|ddBeta x W p| / (l ! : ℝ) + ddOmega x W (l + 1) p) *
        (H * ‖A‖) ^ l * ‖v‖ := by
  have hfac : (p ! : ℝ) ≠ 0 := by positivity
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH (norm_nonneg A)
  have h1 : H ^ (p : ℕ) • C ((A ^ (p : ℕ)) v) =
      (p ! : ℝ) • (((p ! : ℝ)⁻¹ * H ^ (p : ℕ)) • C ((A ^ (p : ℕ)) v)) := by
    rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hfac, one_mul]
  rw [h1, dd_low_order hW C A H hv p, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : ‖(ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l)) • C ((A ^ l) v)‖ ≤
      |ddBeta x W p| / (l ! : ℝ) * ‖C‖ * (H * ‖A‖) ^ l * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (l ! : ℝ)⁻¹ * H ^ l)]
    have h3 : ‖C ((A ^ l) v)‖ ≤ ‖C‖ * (‖A‖ ^ l * ‖v‖) :=
      (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_pow_apply_le A l v) (norm_nonneg C))
    calc |ddBeta x W p| * ((l ! : ℝ)⁻¹ * H ^ l) * ‖C ((A ^ l) v)‖
        ≤ |ddBeta x W p| * ((l ! : ℝ)⁻¹ * H ^ l) * (‖C‖ * (‖A‖ ^ l * ‖v‖)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = |ddBeta x W p| / (l ! : ℝ) * ‖C‖ * (H * ‖A‖) ^ l * ‖v‖ := by
          rw [mul_pow]
          ring
  have h4 : ‖C (ddRem A H x W (l + 1) p v)‖ ≤
      ddOmega x W (l + 1) p * ‖C‖ * (H * ‖A‖) ^ l * ‖v‖ := by
    have h5 := norm_ddRem_le A hH hHA x W (Nat.succ_pos l) p
    have h6 : (H * ‖A‖) ^ (l + 1) ≤ (H * ‖A‖) ^ l := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hx0 l) hHA
    have h7 : ‖ddRem A H x W (l + 1) p‖ ≤ (H * ‖A‖) ^ l * ddOmega x W (l + 1) p :=
      h5.trans (mul_le_mul_of_nonneg_right h6 (ddOmega_nonneg x W _ p))
    calc ‖C (ddRem A H x W (l + 1) p v)‖ ≤ ‖C‖ * (‖ddRem A H x W (l + 1) p‖ * ‖v‖) :=
          (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            ((ddRem A H x W (l + 1) p).le_opNorm v) (norm_nonneg C))
      _ ≤ ‖C‖ * ((H * ‖A‖) ^ l * ddOmega x W (l + 1) p * ‖v‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h7 (norm_nonneg v))
            (norm_nonneg C)
      _ = ddOmega x W (l + 1) p * ‖C‖ * (H * ‖A‖) ^ l * ‖v‖ := by ring
  have h8 := norm_sub_le (-((ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l)) • C ((A ^ l) v)))
    (C (ddRem A H x W (l + 1) p v))
  rw [norm_neg] at h8
  have h9 : (0 : ℝ) < (p ! : ℝ) := by positivity
  calc (p ! : ℝ) * ‖-((ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l)) • C ((A ^ l) v)) -
        C (ddRem A H x W (l + 1) p v)‖
      ≤ (p ! : ℝ) * (|ddBeta x W p| / (l ! : ℝ) * ‖C‖ * (H * ‖A‖) ^ l * ‖v‖ +
          ddOmega x W (l + 1) p * ‖C‖ * (H * ‖A‖) ^ l * ‖v‖) :=
        mul_le_mul_of_nonneg_left (by linarith) h9.le
    _ = (p ! : ℝ) * ‖C‖ * (|ddBeta x W p| / (l ! : ℝ) + ddOmega x W (l + 1) p) *
          (H * ‖A‖) ^ l * ‖v‖ := by ring

/-- **A state whose samples vanish, the mean over the macro step:**
`Σ_{m≤l} H^{m+1}/(m+1)! C A^m v = γ H^{l+1} C A^l v - Σ_{p<l} H/(p+1) C (ddRem (l+1) p v)`. -/
theorem dd_mean (hW : W * Matrix.vandermonde x = 1) (C : E →L[ℝ] Y) (A : E →L[ℝ] E)
    (H : ℝ) {v : E} (hv : ∀ q, C (exp ((x q * H) • A) v) = 0) :
    ∑ m ∈ range (l + 1), (((m + 1) ! : ℝ)⁻¹ * H ^ (m + 1)) • C ((A ^ m) v) =
      (ddGamma x W * H ^ (l + 1)) • C ((A ^ l) v) -
        ∑ p : Fin l, (H / ((p : ℝ) + 1)) • C (ddRem A H x W (l + 1) p v) := by
  have hterm : ∀ p : Fin l, ((((p : ℕ) + 1) ! : ℝ)⁻¹ * H ^ ((p : ℕ) + 1)) • C ((A ^ (p : ℕ)) v) =
      (-(H / ((p : ℝ) + 1) * (ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l)))) • C ((A ^ l) v) -
        (H / ((p : ℝ) + 1)) • C (ddRem A H x W (l + 1) p v) := fun p => by
    have h1 : ((((p : ℕ) + 1) ! : ℝ)⁻¹ * H ^ ((p : ℕ) + 1)) • C ((A ^ (p : ℕ)) v) =
        (H / ((p : ℝ) + 1)) • (((p ! : ℝ)⁻¹ * H ^ (p : ℕ)) • C ((A ^ (p : ℕ)) v)) := by
      rw [smul_smul]
      congr 1
      have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
      have hfac : (p ! : ℝ) ≠ 0 := by positivity
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [h1, dd_low_order hW C A H hv p, smul_sub, smul_neg, smul_smul, neg_smul]
  rw [sum_range_succ, ← Fin.sum_univ_eq_sum_range
    (fun m => (((m + 1) ! : ℝ)⁻¹ * H ^ (m + 1)) • C ((A ^ m) v)) l,
    sum_congr rfl fun p _ => hterm p, sum_sub_distrib, ← sum_smul]
  have hγ : ∑ p : Fin l, -(H / ((p : ℝ) + 1) * (ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l))) +
      (((l + 1) ! : ℝ)⁻¹ * H ^ (l + 1)) = ddGamma x W * H ^ (l + 1) := by
    have hl1 : ((l : ℝ) + 1) ≠ 0 := by positivity
    have hfac : (l ! : ℝ) ≠ 0 := by positivity
    have hs : ∑ p : Fin l, -(H / ((p : ℝ) + 1) * (ddBeta x W p * ((l ! : ℝ)⁻¹ * H ^ l))) =
        -((l ! : ℝ)⁻¹ * H ^ (l + 1) * ∑ p : Fin l, ddBeta x W p / ((p : ℝ) + 1)) := by
      rw [mul_sum, ← sum_neg_distrib]
      exact sum_congr rfl fun p _ => by ring
    unfold ddGamma
    rw [hs, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [← hγ, add_smul]
  abel

/-- **The remainder of the mean:** `‖Σ_{p<l} H/(p+1) C (ddRem (l+1) p v)‖ ≤
(Σ_p ω_p^{l+1}/(p+1)) ‖C‖ H (H ‖A‖)^{l+1} ‖v‖` for `H ‖A‖ ≤ 1`. -/
theorem norm_dd_mean_le (C : E →L[ℝ] Y) (A : E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    (hHA : H * ‖A‖ ≤ 1) (x : Fin l → ℝ) (W : Matrix (Fin l) (Fin l) ℝ) (v : E) :
    ‖∑ p : Fin l, (H / ((p : ℝ) + 1)) • C (ddRem A H x W (l + 1) p v)‖ ≤
      (∑ p : Fin l, ddOmega x W (l + 1) p / ((p : ℝ) + 1)) * ‖C‖ * H * (H * ‖A‖) ^ (l + 1) *
        ‖v‖ := by
  rw [sum_mul, sum_mul, sum_mul, sum_mul]
  refine norm_sum_le_of_le _ fun p _ => ?_
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hH hp1.le)]
  have h1 : ‖C (ddRem A H x W (l + 1) p v)‖ ≤
      ‖C‖ * ((H * ‖A‖) ^ (l + 1) * ddOmega x W (l + 1) p * ‖v‖) :=
    (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (((ddRem A H x W (l + 1) p).le_opNorm v).trans (mul_le_mul_of_nonneg_right
        (norm_ddRem_le A hH hHA x W (Nat.succ_pos l) p) (norm_nonneg v))) (norm_nonneg C))
  calc H / ((p : ℝ) + 1) * ‖C (ddRem A H x W (l + 1) p v)‖
      ≤ H / ((p : ℝ) + 1) * (‖C‖ * ((H * ‖A‖) ^ (l + 1) * ddOmega x W (l + 1) p * ‖v‖)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hH hp1.le)
    _ = ddOmega x W (l + 1) p / ((p : ℝ) + 1) * ‖C‖ * H * (H * ‖A‖) ^ (l + 1) * ‖v‖ := by
        ring

end Vanishing

end CoSimFoundations
