/-
One order per held sample is reached by a rule with bounded weights (the paper, Theorem
`thm:memory` (ii) and the paragraph after it: "adding `H^{l+1} γ_l^σ a_i A^l` of it ... to
polynomial extrapolation keeps the weights bounded. The defect is then `|γ_l^σ| c_i H^{l+1}` to
leading order, so that the bound (ii) is the least defect of the rules with bounded weights,
whether or not the maps are independent").

**Setting**, that of `MemoryLead.lean` and `MemoryLate.lean`: `P = Π_i : E → F`, `C : E → G` the
stack of the outputs of the partners of `i`, `P ∘ A = Ai ∘ P + L ∘ C`, `U = exp (H • A)`, and a
set `S ⊂ ℤ` of `l` sample ages (the sample of the age `r` is `C U^{-r}`; `leadNodes l` for old
samples, `lateNodes l` for the new sample and old ones). The local defect of a rule with the
coefficient `Fi` on the own state and `g r` on the samples is
`𝒯 = P U - Fi P - Σ_{r ∈ S} g r C U^{-r}` (`nodeDefect`). `E` is a finite-dimensional inner
product space and `F`, `G` are finite-dimensional; `𝒱^0 = unseen P C A l`,
`c_i = ‖P A^{l+1}|𝒱^0‖`. No hypothesis on the maps `P`, `C A^p` (independence) is made.

**The rule** (`reachFi`, `reachRule`). Let `δ p r`, `p < l`, `r ∈ S`, be weights with
`Σ_{r ∈ S} δ p r (-r)^n = [p = n]` for `n < l` (the inverse of the Vandermonde matrix of the
nodes, `exists_nodeWeights`): `Σ_r δ p r C U^{-r} = H^p/p! C A^p + O(H^l)` is `H^p/p!` times the
divided difference of order `p`. A generalised inverse `R` of the stack
`N₀ v = (P v, (C A^p v)_{p<l})` (`shownStack`, `exists_generalizedInverse`) gives maps `ΛF`,
`Λ p` with `ΛF (P v) + Σ_{p<l} Λ p (C A^p v) = v - Q₀ v`, `Q₀` the orthogonal projection onto
`𝒱^0 = ker N₀` (`exists_shown_inverse`): the shown part of the state is a linear function of
`P v` and the derivatives `C A^p v`. With `γ = nodeGamma S`, `M = L C A^l` (the paper's
`a_i A^l`) and

  `Fi = Σ_{n ≤ l+1} H^n/n! Ai^n + γ H^{l+1} M ΛF`                            (`reachFi`),
  `g r = Σ_{p<l} δ p r X_p`                                                   (`reachRule`),
  `X_p = Σ_{p < n ≤ l+1} (p!/n!) H^{n-p} Ai^{n-1-p} L + γ p! H^{l+1-p} M Λ p` (`reachMoment`),

the moments of the rule are `Σ_r (-r)^n g r = X_n` for `n < l` and
`Σ_r (-r)^l g r = -Σ_{p<l} nodeCoeff S p X_p`. The first parts of `Fi` and `X_p` integrate the
Taylor polynomial of degree `l + 1` of the own state through the derivatives
(`proj_pow_apply_eq_sum`: `P A^n = Ai^n P + Σ_{k<n} Ai^{n-1-k} L C A^k`); with the divided
differences in place of the derivatives the coefficient of `L C A^l` becomes `γ H^{l+1}`, as for
polynomial extrapolation. The second parts are the correction of the paper,
`γ H^{l+1} M Λ (P v, divided differences)`.

**Statements.**
* `reach_defect_apply`: `𝒯 v = γ H^{l+1} M Q₀ v + ρ_A + ρ_B - ρ_C` with the remainders
  `ρ_A = P R_{l+2}(H A) v` (the exponential series of `U`), `ρ_C = Σ_r g r C R_{l+1}(-r H A) v`
  (that of the samples) and `ρ_B = Σ_p nodeCoeff S p (H^l/l!) (X_p - (p!/(p+1)!) H L) C A^l v`,
  each of the order `H^{l+2}` (`norm_proj_expRem_apply_le`, `norm_sum_coef_expRem_le`,
  `norm_sum_top_le`); `‖M Q₀ v‖ ≤ c_i ‖v‖` (`norm_lead_apply_le`).
* `exists_rule_nodeDefect_le`: there are `w, K ≥ 0` such that for every `0 ≤ H ≤ 1` with
  `H ‖A‖ ≤ 1` the rule has `‖Fi - 1‖ ≤ w H`, `‖g r ∘ C‖ ≤ w H` for every `r ∈ S` (all weights
  bounded, also that of the current sample) and `‖𝒯‖ ≤ |γ| c_i H^{l+1} + K H^{l+2}`.
* `memory_nodes_least`: with `memory_nodes`, the least defect of the rules with bounded weights
  is `|γ| c_i H^{l+1}` to leading order: the upper bound by the rule, and for every `w ≥ 0` and
  every rule with `‖g r ∘ C‖ ≤ w H` for `r ≠ 0` the lower bound
  `‖𝒯‖ ≥ |γ| c_i H^{l+1} - (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1} + b |γ| c_i ‖A‖) H^{l+2}`.
* `memory_lead_least` (all samples old, `localDefect`, `γ = adamsGamma l`) and
  `memory_late_least` (the new sample and old ones, `lateDefect`, `γ = lateGamma l`): the
  paper's two cases, with the constants of `memory_lead` and `memory_late`.

The constants `w` and `K` are existential: they depend on `A`, `Ai`, `L`, `C`, `P`, `S` and the
chosen `ΛF`, `Λ`, `δ`, not on `H`.
-/
import CoSimFoundations.MemoryLate
import CoSimFoundations.RunOrderLead
import CoSimFoundations.DividedDifference
import CoSimFoundations.KernelPerturbation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open NormedSpace Finset
open scoped Nat

namespace CoSimFoundations

section Weights

/-- **Weights of the divided differences at any `l` distinct ages:** for a finite set `S ⊂ ℤ`
there are `δ p r` with `Σ_{r ∈ S} δ p r (-r)^n = [p = n]` for `p, n < #S` (the inverse of the
Vandermonde matrix of the nodes `-r`). -/
theorem exists_nodeWeights (S : Finset ℤ) :
    ∃ δ : ℕ → ℤ → ℝ, ∀ p < S.card, ∀ n < S.card,
      ∑ r ∈ S, δ p r * (-(r : ℝ)) ^ n = if p = n then 1 else 0 := by
  set l := S.card with hl
  let e : S ≃ Fin l := S.equivFin
  let x : Fin l → ℝ := fun q => -(((e.symm q : S) : ℤ) : ℝ)
  have hx : Function.Injective x := by
    intro q q' h
    have h1 : (((e.symm q : S) : ℤ) : ℝ) = (((e.symm q' : S) : ℤ) : ℝ) := neg_injective h
    have h2 : e.symm q = e.symm q' := Subtype.ext (Int.cast_injective h1)
    exact e.symm.injective h2
  set V := Matrix.vandermonde x with hV
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hx)
  set W := V⁻¹ with hW
  have hWV : W * V = 1 := Matrix.nonsing_inv_mul V hdet
  refine ⟨fun p r => if h : r ∈ S ∧ p < l then W ⟨p, h.2⟩ (e ⟨r, h.1⟩) else 0, ?_⟩
  intro p hp n hn
  have h1 : ∑ r ∈ S, (if h : r ∈ S ∧ p < l then W ⟨p, h.2⟩ (e ⟨r, h.1⟩) else 0) *
        (-(r : ℝ)) ^ n =
      ∑ r : S, (if h : (r : ℤ) ∈ S ∧ p < l then W ⟨p, h.2⟩ (e ⟨r, h.1⟩) else 0) *
        (-((r : ℤ) : ℝ)) ^ n :=
    (Finset.sum_coe_sort S _).symm
  have h2 : ∑ r : S, (if h : (r : ℤ) ∈ S ∧ p < l then W ⟨p, h.2⟩ (e ⟨r, h.1⟩) else 0) *
        (-((r : ℤ) : ℝ)) ^ n =
      ∑ q : Fin l, W ⟨p, hp⟩ q * x q ^ n := by
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : ((e.symm q : S) : ℤ) ∈ S ∧ p < l := ⟨(e.symm q).2, hp⟩
    simp [x, hq]
  have h3 := congrFun (congrFun hWV ⟨p, hp⟩) ⟨n, hn⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at h3
  simp only [hV, Matrix.vandermonde_apply] at h3
  rw [h1, h2, h3]
  simp [Fin.ext_iff]

/-- **The moments of a rule built from prescribed moments.** For weights as in
`exists_nodeWeights` and `X : ℕ → M`, the coefficients `g r = Σ_{p<l} δ p r X p` have the moments
`Σ_{r ∈ S} (-r)^n g r = X n` for `n < l`. -/
theorem sum_neg_pow_smul_weights {M : Type*} [AddCommGroup M] [Module ℝ M] {S : Finset ℤ}
    {δ : ℕ → ℤ → ℝ}
    (hδ : ∀ p < S.card, ∀ n < S.card,
      ∑ r ∈ S, δ p r * (-(r : ℝ)) ^ n = if p = n then 1 else 0)
    (X : ℕ → M) {n : ℕ} (hn : n < S.card) :
    ∑ r ∈ S, (-(r : ℝ)) ^ n • ∑ p ∈ range S.card, δ p r • X p = X n := by
  simp only [smul_sum, smul_smul]
  rw [sum_comm]
  have h : ∀ p ∈ range S.card, ∑ r ∈ S, ((-(r : ℝ)) ^ n * δ p r) • X p =
      (if p = n then (1 : ℝ) else 0) • X p := by
    intro p hp
    rw [← sum_smul, ← hδ p (mem_range.1 hp) n hn]
    congr 1
    exact sum_congr rfl fun r _ => mul_comm _ _
  rw [sum_congr rfl h]
  simp [hn]

/-- **The top moment of such a rule:** `Σ_{r ∈ S} (-r)^l g r = -Σ_{p<l} nodeCoeff S p X p`,
`l = #S`, because the ages are the roots of the node polynomial. -/
theorem sum_neg_pow_card_smul_weights {M : Type*} [AddCommGroup M] [Module ℝ M] {S : Finset ℤ}
    {δ : ℕ → ℤ → ℝ}
    (hδ : ∀ p < S.card, ∀ n < S.card,
      ∑ r ∈ S, δ p r * (-(r : ℝ)) ^ n = if p = n then 1 else 0)
    (X : ℕ → M) :
    ∑ r ∈ S, (-(r : ℝ)) ^ S.card • ∑ p ∈ range S.card, δ p r • X p =
      -∑ p ∈ range S.card, nodeCoeff S p • X p := by
  have h1 : ∀ r ∈ S, (-(r : ℝ)) ^ S.card • ∑ p ∈ range S.card, δ p r • X p =
      -∑ m ∈ range S.card, nodeCoeff S m • ((-(r : ℝ)) ^ m • ∑ p ∈ range S.card, δ p r • X p) := by
    intro r hr
    rw [neg_pow_card_eq_neg_sum hr, neg_smul, sum_smul]
    simp only [smul_smul]
  rw [sum_congr rfl h1, sum_neg_distrib, sum_comm]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  rw [← smul_sum, sum_neg_pow_smul_weights hδ X (mem_range.1 hm)]

end Weights

section Taylor

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- The coupling row along the powers of `A`:
`P A^n v = Ai^n P v + Σ_{k<n} Ai^{n-1-k} L C A^k v`. -/
theorem proj_pow_apply_eq_sum (hA : P ∘L A = Ai ∘L P + L ∘L C) (n : ℕ) (v : E) :
    P ((A ^ n) v) = (Ai ^ n) (P v) + ∑ k ∈ range n, (Ai ^ (n - 1 - k)) (L (C ((A ^ k) v))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (A ^ (n + 1)) v = A ((A ^ n) v) := by
      rw [pow_succ']
      rfl
    have h2 : P (A ((A ^ n) v)) = Ai (P ((A ^ n) v)) + L (C ((A ^ n) v)) := by
      have h' := congrArg (fun T : E →L[ℝ] F => T ((A ^ n) v)) hA
      simpa using h'
    have h3 : (Ai ^ (n + 1)) (P v) = Ai ((Ai ^ n) (P v)) := by
      rw [pow_succ']
      rfl
    have h4 : ∀ k ∈ range n, Ai ((Ai ^ (n - 1 - k)) (L (C ((A ^ k) v)))) =
        (Ai ^ (n + 1 - 1 - k)) (L (C ((A ^ k) v))) := by
      intro k hk
      have hk' := mem_range.1 hk
      rw [show n + 1 - 1 - k = n - 1 - k + 1 by omega, pow_succ']
      rfl
    rw [h1, h2, ih, map_add, map_sum, sum_range_succ, h3, sum_congr rfl h4,
      show n + 1 - 1 - n = 0 by omega, pow_zero, one_apply_eq_self]
    abel

/-- The Taylor polynomial of `exp (H Ai)` of degree `l + 1`: `Σ_{n ≤ l+1} H^n/n! Ai^n`. -/
noncomputable def taylorLocal (Ai : F →L[ℝ] F) (H : ℝ) (l : ℕ) : F →L[ℝ] F :=
  ∑ n ∈ range (l + 2), ((n ! : ℝ)⁻¹ * H ^ n) • Ai ^ n

/-- The coefficient of `C A^k` in the Taylor polynomial of degree `l + 1` of the own state:
`Σ_{k < n ≤ l+1} H^n/n! Ai^{n-1-k} L`. -/
noncomputable def taylorRow (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (H : ℝ) (l k : ℕ) : G →L[ℝ] F :=
  ∑ n ∈ range (l + 2), if k < n then ((n ! : ℝ)⁻¹ * H ^ n) • ((Ai ^ (n - 1 - k)) ∘L L) else 0

/-- The same coefficient divided by `H^k/k!`: `Σ_{k < n ≤ l+1} (k!/n!) H^{n-k} Ai^{n-1-k} L`. -/
noncomputable def taylorMoment (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (H : ℝ) (l k : ℕ) :
    G →L[ℝ] F :=
  ∑ n ∈ range (l + 2),
    if k < n then ((k ! : ℝ) / (n ! : ℝ) * H ^ (n - k)) • ((Ai ^ (n - 1 - k)) ∘L L) else 0

/-- The terms of `taylorMoment` of the order `H^2` and higher. -/
noncomputable def taylorMomentTail (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (H : ℝ) (l k : ℕ) :
    G →L[ℝ] F :=
  ∑ n ∈ range (l + 2),
    if k + 1 < n then ((k ! : ℝ) / (n ! : ℝ) * H ^ (n - k)) • ((Ai ^ (n - 1 - k)) ∘L L) else 0

/-- `H^k/k! · taylorMoment k = taylorRow k`. -/
theorem smul_taylorMoment (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (H : ℝ) (l k : ℕ) :
    ((k ! : ℝ)⁻¹ * H ^ k) • taylorMoment Ai L H l k = taylorRow Ai L H l k := by
  unfold taylorMoment taylorRow
  rw [smul_sum]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [smul_smul]
    congr 1
    have hk : (k ! : ℝ) ≠ 0 := by positivity
    have hn : (n ! : ℝ) ≠ 0 := by positivity
    have e : H ^ k * H ^ (n - k) = H ^ n := by rw [← pow_add, Nat.add_sub_cancel' h.le]
    field_simp
    rw [← e]
  · rw [smul_zero]

/-- The coefficient of `C A^l` is the term of the order `H^{l+1}`:
`taylorRow l = H^{l+1}/(l+1)! L`. -/
theorem taylorRow_self (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (H : ℝ) (l : ℕ) :
    taylorRow Ai L H l l = (((l + 1)! : ℝ)⁻¹ * H ^ (l + 1)) • L := by
  unfold taylorRow
  rw [sum_range_succ, sum_eq_zero fun n hn => ite_eq_right (by have := mem_range.1 hn; omega),
    zero_add, ite_eq_left (by omega), show l + 1 - 1 - l = 0 by omega, pow_zero]
  rfl

/-- `taylorMoment k = (k!/(k+1)!) H L + taylorMomentTail k` for `k ≤ l`. -/
theorem taylorMoment_eq (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (H : ℝ) {l k : ℕ} (hk : k ≤ l) :
    taylorMoment Ai L H l k =
      ((k ! : ℝ) / ((k + 1)! : ℝ) * H) • L + taylorMomentTail Ai L H l k := by
  unfold taylorMoment taylorMomentTail
  have h : ∀ n ∈ range (l + 2),
      (if k < n then ((k ! : ℝ) / (n ! : ℝ) * H ^ (n - k)) • ((Ai ^ (n - 1 - k)) ∘L L) else 0) =
        (if k + 1 = n then ((k ! : ℝ) / ((k + 1)! : ℝ) * H) • L else 0) +
        (if k + 1 < n then ((k ! : ℝ) / (n ! : ℝ) * H ^ (n - k)) • ((Ai ^ (n - 1 - k)) ∘L L)
          else 0) := by
    intro n _
    rcases lt_trichotomy (k + 1) n with h1 | h1 | h1
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h1, zero_add]
    · subst h1
      rw [ite_eq_left (by omega), ite_eq_left rfl, ite_eq_right (by omega), add_zero,
        show k + 1 - 1 - k = 0 by omega, show k + 1 - k = 1 by omega, pow_zero, pow_one]
      rfl
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
  rw [sum_congr rfl h, sum_add_distrib, sum_ite_eq]
  rw [ite_eq_left (mem_range.2 (by omega))]

/-- **The Taylor polynomial of the own state through the derivatives:**
`Σ_{n ≤ l+1} H^n/n! P A^n v = taylorLocal (P v) + Σ_{k ≤ l} taylorRow k (C A^k v)`. -/
theorem sum_smul_proj_pow_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) (H : ℝ) (l : ℕ) (v : E) :
    ∑ n ∈ range (l + 2), ((n ! : ℝ)⁻¹ * H ^ n) • P ((A ^ n) v) =
      taylorLocal Ai H l (P v) + ∑ k ∈ range (l + 1), taylorRow Ai L H l k (C ((A ^ k) v)) := by
  rw [sum_congr rfl fun n _ => by rw [proj_pow_apply_eq_sum hA n v]]
  simp only [smul_add]
  rw [sum_add_distrib]
  congr 1
  · unfold taylorLocal
    rw [_root_.sum_apply]
    rfl
  · have hr : ∀ n ∈ range (l + 2),
        ((n ! : ℝ)⁻¹ * H ^ n) • ∑ k ∈ range n, (Ai ^ (n - 1 - k)) (L (C ((A ^ k) v))) =
          ∑ k ∈ range (l + 1), if k < n then
            ((n ! : ℝ)⁻¹ * H ^ n) • (Ai ^ (n - 1 - k)) (L (C ((A ^ k) v))) else 0 := by
      intro n hn
      have hn' := mem_range.1 hn
      rw [← sum_filter, smul_sum]
      refine sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [mem_filter, mem_range]
      omega
    rw [sum_congr rfl hr, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    unfold taylorRow
    rw [_root_.sum_apply]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> rfl

end Taylor

section Samples

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The samples through the derivatives:** for coefficients `g r` of the samples of the ages
`r ∈ S`, `Σ_r g r C U^{-r} v = Σ_{n<b} H^n/n! (Σ_r (-r)^n g r) C A^n v + Σ_r g r C R_r v` with the
remainders `R_r = expRem b (-r H A)` of the exponential series. -/
theorem sum_coef_sample_apply (A : E →L[ℝ] E) (C : E →L[ℝ] G) (S : Finset ℤ)
    (g : ℤ → G →L[ℝ] F) (H : ℝ) (b : ℕ) (v : E) :
    ∑ r ∈ S, g r (C (exp ((-((r : ℝ) * H)) • A) v)) =
      ∑ n ∈ range b, ((n ! : ℝ)⁻¹ * H ^ n) • (∑ r ∈ S, (-(r : ℝ)) ^ n • g r) (C ((A ^ n) v)) +
        ∑ r ∈ S, g r (C (expRem b ((-(r : ℝ) * H) • A) v)) := by
  have h : ∀ r ∈ S, g r (C (exp ((-((r : ℝ) * H)) • A) v)) =
      ∑ n ∈ range b, ((-(r : ℝ)) ^ n * ((n ! : ℝ)⁻¹ * H ^ n)) • g r (C ((A ^ n) v)) +
        g r (C (expRem b ((-(r : ℝ) * H) • A) v)) := by
    intro r _
    rw [← neg_mul, exp_node_eq A H (-(r : ℝ)) b]
    simp only [_root_.add_apply, _root_.sum_apply, _root_.smul_apply,
      map_add, map_sum, map_smul, taylorTerm, smul_smul]
  rw [sum_congr rfl h, sum_add_distrib, sum_comm]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [_root_.sum_apply, smul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [_root_.smul_apply, smul_smul, mul_comm]

end Samples

section Inverse

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- The stack of the own state and the derivatives of the outputs of the partners,
`N₀ v = (P v, (C A^p v)_{p<l})`. Its kernel is `unseen P C A l` (`shownStack_eq_zero_iff`). -/
noncomputable def shownStack (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) :
    E →L[ℝ] F × (Fin l → G) :=
  P.prod (ContinuousLinearMap.pi fun p : Fin l => C ∘L A ^ (p : ℕ))

/-- The kernel of the stack is the space of the states not shown. -/
theorem shownStack_eq_zero_iff (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) (v : E) :
    shownStack P C A l v = 0 ↔ v ∈ unseen P C A l := by
  rw [mem_unseen]
  simp only [shownStack, ContinuousLinearMap.prod_apply, Prod.mk_eq_zero, funext_iff,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, Pi.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => h2 ⟨q, hq⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q => h2 q q.2⟩

/-- **The shown part of the state from the own state and the derivatives** (no independence is
assumed): there are bounded maps `ΛF`, `Λ p` with `ΛF (P v) + Σ_{p<l} Λ p (C A^p v) = v - Q₀ v`,
`Q₀` the orthogonal projection onto the states not shown. -/
theorem exists_shown_inverse (P : E →L[ℝ] F) (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) :
    ∃ (ΛF : F →L[ℝ] E) (Λ : ℕ → G →L[ℝ] E), ∀ v : E,
      ΛF (P v) + ∑ p ∈ range l, Λ p (C ((A ^ p) v)) =
        v - (unseen P C A l).starProjection v := by
  obtain ⟨R, hR⟩ := exists_generalizedInverse (shownStack P C A l)
  set Q₀ := (unseen P C A l).starProjection with hQ₀
  let Λ' : F × (Fin l → G) →L[ℝ] E := (ContinuousLinearMap.id ℝ E - Q₀) ∘L R
  refine ⟨Λ' ∘L ContinuousLinearMap.inl ℝ F (Fin l → G), fun p =>
    if h : p < l then Λ' ∘L (ContinuousLinearMap.inr ℝ F (Fin l → G) ∘L
      ContinuousLinearMap.single ℝ (fun _ : Fin l => G) ⟨p, h⟩) else 0, fun v => ?_⟩
  have hsum : ∑ p ∈ range l, (if h : p < l then Λ' ∘L (ContinuousLinearMap.inr ℝ F (Fin l → G) ∘L
      ContinuousLinearMap.single ℝ (fun _ : Fin l => G) ⟨p, h⟩) else 0) (C ((A ^ p) v)) =
      ∑ q : Fin l, Λ' (0, Pi.single q (C ((A ^ (q : ℕ)) v))) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun q _ => ?_
    simp [q.2]
  have hstack : shownStack P C A l v =
      (P v, 0) + ∑ q : Fin l, ((0 : F), Pi.single q (C ((A ^ (q : ℕ)) v))) := by
    simp only [shownStack, ContinuousLinearMap.prod_apply]
    ext
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_add, Prod.snd_sum]
      rw [zero_add, Finset.univ_sum_single]
      rfl
  have hker : v - R (shownStack P C A l v) ∈ unseen P C A l := by
    rw [← shownStack_eq_zero_iff, map_sub, hR, sub_self]
  have hQ := (Submodule.starProjection_eq_self_iff).2 hker
  rw [← hQ₀, map_sub] at hQ
  rw [hsum]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  rw [← map_sum, ← map_add, ← hstack]
  simp only [Λ', ContinuousLinearMap.comp_apply, _root_.sub_apply,
    ContinuousLinearMap.id_apply]
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at hQ
  rw [← hQ]
  abel

end Inverse

section RuleDef

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The coefficient of the `p`-th divided difference in the rule: the Taylor coefficient and the
correction, `X_p = taylorMoment p + γ p! H^{l+1-p} M Λ_p`. -/
noncomputable def reachMoment (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (M : E →L[ℝ] F)
    (Λ : ℕ → G →L[ℝ] E) (γ H : ℝ) (l p : ℕ) : G →L[ℝ] F :=
  taylorMoment Ai L H l p + (γ * (p ! : ℝ) * H ^ (l + 1 - p)) • (M ∘L Λ p)

/-- The coefficients of the samples of the rule: `g r = Σ_{p<l} δ p r X_p`. -/
noncomputable def reachRule (δ : ℕ → ℤ → ℝ) (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (M : E →L[ℝ] F)
    (Λ : ℕ → G →L[ℝ] E) (γ H : ℝ) (l : ℕ) (r : ℤ) : G →L[ℝ] F :=
  ∑ p ∈ range l, δ p r • reachMoment Ai L M Λ γ H l p

/-- The coefficient of the own state of the rule: `Fi = taylorLocal + γ H^{l+1} M Λ_F`. -/
noncomputable def reachFi (Ai : F →L[ℝ] F) (M : E →L[ℝ] F) (ΛF : F →L[ℝ] E) (γ H : ℝ) (l : ℕ) :
    F →L[ℝ] F :=
  taylorLocal Ai H l + (γ * H ^ (l + 1)) • (M ∘L ΛF)

end RuleDef

section Rule

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- **The defect of the rule.** For weights `δ` of the divided differences and maps `ΛF`, `Λ`
with `ΛF (P v) + Σ_{p<l} Λ p (C A^p v) = v - Q₀ v`, the rule `(reachFi, reachRule)` with
`γ = nodeGamma S`, `M = L C A^l` has the defect
`𝒯 v = γ H^{l+1} M Q₀ v + ρ_A + ρ_B - ρ_C`, with
`ρ_A = P R_{l+2}(H A) v` (the remainder of `P U`),
`ρ_B = Σ_{p<l} nodeCoeff S p (H^l/l!) (X_p - (p!/(p+1)!) H L) C A^l v` and
`ρ_C = Σ_{r ∈ S} g r C R_{l+1}(-r H A) v` (the remainders of the samples). -/
theorem reach_defect_apply (hA : P ∘L A = Ai ∘L P + L ∘L C) {S : Finset ℤ} {l : ℕ}
    (hS : S.card = l) {δ : ℕ → ℤ → ℝ}
    (hδ : ∀ p < S.card, ∀ n < S.card,
      ∑ r ∈ S, δ p r * (-(r : ℝ)) ^ n = if p = n then 1 else 0)
    {ΛF : F →L[ℝ] E} {Λ : ℕ → G →L[ℝ] E}
    (hΛ : ∀ v : E, ΛF (P v) + ∑ p ∈ range l, Λ p (C ((A ^ p) v)) =
      v - (unseen P C A l).starProjection v)
    (H : ℝ) (v : E) :
    nodeDefect P (reachFi Ai ((L ∘L C) ∘L A ^ l) ΛF (nodeGamma S) H l)
        (reachRule δ Ai L ((L ∘L C) ∘L A ^ l) Λ (nodeGamma S) H l) C A H S v =
      (nodeGamma S * H ^ (l + 1)) • L (C ((A ^ l) ((unseen P C A l).starProjection v))) +
        P (expRem (l + 2) (H • A) v) +
        ∑ p ∈ range l, (nodeCoeff S p * ((l ! : ℝ)⁻¹ * H ^ l)) •
          (reachMoment Ai L ((L ∘L C) ∘L A ^ l) Λ (nodeGamma S) H l p -
            ((p ! : ℝ) / ((p + 1)! : ℝ) * H) • L) (C ((A ^ l) v)) -
        ∑ r ∈ S, reachRule δ Ai L ((L ∘L C) ∘L A ^ l) Λ (nodeGamma S) H l r
          (C (expRem (l + 1) ((-(r : ℝ) * H) • A) v)) := by
  subst hS
  set γ := nodeGamma S with hγ
  set M : E →L[ℝ] F := (L ∘L C) ∘L A ^ S.card with hM
  set X := reachMoment Ai L M Λ γ H S.card with hXdef
  set g := reachRule δ Ai L M Λ γ H S.card with hg
  -- the step of the monolithic system
  have h1 : P (exp (H • A) v) =
      ∑ n ∈ range (S.card + 2), ((n ! : ℝ)⁻¹ * H ^ n) • P ((A ^ n) v) +
        P (expRem (S.card + 2) (H • A) v) := by
    have h := exp_node_eq A H 1 (S.card + 2)
    simp only [one_mul, one_pow, one_smul] at h
    rw [h]
    simp only [_root_.add_apply, _root_.sum_apply, map_add, map_sum, taylorTerm,
      _root_.smul_apply, map_smul]
  -- its Taylor polynomial through the derivatives
  have h2 : ∑ n ∈ range (S.card + 2), ((n ! : ℝ)⁻¹ * H ^ n) • P ((A ^ n) v) =
      taylorLocal Ai H S.card (P v) +
        ∑ k ∈ range S.card, taylorRow Ai L H S.card k (C ((A ^ k) v)) +
        (((S.card + 1)! : ℝ)⁻¹ * H ^ (S.card + 1)) • L (C ((A ^ S.card) v)) := by
    rw [sum_smul_proj_pow_apply hA H S.card v, sum_range_succ, taylorRow_self, _root_.smul_apply]
    abel
  -- the coefficient of the own state
  have h3 : reachFi Ai M ΛF γ H S.card (P v) =
      taylorLocal Ai H S.card (P v) +
        (γ * H ^ (S.card + 1)) • L (C ((A ^ S.card) (ΛF (P v)))) := by
    simp only [reachFi, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply, hM]
  -- the samples
  have hmom : ∀ n ∈ range S.card, ∑ r ∈ S, (-(r : ℝ)) ^ n • g r = X n := fun n hn =>
    sum_neg_pow_smul_weights hδ X (mem_range.1 hn)
  have htop : ∑ r ∈ S, (-(r : ℝ)) ^ S.card • g r = -∑ p ∈ range S.card, nodeCoeff S p • X p :=
    sum_neg_pow_card_smul_weights hδ X
  have hX : ∀ n ∈ range S.card, ((n ! : ℝ)⁻¹ * H ^ n) • X n =
      taylorRow Ai L H S.card n + (γ * H ^ (S.card + 1)) • (M ∘L Λ n) := by
    intro n hn
    have hn' := mem_range.1 hn
    rw [hXdef, reachMoment, smul_add, smul_taylorMoment, smul_smul]
    congr 2
    have hf : (n ! : ℝ) ≠ 0 := by positivity
    have e : H ^ n * H ^ (S.card + 1 - n) = H ^ (S.card + 1) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    field_simp
    rw [← e]
    ring
  have h4 : ∑ r ∈ S, g r (C (exp ((-((r : ℝ) * H)) • A) v)) =
      ∑ k ∈ range S.card, taylorRow Ai L H S.card k (C ((A ^ k) v)) +
        (γ * H ^ (S.card + 1)) •
          L (C ((A ^ S.card) (∑ n ∈ range S.card, Λ n (C ((A ^ n) v))))) -
        ∑ p ∈ range S.card, (nodeCoeff S p * ((S.card ! : ℝ)⁻¹ * H ^ S.card)) •
          X p (C ((A ^ S.card) v)) +
        ∑ r ∈ S, g r (C (expRem (S.card + 1) ((-(r : ℝ) * H) • A) v)) := by
    rw [sum_coef_sample_apply A C S g H (S.card + 1) v, sum_range_succ, htop]
    have e1 : ∑ n ∈ range S.card,
        ((n ! : ℝ)⁻¹ * H ^ n) • (∑ r ∈ S, (-(r : ℝ)) ^ n • g r) (C ((A ^ n) v)) =
        ∑ k ∈ range S.card, taylorRow Ai L H S.card k (C ((A ^ k) v)) +
          (γ * H ^ (S.card + 1)) •
            L (C ((A ^ S.card) (∑ n ∈ range S.card, Λ n (C ((A ^ n) v))))) := by
      rw [map_sum, map_sum, map_sum, smul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun n hn => ?_
      rw [hmom n hn, ← _root_.smul_apply, hX n hn]
      simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply, hM]
    have e2 : ((S.card ! : ℝ)⁻¹ * H ^ S.card) •
        (-∑ p ∈ range S.card, nodeCoeff S p • X p) (C ((A ^ S.card) v)) =
        -∑ p ∈ range S.card, (nodeCoeff S p * ((S.card ! : ℝ)⁻¹ * H ^ S.card)) •
          X p (C ((A ^ S.card) v)) := by
      simp only [_root_.neg_apply, _root_.sum_apply, _root_.smul_apply, smul_neg, smul_sum,
        smul_smul, mul_comm]
    rw [e1, e2]
    abel
  -- the shown part
  have h5 : L (C ((A ^ S.card) (ΛF (P v)))) +
      L (C ((A ^ S.card) (∑ n ∈ range S.card, Λ n (C ((A ^ n) v))))) =
      L (C ((A ^ S.card) v)) -
        L (C ((A ^ S.card) ((unseen P C A S.card).starProjection v))) := by
    rw [← map_add, ← map_add, ← map_add, hΛ v, map_sub, map_sub, map_sub]
  -- the leading constant
  have h6 : ∑ p ∈ range S.card, (nodeCoeff S p * ((S.card ! : ℝ)⁻¹ * H ^ S.card)) •
        X p (C ((A ^ S.card) v)) =
      (∑ p ∈ range S.card, nodeCoeff S p * ((S.card ! : ℝ)⁻¹ * H ^ S.card) *
          ((p ! : ℝ) / ((p + 1)! : ℝ) * H)) • L (C ((A ^ S.card) v)) +
        ∑ p ∈ range S.card, (nodeCoeff S p * ((S.card ! : ℝ)⁻¹ * H ^ S.card)) •
          (X p - ((p ! : ℝ) / ((p + 1)! : ℝ) * H) • L) (C ((A ^ S.card) v)) := by
    rw [sum_smul, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [_root_.sub_apply, _root_.smul_apply, smul_sub, smul_smul]
    abel
  have h7 : ((S.card + 1)! : ℝ)⁻¹ * H ^ (S.card + 1) +
      ∑ p ∈ range S.card, nodeCoeff S p * ((S.card ! : ℝ)⁻¹ * H ^ S.card) *
        ((p ! : ℝ) / ((p + 1)! : ℝ) * H) = γ * H ^ (S.card + 1) := by
    rw [hγ, nodeGamma_mul S (H ^ (S.card + 1))]
    congr 1
    · ring
    · refine sum_congr rfl fun p _ => ?_
      ring
  simp only [nodeDefect, _root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.sum_apply]
  linear_combination (norm := module) h1 + h2 - h3 - h4 - (γ * H ^ (S.card + 1)) • h5 + h6 +
    h7 • L (C ((A ^ S.card) v))

end Rule

section Bounds

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `‖T^j‖ ≤ (1 + ‖T‖)^j`. -/
theorem norm_pow_le_one_add_pow (T : F →L[ℝ] F) (j : ℕ) : ‖T ^ j‖ ≤ (1 + ‖T‖) ^ j := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ j ih =>
    rw [pow_succ, pow_succ]
    calc ‖T ^ j * T‖ ≤ ‖T ^ j‖ * ‖T‖ := norm_mul_le _ _
      _ ≤ (1 + ‖T‖) ^ j * (1 + ‖T‖) :=
        mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity)

/-- `‖T^j‖ ≤ (1 + ‖T‖)^m` for `j ≤ m`. -/
theorem norm_pow_le_one_add_pow_of_le (T : F →L[ℝ] F) {j m : ℕ} (hjm : j ≤ m) :
    ‖T ^ j‖ ≤ (1 + ‖T‖) ^ m :=
  (norm_pow_le_one_add_pow T j).trans
    (pow_le_pow_right₀ (by linarith [norm_nonneg T]) hjm)

/-- A term of `taylorMoment` is of the order `H^j` if `p + j ≤ n`, for `0 ≤ H ≤ 1`. -/
theorem norm_taylorMoment_term_le (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) {H : ℝ} (hH0 : 0 ≤ H)
    (hH1 : H ≤ 1) {l p n j : ℕ} (hj : p + j ≤ n) (hn : n < l + 2) :
    ‖((p ! : ℝ) / (n ! : ℝ) * H ^ (n - p)) • ((Ai ^ (n - 1 - p)) ∘L L)‖ ≤
      H ^ j * ((1 + ‖Ai‖) ^ (l + 1) * ‖L‖) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : (p ! : ℝ) / (n ! : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le (by omega)
  have h2 : H ^ (n - p) ≤ H ^ j := pow_le_pow_of_le_one hH0 hH1 (by omega)
  have h3 : ‖(Ai ^ (n - 1 - p)) ∘L L‖ ≤ (1 + ‖Ai‖) ^ (l + 1) * ‖L‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_pow_le_one_add_pow_of_le Ai (by omega)) (norm_nonneg _))
  have h4 := mul_le_mul (mul_le_mul h1 h2 (by positivity) zero_le_one) h3 (norm_nonneg _)
    (by positivity)
  linarith

/-- The constant `(l + 2) (1 + ‖Ai‖)^{l+1} ‖L‖` of the Taylor coefficients. -/
noncomputable def taylorConst (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (l : ℕ) : ℝ :=
  (l + 2) * ((1 + ‖Ai‖) ^ (l + 1) * ‖L‖)

theorem taylorConst_nonneg (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (l : ℕ) :
    0 ≤ taylorConst Ai L l := by
  unfold taylorConst
  have := norm_nonneg Ai
  positivity

/-- `‖taylorMoment p‖ ≤ H · taylorConst` for `0 ≤ H ≤ 1`. -/
theorem norm_taylorMoment_le (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) {H : ℝ} (hH0 : 0 ≤ H)
    (hH1 : H ≤ 1) (l p : ℕ) : ‖taylorMoment Ai L H l p‖ ≤ H * taylorConst Ai L l := by
  unfold taylorMoment taylorConst
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ n ∈ range (l + 2), ‖if p < n then ((p ! : ℝ) / (n ! : ℝ) * H ^ (n - p)) •
      ((Ai ^ (n - 1 - p)) ∘L L) else 0‖ ≤ H ^ 1 * ((1 + ‖Ai‖) ^ (l + 1) * ‖L‖) := by
    intro n hn
    split_ifs with hpn
    · exact norm_taylorMoment_term_le Ai L hH0 hH1 (by omega) (mem_range.1 hn)
    · rw [norm_zero]
      have := norm_nonneg Ai
      positivity
  refine (sum_le_sum h).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul, pow_one]
  push_cast
  ring

/-- `‖taylorMomentTail p‖ ≤ H^2 · taylorConst` for `0 ≤ H ≤ 1`. -/
theorem norm_taylorMomentTail_le (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) {H : ℝ} (hH0 : 0 ≤ H)
    (hH1 : H ≤ 1) (l p : ℕ) : ‖taylorMomentTail Ai L H l p‖ ≤ H ^ 2 * taylorConst Ai L l := by
  unfold taylorMomentTail taylorConst
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ n ∈ range (l + 2), ‖if p + 1 < n then ((p ! : ℝ) / (n ! : ℝ) * H ^ (n - p)) •
      ((Ai ^ (n - 1 - p)) ∘L L) else 0‖ ≤ H ^ 2 * ((1 + ‖Ai‖) ^ (l + 1) * ‖L‖) := by
    intro n hn
    split_ifs with hpn
    · exact norm_taylorMoment_term_le Ai L hH0 hH1 (by omega) (mem_range.1 hn)
    · rw [norm_zero]
      have := norm_nonneg Ai
      positivity
  refine (sum_le_sum h).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `‖taylorLocal - 1‖ ≤ H (l + 1) (1 + ‖Ai‖)^{l+1}` for `0 ≤ H ≤ 1`. -/
theorem norm_taylorLocal_sub_one_le (Ai : F →L[ℝ] F) {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1)
    (l : ℕ) : ‖taylorLocal Ai H l - 1‖ ≤ H * ((l + 1) * (1 + ‖Ai‖) ^ (l + 1)) := by
  unfold taylorLocal
  rw [sum_range_succ', Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one, one_smul,
    pow_zero, add_sub_cancel_right]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ n ∈ range (l + 1), ‖((((n + 1)! : ℕ) : ℝ)⁻¹ * H ^ (n + 1)) • Ai ^ (n + 1)‖ ≤
      H * (1 + ‖Ai‖) ^ (l + 1) := by
    intro n hn
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 : ((((n + 1)! : ℕ) : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
    have h2 : H ^ (n + 1) ≤ H := by
      simpa using pow_le_pow_of_le_one hH0 hH1 (by omega : 1 ≤ n + 1)
    have h3 := norm_pow_le_one_add_pow_of_le Ai (by have := mem_range.1 hn; omega :
      n + 1 ≤ l + 1)
    have h4 := mul_le_mul (mul_le_mul h1 h2 (by positivity) zero_le_one) h3 (norm_nonneg _)
      (by positivity)
    linarith
  refine (sum_le_sum h).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The constant of the coefficient `X_p`: `taylorConst + |γ| p! ‖M Λ_p‖`. -/
noncomputable def reachConst (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (M : E →L[ℝ] F)
    (Λ : ℕ → G →L[ℝ] E) (γ : ℝ) (l p : ℕ) : ℝ :=
  taylorConst Ai L l + |γ| * (p ! : ℝ) * ‖M ∘L Λ p‖

theorem reachConst_nonneg (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (M : E →L[ℝ] F)
    (Λ : ℕ → G →L[ℝ] E) (γ : ℝ) (l p : ℕ) : 0 ≤ reachConst Ai L M Λ γ l p := by
  have := taylorConst_nonneg Ai L l
  unfold reachConst
  positivity

/-- `‖X_p‖ ≤ H · reachConst p` for `p < l`, `0 ≤ H ≤ 1`. -/
theorem norm_reachMoment_le (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (M : E →L[ℝ] F)
    (Λ : ℕ → G →L[ℝ] E) (γ : ℝ) {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1) {l p : ℕ} (hp : p < l) :
    ‖reachMoment Ai L M Λ γ H l p‖ ≤ H * reachConst Ai L M Λ γ l p := by
  unfold reachMoment reachConst
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_taylorMoment_le Ai L hH0 hH1 l p
  have h2 : H ^ (l + 1 - p) ≤ H := by
    simpa using pow_le_pow_of_le_one hH0 hH1 (by omega : 1 ≤ l + 1 - p)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast,
    abs_of_nonneg (pow_nonneg hH0 _)]
  have h3 : |γ| * (p ! : ℝ) * H ^ (l + 1 - p) * ‖M ∘L Λ p‖ ≤
      |γ| * (p ! : ℝ) * H * ‖M ∘L Λ p‖ := by gcongr
  nlinarith

/-- `‖X_p - (p!/(p+1)!) H L‖ ≤ H^2 · reachConst p` for `p < l`, `0 ≤ H ≤ 1`. -/
theorem norm_reachMoment_sub_le (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (M : E →L[ℝ] F)
    (Λ : ℕ → G →L[ℝ] E) (γ : ℝ) {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1) {l p : ℕ} (hp : p < l) :
    ‖reachMoment Ai L M Λ γ H l p - ((p ! : ℝ) / ((p + 1)! : ℝ) * H) • L‖ ≤
      H ^ 2 * reachConst Ai L M Λ γ l p := by
  have e : reachMoment Ai L M Λ γ H l p - ((p ! : ℝ) / ((p + 1)! : ℝ) * H) • L =
      taylorMomentTail Ai L H l p + (γ * (p ! : ℝ) * H ^ (l + 1 - p)) • (M ∘L Λ p) := by
    rw [reachMoment, taylorMoment_eq Ai L H hp.le]
    abel
  rw [e]
  unfold reachConst
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_taylorMomentTail_le Ai L hH0 hH1 l p
  have h2 : H ^ (l + 1 - p) ≤ H ^ 2 := pow_le_pow_of_le_one hH0 hH1 (by omega)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast,
    abs_of_nonneg (pow_nonneg hH0 _)]
  have h3 : |γ| * (p ! : ℝ) * H ^ (l + 1 - p) * ‖M ∘L Λ p‖ ≤
      |γ| * (p ! : ℝ) * H ^ 2 * ‖M ∘L Λ p‖ := by gcongr
  nlinarith

/-- `‖g r‖ ≤ H Σ_{p<l} |δ p r| reachConst p` for `0 ≤ H ≤ 1`. -/
theorem norm_reachRule_le (δ : ℕ → ℤ → ℝ) (Ai : F →L[ℝ] F) (L : G →L[ℝ] F) (M : E →L[ℝ] F)
    (Λ : ℕ → G →L[ℝ] E) (γ : ℝ) {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (l : ℕ) (r : ℤ) :
    ‖reachRule δ Ai L M Λ γ H l r‖ ≤
      H * ∑ p ∈ range l, |δ p r| * reachConst Ai L M Λ γ l p := by
  unfold reachRule
  rw [mul_sum]
  refine norm_sum_le_of_le _ fun p hp => ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h := norm_reachMoment_le Ai L M Λ γ hH0 hH1 (mem_range.1 hp)
  calc |δ p r| * ‖reachMoment Ai L M Λ γ H l p‖
      ≤ |δ p r| * (H * reachConst Ai L M Λ γ l p) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = H * (|δ p r| * reachConst Ai L M Λ γ l p) := by ring

variable [CompleteSpace E]

/-- The remainder of the step of the monolithic system:
`‖P R_b(H A) v‖ ≤ ‖P‖ ε_b ‖A‖^b H^b ‖v‖` for `H ‖A‖ ≤ 1`. -/
theorem norm_proj_expRem_apply_le (P : E →L[ℝ] F) (A : E →L[ℝ] E) {H : ℝ} (hH0 : 0 ≤ H)
    (hx1 : H * ‖A‖ ≤ 1) {b : ℕ} (hb : 0 < b) (v : E) :
    ‖P (expRem b (H • A) v)‖ ≤ ‖P‖ * expTail b 1 * ‖A‖ ^ b * H ^ b * ‖v‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH0 (norm_nonneg A)
  have h1 : ‖expRem b (H • A)‖ ≤ expTail b 1 * (H * ‖A‖) ^ b := by
    have h := norm_expRem_le (H • A) hb
    rw [norm_smul, Real.norm_of_nonneg hH0] at h
    exact h.trans (expTail_le_mul_pow b hx0 hx1)
  calc ‖P (expRem b (H • A) v)‖ ≤ ‖P‖ * (‖expRem b (H • A)‖ * ‖v‖) :=
        (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((expRem b (H • A)).le_opNorm v)
          (norm_nonneg P))
    _ ≤ ‖P‖ * (expTail b 1 * (H * ‖A‖) ^ b * ‖v‖) := by gcongr
    _ = ‖P‖ * expTail b 1 * ‖A‖ ^ b * H ^ b * ‖v‖ := by ring

/-- The remainders of the samples: if `‖g r‖ ≤ H γ_r`, then
`‖Σ_{r ∈ S} g r C R_b(-r H A) v‖ ≤ H^{b+1} Σ_r γ_r ‖C‖ ‖A‖^b ε_b(|r|) ‖v‖` for `H ‖A‖ ≤ 1`. -/
theorem norm_sum_coef_expRem_le (C : E →L[ℝ] G) (A : E →L[ℝ] E) (S : Finset ℤ)
    (g : ℤ → G →L[ℝ] F) (gc : ℤ → ℝ) {H : ℝ} (hH0 : 0 ≤ H) (hx1 : H * ‖A‖ ≤ 1)
    (hg : ∀ r ∈ S, ‖g r‖ ≤ H * gc r) {b : ℕ} (hb : 0 < b) (v : E) :
    ‖∑ r ∈ S, g r (C (expRem b ((-(r : ℝ) * H) • A) v))‖ ≤
      H ^ (b + 1) * (∑ r ∈ S, gc r * ‖C‖ * (‖A‖ ^ b * expTail b |(r : ℝ)|)) * ‖v‖ := by
  have hx0 : 0 ≤ H * ‖A‖ := mul_nonneg hH0 (norm_nonneg A)
  rw [mul_sum, sum_mul]
  refine norm_sum_le_of_le _ fun r hr => ?_
  have h1 : ‖expRem b ((-(r : ℝ) * H) • A)‖ ≤ (H * ‖A‖) ^ b * expTail b |(r : ℝ)| := by
    have h := norm_expRem_le ((-(r : ℝ) * H) • A) hb
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hH0, mul_assoc] at h
    exact h.trans (expTail_mul_le b (abs_nonneg _) hx0 hx1)
  have h2 := hg r hr
  have hgc : 0 ≤ H * gc r := (norm_nonneg _).trans h2
  calc ‖g r (C (expRem b ((-(r : ℝ) * H) • A) v))‖
      ≤ ‖g r‖ * (‖C‖ * (‖expRem b ((-(r : ℝ) * H) • A)‖ * ‖v‖)) :=
        ((g r).le_opNorm _).trans (mul_le_mul_of_nonneg_left ((C.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((expRem b _).le_opNorm v) (norm_nonneg C)))
          (norm_nonneg _))
    _ ≤ (H * gc r) * (‖C‖ * ((H * ‖A‖) ^ b * expTail b |(r : ℝ)| * ‖v‖)) := by gcongr
    _ = H ^ (b + 1) * (gc r * ‖C‖ * (‖A‖ ^ b * expTail b |(r : ℝ)|)) * ‖v‖ := by ring

/-- The remainder of the top moment: if `‖Y_p‖ ≤ H^2 κ_p` for `p < l`, then
`‖Σ_{p<l} (a_p H^l/l!) Y_p C A^l v‖ ≤ H^{l+2} Σ_p |a_p| κ_p ‖C‖ ‖A‖^l ‖v‖` for `H ≥ 0`. -/
theorem norm_sum_top_le (C : E →L[ℝ] G) (A : E →L[ℝ] E) (l : ℕ) (a : ℕ → ℝ)
    (Y : ℕ → G →L[ℝ] F) (κ : ℕ → ℝ) {H : ℝ} (hH0 : 0 ≤ H)
    (hY : ∀ p ∈ range l, ‖Y p‖ ≤ H ^ 2 * κ p) (v : E) :
    ‖∑ p ∈ range l, (a p * ((l ! : ℝ)⁻¹ * H ^ l)) • Y p (C ((A ^ l) v))‖ ≤
      H ^ (l + 2) * (∑ p ∈ range l, |a p| * (κ p * (‖C‖ * ‖A‖ ^ l))) * ‖v‖ := by
  rw [mul_sum, sum_mul]
  refine norm_sum_le_of_le _ fun p hp => ?_
  have h1 := hY p hp
  have hκ : 0 ≤ H ^ 2 * κ p := (norm_nonneg _).trans h1
  have hf : (l ! : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  have hy : ‖C ((A ^ l) v)‖ ≤ ‖C‖ * (‖A‖ ^ l * ‖v‖) :=
    (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_pow_apply_le A l v) (norm_nonneg C))
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l ! : ℝ)⁻¹),
    abs_of_nonneg (pow_nonneg hH0 _)]
  calc |a p| * ((l ! : ℝ)⁻¹ * H ^ l) * ‖Y p (C ((A ^ l) v))‖
      ≤ |a p| * (1 * H ^ l) * (‖Y p‖ * ‖C ((A ^ l) v)‖) := by
        gcongr
        exact (Y p).le_opNorm _
    _ ≤ |a p| * (1 * H ^ l) * ((H ^ 2 * κ p) * (‖C‖ * (‖A‖ ^ l * ‖v‖))) := by gcongr
    _ = H ^ (l + 2) * (|a p| * (κ p * (‖C‖ * ‖A‖ ^ l))) * ‖v‖ := by ring

end Bounds

section Main

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- On the states not shown up to the order `l`, `L C A^l` is the response `P A^{l+1}` (the
paper's `a_i A^l = Π_i A^{l+1}` on `𝒱_i^0`). -/
theorem coupling_pow_apply_of_mem (hA : P ∘L A = Ai ∘L P + L ∘L C) {l : ℕ} {u : E}
    (hu : u ∈ unseen P C A l) : L (C ((A ^ l) u)) = P ((A ^ (l + 1)) u) := by
  have h1 : (A ^ (l + 1)) u = A ((A ^ l) u) := by
    rw [pow_succ']
    rfl
  have h2 : P (A ((A ^ l) u)) = Ai (P ((A ^ l) u)) + L (C ((A ^ l) u)) := by
    have h' := congrArg (fun T : E →L[ℝ] F => T ((A ^ l) u)) hA
    simpa using h'
  rw [h1, h2, proj_pow_eq_zero hA le_rfl hu, map_zero, zero_add]

/-- The leading term of the defect is at most `c_i ‖v‖`:
`‖L C A^l Q₀ v‖ ≤ ‖P A^{l+1}|𝒱^0‖ ‖v‖`. -/
theorem norm_lead_apply_le (hA : P ∘L A = Ai ∘L P + L ∘L C) (l : ℕ) (v : E) :
    ‖L (C ((A ^ l) ((unseen P C A l).starProjection v)))‖ ≤
      ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * ‖v‖ := by
  set V := unseen P C A l with hV
  have hu : V.starProjection v ∈ V := Submodule.starProjection_apply_mem V v
  rw [coupling_pow_apply_of_mem hA hu]
  have h1 := ((P ∘L (A ^ (l + 1))) ∘L V.subtypeL).le_opNorm ⟨_, hu⟩
  have h2 : ‖V.starProjection v‖ ≤ ‖v‖ := by
    have h3 := V.starProjection.le_opNorm v
    have h4 := V.starProjection_norm_le
    have h5 : ‖V.starProjection‖ * ‖v‖ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right h4 (norm_nonneg v)
    linarith
  calc ‖P ((A ^ (l + 1)) (V.starProjection v))‖
      = ‖((P ∘L (A ^ (l + 1))) ∘L V.subtypeL) ⟨_, hu⟩‖ := rfl
    _ ≤ ‖(P ∘L (A ^ (l + 1))) ∘L V.subtypeL‖ * ‖V.starProjection v‖ := h1
    _ ≤ ‖(P ∘L (A ^ (l + 1))) ∘L V.subtypeL‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The bound (ii) of Theorem `thm:memory` is reached, for every set of `l` sample ages and
without independence of the maps.** There are constants `w, K ≥ 0` such that for every
`0 ≤ H ≤ 1` with `H ‖A‖ ≤ 1` some rule `(Fi, g)` has bounded weights, `‖Fi - 1‖ ≤ w H` and
`‖g r ∘ C‖ ≤ w H` for every age `r ∈ S`, and the local defect
`‖𝒯‖ ≤ |γ_S| c_i H^{l+1} + K H^{l+2}`, `γ_S = nodeGamma S`,
`c_i = ‖P A^{l+1}|𝒱^0‖`, `𝒱^0 = unseen P C A l`, `l = #S`. -/
theorem exists_rule_nodeDefect_le (hA : P ∘L A = Ai ∘L P + L ∘L C) (S : Finset ℤ) :
    ∃ w K : ℝ, 0 ≤ w ∧ 0 ≤ K ∧ ∀ H : ℝ, 0 ≤ H → H ≤ 1 → H * ‖A‖ ≤ 1 →
      ∃ (Fi : F →L[ℝ] F) (g : ℤ → G →L[ℝ] F), ‖Fi - 1‖ ≤ w * H ∧
        (∀ r ∈ S, ‖g r ∘L C‖ ≤ w * H) ∧
        ‖nodeDefect P Fi g C A H S‖ ≤
          |nodeGamma S| * ‖(P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL‖ *
            H ^ (S.card + 1) + K * H ^ (S.card + 2) := by
  obtain ⟨δ, hδ⟩ := exists_nodeWeights S
  obtain ⟨ΛF, Λ, hΛ⟩ := exists_shown_inverse P C A S.card
  set γ := nodeGamma S with hγ
  set M : E →L[ℝ] F := (L ∘L C) ∘L A ^ S.card with hM
  set c := ‖(P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL‖ with hc
  set κ : ℕ → ℝ := reachConst Ai L M Λ γ S.card with hκ
  set gc : ℤ → ℝ := fun r => ∑ p ∈ range S.card, |δ p r| * κ p with hgc
  have hκ0 : ∀ p, 0 ≤ κ p := fun p => reachConst_nonneg Ai L M Λ γ S.card p
  have hgc0 : ∀ r, 0 ≤ gc r := fun r =>
    sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (hκ0 p)
  have hgcS : 0 ≤ ∑ r ∈ S, gc r := sum_nonneg fun r _ => hgc0 r
  have hAi := norm_nonneg Ai
  set w := ((S.card : ℝ) + 1) * (1 + ‖Ai‖) ^ (S.card + 1) + |γ| * ‖M ∘L ΛF‖ +
    (∑ r ∈ S, gc r) * ‖C‖ with hw
  set KB := ∑ p ∈ range S.card, |nodeCoeff S p| * (κ p * (‖C‖ * ‖A‖ ^ S.card)) with hKB
  set KC := ∑ r ∈ S, gc r * ‖C‖ * (‖A‖ ^ (S.card + 1) * expTail (S.card + 1) |(r : ℝ)|)
    with hKC
  have hKB0 : 0 ≤ KB := sum_nonneg fun p _ => by
    have := hκ0 p
    positivity
  have hKC0 : 0 ≤ KC := sum_nonneg fun r _ => by
    have := hgc0 r
    have := expTail_nonneg (S.card + 1) (abs_nonneg (r : ℝ))
    positivity
  have hε := expTail_nonneg (S.card + 2) (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨w, ‖P‖ * expTail (S.card + 2) 1 * ‖A‖ ^ (S.card + 2) + KB + KC, ?_, ?_, ?_⟩
  · rw [hw]
    positivity
  · positivity
  intro H hH0 hH1 hx1
  refine ⟨reachFi Ai M ΛF γ H S.card, reachRule δ Ai L M Λ γ H S.card, ?_, ?_, ?_⟩
  · -- the coefficient of the own state
    have e : reachFi Ai M ΛF γ H S.card - 1 =
        (taylorLocal Ai H S.card - 1) + (γ * H ^ (S.card + 1)) • (M ∘L ΛF) := by
      rw [reachFi]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_taylorLocal_sub_one_le Ai hH0 hH1 S.card
    have h2 : H ^ (S.card + 1) ≤ H := by
      simpa using pow_le_pow_of_le_one hH0 hH1 (by omega : 1 ≤ S.card + 1)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hH0 _)]
    have h3 : |γ| * H ^ (S.card + 1) * ‖M ∘L ΛF‖ ≤ |γ| * H * ‖M ∘L ΛF‖ := by gcongr
    have h4 : 0 ≤ H * ((∑ r ∈ S, gc r) * ‖C‖) := by positivity
    rw [hw]
    nlinarith
  · -- the weights
    intro r hr
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := norm_reachRule_le δ Ai L M Λ γ hH0 hH1 S.card r
    have h2 : gc r ≤ ∑ r ∈ S, gc r := single_le_sum (fun r _ => hgc0 r) hr
    have h3 : ‖reachRule δ Ai L M Λ γ H S.card r‖ * ‖C‖ ≤ H * (∑ r ∈ S, gc r) * ‖C‖ := by
      have h4 : H * gc r ≤ H * ∑ r ∈ S, gc r := mul_le_mul_of_nonneg_left h2 hH0
      exact mul_le_mul_of_nonneg_right (h1.trans h4) (norm_nonneg C)
    have h5 : 0 ≤ H * (((S.card : ℝ) + 1) * (1 + ‖Ai‖) ^ (S.card + 1) + |γ| * ‖M ∘L ΛF‖) := by
      positivity
    rw [hw]
    nlinarith
  · -- the defect
    have hK : 0 ≤ (|γ| * c * H ^ (S.card + 1) +
        (‖P‖ * expTail (S.card + 2) 1 * ‖A‖ ^ (S.card + 2) + KB + KC) * H ^ (S.card + 2)) := by
      positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun v => ?_
    rw [reach_defect_apply hA rfl hδ hΛ H v]
    have hlead : ‖(γ * H ^ (S.card + 1)) •
        L (C ((A ^ S.card) ((unseen P C A S.card).starProjection v)))‖ ≤
        |γ| * c * H ^ (S.card + 1) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hH0 _)]
      have h := norm_lead_apply_le hA S.card v
      calc |γ| * H ^ (S.card + 1) *
            ‖L (C ((A ^ S.card) ((unseen P C A S.card).starProjection v)))‖
          ≤ |γ| * H ^ (S.card + 1) * (c * ‖v‖) := by gcongr
        _ = |γ| * c * H ^ (S.card + 1) * ‖v‖ := by ring
    have hA' := norm_proj_expRem_apply_le P A hH0 hx1 (by omega : 0 < S.card + 2) v
    have hB := norm_sum_top_le C A S.card (nodeCoeff S)
      (fun p => reachMoment Ai L M Λ γ H S.card p - ((p ! : ℝ) / ((p + 1)! : ℝ) * H) • L) κ hH0
      (fun p hp => norm_reachMoment_sub_le Ai L M Λ γ hH0 hH1 (mem_range.1 hp)) v
    have hC := norm_sum_coef_expRem_le C A S (reachRule δ Ai L M Λ γ H S.card) gc hH0 hx1
      (fun r _ => norm_reachRule_le δ Ai L M Λ γ hH0 hH1 S.card r) (by omega : 0 < S.card + 1) v
    rw [show S.card + 1 + 1 = S.card + 2 by omega] at hC
    rw [← hγ, ← hM]
    refine (norm_sub_le _ _).trans ?_
    have h3 : ∀ x y z : F, ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := fun x y z => norm_add₃_le
    refine (add_le_add_left (h3 _ _ _) _).trans ?_
    have hv := norm_nonneg v
    nlinarith [hlead, hA', hB, hC]

end Main

section Least

/-- From `a - R ≤ (1 + b x) t` to `a - R - b x a ≤ t` for `a, R, b, x ≥ 0`. -/
theorem sub_sub_mul_le_of_le_mul {a R t b x : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (h : a - R ≤ (1 + b * x) * t) : a - R - b * x * a ≤ t := by
  have hbx : 0 ≤ b * x := mul_nonneg hb hx
  rcases le_total t a with h1 | h1
  · nlinarith [mul_le_mul_of_nonneg_left h1 hbx]
  · nlinarith [mul_nonneg hbx ha]

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {P : E →L[ℝ] F} {C : E →L[ℝ] G} {A : E →L[ℝ] E} {Ai : F →L[ℝ] F} {L : G →L[ℝ] F}

/-- **The least defect of the rules with bounded weights, for any set `S` of `l` sample ages**
(Theorem `thm:memory` (ii) with its attainment; no independence of the maps). With
`c_i = ‖P A^{l+1}|𝒱^0‖` and `γ_S = nodeGamma S`:
* some rule with bounded weights has `‖𝒯‖ ≤ |γ_S| c_i H^{l+1} + K H^{l+2}`: there are
  `w₀, K ≥ 0` such that for every `0 ≤ H ≤ 1` with `H ‖A‖ ≤ 1` a rule has `‖g r ∘ C‖ ≤ w₀ H` for
  all `r ∈ S` and this defect (`exists_rule_nodeDefect_le`);
* every rule with `‖g r ∘ C‖ ≤ w H` for `r ∈ S`, `r ≠ 0`, has
  `‖𝒯‖ ≥ |γ_S| c_i H^{l+1} - (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1} + b |γ_S| c_i ‖A‖) H^{l+2}` for
  `H ‖A‖ ≤ 1`, with the constants `C_1 = nodeC1 S`, `C_2 = nodeC2 S`, `b = nodeB S` of
  `memory_nodes`.
Hence the least defect of the rules with weights at most `w H`, `w ≥ w₀`, is
`|γ_S| c_i H^{l+1} + O(H^{l+2})`. -/
theorem memory_nodes_least (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) (S : Finset ℤ) :
    (∃ w₀ K : ℝ, 0 ≤ w₀ ∧ 0 ≤ K ∧ ∀ H : ℝ, 0 ≤ H → H ≤ 1 → H * ‖A‖ ≤ 1 →
      ∃ (Fi : F →L[ℝ] F) (g : ℤ → G →L[ℝ] F), (∀ r ∈ S, ‖g r ∘L C‖ ≤ w₀ * H) ∧
        ‖nodeDefect P Fi g C A H S‖ ≤
          |nodeGamma S| * ‖(P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL‖ *
            H ^ (S.card + 1) + K * H ^ (S.card + 2)) ∧
    ∀ w H : ℝ, 0 ≤ w → 0 ≤ H → H * ‖A‖ ≤ 1 → ∀ (Fi : F →L[ℝ] F) (g : ℤ → G →L[ℝ] F),
      (∀ r ∈ S, r ≠ 0 → ‖g r ∘L C‖ ≤ w * H) →
      |nodeGamma S| * ‖(P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL‖ *
          H ^ (S.card + 1) -
        (nodeC1 S * ‖A‖ ^ (S.card + 2) + nodeC2 S * w * ‖A‖ ^ (S.card + 1) +
          nodeB S * |nodeGamma S| *
            ‖(P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL‖ * ‖A‖) *
          H ^ (S.card + 2) ≤
        ‖nodeDefect P Fi g C A H S‖ := by
  refine ⟨?_, fun w H hw hH hx1 Fi g hg => ?_⟩
  · obtain ⟨w, K, hw, hK, h⟩ := exists_rule_nodeDefect_le hA S
    exact ⟨w, K, hw, hK, fun H hH0 hH1 hx1 => by
      obtain ⟨Fi, g, -, hg, hT⟩ := h H hH0 hH1 hx1
      exact ⟨Fi, g, hg, hT⟩⟩
  · have h := memory_nodes hA hP Fi g hH hw hx1 rfl hg
    have hc := norm_nonneg ((P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL)
    have hR : 0 ≤ (nodeC1 S * ‖A‖ ^ (S.card + 2) + nodeC2 S * w * ‖A‖ ^ (S.card + 1)) *
        H ^ (S.card + 2) := by
      have := nodeC1_nonneg S
      have := nodeC2_nonneg S
      positivity
    have h2 := sub_sub_mul_le_of_le_mul (by positivity) hR (nodeB_nonneg S)
      (mul_nonneg hH (norm_nonneg A)) h
    have e : nodeB S * (H * ‖A‖) * (|nodeGamma S| *
        ‖(P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL‖ * H ^ (S.card + 1)) =
        nodeB S * |nodeGamma S| *
          ‖(P ∘L (A ^ (S.card + 1))) ∘L (unseen P C A S.card).subtypeL‖ * ‖A‖ *
            H ^ (S.card + 2) := by ring
    rw [e] at h2
    linarith

/-- **Theorem `thm:memory` (ii) is the least defect, all samples old** (the subsystem runs before
all of its partners, `l ≥ 1` samples of the ages `0, …, l-1`, `γ_l = adamsGamma l`): some rule
with `‖g r ∘ C‖ ≤ w₀ H` for all `r < l` has `‖𝒯‖ ≤ γ_l c_i H^{l+1} + K H^{l+2}`, and every rule
with `‖g r ∘ C‖ ≤ w H` for `1 ≤ r < l` has
`‖𝒯‖ ≥ γ_l c_i H^{l+1} - (C_1 ‖A‖^{l+2} + C_2 w ‖A‖^{l+1} + b_l γ_l c_i ‖A‖) H^{l+2}` with the
constants of `memory_lead`. -/
theorem memory_lead_least (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) :
    (∃ w₀ K : ℝ, 0 ≤ w₀ ∧ 0 ≤ K ∧ ∀ H : ℝ, 0 ≤ H → H ≤ 1 → H * ‖A‖ ≤ 1 →
      ∃ (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F), (∀ r < l, ‖g r ∘L C‖ ≤ w₀ * H) ∧
        ‖localDefect P Fi g C A H l‖ ≤
          adamsGamma l * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) +
            K * H ^ (l + 2)) ∧
    ∀ w H : ℝ, 0 ≤ w → 0 ≤ H → H * ‖A‖ ≤ 1 → ∀ (Fi : F →L[ℝ] F) (g : ℕ → G →L[ℝ] F),
      (∀ r, 1 ≤ r → r < l → ‖g r ∘L C‖ ≤ w * H) →
      adamsGamma l * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) -
        (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1) +
          memB l * adamsGamma l * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * ‖A‖) *
          H ^ (l + 2) ≤
        ‖localDefect P Fi g C A H l‖ := by
  refine ⟨?_, fun w H hw hH hx1 Fi g hg => ?_⟩
  · obtain ⟨w, K, hw, hK, h⟩ := exists_rule_nodeDefect_le hA (leadNodes l)
    refine ⟨w, K, hw, hK, fun H hH0 hH1 hx1 => ?_⟩
    obtain ⟨Fi, g, -, hg, hT⟩ := h H hH0 hH1 hx1
    refine ⟨Fi, fun n => g n, fun r hr => hg r (mem_map.2 ⟨r, mem_range.2 hr, rfl⟩), ?_⟩
    have e : localDefect P Fi (fun n => g n) C A H l = nodeDefect P Fi g C A H (leadNodes l) := by
      rw [← nodeDefect_leadNodes]
      unfold nodeDefect
      rw [sum_leadNodes, sum_leadNodes]
      simp only [Int.toNat_natCast]
    rw [e]
    rw [card_leadNodes, nodeGamma_leadNodes, abs_of_nonneg (adamsGamma_nonneg l)] at hT
    exact hT
  · have h := memory_lead hA hP Fi g hH hw hx1 hl hg
    have hc := norm_nonneg ((P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL)
    have hR : 0 ≤ (memC1 l * ‖A‖ ^ (l + 2) + memC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) := by
      have := memC1_nonneg l
      have := memC2_nonneg l
      positivity
    have hγ := adamsGamma_nonneg l
    have h2 := sub_sub_mul_le_of_le_mul (by positivity) hR (memB_nonneg l)
      (mul_nonneg hH (norm_nonneg A)) h
    have e : memB l * (H * ‖A‖) * (adamsGamma l *
        ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1)) =
        memB l * adamsGamma l * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * ‖A‖ *
          H ^ (l + 2) := by ring
    rw [e] at h2
    linarith

/-- **Theorem `thm:memory` (ii) is the least defect, the new sample and old ones** (the subsystem
runs after all of its partners, `l ≥ 1` samples of the ages `-1, 0, …, l-2`,
`γ'_l = lateGamma l`): some rule with `‖gNew ∘ C‖ ≤ w₀ H` and `‖g r ∘ C‖ ≤ w₀ H` for all
`r < l - 1` has `‖𝒯‖ ≤ |γ'_l| c_i H^{l+1} + K H^{l+2}`, and every rule with `‖gNew ∘ C‖ ≤ w H`
and `‖g r ∘ C‖ ≤ w H` for `1 ≤ r < l - 1` has
`‖𝒯‖ ≥ |γ'_l| c_i H^{l+1} - (C'_1 ‖A‖^{l+2} + C'_2 w ‖A‖^{l+1} + b'_l |γ'_l| c_i ‖A‖) H^{l+2}`
with the constants of `memory_late`. -/
theorem memory_late_least (hA : P ∘L A = Ai ∘L P + L ∘L C) (hP : ‖P‖ ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) :
    (∃ w₀ K : ℝ, 0 ≤ w₀ ∧ 0 ≤ K ∧ ∀ H : ℝ, 0 ≤ H → H ≤ 1 → H * ‖A‖ ≤ 1 →
      ∃ (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F),
        ‖gNew ∘L C‖ ≤ w₀ * H ∧ (∀ r < l - 1, ‖g r ∘L C‖ ≤ w₀ * H) ∧
        ‖lateDefect P Fi gNew g C A H l‖ ≤
          |lateGamma l| * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) +
            K * H ^ (l + 2)) ∧
    ∀ w H : ℝ, 0 ≤ w → 0 ≤ H → H * ‖A‖ ≤ 1 →
      ∀ (Fi : F →L[ℝ] F) (gNew : G →L[ℝ] F) (g : ℕ → G →L[ℝ] F),
      ‖gNew ∘L C‖ ≤ w * H → (∀ r, 1 ≤ r → r < l - 1 → ‖g r ∘L C‖ ≤ w * H) →
      |lateGamma l| * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1) -
        (lateC1 l * ‖A‖ ^ (l + 2) + lateC2 l * w * ‖A‖ ^ (l + 1) +
          lateB l * |lateGamma l| * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ *
            ‖A‖) * H ^ (l + 2) ≤
        ‖lateDefect P Fi gNew g C A H l‖ := by
  refine ⟨?_, fun w H hw hH hx1 Fi gNew g hgNew hg => ?_⟩
  · obtain ⟨w, K, hw, hK, h⟩ := exists_rule_nodeDefect_le hA (lateNodes l)
    refine ⟨w, K, hw, hK, fun H hH0 hH1 hx1 => ?_⟩
    obtain ⟨Fi, g, -, hg, hT⟩ := h H hH0 hH1 hx1
    refine ⟨Fi, g (-1), fun n => g n, hg (-1) (mem_insert_self _ _),
      fun r hr => hg r (mem_insert_of_mem (mem_map.2 ⟨r, mem_range.2 hr, rfl⟩)), ?_⟩
    have e : lateDefect P Fi (g (-1)) (fun n => g n) C A H l =
        nodeDefect P Fi g C A H (lateNodes l) := by
      rw [← nodeDefect_lateNodes]
      unfold nodeDefect
      rw [sum_lateNodes, sum_lateNodes]
      have h1 : ∀ k ∈ range (l - 1), lateCoef (g (-1)) (fun n => g n) (k : ℤ) = g k := by
        intro k _
        have hk : (k : ℤ) ≠ -1 := by omega
        simp [lateCoef, hk]
      rw [sum_congr rfl fun k hk => by rw [h1 k hk]]
      simp [lateCoef]
    rw [e]
    rw [card_lateNodes hl] at hT
    exact hT
  · have h := memory_late hA hP Fi gNew g hH hw hx1 hl hgNew hg
    have hc := norm_nonneg ((P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL)
    have hR : 0 ≤ (lateC1 l * ‖A‖ ^ (l + 2) + lateC2 l * w * ‖A‖ ^ (l + 1)) * H ^ (l + 2) := by
      have := lateC1_nonneg l
      have := lateC2_nonneg l
      positivity
    have h2 := sub_sub_mul_le_of_le_mul (by positivity) hR (lateB_nonneg l)
      (mul_nonneg hH (norm_nonneg A)) h
    have e : lateB l * (H * ‖A‖) * (|lateGamma l| *
        ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * H ^ (l + 1)) =
        lateB l * |lateGamma l| * ‖(P ∘L (A ^ (l + 1))) ∘L (unseen P C A l).subtypeL‖ * ‖A‖ *
          H ^ (l + 2) := by ring
    rw [e] at h2
    linarith

end Least

end CoSimFoundations
