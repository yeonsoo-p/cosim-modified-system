/-
The value of a chain of `n` stores without injection (the paper, Section 5, the bound (chainn)
in its matrix form).

Statement. Let `2 ≤ n` (the paper has `n ≥ 3`; for `n = 2` the statement is `0 ≤ tr S`) and let
`S` be a real symmetric positive semidefinite `n × n` matrix with

  `S a (a+2) = β`   (stores two links apart),      `S a b = 0` for `b > a + 2`.

Then `2 (n - 2) β ≤ tr S` (`chain_trace_bound`). In the paper `S` is the numerical dissipation to
leading order, `β = H ω² / 2`, and the bound is `ν ≥ (n - 2) H ω²` to leading order. The entries
between neighbouring stores are free.

Proof (the paper's). Let `Z a b = (-1)^((a-b)/2)` for even `a - b` and `0` otherwise (`chainZ`,
`chainZ_apply_of_le`). `Z` is the sum of two rank-one matrices `v vᵀ + w wᵀ`, `v` supported on the
even and `w` on the odd indices with the entries `(-1)^(a/2)` (`chainZ_eq`), hence positive
semidefinite (`chainZ_posSemidef`), and `tr (S Z) = vᵀ S v + wᵀ S w ≥ 0`
(`trace_mul_chainZ_nonneg`). On the other hand `Z a a = 1`, `Z a (a ± 2) = -1`, and `Z` vanishes
between indices at odd distance, while `S` vanishes at distance greater than two, so
`tr (S Z) = tr S - 2 (n - 2) β` (`trace_mul_chainZ`).

The bound is attained: `T = β Σ_{k < n-2} (e_k + e_{k+2}) (e_k + e_{k+2})ᵀ` (`chainExt`) is
positive semidefinite for `β ≥ 0` (`chainExt_posSemidef`), has `T a (a+2) = β`
(`chainExt_apply_two`), vanishes at all other places off the diagonal (`chainExt_apply_of_ne`, in
particular beyond distance two, `chainExt_apply_far`), and `tr T = 2 (n - 2) β`
(`chainExt_trace`).
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Matrix Finset

namespace CoSimFoundations

variable {n : ℕ}

/-- The two vectors of the rank-one decomposition of `Z`: `chainV r` has the entries `(-1)^(a/2)`
at the indices `a` of parity `r` and `0` elsewhere. -/
def chainV (r : ℕ) (a : Fin n) : ℝ := if (a : ℕ) % 2 = r then (-1) ^ ((a : ℕ) / 2) else 0

/-- The matrix `Z` of the paper: `Z a b = (-1)^((a-b)/2)` if `a - b` is even, `0` otherwise
(written with `(-1)^(a/2 + b/2)`, which is the same sign; see `chainZ_apply_of_le`). -/
def chainZ (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    if (a : ℕ) % 2 = (b : ℕ) % 2 then (-1 : ℝ) ^ ((a : ℕ) / 2 + (b : ℕ) / 2) else 0

/-- Entries of `Z`. -/
theorem chainZ_apply (a b : Fin n) :
    chainZ n a b =
      if (a : ℕ) % 2 = (b : ℕ) % 2 then (-1 : ℝ) ^ ((a : ℕ) / 2 + (b : ℕ) / 2) else 0 := rfl

/-- **The entries of `Z` in the paper's form:** `Z a b = (-1)^((a-b)/2)` for `b ≤ a` with `a - b`
even. -/
theorem chainZ_apply_of_le {a b : Fin n} (hba : (b : ℕ) ≤ a) (h : ((a : ℕ) - b) % 2 = 0) :
    chainZ n a b = (-1 : ℝ) ^ (((a : ℕ) - b) / 2) := by
  have hpar : (a : ℕ) % 2 = (b : ℕ) % 2 := by omega
  have he : (a : ℕ) / 2 + (b : ℕ) / 2 = ((a : ℕ) - b) / 2 + 2 * ((b : ℕ) / 2) := by omega
  rw [chainZ_apply, ite_eq_left hpar, he, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- `Z` vanishes between indices of different parity. -/
theorem chainZ_apply_of_odd {a b : Fin n} (h : (a : ℕ) % 2 ≠ (b : ℕ) % 2) : chainZ n a b = 0 := by
  rw [chainZ_apply, ite_eq_right h]

/-- `Z` is symmetric. -/
theorem chainZ_symm (a b : Fin n) : chainZ n a b = chainZ n b a := by
  rw [chainZ_apply, chainZ_apply, add_comm]
  by_cases h : (a : ℕ) % 2 = (b : ℕ) % 2
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

/-- **`Z` is the sum of two rank-one matrices,** one on the even and one on the odd indices. -/
theorem chainZ_eq (n : ℕ) :
    chainZ n = vecMulVec (chainV 0) (chainV 0) + vecMulVec (chainV 1) (chainV 1) := by
  ext a b
  rw [Matrix.add_apply, vecMulVec_apply, vecMulVec_apply, chainZ_apply]
  unfold chainV
  rcases Nat.mod_two_eq_zero_or_one (a : ℕ) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (b : ℕ) with hb | hb <;>
    simp [ha, hb, pow_add]

/-- **`Z` is positive semidefinite.** -/
theorem chainZ_posSemidef (n : ℕ) : (chainZ n).PosSemidef := by
  rw [chainZ_eq]
  have h : ∀ r : ℕ, (vecMulVec (chainV (n := n) r) (chainV r)).PosSemidef := fun r => by
    have h0 := posSemidef_vecMulVec_self_star (chainV (n := n) r)
    rwa [star_trivial] at h0
  exact (h 0).add (h 1)

/-- The trace of a product with a rank-one matrix is a quadratic form. -/
theorem trace_mul_vecMulVec_self (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (S * vecMulVec v v).trace = star v ⬝ᵥ (S *ᵥ v) := by
  simp only [trace, diag_apply, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    star_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **`tr (S Z) ≥ 0` for every positive semidefinite `S`.** -/
theorem trace_mul_chainZ_nonneg {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) :
    0 ≤ (S * chainZ n).trace := by
  rw [chainZ_eq, Matrix.mul_add, trace_add, trace_mul_vecMulVec_self, trace_mul_vecMulVec_self]
  exact add_nonneg (hS.dotProduct_mulVec_nonneg _) (hS.dotProduct_mulVec_nonneg _)

/-- A sum over `Fin n` that selects the index with a given value. -/
theorem sum_fin_ite_val_eq (k : ℕ) (c : ℝ) :
    ∑ b : Fin n, (if (b : ℕ) = k then c else 0) = if k < n then c else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = k then c else 0) n, Finset.sum_ite_eq']
  simp only [Finset.mem_range]

/-- The number of indices `a` with `a + 2 < n`, as a weighted sum. -/
theorem sum_fin_ite_add_two_lt (hn : 2 ≤ n) (c : ℝ) :
    ∑ a : Fin n, (if (a : ℕ) + 2 < n then c else 0) = ((n : ℝ) - 2) * c := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 2 < n then c else 0) n, ← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun i => i + 2 < n) = Finset.range (n - 2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_ofNat]

/-- The number of indices `a` with `2 ≤ a`, as a weighted sum. -/
theorem sum_fin_ite_two_le (hn : 2 ≤ n) (c : ℝ) :
    ∑ a : Fin n, (if 2 ≤ (a : ℕ) then c else 0) = ((n : ℝ) - 2) * c := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if 2 ≤ i then c else 0) n, ← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun i => 2 ≤ i) = Finset.Ico 2 n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_ofNat]

/-- **The trace of `S Z`:** if `S` is symmetric with `S a (a+2) = β` and `S a b = 0` for
`b > a + 2`, then `tr (S Z) = tr S - 2 (n - 2) β`. -/
theorem trace_mul_chainZ (hn : 2 ≤ n) {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsHermitian) {β : ℝ}
    (h2 : ∀ a b : Fin n, (a : ℕ) + 2 = b → S a b = β)
    (hfar : ∀ a b : Fin n, (a : ℕ) + 2 < b → S a b = 0) :
    (S * chainZ n).trace = S.trace - 2 * ((n : ℝ) - 2) * β := by
  have hsym : ∀ a b : Fin n, S a b = S b a := fun a b => by
    have h := hS.apply b a
    rwa [star_trivial] at h
  have hterm : ∀ a b : Fin n, S a b * chainZ n b a =
      (if b = a then S a a else 0) - (if (b : ℕ) = (a : ℕ) + 2 then β else 0) -
        (if (b : ℕ) = (a : ℕ) - 2 then (if 2 ≤ (a : ℕ) then β else 0) else 0) := by
    intro a b
    by_cases hba : b = a
    · subst hba
      have he : (b : ℕ) / 2 + (b : ℕ) / 2 = 2 * ((b : ℕ) / 2) := by omega
      rw [chainZ_apply, ite_eq_left rfl, he, pow_mul, neg_one_sq, one_pow, ite_eq_left rfl,
        ite_eq_right (by omega)]
      by_cases hb2 : 2 ≤ (b : ℕ)
      · rw [ite_eq_right (by omega)]
        ring
      · rw [ite_eq_right hb2]
        simp
    · rw [ite_eq_right hba]
      have hne : (b : ℕ) ≠ (a : ℕ) := fun h => hba (Fin.ext h)
      by_cases h1 : (b : ℕ) = (a : ℕ) + 2
      · have he : (b : ℕ) / 2 + (a : ℕ) / 2 = 2 * ((a : ℕ) / 2) + 1 := by omega
        rw [ite_eq_left h1, ite_eq_right (by omega), h2 a b h1.symm, chainZ_apply,
          ite_eq_left (by omega), he,
          pow_succ, pow_mul, neg_one_sq, one_pow]
        ring
      · rw [ite_eq_right h1]
        by_cases h3 : (b : ℕ) + 2 = (a : ℕ)
        · have he : (b : ℕ) / 2 + (a : ℕ) / 2 = 2 * ((b : ℕ) / 2) + 1 := by omega
          rw [ite_eq_left (by omega), ite_eq_left (by omega), hsym a b, h2 b a h3, chainZ_apply,
            ite_eq_left (by omega), he, pow_succ, pow_mul, neg_one_sq, one_pow]
          ring
        · have h4 : (if (b : ℕ) = (a : ℕ) - 2 then (if 2 ≤ (a : ℕ) then β else 0) else 0) = 0 := by
            by_cases h5 : (b : ℕ) = (a : ℕ) - 2
            · rw [ite_eq_left h5, ite_eq_right (by omega)]
            · rw [ite_eq_right h5]
          rw [h4]
          by_cases hpar : (b : ℕ) % 2 = (a : ℕ) % 2
          · have hS0 : S a b = 0 := by
              rcases Nat.lt_or_ge (a : ℕ) (b : ℕ) with hlt | hge
              · exact hfar a b (by omega)
              · rw [hsym a b]
                exact hfar b a (by omega)
            rw [hS0]
            ring
          · rw [chainZ_apply_of_odd hpar]
            ring
  have hrow : ∀ a : Fin n, ∑ b, S a b * chainZ n b a =
      S a a - (if (a : ℕ) + 2 < n then β else 0) - (if 2 ≤ (a : ℕ) then β else 0) := by
    intro a
    rw [Finset.sum_congr rfl fun b _ => hterm a b, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a, ite_eq_left (Finset.mem_univ a),
      sum_fin_ite_val_eq, sum_fin_ite_val_eq, ite_eq_left (show (a : ℕ) - 2 < n by omega)]
  have htr : (S * chainZ n).trace = ∑ a, ∑ b, S a b * chainZ n b a := by
    simp only [trace, diag_apply, Matrix.mul_apply]
  rw [htr, Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, sum_fin_ite_add_two_lt hn, sum_fin_ite_two_le hn]
  simp only [trace, diag_apply]
  ring

/-- **The bound (chainn) of the paper, matrix form.** A real symmetric positive semidefinite
`n × n` matrix `S`, `n ≥ 2`, whose entries between indices two apart equal `β` and whose entries
between indices more than two apart vanish has `tr S ≥ 2 (n - 2) β`. (With `S` the numerical
dissipation to leading order and `β = H ω² / 2` this is `ν ≥ (n - 2) H ω²` to leading order.) -/
theorem chain_trace_bound (hn : 2 ≤ n) {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) {β : ℝ}
    (h2 : ∀ a b : Fin n, (a : ℕ) + 2 = b → S a b = β)
    (hfar : ∀ a b : Fin n, (a : ℕ) + 2 < b → S a b = 0) :
    2 * ((n : ℝ) - 2) * β ≤ S.trace := by
  have h := trace_mul_chainZ_nonneg hS
  rw [trace_mul_chainZ hn hS.1 h2 hfar] at h
  linarith

/-- The vector `e_k + e_{k+2}`. -/
def chainU (k : ℕ) (c : Fin n) : ℝ := if (c : ℕ) = k ∨ (c : ℕ) = k + 2 then 1 else 0

/-- The matrix that attains the bound: `β Σ_{k < n-2} (e_k + e_{k+2}) (e_k + e_{k+2})ᵀ`. -/
def chainExt (n : ℕ) (β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  β • ∑ k ∈ Finset.range (n - 2), vecMulVec (chainU k) (chainU k)

/-- Entries of the attaining matrix. -/
theorem chainExt_apply (β : ℝ) (a b : Fin n) :
    chainExt n β a b = β * ∑ k ∈ Finset.range (n - 2), chainU k a * chainU k b := by
  simp only [chainExt, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]

/-- **The attaining matrix is positive semidefinite** for `β ≥ 0`. -/
theorem chainExt_posSemidef (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) : (chainExt n β).PosSemidef := by
  have h : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, vecMulVec (chainU (n := n) k) (chainU k)).PosSemidef := by
    intro m
    induction m with
    | zero =>
      rw [Finset.sum_range_zero]
      exact PosSemidef.zero
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h0 := posSemidef_vecMulVec_self_star (chainU (n := n) m)
      rw [star_trivial] at h0
      exact ih.add h0
  exact (h (n - 2)).smul hβ

/-- **The attaining matrix has the prescribed entries two apart:** `T a (a+2) = β`. -/
theorem chainExt_apply_two (β : ℝ) {a b : Fin n} (h : (a : ℕ) + 2 = b) :
    chainExt n β a b = β := by
  have hterm : ∀ k : ℕ, chainU k a * chainU k b = if k = (a : ℕ) then 1 else 0 := by
    intro k
    unfold chainU
    by_cases hk : k = (a : ℕ)
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hk, mul_one]
    · by_cases h1 : (a : ℕ) = k ∨ (a : ℕ) = k + 2
      · rw [ite_eq_right (show ¬ ((b : ℕ) = k ∨ (b : ℕ) = k + 2) by omega), mul_zero,
          ite_eq_right hk]
      · rw [ite_eq_right h1, zero_mul, ite_eq_right hk]
  have hb := b.isLt
  rw [chainExt_apply, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_range.2 (by omega)), mul_one]

/-- **The attaining matrix vanishes off the diagonal except two apart.** -/
theorem chainExt_apply_of_ne (β : ℝ) {a b : Fin n} (hab : a ≠ b) (h1 : (a : ℕ) + 2 ≠ b)
    (h2 : (b : ℕ) + 2 ≠ a) : chainExt n β a b = 0 := by
  have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
  have hterm : ∀ k : ℕ, chainU k a * chainU k b = 0 := by
    intro k
    unfold chainU
    by_cases h3 : (a : ℕ) = k ∨ (a : ℕ) = k + 2
    · rw [ite_eq_right (show ¬ ((b : ℕ) = k ∨ (b : ℕ) = k + 2) by omega), mul_zero]
    · rw [ite_eq_right h3, zero_mul]
  rw [chainExt_apply, Finset.sum_eq_zero fun k _ => hterm k, mul_zero]

/-- The attaining matrix vanishes between indices more than two apart. -/
theorem chainExt_apply_far (β : ℝ) {a b : Fin n} (h : (a : ℕ) + 2 < b) :
    chainExt n β a b = 0 :=
  chainExt_apply_of_ne β (fun hab => by rw [hab] at h; omega) (by omega) (by omega)

/-- **The attaining matrix has the trace `2 (n - 2) β`:** the bound `chain_trace_bound` is
attained. -/
theorem chainExt_trace (hn : 2 ≤ n) (β : ℝ) : (chainExt n β).trace = 2 * ((n : ℝ) - 2) * β := by
  have hterm : ∀ (k : ℕ) (c : Fin n), chainU k c * chainU k c =
      (if (c : ℕ) = k then 1 else 0) + (if (c : ℕ) = k + 2 then 1 else 0) := by
    intro k c
    unfold chainU
    by_cases h1 : (c : ℕ) = k
    · rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_right (by omega)]
      ring
    · by_cases h2 : (c : ℕ) = k + 2
      · rw [ite_eq_left (Or.inr h2), ite_eq_right h1, ite_eq_left h2]
        ring
      · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]
        ring
  have hsum : ∀ k ∈ Finset.range (n - 2), ∑ c : Fin n, chainU k c * chainU k c = 2 := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [Finset.sum_congr rfl fun c _ => hterm k c, Finset.sum_add_distrib, sum_fin_ite_val_eq,
      sum_fin_ite_val_eq, ite_eq_left (by omega), ite_eq_left (by omega)]
    norm_num
  have htr : (chainExt n β).trace = β * ∑ k ∈ Finset.range (n - 2), ∑ c : Fin n,
      chainU k c * chainU k c := by
    simp only [trace, diag_apply, chainExt_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [htr, Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_sub hn, Nat.cast_ofNat]
  ring

end CoSimFoundations
