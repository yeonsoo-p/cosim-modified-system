/-
The accumulation law: a floor under the one-step error is a floor under the error over a run.

`X` is the one-step map of a co-simulation, `U` that of the reference, in a real normed algebra
(matrices, operators). With `E k = X ^ k - U ^ k` the error after `k` macro steps and
`S K = Σ_{k < K} U ^ k`:

  `(X - U) * S K = E K + (1 - X) * Σ_{k < K} E k`     (identity, any ring)

Proof: `E (k+1) - X * E k = (X - U) * U ^ k`; sum over `k < K`; `E 0 = 0`.

Hence, if `‖E k‖ ≤ δ` for all `k ≤ K` (`K ≥ 1`):

  `‖(X - U) * S K‖ ≤ δ (1 + (K - 1) ‖1 - X‖) ≤ δ (1 + (K - 1) (‖1 - U‖ + δ))`,

and if `S K` has a right inverse `S'`, `‖X - U‖ ≤ δ (1 + (K - 1)(‖1 - U‖ + δ)) ‖S'‖`.

Reading: `‖X - U‖` is bounded below by a one-step floor `c` (of second order in the macro step
`H`); over a horizon `τ = K H` of the order of the reference's time scale, `‖S'‖` is of order
`1 / K` and `K ‖1 - U‖` of order one, so the largest error over the run is at least of order
`c / H`: first order. No scheme of a class with a one-step floor of second order converges faster
than first order over a run.
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Basic

open Finset

namespace CoSimFoundations

section Ring

variable {R : Type*} [Ring R]

/-- One step of the error: `E (k+1) - X * E k = (X - U) * U ^ k`. -/
theorem error_succ_sub (X U : R) (k : ℕ) :
    (X ^ (k + 1) - U ^ (k + 1)) - X * (X ^ k - U ^ k) = (X - U) * U ^ k := by
  rw [pow_succ', pow_succ', mul_sub, sub_mul]
  abel

/-- **The accumulation identity.** -/
theorem accumulation_identity (X U : R) (K : ℕ) :
    (X - U) * ∑ k ∈ range K, U ^ k =
      (X ^ K - U ^ K) + (1 - X) * ∑ k ∈ range K, (X ^ k - U ^ k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [sum_range_succ, mul_add, ih]
    rw [← error_succ_sub X U K]
    simp only [sub_mul, one_mul]
    abel

end Ring

section Normed

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- **The accumulation law.** If the error stays below `δ` for `K ≥ 1` steps, the one-step error
times the sum of the reference's powers is at most `δ (1 + (K - 1) ‖1 - X‖)`. -/
theorem norm_step_error_mul_sum_le (X U : 𝔸) {K : ℕ} (hK : 1 ≤ K) {δ : ℝ}
    (hδ : ∀ k ≤ K, ‖X ^ k - U ^ k‖ ≤ δ) :
    ‖(X - U) * ∑ k ∈ range K, U ^ k‖ ≤ δ * (1 + ((K : ℝ) - 1) * ‖1 - X‖) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le' hK
  have hsum : ‖∑ k ∈ range (K + 1), (X ^ k - U ^ k)‖ ≤ K * δ := by
    rw [sum_range_succ']
    simp only [pow_zero, sub_self, add_zero]
    calc ‖∑ k ∈ range K, (X ^ (k + 1) - U ^ (k + 1))‖ ≤ ∑ _k ∈ range K, δ :=
          norm_sum_le_of_le _ fun k hk => hδ (k + 1) (by rw [mem_range] at hk; omega)
      _ = K * δ := by simp
  rw [accumulation_identity]
  calc ‖(X ^ (K + 1) - U ^ (K + 1)) + (1 - X) * ∑ k ∈ range (K + 1), (X ^ k - U ^ k)‖
      ≤ ‖X ^ (K + 1) - U ^ (K + 1)‖ + ‖1 - X‖ * ‖∑ k ∈ range (K + 1), (X ^ k - U ^ k)‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
    _ ≤ δ + ‖1 - X‖ * (K * δ) :=
        add_le_add (hδ _ le_rfl) (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
    _ = δ * (1 + (((K + 1 : ℕ) : ℝ) - 1) * ‖1 - X‖) := by push_cast; ring

/-- The same with the reference's own step in the bound: `‖1 - X‖ ≤ ‖1 - U‖ + δ`. -/
theorem norm_step_error_mul_sum_le' (X U : 𝔸) {K : ℕ} (hK : 1 ≤ K) {δ : ℝ}
    (hδ : ∀ k ≤ K, ‖X ^ k - U ^ k‖ ≤ δ) :
    ‖(X - U) * ∑ k ∈ range K, U ^ k‖ ≤ δ * (1 + ((K : ℝ) - 1) * (‖1 - U‖ + δ)) := by
  have h0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (Nat.zero_le _))
  have h1 : ‖X - U‖ ≤ δ := by simpa only [pow_one] using hδ 1 hK
  have hK' : (0 : ℝ) ≤ (K : ℝ) - 1 := by
    rw [sub_nonneg]
    exact_mod_cast hK
  have hX : ‖1 - X‖ ≤ ‖1 - U‖ + δ :=
    calc ‖1 - X‖ = ‖(1 - U) - (X - U)‖ := by congr 1; abel
      _ ≤ ‖1 - U‖ + ‖X - U‖ := norm_sub_le _ _
      _ ≤ ‖1 - U‖ + δ := add_le_add le_rfl h1
  calc ‖(X - U) * ∑ k ∈ range K, U ^ k‖ ≤ δ * (1 + ((K : ℝ) - 1) * ‖1 - X‖) :=
        norm_step_error_mul_sum_le X U hK hδ
    _ ≤ δ * (1 + ((K : ℝ) - 1) * (‖1 - U‖ + δ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hX hK')) h0

/-- **A one-step floor is a floor over a run.** If the sum of the reference's powers has a right
inverse `S'`, the one-step error is bounded by the largest error over the run. -/
theorem norm_step_error_le_of_run (X U S' : 𝔸) {K : ℕ} (hK : 1 ≤ K) {δ : ℝ}
    (hδ : ∀ k ≤ K, ‖X ^ k - U ^ k‖ ≤ δ) (hS : (∑ k ∈ range K, U ^ k) * S' = 1) :
    ‖X - U‖ ≤ δ * (1 + ((K : ℝ) - 1) * (‖1 - U‖ + δ)) * ‖S'‖ :=
  calc ‖X - U‖ = ‖((X - U) * ∑ k ∈ range K, U ^ k) * S'‖ := by rw [mul_assoc, hS, mul_one]
    _ ≤ ‖(X - U) * ∑ k ∈ range K, U ^ k‖ * ‖S'‖ := norm_mul_le _ _
    _ ≤ δ * (1 + ((K : ℝ) - 1) * (‖1 - U‖ + δ)) * ‖S'‖ :=
        mul_le_mul_of_nonneg_right (norm_step_error_mul_sum_le' X U hK hδ) (norm_nonneg _)

end Normed

end CoSimFoundations
