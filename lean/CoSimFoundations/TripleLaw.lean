/-
The triple law: damping, injection and a forced entry of the difference cannot all be small.

`Δ` is the difference between the modified system of a co-simulation and the reference, a real
`n × n` matrix in energy coordinates. Two properties of a run are read from it:

* the total numerical damping `ν = -tr Δ` (invariant under a change of coordinates);
* the injection rate `ι = λ_max (sym Δ)`: the largest rate at which the modified system gains
  energy relative to the reference. In the statement `ι` enters through any `lam` with
  `xᵀ Δ x ≤ lam · xᵀ x` for all `x`.

**Triple law.** For two distinct coordinates `i`, `j`:

  `|Δ i j + Δ j i| ≤ n · lam - tr Δ`,   that is,   `ν + n ι ≥ 2 |sym(Δ)_ij|`.

It holds for every matrix, hence for every scheme whatever its class. A class enters through the
entry it forces: for a Jacobi scheme with one held sample and two stores that are two coupling
links apart, `sym(Δ)_ij = -(H/2) [A²]_ij` to leading order. Then a scheme that never injects
(`ι ≤ 0`) has `ν ≥ H |[A²]_ij|`, and a scheme that keeps the total damping (`ν = 0`) injects at a
rate of at least `H |[A²]_ij| / n`.

Proof: test the quadratic form on `e_i + e_j` and `e_i - e_j`: `2 lam - Δ i i - Δ j j ≥
|Δ i j + Δ j i|`; every other diagonal entry is at most `lam`; add up.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

open Matrix

namespace CoSimFoundations

variable {n : ℕ}

/-- The bilinear form of `Δ` on two coordinate vectors is an entry of `Δ`. -/
theorem single_dotProduct_mulVec_single (Δ : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    (Pi.single a 1 : Fin n → ℝ) ⬝ᵥ (Δ *ᵥ (Pi.single b 1 : Fin n → ℝ)) = Δ a b := by
  rw [mulVec_single_one, single_one_dotProduct, col_apply]

/-- A coordinate vector has unit length. -/
theorem single_dotProduct_single_self (a : Fin n) :
    (Pi.single a 1 : Fin n → ℝ) ⬝ᵥ (Pi.single a 1 : Fin n → ℝ) = 1 := by
  rw [single_one_dotProduct, Pi.single_eq_same]

/-- Two distinct coordinate vectors are orthogonal. -/
theorem single_dotProduct_single_of_ne {a b : Fin n} (h : a ≠ b) :
    (Pi.single a 1 : Fin n → ℝ) ⬝ᵥ (Pi.single b 1 : Fin n → ℝ) = 0 := by
  rw [single_one_dotProduct, Pi.single_eq_of_ne h]

/-- A diagonal entry is at most the bound of the quadratic form. -/
theorem diag_le_of_quadForm_le (Δ : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) (k : Fin n) :
    Δ k k ≤ lam := by
  have h := hlam (Pi.single k 1)
  rwa [single_dotProduct_mulVec_single, single_dotProduct_single_self, mul_one] at h

/-- Two diagonal entries and the symmetric off-diagonal pair between them. -/
theorem abs_offDiag_le_of_quadForm_le (Δ : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) {i j : Fin n} (hij : i ≠ j) :
    |Δ i j + Δ j i| ≤ (lam - Δ i i) + (lam - Δ j j) := by
  have hp := hlam (Pi.single i 1 + Pi.single j 1)
  have hm := hlam (Pi.single i 1 - Pi.single j 1)
  simp only [mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct_mulVec_single,
    single_dotProduct_single_self, single_dotProduct_single_of_ne hij,
    single_dotProduct_single_of_ne hij.symm] at hp
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub, single_dotProduct_mulVec_single,
    single_dotProduct_single_self, single_dotProduct_single_of_ne hij,
    single_dotProduct_single_of_ne hij.symm] at hm
  rw [abs_le]
  constructor <;> linarith

/-- **The triple law.** -/
theorem triple_law (Δ : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) {i j : Fin n} (hij : i ≠ j) :
    |Δ i j + Δ j i| ≤ n * lam - Δ.trace := by
  have htr : Δ.trace = ∑ k, Δ k k := rfl
  have hsum : ∑ k, (lam - Δ k k) = n * lam - ∑ k, Δ k k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hsub : ∑ k ∈ ({i, j} : Finset (Fin n)), (lam - Δ k k) ≤ ∑ k, (lam - Δ k k) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => sub_nonneg.mpr (diag_le_of_quadForm_le Δ hlam k))
  rw [Finset.sum_pair hij] at hsub
  have hpair := abs_offDiag_le_of_quadForm_le Δ hlam hij
  linarith

/-- **Never injecting costs damping:** if the modified system gains no energy relative to the
reference in any state, its total numerical damping is at least the forced symmetric pair. -/
theorem damping_of_no_injection (Δ : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ 0) {i j : Fin n} (hij : i ≠ j) :
    |Δ i j + Δ j i| ≤ -Δ.trace := by
  have h0 := triple_law Δ (lam := 0) (fun x => (h x).trans_eq (zero_mul _).symm) hij
  rwa [mul_zero, zero_sub] at h0

/-- **Keeping the damping costs injection:** if the total damping is that of the reference, the
injection rate is at least the forced symmetric pair divided by `n`. -/
theorem injection_of_trace_zero (Δ : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) (htr : Δ.trace = 0)
    {i j : Fin n} (hij : i ≠ j) :
    |Δ i j + Δ j i| ≤ n * lam := by
  have h0 := triple_law Δ hlam hij
  rwa [htr, sub_zero] at h0

end CoSimFoundations
