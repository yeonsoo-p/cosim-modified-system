/-
The sign rule behind held samples in a Jacobi scheme (the paper, Proposition 5.11
`prop:parity`, the last sentences of its proof and the consequences stated after `eq:parity`).

**The sign rule.** Let `A` be a real matrix whose off-diagonal entries satisfy `A j i = -A i j`
(the diagonal is arbitrary: local dissipation), and let `i`, `k` be at least `d` links apart:
there is no walk `i = v_0, v_1, …, v_q = k` of `q < d` steps between distinct neighbours with all
factors `A v_t v_{t+1}` non-zero (`Linked A q i k`). Then

  `(A ^ d) k i = (-1) ^ d * (A ^ d) i k`        (`pow_apply_swap`).

Proof. More generally let `B i j = s A i j` off the diagonal. Then `(B ^ d) i k = s^d (A ^ d) i k`
(`pow_apply_scale`), by induction on `d`: in `(B^{d+1})_ik = Σ_j B_ij (B^d)_jk` the term `j = i`
vanishes because `(B^d)_ik = 0` (`i`, `k` are more than `d` links apart,
`pow_apply_eq_zero_of_not_linked`), a term with `A_ij = 0` vanishes, and for a neighbour `j` of
`i` the stores `j`, `k` are at least `d` links apart, so the induction hypothesis applies. The
sign rule is the case `B = Aᵀ`, `s = -1`. (The paper argues with the sum over paths: reversing a
path changes the sign of each of its `d` factors. The induction is the same argument without
the enumeration of paths; it also shows that loops, that is, diagonal entries, do not enter.)

**Consequences** (stated as implications, with explicit remainders `ρ₁`, `ρ₂` in place of
`O(H^{l+1})`; exact entries are the case `ρ₁ = ρ₂ = 0`). Let `i`, `k` be at least `l + 1` links
apart and let the difference `Δ` satisfy the first formula of `eq:parity` for both orders of
the pair, with `c = γ_l H^l`:

  `|Δ i k + c (A^{l+1}) i k| ≤ ρ₁`,   `|Δ k i + c (A^{l+1}) k i| ≤ ρ₂`.

Then
* `|Δ k i - (-1)^{l+1} Δ i k| ≤ ρ₁ + ρ₂` (second formula of `eq:parity`, `parity_pair`);
* `l` odd: the numerical dissipation `Δ_R = -sym Δ` has
  `|(Δ_R) i k - c (A^{l+1}) i k| ≤ (ρ₁ + ρ₂)/2` (`numerical_dissipation_of_odd`);
* `l` even: `|(Δ_R) i k| ≤ (ρ₁ + ρ₂)/2`, a numerical interconnection
  (`numerical_dissipation_of_even`);
* `l` odd: `ν + n ι ≥ 2 c |(A^{l+1}) i k| - (ρ₁ + ρ₂)` with `ν = -tr Δ` and any `ι` with
  `xᵀ Δ x ≤ ι xᵀ x` (`damping_add_injection_ge_of_odd`, from `thm:triple`).

The signs agree with the paper: `Δ_ik = -γ_l H^l [A^{l+1}]_ik`, `Δ_ki = (-1)^{l+1} Δ_ik`,
`[Δ_R]_ik = +γ_l H^l [A^{l+1}]_ik` for odd `l`.

Not in this file: the first formula of `eq:parity` itself (that a Jacobi scheme with bounded
weights and `‖P̃ - U‖ = O(H^{l+1})` has these entries); it is a hypothesis here.
-/
import CoSimFoundations.TripleLawGeneral

open Matrix Finset

namespace CoSimFoundations

section SignRule

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Linked A q i k`: there is a walk of `q` steps from `i` to `k`, each step between two
distinct indices `u`, `v` with `A u v ≠ 0`. -/
def Linked (A : Matrix ι ι ℝ) : ℕ → ι → ι → Prop
  | 0, i, k => i = k
  | q + 1, i, k => ∃ j, j ≠ i ∧ A i j ≠ 0 ∧ Linked A q j k

/-- A walk of no step ends where it starts. -/
theorem linked_zero (A : Matrix ι ι ℝ) (i k : ι) : Linked A 0 i k ↔ i = k :=
  Iff.rfl

/-- A walk of `q + 1` steps is a step to a neighbour followed by a walk of `q` steps. -/
theorem linked_succ (A : Matrix ι ι ℝ) (q : ℕ) (i k : ι) :
    Linked A (q + 1) i k ↔ ∃ j, j ≠ i ∧ A i j ≠ 0 ∧ Linked A q j k :=
  Iff.rfl

/-- **Powers vanish beyond the distance.** If `M` has no off-diagonal entry where `A` has none
and there is no walk of at most `q` steps from `i` to `k`, then `(M ^ q) i k = 0`. -/
theorem pow_apply_eq_zero_of_not_linked (A M : Matrix ι ι ℝ)
    (hM : ∀ i j, i ≠ j → A i j = 0 → M i j = 0) :
    ∀ (q : ℕ) (i k : ι), (∀ p ≤ q, ¬ Linked A p i k) → (M ^ q) i k = 0 := by
  intro q
  induction q with
  | zero =>
    intro i k h
    rw [pow_zero]
    exact one_apply_ne (h 0 le_rfl)
  | succ q ih =>
    intro i k h
    rw [pow_succ', mul_apply]
    refine sum_eq_zero fun j _ => ?_
    rcases eq_or_ne j i with rfl | hji
    · rw [ih j k fun p hp => h p (Nat.le_succ_of_le hp), mul_zero]
    · rcases eq_or_ne (A i j) 0 with h0 | h0
      · rw [hM i j hji.symm h0, zero_mul]
      · rw [ih j k fun p hp hl => h (p + 1) (Nat.succ_le_succ hp) ⟨j, hji, h0, hl⟩, mul_zero]

/-- **Scaling the links.** If `B i j = s A i j` off the diagonal and `i`, `k` are at least `d`
links apart, then `(B ^ d) i k = s ^ d (A ^ d) i k`. -/
theorem pow_apply_scale (A B : Matrix ι ι ℝ) (s : ℝ) (hB : ∀ i j, i ≠ j → B i j = s * A i j) :
    ∀ (d : ℕ) (i k : ι), (∀ q < d, ¬ Linked A q i k) → (B ^ d) i k = s ^ d * (A ^ d) i k := by
  have hBA : ∀ i j, i ≠ j → A i j = 0 → B i j = 0 := fun i j hij h0 => by
    rw [hB i j hij, h0, mul_zero]
  intro d
  induction d with
  | zero =>
    intro i k _
    rw [pow_zero, pow_zero, pow_zero, one_mul]
  | succ d ih =>
    intro i k h
    rw [pow_succ', mul_apply, pow_succ' A, mul_apply, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rcases eq_or_ne j i with rfl | hji
    · have hfar : ∀ p ≤ d, ¬ Linked A p j k := fun p hp => h p (Nat.lt_succ_of_le hp)
      rw [pow_apply_eq_zero_of_not_linked A B hBA d j k hfar,
        pow_apply_eq_zero_of_not_linked A A (fun _ _ _ h0 => h0) d j k hfar]
      ring
    · rcases eq_or_ne (A i j) 0 with h0 | h0
      · rw [hBA i j hji.symm h0, h0]
        ring
      · rw [ih j k fun q hq hl => h (q + 1) (Nat.succ_lt_succ hq) ⟨j, hji, h0, hl⟩,
          hB i j hji.symm]
        ring

/-- **The sign rule** (proof of Proposition 5.11). For a real matrix with `A j i = -A i j` off
the diagonal and two indices `i`, `k` at least `d` links apart (no walk of fewer than `d` steps
with all factors non-zero): `(A ^ d) k i = (-1) ^ d * (A ^ d) i k`. -/
theorem pow_apply_swap (A : Matrix ι ι ℝ) (hA : ∀ i j, i ≠ j → A j i = -A i j) {d : ℕ}
    {i k : ι} (hd : ∀ q < d, ¬ Linked A q i k) : (A ^ d) k i = (-1) ^ d * (A ^ d) i k := by
  have h := pow_apply_scale A Aᵀ (-1)
    (fun i j hij => by rw [transpose_apply, hA i j hij, neg_one_mul]) d i k hd
  rwa [← transpose_pow, transpose_apply] at h

/-- Stores that are at least one link apart are distinct. -/
theorem ne_of_not_linked_zero {A : Matrix ι ι ℝ} {i k : ι} (h : ¬ Linked A 0 i k) : i ≠ k :=
  h

/-- **Second formula of `eq:parity`.** If `i`, `k` are at least `l + 1` links apart and
`Δ i k = -c (A^{l+1}) i k` up to `ρ₁`, `Δ k i = -c (A^{l+1}) k i` up to `ρ₂`, then
`Δ k i = (-1)^{l+1} Δ i k` up to `ρ₁ + ρ₂`. -/
theorem parity_pair (A Δ : Matrix ι ι ℝ) (hA : ∀ i j, i ≠ j → A j i = -A i j) {l : ℕ}
    {i k : ι} (hd : ∀ q < l + 1, ¬ Linked A q i k) {c ρ₁ ρ₂ : ℝ}
    (h1 : |Δ i k + c * (A ^ (l + 1)) i k| ≤ ρ₁) (h2 : |Δ k i + c * (A ^ (l + 1)) k i| ≤ ρ₂) :
    |Δ k i - (-1) ^ (l + 1) * Δ i k| ≤ ρ₁ + ρ₂ := by
  have hs := pow_apply_swap A hA hd
  have hone : |((-1 : ℝ)) ^ (l + 1)| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  have e : Δ k i - (-1) ^ (l + 1) * Δ i k =
      (Δ k i + c * (A ^ (l + 1)) k i) - (-1) ^ (l + 1) * (Δ i k + c * (A ^ (l + 1)) i k) := by
    rw [hs]
    ring
  rw [e]
  have h3 := abs_sub (Δ k i + c * (A ^ (l + 1)) k i)
    ((-1) ^ (l + 1) * (Δ i k + c * (A ^ (l + 1)) i k))
  rw [abs_mul, hone, one_mul] at h3
  linarith

/-- The entry of the numerical dissipation `Δ_R = -sym Δ`. -/
theorem neg_sym_apply (Δ : Matrix ι ι ℝ) (i k : ι) :
    (-sym Δ) i k = -((Δ i k + Δ k i) / 2) := by
  simp only [sym, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply, transpose_apply,
    smul_eq_mul]
  ring

/-- **Odd number of held samples: a numerical dissipation.** If `l` is odd, `i`, `k` are at
least `l + 1` links apart and `Δ i k`, `Δ k i` are `-c (A^{l+1}) i k`, `-c (A^{l+1}) k i` up to
`ρ₁`, `ρ₂`, then `(Δ_R) i k = c (A^{l+1}) i k` up to `(ρ₁ + ρ₂)/2`. -/
theorem numerical_dissipation_of_odd (A Δ : Matrix ι ι ℝ) (hA : ∀ i j, i ≠ j → A j i = -A i j)
    {l : ℕ} (hl : Odd l) {i k : ι} (hd : ∀ q < l + 1, ¬ Linked A q i k) {c ρ₁ ρ₂ : ℝ}
    (h1 : |Δ i k + c * (A ^ (l + 1)) i k| ≤ ρ₁) (h2 : |Δ k i + c * (A ^ (l + 1)) k i| ≤ ρ₂) :
    |(-sym Δ) i k - c * (A ^ (l + 1)) i k| ≤ (ρ₁ + ρ₂) / 2 := by
  have hs := pow_apply_swap A hA hd
  rw [(Odd.add_odd hl odd_one).neg_one_pow, one_mul] at hs
  rw [hs] at h2
  have e : (-sym Δ) i k - c * (A ^ (l + 1)) i k =
      -((Δ i k + c * (A ^ (l + 1)) i k) + (Δ k i + c * (A ^ (l + 1)) i k)) / 2 := by
    rw [neg_sym_apply]
    ring
  rw [e, abs_div, abs_neg, abs_two]
  have h3 := abs_add_le (Δ i k + c * (A ^ (l + 1)) i k) (Δ k i + c * (A ^ (l + 1)) i k)
  have h4 : |(Δ i k + c * (A ^ (l + 1)) i k) + (Δ k i + c * (A ^ (l + 1)) i k)| ≤ ρ₁ + ρ₂ := by
    linarith
  exact div_le_div_of_nonneg_right h4 (by norm_num)

/-- **Even number of held samples: a numerical interconnection.** If `l` is even, `i`, `k` are
at least `l + 1` links apart and `Δ i k`, `Δ k i` are `-c (A^{l+1}) i k`, `-c (A^{l+1}) k i` up
to `ρ₁`, `ρ₂`, then the entry `(Δ_R) i k` of the numerical dissipation is at most
`(ρ₁ + ρ₂)/2`: to leading order the pair is antisymmetric. -/
theorem numerical_dissipation_of_even (A Δ : Matrix ι ι ℝ)
    (hA : ∀ i j, i ≠ j → A j i = -A i j) {l : ℕ} (hl : Even l) {i k : ι}
    (hd : ∀ q < l + 1, ¬ Linked A q i k) {c ρ₁ ρ₂ : ℝ}
    (h1 : |Δ i k + c * (A ^ (l + 1)) i k| ≤ ρ₁) (h2 : |Δ k i + c * (A ^ (l + 1)) k i| ≤ ρ₂) :
    |(-sym Δ) i k| ≤ (ρ₁ + ρ₂) / 2 := by
  have hs := pow_apply_swap A hA hd
  rw [(Even.add_odd hl odd_one).neg_one_pow, neg_one_mul] at hs
  rw [hs] at h2
  have e : (-sym Δ) i k =
      -((Δ i k + c * (A ^ (l + 1)) i k) + (Δ k i + c * -(A ^ (l + 1)) i k)) / 2 := by
    rw [neg_sym_apply]
    ring
  rw [e, abs_div, abs_neg, abs_two]
  have h3 := abs_add_le (Δ i k + c * (A ^ (l + 1)) i k) (Δ k i + c * -(A ^ (l + 1)) i k)
  have h4 : |(Δ i k + c * (A ^ (l + 1)) i k) + (Δ k i + c * -(A ^ (l + 1)) i k)| ≤ ρ₁ + ρ₂ := by
    linarith
  exact div_le_div_of_nonneg_right h4 (by norm_num)

end SignRule

section Trade

variable {n : ℕ}

/-- **Proposition 5.11, the trade for an odd number of held samples.** Let `A` have
`A j i = -A i j` off the diagonal, let the stores `i`, `k` be at least `l + 1` links apart, `l`
odd, and let the difference `Δ` of a co-simulation have the entries `-c (A^{l+1}) i k` and
`-c (A^{l+1}) k i` up to `ρ₁`, `ρ₂` (`c = γ_l H^l` in the paper). Then the numerical damping
`ν = -tr Δ` and every injection rate `ι` (`xᵀ Δ x ≤ ι xᵀ x` for all `x`) satisfy
`ν + n ι ≥ 2 c |(A^{l+1}) i k| - (ρ₁ + ρ₂)`. -/
theorem damping_add_injection_ge_of_odd (A Δ : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, i ≠ j → A j i = -A i j) {l : ℕ} (hl : Odd l) {i k : Fin n}
    (hd : ∀ q < l + 1, ¬ Linked A q i k) {c ρ₁ ρ₂ : ℝ}
    (h1 : |Δ i k + c * (A ^ (l + 1)) i k| ≤ ρ₁) (h2 : |Δ k i + c * (A ^ (l + 1)) k i| ≤ ρ₂)
    {ι : ℝ} (hι : ∀ x : Fin n → ℝ, x ⬝ᵥ (Δ *ᵥ x) ≤ ι * (x ⬝ᵥ x)) :
    2 * c * |(A ^ (l + 1)) i k| - (ρ₁ + ρ₂) ≤ -Δ.trace + n * ι := by
  have hik : i ≠ k := ne_of_not_linked_zero (hd 0 (Nat.succ_pos l))
  have h := damping_add_injection_ge_of_difference Δ hι (single_dotProduct_single_self i)
    (single_dotProduct_single_self k) (single_dotProduct_single_of_ne hik)
  rw [single_dotProduct_mulVec_single] at h
  have h3 := numerical_dissipation_of_odd A Δ hA hl hd h1 h2
  have h4 := abs_sub_abs_le_abs_sub (c * (A ^ (l + 1)) i k) ((-sym Δ) i k)
  rw [abs_sub_comm, abs_mul] at h4
  have h5 : c * |(A ^ (l + 1)) i k| ≤ |c| * |(A ^ (l + 1)) i k| :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg _)
  linarith

end Trade

end CoSimFoundations
