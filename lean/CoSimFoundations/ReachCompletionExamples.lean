/-
The closed forms of the least spread and the least norm (the paper), with `lamMax`, `lamMin`, `spr`
of `ReachCompletion`.

* **Clique bound** (`abs_dotProduct_sub_trace_le`, `clique_bound`, `spr_ge_of_offDiag`):
  for a sign vector `s` of length `m ≥ 2` and symmetric `M`,
  `spr M ≥ 2 |Σ_{p<q} s_p s_q M_pq| / (m - 1)`, the diagonal arbitrary; if `M_pq = b s_p s_q` for
  `p ≠ q`, then `spr M ≥ m |b|`.
* **Star attainment** (`spr_star`, `norm_star_sub_eq`, `isLeast_spr_offDiag`,
`isLeast_norm_offDiag`): `spr (b (s sᵀ - 1)) = m |b|` and `‖b (s sᵀ - 1) - c 1‖ = m |b| / 2`
  for `c = (m - 2) b / 2`; over all diagonals the least spread is `m |b|`, the least norm
  `m |b| / 2`.
* **Disjoint pairs** (`norm_opE_add_transpose_of_side`, `spr_add_transpose_of_side`, `pair_blocks`):
if every `A_k` has its rows in one set `I_k` and its columns in another `J_k`,
  all these sets pairwise disjoint, then `M = Σ_k (A_k + A_kᵀ)` (a direct sum of the blocks
  `[[0, F_k], [F_kᵀ, 0]]` and a zero block after a permutation) has `‖M‖ = max_k ‖A_k‖` and
  `spr M = 2 max_k ‖A_k‖`.
* **The chain without injection** (`two_mul_abs_le_norm_of_form_nonpos`, `chainMin_form_nonpos`,
`norm_chainMin`, `inner_chainSkew_self`, `chainSkew_apply`, `norm_chainSkew`): if `⟪x, M x⟫ ≤ 0` for
all `x` and `M_ij = M_ji = p`, `i ≠ j`, then
  `‖M‖ ≥ 2 |p|`; `chainMin i j p = -|p| (e_i e_iᵀ + e_j e_jᵀ) + p (e_i e_jᵀ + e_j e_iᵀ)` has
  these entries, a form `≤ 0` and norm `2 |p|`; `chainSkew i j p = p (e_i e_jᵀ - e_j e_iᵀ)` has
  the form `0` and norm `|p|`.
-/
import CoSimFoundations.ReachCompletion

open Matrix Metric
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n m : ℕ}

/-! ### The clique bound -/

section Clique

/-- A sign has square one. -/
theorem sq_eq_one_of_sign {t : ℝ} (ht : t = 1 ∨ t = -1) : t ^ 2 = 1 := by
  rcases ht with rfl | rfl <;> norm_num

/-- A sign vector of length `m` has `s ⬝ᵥ s = m`. -/
theorem dotProduct_self_of_sign {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) :
    s ⬝ᵥ s = m := by
  simp only [dotProduct, ← sq, fun p => sq_eq_one_of_sign (hs p), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **The clique bound, general form.** For any square matrix `M` of size `m ≥ 1` and a sign
vector `s`: `|sᵀ M s - tr M| ≤ (m - 1) spr (M)` (`λ_max ≥ uᵀ M u` and
`λ_min ≤ (tr M - uᵀ M u) / (m - 1)` for `u = s / √m`). -/
theorem abs_dotProduct_sub_trace_le (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) :
    |s ⬝ᵥ (M *ᵥ s) - M.trace| ≤ ((m : ℝ) - 1) * spr M := by
  have hss := dotProduct_self_of_sign hs
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h1 := dotProduct_le_lamMax M s
  have h2 := lamMin_mul_le_dotProduct M s
  have h3 := quadForm_le_trace_add M (ι := -lamMin M)
    (fun x => by rw [neg_neg]; exact lamMin_mul_le_dotProduct M x) s
  have h4 := quadForm_le_trace_add (-M) (ι := lamMax M) (fun x => by
    rw [neg_mulVec, dotProduct_neg]
    have := dotProduct_le_lamMax M x
    linarith) s
  rw [neg_mulVec, dotProduct_neg, trace_neg] at h4
  rw [hss] at h1 h2 h3 h4
  have k1 := mul_le_mul_of_nonneg_left h1 hm1
  have k2 := mul_le_mul_of_nonneg_left h2 hm1
  rw [abs_le, spr]
  constructor
  · have : (m : ℝ) * (-((m - 1) * (lamMax M - lamMin M))) ≤
        (m : ℝ) * (s ⬝ᵥ (M *ᵥ s) - M.trace) := by nlinarith
    exact le_of_mul_le_mul_left this hmpos
  · have : (m : ℝ) * (s ⬝ᵥ (M *ᵥ s) - M.trace) ≤
        (m : ℝ) * ((m - 1) * (lamMax M - lamMin M)) := by nlinarith
    exact le_of_mul_le_mul_left this hmpos

/-- For a symmetric `M` and a sign vector: `sᵀ M s - tr M = 2 Σ_{p<q} s_p s_q M_pq`. -/
theorem dotProduct_sub_trace_eq {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.IsSymm)
    {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) :
    s ⬝ᵥ (M *ᵥ s) - M.trace = 2 * ∑ p, ∑ q ∈ Finset.Ioi p, s p * s q * M p q := by
  set f : Fin m → Fin m → ℝ := fun p q => s p * s q * M p q with hfdef
  show _ = 2 * ∑ p, ∑ q ∈ Finset.Ioi p, f p q
  have hf : ∀ p q, f q p = f p q := fun p q => by
    simp only [hfdef]
    rw [hM.apply p q]
    ring
  have h1 : s ⬝ᵥ (M *ᵥ s) = ∑ p, ∑ q, f p q := by
    simp only [dotProduct, mulVec, Finset.mul_sum, hfdef]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have h2 : M.trace = ∑ p, f p p := by
    simp only [Matrix.trace, Matrix.diag, hfdef]
    exact Finset.sum_congr rfl fun p _ => by rw [← sq, sq_eq_one_of_sign (hs p), one_mul]
  have hsplit : ∀ p q, f p q = (if p < q then f p q else 0) + (if q < p then f p q else 0) +
      (if p = q then f p q else 0) := by
    intro p q
    rcases lt_trichotomy p q with h | rfl | h
    · simp [h, lt_asymm h, h.ne]
    · simp
    · simp [h, lt_asymm h, h.ne']
  have h3 : ∑ p, ∑ q, f p q = ∑ p, ∑ q, (if p < q then f p q else 0) +
      ∑ p, ∑ q, (if q < p then f p q else 0) + ∑ p, f p p := by
    refine (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hsplit p q).trans ?_
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h4 : ∑ p, ∑ q, (if q < p then f p q else 0) = ∑ p, ∑ q, (if p < q then f p q else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hf]
  have h5 : ∀ p, ∑ q ∈ Finset.Ioi p, f p q = ∑ q, (if p < q then f p q else 0) := fun p => by
    rw [← Finset.filter_lt_eq_Ioi, Finset.sum_filter]
  rw [h1, h2, h3, h4, Finset.sum_congr rfl fun p _ => h5 p]
  ring

/-- **The clique bound**. For a symmetric `m × m` matrix `M`, `m ≥ 2`, any diagonal, and
a sign vector `s`: `spr (M) ≥ 2 |Σ_{p<q} s_p s_q M_pq| / (m - 1)`. -/
theorem clique_bound (hm : 2 ≤ m) {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.IsSymm)
    {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) :
    2 * |∑ p, ∑ q ∈ Finset.Ioi p, s p * s q * M p q| / ((m : ℝ) - 1) ≤ spr M := by
  have h := abs_dotProduct_sub_trace_le (by omega) M hs
  rw [dotProduct_sub_trace_eq hM hs, abs_mul, abs_two] at h
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [div_le_iff₀ hm1]
  linarith

/-- **The clique bound for prescribed off-diagonal entries**. If `M p q = b s_p s_q` for
all `p ≠ q` (`m ≥ 2`, any diagonal), then `spr (M) ≥ m |b|`. -/
theorem spr_ge_of_offDiag (hm : 2 ≤ m) {M : Matrix (Fin m) (Fin m) ℝ} {s : Fin m → ℝ}
    (hs : ∀ p, s p = 1 ∨ s p = -1) {b : ℝ} (hb : ∀ p q, p ≠ q → M p q = b * s p * s q) :
    m * |b| ≤ spr M := by
  have h := abs_dotProduct_sub_trace_le (by omega) M hs
  have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hrow : ∀ p, s p * (M *ᵥ s) p - M p p = b * ((m : ℝ) - 1) := by
    intro p
    simp only [mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hq : ∀ q ∈ Finset.univ.erase p, M p q * s q = b * s p := fun q hq => by
      rw [hb p q (Finset.ne_of_mem_erase hq).symm, mul_assoc, ← sq, sq_eq_one_of_sign (hs q),
        mul_one]
    rw [Finset.sum_congr rfl hq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
    linear_combination (M p p + ((m : ℝ) - 1) * b) * sq_eq_one_of_sign (hs p)
  have e : s ⬝ᵥ (M *ᵥ s) - M.trace = (m : ℝ) * (b * ((m : ℝ) - 1)) := by
    rw [dotProduct, Matrix.trace, ← Finset.sum_sub_distrib]
    simp only [Matrix.diag, hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [e, abs_mul, abs_mul, abs_of_pos hm1, Nat.abs_cast] at h
  nlinarith

end Clique

/-! ### The star: attainment -/

section Star

/-- The off-diagonal entries of the star matrix `b (s sᵀ - 1)`. -/
theorem star_apply_ne (s : Fin m → ℝ) (b : ℝ) {p q : Fin m} (hpq : p ≠ q) :
    (b • (vecMulVec s s - 1)) p q = b * s p * s q := by
  rw [Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply_ne hpq, sub_zero,
    smul_eq_mul, mul_assoc]

/-- The star matrix is symmetric. -/
theorem isSymm_star (s : Fin m → ℝ) (b : ℝ) : (b • (vecMulVec s s - 1)).IsSymm := by
  refine IsSymm.smul (IsSymm.sub ?_ isSymm_one) b
  unfold Matrix.IsSymm
  rw [transpose_vecMulVec]

/-- The form of the star matrix: `⟪x, b (s sᵀ - 1) x⟫ = b ((s ⬝ᵥ x)² - ‖x‖²)`. -/
theorem inner_opE_star (s : Fin m → ℝ) (b : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ⟪x, opE (b • (vecMulVec s s - 1)) x⟫ = b * ((s ⬝ᵥ WithLp.ofLp x) ^ 2 - ‖x‖ ^ 2) := by
  rw [inner_opE_eq_dotProduct, ← real_inner_self_eq_norm_sq, inner_eq_dotProduct, smul_mulVec,
    sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm (WithLp.ofLp x) s]
  ring

/-- Cauchy-Schwarz: `(s ⬝ᵥ x)² ≤ (s ⬝ᵥ s) ‖x‖²`. -/
theorem sq_dotProduct_le (s : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    (s ⬝ᵥ WithLp.ofLp x) ^ 2 ≤ (s ⬝ᵥ s) * ‖x‖ ^ 2 := by
  have h := real_inner_mul_inner_self_le (WithLp.toLp 2 s : EuclideanSpace ℝ (Fin m)) x
  rw [real_inner_self_eq_norm_sq x] at h
  simp only [inner_eq_dotProduct] at h
  rw [sq]
  exact h

/-- **The centred star has norm at most `m |b| / 2`:** `‖b (s sᵀ - 1) - c 1‖ ≤ m |b| / 2` for
`c = (m - 2) b / 2` and a sign vector `s`. -/
theorem norm_opE_star_sub_le {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) (b : ℝ) :
    ‖opE (b • (vecMulVec s s - 1) - (((m : ℝ) - 2) * b / 2) • 1)‖ ≤ m * |b| / 2 := by
  have hsym := (isSymm_star s b).sub (isSymm_one.smul (((m : ℝ) - 2) * b / 2))
  refine norm_opE_le_of_abs_inner_self_le hsym (by positivity) fun x => ?_
  rw [inner_opE_sub_smul_one, inner_opE_star]
  have hd := sq_dotProduct_le s x
  rw [dotProduct_self_of_sign hs] at hd
  have hd0 := sq_nonneg (s ⬝ᵥ WithLp.ofLp x)
  rw [abs_le]
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    have k := mul_le_mul_of_nonneg_left hd hb
    constructor <;> nlinarith
  · rw [abs_of_nonpos hb]
    have k := mul_le_mul_of_nonpos_left hd hb
    constructor <;> nlinarith

/-- **The spread of the star**: `spr (b (s sᵀ - 1)) = m |b|` for a sign vector `s` of
length `m ≥ 2` (eigenvalues `(m - 1) b` and `-b`). -/
theorem spr_star (hm : 2 ≤ m) {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) (b : ℝ) :
    spr (b • (vecMulVec s s - 1)) = m * |b| := by
  refine le_antisymm ?_ (spr_ge_of_offDiag hm hs fun p q hpq => star_apply_ne s b hpq)
  have h1 := spr_le_two_mul_norm_sub (b • (vecMulVec s s - 1)) (((m : ℝ) - 2) * b / 2)
  have h2 := norm_opE_star_sub_le hs b
  linarith

/-- **The norm of the centred star**: `‖b (s sᵀ - 1) - c 1‖ = m |b| / 2` for
`c = (m - 2) b / 2`, a sign vector `s` of length `m ≥ 2`. -/
theorem norm_star_sub_eq (hm : 2 ≤ m) {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) (b : ℝ) :
    ‖opE (b • (vecMulVec s s - 1) - (((m : ℝ) - 2) * b / 2) • 1)‖ = m * |b| / 2 := by
  refine le_antisymm (norm_opE_star_sub_le hs b) ?_
  have h := spr_le_two_mul_norm_sub (b • (vecMulVec s s - 1)) (((m : ℝ) - 2) * b / 2)
  rw [spr_star hm hs b] at h
  linarith

/-- **The least spread over all diagonals**: among the `m × m` matrices with the
off-diagonal entries `b s_p s_q` (`s` a sign vector, `m ≥ 2`) the least spread is `m |b|`. -/
theorem isLeast_spr_offDiag (hm : 2 ≤ m) {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1)
    (b : ℝ) :
    IsLeast {r | ∃ M : Matrix (Fin m) (Fin m) ℝ,
      (∀ p q, p ≠ q → M p q = b * s p * s q) ∧ r = spr M} (m * |b|) :=
  ⟨⟨_, fun p q hpq => star_apply_ne s b hpq, (spr_star hm hs b).symm⟩, by
    rintro _ ⟨M, hM, rfl⟩
    exact spr_ge_of_offDiag hm hs hM⟩

/-- **The least norm over all diagonals**: among the `m × m` matrices with the
off-diagonal entries `b s_p s_q` (`s` a sign vector, `m ≥ 2`) the least norm is `m |b| / 2`. -/
theorem isLeast_norm_offDiag (hm : 2 ≤ m) {s : Fin m → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1)
    (b : ℝ) :
    IsLeast {r | ∃ M : Matrix (Fin m) (Fin m) ℝ,
      (∀ p q, p ≠ q → M p q = b * s p * s q) ∧ r = ‖opE M‖} (m * |b| / 2) := by
  refine ⟨⟨_, fun p q hpq => ?_, (norm_star_sub_eq hm hs b).symm⟩, ?_⟩
  · rw [Matrix.sub_apply, star_apply_ne s b hpq, Matrix.smul_apply, Matrix.one_apply_ne hpq,
      smul_zero, sub_zero]
  · rintro _ ⟨M, hM, rfl⟩
    have h1 := spr_ge_of_offDiag hm hs hM
    have h2 := spr_le_two_mul_norm_sub M 0
    rw [zero_smul, sub_zero] at h2
    linarith

end Star

/-! ### Disjoint pairs -/

section Pairs

/-- **A spectrum symmetric about zero.** If a sign vector `σ` changes the sign of every nonzero
entry (`M p q ≠ 0 → σ_p σ_q = -1`), then `λ_max (M) + λ_min (M) = 0`. -/
theorem lamMax_add_lamMin_of_sign {M : Matrix (Fin n) (Fin n) ℝ} {σ : Fin n → ℝ}
    (hσ : ∀ p, σ p ^ 2 = 1) (hM : ∀ p q, M p q ≠ 0 → σ p * σ q = -1) :
    lamMax M + lamMin M = 0 := by
  have hform : ∀ x, ⟪opE (diagonal σ) x, opE M (opE (diagonal σ) x)⟫ = -⟪x, opE M x⟫ := by
    intro x
    rw [inner_opE_eq_sum, inner_opE_eq_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [opE_diagonal_apply, opE_diagonal_apply]
    by_cases h : M p q = 0
    · rw [h]
      ring
    · linear_combination (x p * M p q * x q) * hM p q h
  have hnorm : ∀ x, ‖opE (diagonal σ) x‖ = ‖x‖ := by
    intro x
    have h : ‖opE (diagonal σ) x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [opE_diagonal_apply, mul_pow, hσ, one_mul]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  rcases isEmpty_or_nonempty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with h | h
  · rw [(lamMax_lamMin_of_isEmpty M).1, (lamMax_lamMin_of_isEmpty M).2, add_zero]
  · have h1 : lamMax M ≤ -lamMin M := lamMax_le_of fun x => by
      have h2 := lamMin_le_inner M (opE (diagonal σ) x)
      rw [hform, hnorm] at h2
      linarith
    have h2 : -lamMax M ≤ lamMin M := le_lamMin_of fun x => by
      have h3 := inner_le_lamMax M (opE (diagonal σ) x)
      rw [hform, hnorm] at h3
      linarith
    linarith

/-- **The norm of a pair block**. If `A` has its rows on one side and its columns on the
other (`A p q ≠ 0 → side p ∧ ¬ side q`), then `‖A + Aᵀ‖ = ‖A‖`; `A + Aᵀ` is the block
`[[0, F], [Fᵀ, 0]]` after a permutation. -/
theorem norm_opE_add_transpose_of_side (side : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, A p q ≠ 0 → side p = true ∧ side q = false) :
    ‖opE (A + Aᵀ)‖ = ‖opE A‖ := by
  let N : Bool → Matrix (Fin n) (Fin n) ℝ := fun b => bif b then A else Aᵀ
  have hrow : ∀ b p q, side p ≠ b → N b p q = 0 := by
    intro b p q hp
    cases b
    · show A q p = 0
      by_contra h
      exact hp (hA q p h).2
    · show A p q = 0
      by_contra h
      exact hp (hA p q h).1
  have hAA : A * A = 0 := by
    ext p q
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases h1 : A p r = 0
    · rw [h1, zero_mul]
    · by_cases h2 : A r q = 0
      · rw [h2, mul_zero]
      · exact absurd ((hA p r h1).2.symm.trans (hA r q h2).1) Bool.false_ne_true
  have horth : ∀ b c, b ≠ c → N b * (N c)ᵀ = 0 := by
    intro b c hbc
    cases b <;> cases c
    · exact absurd rfl hbc
    · show Aᵀ * Aᵀ = 0
      rw [← transpose_mul, hAA, transpose_zero]
    · show A * Aᵀᵀ = 0
      rw [transpose_transpose, hAA]
    · exact absurd rfl hbc
  have h := norm_opE_sum_eq_iSup side N hrow horth
  have hsum : ∑ b, N b = A + Aᵀ := by
    rw [Fintype.sum_bool]
    rfl
  have hN : ∀ b, ‖opE (N b)‖ = ‖opE A‖ := by
    intro b
    cases b
    · exact norm_opE_transpose A
    · rfl
  rw [hsum] at h
  rw [h]
  simp only [hN, ciSup_const]

/-- **The spread of a pair block**: `spr (A + Aᵀ) = 2 ‖A‖` for `A` with its rows on one
side and its columns on the other. -/
theorem spr_add_transpose_of_side (side : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ p q, A p q ≠ 0 → side p = true ∧ side q = false) :
    spr (A + Aᵀ) = 2 * ‖opE A‖ := by
  have hsym : (A + Aᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_add, transpose_transpose, add_comm]
  have hσ : ∀ p, (fun p => if side p then (1 : ℝ) else -1) p ^ 2 = 1 := fun p => by
    by_cases h : side p <;> simp [h]
  have hM : ∀ p q, (A + Aᵀ) p q ≠ 0 →
      (fun p => if side p then (1 : ℝ) else -1) p * (fun p => if side p then (1 : ℝ) else -1) q
        = -1 := by
    intro p q hpq
    rw [Matrix.add_apply, Matrix.transpose_apply] at hpq
    by_cases h1 : A p q = 0
    · rw [h1, zero_add] at hpq
      obtain ⟨hq, hp⟩ := hA q p hpq
      simp [hq, hp]
    · obtain ⟨hp, hq⟩ := hA p q h1
      simp [hp, hq]
  rw [spr_eq_two_mul_norm_of_add_eq_zero hsym (lamMax_add_lamMin_of_sign hσ hM),
    norm_opE_add_transpose_of_side side hA]

/-- **Disjoint pairs**. Let `A_k` have its rows in the set `{blk = k, side}` and its
columns in `{blk = k, ¬ side}`, so that all the row and column sets are pairwise disjoint. Then
`M = Σ_k (A_k + A_kᵀ)`, a direct sum of the blocks `[[0, F_k], [F_kᵀ, 0]]` and a zero block after
a permutation, has `‖M‖ = max_k ‖A_k‖` and `spr (M) = 2 max_k ‖A_k‖`. -/
theorem pair_blocks {κ : Type*} [Fintype κ] [DecidableEq κ] (blk : Fin n → κ)
    (side : Fin n → Bool) (A : κ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k p q, A k p q ≠ 0 → blk p = k ∧ blk q = k ∧ side p = true ∧ side q = false) :
    ‖opE (∑ k, (A k + (A k)ᵀ))‖ = ⨆ k, ‖opE (A k)‖ ∧
      spr (∑ k, (A k + (A k)ᵀ)) = 2 * ⨆ k, ‖opE (A k)‖ := by
  have hB : ∑ k, (A k + (A k)ᵀ) = (∑ k, A k) + (∑ k, A k)ᵀ := by
    rw [Finset.sum_add_distrib, transpose_sum]
  have hBs : ∀ p q, (∑ k, A k) p q ≠ 0 → side p = true ∧ side q = false := by
    intro p q h
    rw [Matrix.sum_apply] at h
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨(hA k p q hk).2.2.1, (hA k p q hk).2.2.2⟩
  have hnB : ‖opE (∑ k, A k)‖ = ⨆ k, ‖opE (A k)‖ := by
    refine norm_opE_sum_eq_iSup blk A (fun k p q hp => ?_) (fun k j hkj => ?_)
    · by_contra h
      exact hp (hA k p q h).1
    · ext p q
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [Matrix.transpose_apply]
      by_cases h1 : A k p r = 0
      · rw [h1, zero_mul]
      · by_cases h2 : A j q r = 0
        · rw [h2, mul_zero]
        · exact absurd ((hA k p r h1).2.1.symm.trans (hA j q r h2).2.1) hkj
  rw [hB, norm_opE_add_transpose_of_side side hBs, spr_add_transpose_of_side side hBs, hnB]
  exact ⟨rfl, rfl⟩

end Pairs

/-! ### The chain without injection -/

section Chain

/-- The matrix element of `e_a e_bᵀ`: `⟪x, e_a e_bᵀ y⟫ = x_a y_b`. -/
theorem inner_opE_single (a b : Fin n) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (single a b (1 : ℝ)) y⟫ = x a * y b := by
  rw [inner_opE_eq_sum, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · rw [single_apply_same, mul_one]
  · intro q _ hq
    rw [single_apply_of_col_ne _ _ (Ne.symm hq), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    exact Finset.sum_eq_zero fun q _ => by
      rw [single_apply_of_row_ne (Ne.symm hp), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Two coordinates of a vector: `x_i² + x_j² ≤ ‖x‖²` for `i ≠ j`. -/
theorem sq_add_sq_le_norm_sq {i j : Fin n} (hij : i ≠ j) (x : EuclideanSpace ℝ (Fin n)) :
    x i ^ 2 + x j ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j})
    (fun k _ _ => sq_nonneg (x k))
  rw [Finset.sum_pair hij] at h
  rw [EuclideanSpace.real_norm_sq_eq]
  exact h

/-- The form on `e_i + t e_j`. -/
theorem inner_opE_unitE_add (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (t : ℝ) :
    ⟪unitE i + t • unitE j, opE M (unitE i + t • unitE j)⟫ =
      M i i + t * (M i j + M j i) + t ^ 2 * M j j := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_unitE_opE]
  ring

/-- `‖e_i + t e_j‖² = 1 + t²` for `i ≠ j`. -/
theorem norm_unitE_add_sq {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    ‖unitE i + t • unitE j‖ ^ 2 = 1 + t ^ 2 := by
  have h := inner_opE_unitE_add (1 : Matrix (Fin n) (Fin n) ℝ) i j t
  rw [opE_one, one_apply_eq_self, real_inner_self_eq_norm_sq, Matrix.one_apply_eq,
    Matrix.one_apply_eq, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)] at h
  linarith

/-- **The non-injection value of the chain**. If `⟪x, M x⟫ ≤ 0` for all `x` (`sym M ⪯ 0`)
and `M i j = M j i = p` for `i ≠ j`, then `‖M‖ ≥ 2 |p|`. -/
theorem two_mul_abs_le_norm_of_form_nonpos {M : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n}
    (hij : i ≠ j) {p : ℝ} (hpij : M i j = p) (hpji : M j i = p)
    (hneg : ∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE M x⟫ ≤ 0) : 2 * |p| ≤ ‖opE M‖ := by
  have form : ∀ t : ℝ, t ^ 2 = 1 →
      ⟪unitE i + t • unitE j, opE M (unitE i + t • unitE j)⟫ = M i i + 2 * t * p + M j j := by
    intro t ht
    rw [inner_opE_unitE_add, hpij, hpji, ht]
    ring
  have key : ∀ t : ℝ, t ^ 2 = 1 → |M i i + 2 * t * p + M j j| ≤ 2 * ‖opE M‖ := by
    intro t ht
    have h := abs_inner_opE_self_le M (unitE i + t • unitE j)
    rw [form t ht, norm_unitE_add_sq hij, ht] at h
    linarith
  have h1 := hneg (unitE i + (1 : ℝ) • unitE j)
  have h2 := hneg (unitE i + (-1 : ℝ) • unitE j)
  rw [form 1 (by norm_num)] at h1
  rw [form (-1) (by norm_num)] at h2
  have k1 := key 1 (by norm_num)
  have k2 := key (-1) (by norm_num)
  have a1 := neg_abs_le (M i i + 2 * 1 * p + M j j)
  have a2 := neg_abs_le (M i i + 2 * (-1) * p + M j j)
  rcases le_total 0 p with hp | hp
  · rw [abs_of_nonneg hp]
    linarith
  · rw [abs_of_nonpos hp]
    linarith

/-- The matrix `-|p| (e_i e_iᵀ + e_j e_jᵀ) + p (e_i e_jᵀ + e_j e_iᵀ)` (the minimiser of the
chain without injection). -/
noncomputable def chainMin (i j : Fin n) (p : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (-|p|) • (single i i 1 + single j j 1) + p • (single i j 1 + single j i 1)

/-- The skew matrix `p (e_i e_jᵀ - e_j e_iᵀ)`. -/
noncomputable def chainSkew (i j : Fin n) (p : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  p • (single i j 1 - single j i 1)

/-- The form of `chainMin i j p`: `-|p| (x_i² + x_j²) + 2 p x_i x_j`. -/
theorem inner_chainMin (i j : Fin n) (p : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (chainMin i j p) x⟫ = -|p| * (x i ^ 2 + x j ^ 2) + 2 * p * (x i * x j) := by
  simp only [chainMin, inner_opE_add, inner_opE_smul, inner_opE_single]
  ring

/-- **The minimiser of the chain without injection**: the matrix
`chainMin i j p = -|p| (e_i e_iᵀ + e_j e_jᵀ) + p (e_i e_jᵀ + e_j e_iᵀ)` has the entries `p` at
`(i, j)` and `(j, i)` and a form `≤ 0`. -/
theorem chainMin_form_nonpos {i j : Fin n} (hij : i ≠ j) (p : ℝ) :
    chainMin i j p i j = p ∧ chainMin i j p j i = p ∧
      ∀ x : EuclideanSpace ℝ (Fin n), ⟪x, opE (chainMin i j p) x⟫ ≤ 0 := by
  refine ⟨by simp [chainMin, hij, Ne.symm hij],
    by simp [chainMin, hij, Ne.symm hij], fun x => ?_⟩
  rw [inner_chainMin]
  rcases le_total 0 p with hp | hp
  · rw [abs_of_nonneg hp]
    nlinarith [mul_nonneg hp (sq_nonneg (x i - x j))]
  · rw [abs_of_nonpos hp]
    nlinarith [mul_nonneg (neg_nonneg.2 hp) (sq_nonneg (x i + x j))]

/-- **The non-injection value of the chain is attained**: `‖chainMin i j p‖ = 2 |p|`. -/
theorem norm_chainMin {i j : Fin n} (hij : i ≠ j) (p : ℝ) :
    ‖opE (chainMin i j p)‖ = 2 * |p| := by
  obtain ⟨h1, h2, h3⟩ := chainMin_form_nonpos hij p
  refine le_antisymm ?_ (two_mul_abs_le_norm_of_form_nonpos hij h1 h2 h3)
  have hsym : (chainMin i j p).IsSymm := by
    unfold Matrix.IsSymm chainMin
    simp only [transpose_add, transpose_smul, transpose_single]
    rw [add_comm (single j i (1 : ℝ))]
  refine norm_opE_le_of_abs_inner_self_le hsym (by positivity) fun x => ?_
  have hx := sq_add_sq_le_norm_sq hij x
  have hle := h3 x
  rw [inner_chainMin] at hle ⊢
  rw [abs_le]
  constructor
  · rcases le_total 0 p with hp | hp
    · rw [abs_of_nonneg hp]
      nlinarith [mul_nonneg hp (sq_nonneg (x i + x j)), mul_le_mul_of_nonneg_left hx hp]
    · rw [abs_of_nonpos hp]
      nlinarith [mul_nonneg (neg_nonneg.2 hp) (sq_nonneg (x i - x j)),
        mul_le_mul_of_nonpos_left hx hp]
  · nlinarith [mul_nonneg (abs_nonneg p) (sq_nonneg ‖x‖)]

/-- **The skew matrix of the chain**: `chainSkew i j p = p (e_i e_jᵀ - e_j e_iᵀ)` has the
form `0` (`sym = 0`). -/
theorem inner_chainSkew_self (i j : Fin n) (p : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (chainSkew i j p) x⟫ = 0 := by
  rw [chainSkew, inner_opE_smul, inner_opE_sub, inner_opE_single, inner_opE_single]
  ring

/-- The entry `(i, j)` of `chainSkew i j p` is `p`, the entry `(j, i)` is `-p` (`i ≠ j`). -/
theorem chainSkew_apply {i j : Fin n} (hij : i ≠ j) (p : ℝ) :
    chainSkew i j p i j = p ∧ chainSkew i j p j i = -p := by
  constructor <;> simp [chainSkew, hij, Ne.symm hij]

/-- **The skew matrix of the chain**: `‖chainSkew i j p‖ = |p|` for `i ≠ j`. -/
theorem norm_chainSkew {i j : Fin n} (hij : i ≠ j) (p : ℝ) :
    ‖opE (chainSkew i j p)‖ = |p| := by
  rw [chainSkew]
  refine le_antisymm (norm_opE_le_of_abs_inner_le (abs_nonneg p) fun x y => ?_) ?_
  · rw [inner_opE_smul, inner_opE_sub, inner_opE_single, inner_opE_single, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg p)
    have hx := sq_add_sq_le_norm_sq hij x
    have hy := sq_add_sq_le_norm_sq hij y
    have hsq : (x i * y j - x j * y i) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
      have hl : (x i * y j - x j * y i) ^ 2 ≤ (x i ^ 2 + x j ^ 2) * (y i ^ 2 + y j ^ 2) := by
        nlinarith [sq_nonneg (x i * y i + x j * y j)]
      rw [mul_pow]
      exact hl.trans (mul_le_mul hx hy (by positivity) (sq_nonneg _))
    exact abs_le_of_sq_le_sq hsq (by positivity)
  · have h := abs_inner_opE_le (p • (single i j (1 : ℝ) - single j i 1)) (unitE i) (unitE j)
    rw [inner_unitE_opE, norm_unitE, norm_unitE, mul_one, mul_one] at h
    rw [Matrix.smul_apply, Matrix.sub_apply, single_apply_same,
      single_apply_of_row_ne (Ne.symm hij),
      sub_zero, smul_eq_mul, mul_one] at h
    exact h

end Chain

end CoSimFoundations
