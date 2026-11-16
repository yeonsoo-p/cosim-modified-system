/-
An error behind a port, with an explicit remainder (the paper, Proposition 5.1
`prop:onesided`, equations `eq:onesided` and `eq:return`; the paper states them "+ O(H³)").

Setting of `ForcedBlock` and `Reaction`: a `HeldScheme` on the states `Fin n`, which `sub` groups
into subsystems, so that a subsystem may have several states; `U = exp (H • A)`; spectral norms.
The scheme carries the products `M = G^old C`, `N = G^new C`, not the port matrices `B_j`. The
kernel of `B_jᵀ` is therefore expressed by what it implies (`Hidden`): a vector `v` supported on
the subsystem `t` is *hidden* if `M v = 0`, `N v = 0` (the samples do not show it) and `A v` is
supported on `t` (`A_{kt} v = B_k L_{kt} B_tᵀ v = 0` for `k ≠ t`). `Hidden.of_ports` derives this
from a factorisation `M = G^old C`, `N = G^new C`, `A = B L C` between different subsystems and
`C v = 0`, which is the paper's `B_tᵀ v_t = 0` for `C = diag(B_kᵀ)`.

1. **The block towards the partner** (`Consistent.one_sided`, `eq:onesided`). `s ≠ t`, `x`
   supported on `s`, `v` hidden in `t`:
     `|⟪x, (X - U) v⟫ - ½H² ς_{st} ⟪x, A (A v)⟫| ≤ C₃ H³ ‖x‖ ‖v‖`,   `C₃ = reactionC a b c ‖A‖ H`.
   Since `A v = A_t v` lies in `t`, `⟪x, A (A v)⟫ = ⟪x, A_{st} A_t v⟫`: this is
   `Π_s (X - U) Π_tᵀ Θ_t = ½H² ς_{st} A_{st} A_t Θ_t + O(H³)`.
   Proof: the row identity of `Reaction` (`Consistent.reaction_row`), in which `(M + N) v = 0`,
   `Π_s (F - 1 - H A) v = 0`, and `ς_s A v = ς_{st} A v`.
   The hypothesis that `s` and `t` are partners is not needed (for non-partners `A_{st} = 0`).

2. **The opposite block** (`Consistent.opposite_block`). If moreover `A_{kl} = -A_{lk}ᵀ` between
   different subsystems (`hskew`), then
     `|⟪v, (X - U) x⟫ - ⟪v, (M + N) x⟫ + ½H² ⟪v, A (A x)⟫| ≤ C₃ H³ ‖v‖ ‖x‖`,
   that is `Θ_t Π_t (X - U) Π_sᵀ = (Θ_t G_{ts} - ½H² Θ_t A_t B_t L_{ts}) B_sᵀ + O(H³)`:
   `⟪v, (M + N) x⟫ = vᵀ G_{ts} B_sᵀ x` is the coefficient row, which is not prescribed.
   Proof: the row identity for the rows of `t`; `vᵀ A` is supported on `t`, where `ς_t = -1`.

3. **Returning the error** (`Consistent.returned_block`, `Consistent.one_sided_sym`). If the
   coefficient row obeys `eq:return` up to `c_G H³`,
     `|⟪v, (M + N) x⟫ - ½H² (⟪v, A (A x)⟫ + ς_{st} ⟪A v, A x⟫)| ≤ c_G H³ ‖v‖ ‖x‖`
   (`Θ_t G_{ts} B_sᵀ = ½H² Θ_t (A_t + ς_{st} A_tᵀ) B_t L_{ts} B_sᵀ + O(H³)`), then
     `|⟪v, (X - U) x⟫ + ½H² ς_{st} ⟪x, A (A v)⟫| ≤ (C₃ + c_G) H³ ‖x‖ ‖v‖`:
   the opposite block is the negative transpose of the block of 1., and
     `|⟪x, (X - U) v⟫ + ⟪v, (X - U) x⟫| ≤ (2 C₃ + c_G) H³ ‖x‖ ‖v‖`:
   the symmetric part of the pair vanishes to the order `H²`.

4. **The algebra, with the port matrices** (`return_identity`). For real matrices `A_j`, `B_j`,
   `L_{ji}`, `B_i`, a symmetric `Θ`, `L_{ij} = -L_{ji}ᵀ` and `G = ½H² (A_j + ς A_jᵀ) B_j L_{ji}`:
     `(Θ G - ½H² Θ A_j B_j L_{ji}) B_iᵀ = -(½H² ς A_{ij} A_j Θ)ᵀ`,   `A_{ij} = B_i L_{ij} B_jᵀ`.
-/
import CoSimFoundations.ReactionDiag

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

namespace OneStep

variable {n : ℕ}

/-- The matrix element as a sum over the columns: `⟪v, T w⟫ = Σ_q (vᵀ T)_q w_q`. -/
theorem inner_opE_eq_sum_col (T : Matrix (Fin n) (Fin n) ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪v, opE T w⟫ = ∑ q, (∑ p, v p * T p q) * w q := by
  rw [inner_opE_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]

/-- A product `G C` annihilates the vectors that `C` annihilates, in components. -/
theorem sum_mul_apply_eq_zero {m : ℕ} (G : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) {v : Fin n → ℝ} (hC : ∀ j, ∑ q, C j q * v q = 0)
    (p : Fin n) : ∑ q, (G * C) p q * v q = 0 := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp only [mul_assoc]
  rw [← Finset.mul_sum, hC j, mul_zero]

end OneStep

open OneStep

variable {n : ℕ}

namespace HeldScheme

variable {κ : Type*} (S : HeldScheme n κ)

/-- A state `v` of the subsystem `t` that its output does not show (the paper: `v = Θ_t v`, in
the kernel of `B_tᵀ`), expressed through the scheme and the monolithic system: no sample shows
it, `M v = 0` and `N v = 0`, and it does not act on the other subsystems, `A_{kt} v = 0`. -/
structure Hidden (A : Matrix (Fin n) (Fin n) ℝ) (t : κ) (v : EuclideanSpace ℝ (Fin n)) :
    Prop where
  /-- `v` is a state of the subsystem `t` -/
  supp : ∀ q, S.sub q ≠ t → v q = 0
  /-- the old samples do not show `v` -/
  hM : ∀ p, (opE S.M v) p = 0
  /-- the new samples do not show `v` -/
  hN : ∀ p, (opE S.N v) p = 0
  /-- `A v` is a state of the subsystem `t`: `A_{kt} v = 0` for `k ≠ t` -/
  hA : ∀ p, S.sub p ≠ t → (opE A v) p = 0

variable {S}

/-- **Hidden states from the port matrices.** If `M = G^old C`, `N = G^new C` and, between
different subsystems, `A = B L C` (`C = diag(B_kᵀ)` the outputs), then every `v` supported on a
subsystem `t` with `C v = 0` (that is, `B_tᵀ v_t = 0`) is hidden. -/
theorem Hidden.of_ports {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {C : Matrix (Fin m) (Fin n) ℝ}
    {Gold Gnew BL : Matrix (Fin n) (Fin m) ℝ} (hM : S.M = Gold * C) (hN : S.N = Gnew * C)
    (hA : ∀ p q, S.sub p ≠ S.sub q → A p q = (BL * C) p q) {t : κ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : ∀ q, S.sub q ≠ t → v q = 0)
    (hC : ∀ j, ∑ q, C j q * v q = 0) : S.Hidden A t v := by
  refine ⟨hv, fun p => ?_, fun p => ?_, fun p hp => ?_⟩
  · rw [opE_apply, hM]
    exact sum_mul_apply_eq_zero Gold C hC p
  · rw [opE_apply, hN]
    exact sum_mul_apply_eq_zero Gnew C hC p
  · rw [opE_apply, ← sum_mul_apply_eq_zero BL C hC p]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : S.sub q = t
    · rw [hA p q (by rw [hq]; exact hp)]
    · rw [hv q hq, mul_zero, mul_zero]

/-- The samples carry nothing of a hidden state. -/
theorem Hidden.inner_coupling {A : Matrix (Fin n) (Fin n) ℝ} {t : κ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : S.Hidden A t v) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.M + S.N) v⟫ = 0 := by
  rw [inner_opE_add, inner_eq_sum, inner_eq_sum]
  simp [hv.hM, hv.hN]

/-- A hidden state of `t` does not act on another subsystem `s` to first order. -/
theorem Hidden.inner_A {A : Matrix (Fin n) (Fin n) ℝ} {s t : κ} (hst : s ≠ t)
    {x v : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hv : S.Hidden A t v) : ⟪x, opE A v⟫ = 0 := by
  rw [inner_eq_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : S.sub p = t
  · rw [hx p (by rw [hp]; exact hst.symm), zero_mul]
  · rw [hv.hA p hp, mul_zero]

/-- On the image `A v` of a hidden state of `t`, the signs `ς_s` are the constant `ς_{st}`. -/
theorem Hidden.sgn_apply {A : Matrix (Fin n) (Fin n) ℝ} {t : κ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : S.Hidden A t v) (s : κ) :
    opE (S.sgn s) (opE A v) = S.sg s t • opE A v := by
  ext r
  have e : (opE (S.sgn s) (opE A v)) r = S.sg s (S.sub r) * (opE A v) r :=
    opE_diagonal_apply _ _ r
  rw [e, PiLp.smul_apply, smul_eq_mul]
  by_cases hr : S.sub r = t
  · rw [hr]
  · rw [hv.hA r hr, mul_zero, mul_zero]

/-- **An error behind a port** (Proposition 5.1, `eq:onesided`, with its remainder). For a
consistent scheme with one held sample, in any order of execution, `x` supported on a subsystem
`s` and `v` a hidden state of another subsystem `t`:
`|⟪x, (X - U) v⟫ - ½H² ς_{st} ⟪x, A (A v)⟫| ≤ C₃ H³ ‖x‖ ‖v‖`, `C₃ = reactionC a b c ‖A‖ H`;
`⟪x, A (A v)⟫ = ⟪x, A_{st} A_t v⟫`. Whatever the coefficients. -/
theorem Consistent.one_sided {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) {s t : κ} (hst : s ≠ t) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hv : S.Hidden A t v) :
    |⟪x, opE (S.X - U) v⟫ - H ^ 2 / 2 * (S.sg s t * ⟪x, opE A (opE A v)⟫)| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖v‖) := by
  have h1 := h.reaction_row hx v
  have hF : ⟪x, opE S.F v⟫ = 0 :=
    inner_opE_eq_zero hx hv.supp fun p q hp hq => S.hF p q (by rw [hp, hq]; exact hst)
  have hI : ⟪x, opE (1 : Matrix (Fin n) (Fin n) ℝ) v⟫ = 0 :=
    inner_opE_eq_zero hx hv.supp fun p q hp hq =>
      Matrix.one_apply_ne fun e => hst (by rw [← hp, ← hq, e])
  have h0 : ⟪x, opE (S.F - 1 - H • A) v⟫ = 0 := by
    rw [inner_opE_sub, inner_opE_sub, inner_opE_smul, hF, hI, hv.inner_A hst hx]
    ring
  have h2 : ⟪x, opE (A * S.sgn s * A) v⟫ = S.sg s t * ⟪x, opE A (opE A v)⟫ := by
    rw [opE_mul_apply, opE_mul_apply, hv.sgn_apply s, map_smul, inner_smul_right]
  rwa [h0, sub_zero, hv.inner_coupling x, sub_zero, h2] at h1

/-- With `A_{kl} = -A_{lk}ᵀ` between different subsystems, a hidden state of `t` is not driven
by the other subsystems: `vᵀ A` is supported on `t`. -/
theorem Hidden.left {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {t : κ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : S.Hidden A t v) {q : Fin n} (hq : S.sub q ≠ t) :
    ∑ p, v p * A p q = 0 := by
  have h := hv.hA q hq
  rw [opE_apply] at h
  have e : ∑ p, v p * A p q = -∑ p, A q p * v p := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : S.sub p = t
    · rw [hskew q p (by rw [hp]; exact hq)]
      ring
    · rw [hv.supp p hp]
      ring
  rw [e, h, neg_zero]

/-- A hidden state of `t` is not driven by another subsystem `s` to first order. -/
theorem Hidden.inner_A_left {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {s t : κ} (hst : s ≠ t)
    {x v : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ s → x p = 0)
    (hv : S.Hidden A t v) : ⟪v, opE A x⟫ = 0 := by
  rw [inner_opE_eq_sum_col]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : S.sub q = t
  · rw [hx q (by rw [hq]; exact hst.symm), mul_zero]
  · rw [hv.left hskew hq, zero_mul]

/-- In the rows of a hidden state of `t`, `A ς_t A = -A A`: only the subsystem `t` itself
contributes, with the sign `-1`. -/
theorem Hidden.inner_sgn_left {A : Matrix (Fin n) (Fin n) ℝ}
    (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q) {t : κ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : S.Hidden A t v) (w : EuclideanSpace ℝ (Fin n)) :
    ⟪v, opE (A * S.sgn t * A) w⟫ = -⟪v, opE A (opE A w)⟫ := by
  rw [opE_mul_apply, opE_mul_apply, inner_opE_eq_sum_col, inner_opE_eq_sum_col,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have e : (opE (S.sgn t) (opE A w)) q = S.sg t (S.sub q) * (opE A w) q :=
    opE_diagonal_apply _ _ q
  rw [e]
  by_cases hq : S.sub q = t
  · have e2 : S.sg t (S.sub q) = -1 := by
      rw [hq]
      simp [sg]
    rw [e2]
    ring
  · rw [hv.left hskew hq]
    ring

/-- **The opposite block** (Proposition 5.1, second statement, with its remainder). `x`
supported on `s`, `v` a hidden state of `t ≠ s`, `A_{kl} = -A_{lk}ᵀ` between different
subsystems: `|⟪v, (X - U) x⟫ - ⟪v, (M + N) x⟫ + ½H² ⟪v, A (A x)⟫| ≤ C₃ H³ ‖v‖ ‖x‖`. Here
`⟪v, (M + N) x⟫ = vᵀ G_{ts} B_sᵀ x` is the coefficient row on the hidden states, which the class
does not prescribe, and `⟪v, A (A x)⟫ = vᵀ A_t A_{ts} x`. -/
theorem Consistent.opposite_block {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s t : κ} (hst : s ≠ t) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hv : S.Hidden A t v) :
    |⟪v, opE (S.X - U) x⟫ - ⟪v, opE (S.M + S.N) x⟫ + H ^ 2 / 2 * ⟪v, opE A (opE A x)⟫| ≤
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖v‖ * ‖x‖) := by
  have h1 := h.reaction_row hv.supp x
  have hF : ⟪v, opE S.F x⟫ = 0 :=
    inner_opE_eq_zero hv.supp hx fun p q hp hq => S.hF p q (by rw [hp, hq]; exact hst.symm)
  have hI : ⟪v, opE (1 : Matrix (Fin n) (Fin n) ℝ) x⟫ = 0 :=
    inner_opE_eq_zero hv.supp hx fun p q hp hq =>
      Matrix.one_apply_ne fun e => hst (by rw [← hp, ← hq, e])
  have h0 : ⟪v, opE (S.F - 1 - H • A) x⟫ = 0 := by
    rw [inner_opE_sub, inner_opE_sub, inner_opE_smul, hF, hI, hv.inner_A_left hskew hst hx]
    ring
  rwa [h0, sub_zero, hv.inner_sgn_left hskew x, mul_neg, sub_neg_eq_add] at h1

/-- **Returning the error** (Proposition 5.1, `eq:return`, with its remainder). If the
coefficient row on the hidden states obeys `eq:return` up to `c_G H³`, that is
`vᵀ G_{ts} B_sᵀ x = ½H² (vᵀ A_t A_{ts} x + ς_{st} (A_t v)ᵀ A_{ts} x) + O(H³)`, then the opposite
block is the negative transpose of the block of `Consistent.one_sided`:
`|⟪v, (X - U) x⟫ + ½H² ς_{st} ⟪x, A (A v)⟫| ≤ (C₃ + c_G) H³ ‖x‖ ‖v‖`. -/
theorem Consistent.returned_block {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c cG : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s t : κ} (hst : s ≠ t) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hv : S.Hidden A t v)
    (hret : |⟪v, opE (S.M + S.N) x⟫ - H ^ 2 / 2 * (⟪v, opE A (opE A x)⟫ +
      S.sg s t * ⟪opE A v, opE A x⟫)| ≤ cG * H ^ 3 * (‖v‖ * ‖x‖)) :
    |⟪v, opE (S.X - U) x⟫ + H ^ 2 / 2 * (S.sg s t * ⟪x, opE A (opE A v)⟫)| ≤
      (reactionC a b c ‖opE A‖ H + cG) * H ^ 3 * (‖x‖ * ‖v‖) := by
  have h1 := h.opposite_block hskew hst hx hv
  have hsk : ⟪x, opE A (opE A v)⟫ = -⟪opE A v, opE A x⟫ := by
    rw [real_inner_comm (opE A x) (opE A v)]
    exact S.inner_opE_skew hskew hx fun r hr => hv.hA r (by rw [hr]; exact hst)
  have e : ⟪v, opE (S.X - U) x⟫ + H ^ 2 / 2 * (S.sg s t * ⟪x, opE A (opE A v)⟫) =
      (⟪v, opE (S.X - U) x⟫ - ⟪v, opE (S.M + S.N) x⟫ + H ^ 2 / 2 * ⟪v, opE A (opE A x)⟫) +
      (⟪v, opE (S.M + S.N) x⟫ - H ^ 2 / 2 * (⟪v, opE A (opE A x)⟫ +
        S.sg s t * ⟪opE A v, opE A x⟫)) := by
    rw [hsk]
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have e2 : (reactionC a b c ‖opE A‖ H + cG) * H ^ 3 * (‖x‖ * ‖v‖) =
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖v‖ * ‖x‖) + cG * H ^ 3 * (‖v‖ * ‖x‖) := by ring
  rw [e2]
  exact add_le_add h1 hret

/-- **The returned error costs no energy to leading order** (Proposition 5.1, last statement).
Under the hypotheses of `Consistent.returned_block` the two blocks are opposite up to `O(H³)`:
`|⟪x, (X - U) v⟫ + ⟪v, (X - U) x⟫| ≤ (2 C₃ + c_G) H³ ‖x‖ ‖v‖`. -/
theorem Consistent.one_sided_sym {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c cG : ℝ}
    (h : S.Consistent A U H a b c) (hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q)
    {s t : κ} (hst : s ≠ t) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ s → x p = 0) (hv : S.Hidden A t v)
    (hret : |⟪v, opE (S.M + S.N) x⟫ - H ^ 2 / 2 * (⟪v, opE A (opE A x)⟫ +
      S.sg s t * ⟪opE A v, opE A x⟫)| ≤ cG * H ^ 3 * (‖v‖ * ‖x‖)) :
    |⟪x, opE (S.X - U) v⟫ + ⟪v, opE (S.X - U) x⟫| ≤
      (2 * reactionC a b c ‖opE A‖ H + cG) * H ^ 3 * (‖x‖ * ‖v‖) := by
  have h1 := h.one_sided hst hx hv
  have h2 := h.returned_block hskew hst hx hv hret
  have e : ⟪x, opE (S.X - U) v⟫ + ⟪v, opE (S.X - U) x⟫ =
      (⟪x, opE (S.X - U) v⟫ - H ^ 2 / 2 * (S.sg s t * ⟪x, opE A (opE A v)⟫)) +
      (⟪v, opE (S.X - U) x⟫ + H ^ 2 / 2 * (S.sg s t * ⟪x, opE A (opE A v)⟫)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have e2 : (2 * reactionC a b c ‖opE A‖ H + cG) * H ^ 3 * (‖x‖ * ‖v‖) =
      reactionC a b c ‖opE A‖ H * H ^ 3 * (‖x‖ * ‖v‖) +
      (reactionC a b c ‖opE A‖ H + cG) * H ^ 3 * (‖x‖ * ‖v‖) := by ring
  rw [e2]
  exact add_le_add h1 h2

end HeldScheme

section Ports

variable {ni nj mi mj : Type*} [Fintype ni] [Fintype nj] [Fintype mi] [Fintype mj]

/-- **The algebra of `eq:return`, with the port matrices.** `A_j` the partner, `B_j`, `B_i` the
ports, `L_{ij} = -L_{ji}ᵀ` the coupling, `Θ` symmetric (the projection onto the kernel of
`B_jᵀ`), `ς` a sign. With the coefficient rows `Θ G = ½H² Θ (A_j + ς A_jᵀ) B_j L_{ji}` the leading
term `(Θ G - ½H² Θ A_j B_j L_{ji}) B_iᵀ` of the opposite block is the negative transpose of
`½H² ς A_{ij} A_j Θ`, `A_{ij} = B_i L_{ij} B_jᵀ`. -/
theorem return_identity (H ς : ℝ) (Aj Θ : Matrix nj nj ℝ) (Bj : Matrix nj mj ℝ)
    (Bi : Matrix ni mi ℝ) (Lji : Matrix mj mi ℝ) (Lij : Matrix mi mj ℝ) (hL : Lij = -Ljiᵀ)
    (hΘ : Θᵀ = Θ) :
    (Θ * ((H ^ 2 / 2) • ((Aj + ς • Ajᵀ) * Bj * Lji)) - (H ^ 2 / 2) • (Θ * Aj * Bj * Lji)) * Biᵀ =
      -((H ^ 2 / 2) • (ς • (Bi * Lij * Bjᵀ * Aj * Θ)))ᵀ := by
  subst hL
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_neg,
    Matrix.transpose_transpose, hΘ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, smul_add, smul_neg,
    neg_neg, Matrix.sub_mul]
  abel

end Ports

end CoSimFoundations
