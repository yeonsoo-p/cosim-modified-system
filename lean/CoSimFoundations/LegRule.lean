/-
The half-step term `½H² A_ς A` for couplings of both kinds: the leg rule, the sign of the reaction
and the trace of the relation (the paper, Section 4: Theorem "half a macro step", Corollary "the
blocks that the coefficients do not reach" (a), (c), Proposition "energy stored and energy created"
(ii); there the coupling is power-conserving, `A_{ki} = -A_{ik}ᵀ`).

Setting of `HalfStep` and `StoredEnergy`: a `HeldScheme` (`X = F + M + N * X`, states grouped by
`sub`, stages `stage`), the signed coupling `A_ς = signedCoupling A` with `ς_{sk} = S.sg s k` (`+1`
if `k` runs at an earlier stage than `s`, `-1` if not), the leading term `½H² A_ς A` of `X - U`.
`StoredEnergy` and `ReactionDiag` read this term under
`hskew : ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q`. Here nothing is assumed of the coupling as a
whole; each link has a kind.

1. **The kind of a link** (`LinkKind`, `LinkKind.symm`, `linkKind_of_mul_self_eq_one`,
   `forall_linkKind_neg_one_iff`). `S.LinkKind A s k ε`: `A q p = ε A p q` for the states `p`, `q`
   of `s` and `k`, in both directions (`A_{ks} = ε A_{sk}ᵀ` and `A_{sk} = ε A_{ks}ᵀ`). `ε = -1` is a
   conservative link (a spring between power-conjugate ports), `ε = 1` a dissipative one (a
   damper). `hskew` says that every link is conservative.

2. **The leg rule** (`signedCoupling_mul_apply`, `signedCoupling_mul_apply_filter`, `leg_rule`,
   `inner_leg_rule`, four corollaries, `signedCoupling_mul_apply_sum`,
   `signedCoupling_mul_apply_partners`, `leg_rule_sum`). For all states `p`, `q`,
     `(A_ς A) p q = Σ_{r ∉ sub p} ς(sub p, sub r) A p r A r q`.
   Let `p` be in `i`, `q` in `j`, and let `k ≠ i, j` be the only subsystem through which `i` and
   `j` are joined (`A p r A r q = 0` and `A q r A r p = 0` unless `sub r = k`). If the link `i`-`k`
   has kind `ε₁` and the link `k`-`j` kind `ε₂`, then `A q r A r p = ε₁ ε₂ A p r A r q`, hence
     `(A_ς A) q p = ε₁ ε₂ ς_{jk} ς_{ik} (A_ς A) p q`   (`ς_{ik}² = 1`).
   Two links of the same kind (`ε₁ ε₂ = 1`): the two entries are equal if `ς_{ik} = ς_{jk}` (`k`
   runs before both or not before either) and opposite if `ς_{jk} = -ς_{ik}` (`k` runs between
   them). Links of different kinds (`ε₁ ε₂ = -1`): the other way round. With several common
   partners, `A mask_k A` being the leg through `k` (`Σ_{r ∈ k} A p r A r q`), and no direct link
   between `i` and `j`:
     `(A_ς A) p q = Σ_{k ≠ i, j} ς_{ik} (A mask_k A) p q`,
     `(A_ς A) q p = Σ_{k ≠ i, j} ε₁(k) ε₂(k) ς_{jk} (A mask_k A) p q`.

3. **The sign of the reaction** (`inner_signedCoupling_mul_row`, `signedCoupling_mul_apply_kind`,
   `inner_signedCoupling_mul_kind`, `inner_signedCoupling_mul_self_kind`, two corollaries). For
   `x` supported on `i` and every `y`,
     `⟪x, A_ς A y⟫ = Σ_{r ∉ i} ς(i, sub r) (Σ_p A p r x p) (Σ_q A r q y q)`,
   and if every link `i`-`k` has a kind `ε k`, for `x`, `y` supported on `i`,
     `⟪x, A_ς A x⟫ = Σ_{r ∉ i} ε(sub r) ς(i, sub r) (Σ_p A p r x p)²`.
   Through a conservative link the reaction has the sign `-ς`, through a dissipative link `+ς`.

4. **The trace of the relation** (`sample_bracket_diag`, `Consistent.half_step_trace_M`,
   `Consistent.half_step_trace`, `Consistent.trace_partner_weights`,
   `trace_signedCoupling_mul_kind`). For a consistent scheme and every matrix `A`:
     `|tr (X - U) - tr (F - 1 - H A₀ - ½H² A₀²) - tr M - ½H² tr (A_ς A)| ≤ n C₃ H³`,
   `C₃ = reactionC a b c ‖A‖ H` (the rows `p` of `Consistent.half_step_row` with `x = y = e_p`,
   added). The bracket of the partner samples has the diagonal entries of `M` (`N`, `A_c` and
   `A₀ A_c` have none), and `tr M = 0` if no subsystem is its own partner; then the term `tr M` is
   absent. With `F = exp (H A₀)` (partner weights only) the first bracket is a Taylor remainder:
     `|tr (X - U) - ½H² tr (A_ς A)| ≤ n (C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H³`.
   If every link `s`-`k` has a kind `ε s k`:
     `tr (A_ς A) = Σ_p Σ_{r ∉ sub p} ε(sub p, sub r) ς(sub p, sub r) (A p r)²`.
-/
import CoSimFoundations.StoredEnergy

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n : ℕ}

namespace HeldScheme

section Kind

variable {κ : Type*} (S : HeldScheme n κ)

/-! ### The kind of a link -/

/-- **The kind of the link between the subsystems `s` and `k`.** `S.LinkKind A s k ε` says that
the two blocks of `A` between `s` and `k` are `ε` times the transposes of each other:
`A q p = ε * A p q` for `p` in `s` and `q` in `k`, and for `p` in `k` and `q` in `s`. `ε = -1` is a
conservative link, `ε = 1` a dissipative one. -/
def LinkKind (A : Matrix (Fin n) (Fin n) ℝ) (s k : κ) (ε : ℝ) : Prop :=
  (∀ p q, S.sub p = s → S.sub q = k → A q p = ε * A p q) ∧
    ∀ p q, S.sub p = k → S.sub q = s → A q p = ε * A p q

variable {S}

/-- The kind of a link does not depend on the direction in which the link is named. -/
theorem LinkKind.symm {A : Matrix (Fin n) (Fin n) ℝ} {s k : κ} {ε : ℝ}
    (h : S.LinkKind A s k ε) : S.LinkKind A k s ε :=
  ⟨h.2, h.1⟩

/-- The link `s`-`k` has the kind `ε` if and only if the link `k`-`s` has. -/
theorem linkKind_comm {A : Matrix (Fin n) (Fin n) ℝ} {s k : κ} {ε : ℝ} :
    S.LinkKind A s k ε ↔ S.LinkKind A k s ε :=
  ⟨LinkKind.symm, LinkKind.symm⟩

/-- For a sign `ε` (`ε * ε = 1`, in particular `ε = -1` and `ε = 1`) one direction is enough:
if `A q p = ε * A p q` for `p` in `s` and `q` in `k`, the link has the kind `ε`. -/
theorem linkKind_of_mul_self_eq_one {A : Matrix (Fin n) (Fin n) ℝ} {s k : κ} {ε : ℝ}
    (hε : ε * ε = 1) (h : ∀ p q, S.sub p = s → S.sub q = k → A q p = ε * A p q) :
    S.LinkKind A s k ε := by
  refine ⟨h, fun p q hp hq => ?_⟩
  have h1 : A p q = ε * A q p := h q p hq hp
  rw [h1, ← mul_assoc, hε, one_mul]

/-- **A power-conserving coupling is a coupling whose links are all conservative:** the hypothesis
`hskew` of `StoredEnergy` and `ReactionDiag` holds if and only if every link between two different
subsystems has the kind `-1`. -/
theorem forall_linkKind_neg_one_iff {A : Matrix (Fin n) (Fin n) ℝ} :
    (∀ s k, s ≠ k → S.LinkKind A s k (-1)) ↔ ∀ p q, S.sub p ≠ S.sub q → A q p = -A p q := by
  constructor
  · intro h p q hpq
    rw [(h _ _ hpq).1 p q rfl rfl, neg_one_mul]
  · intro hskew s k hsk
    refine ⟨fun p q hp hq => ?_, fun p q hp hq => ?_⟩
    · rw [hskew p q (by rw [hp, hq]; exact hsk), neg_one_mul]
    · rw [hskew p q (by rw [hp, hq]; exact hsk.symm), neg_one_mul]

variable (S)

/-! ### The signs of two subsystems towards a third -/

/-- The square of a sign is one: `ς_{sk}² = 1`. -/
theorem sg_mul_self (s k : κ) : S.sg s k * S.sg s k = 1 := by
  unfold sg
  by_cases h : S.stage k < S.stage s
  · rw [ite_eq_left h, one_mul]
  · rw [ite_eq_right h]
    norm_num

/-- If `k` runs before both `i` and `j`, or before neither, the two signs towards `k` are equal:
`ς_{ik} = ς_{jk}`. -/
theorem sg_eq_sg_of_iff {i j k : κ} (h : S.stage k < S.stage i ↔ S.stage k < S.stage j) :
    S.sg i k = S.sg j k := by
  unfold sg
  by_cases hi : S.stage k < S.stage i
  · rw [ite_eq_left hi, ite_eq_left (h.1 hi)]
  · rw [ite_eq_right hi, ite_eq_right fun hj => hi (h.2 hj)]

end Kind

section Leg

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-! ### The leg rule -/

/-- **The entries of the half-step term:**
`(A_ς A) p q = Σ_{r ∉ sub p} ς(sub p, sub r) A p r A r q`, for all states `p`, `q` and every
matrix `A`. -/
theorem signedCoupling_mul_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    (S.signedCoupling A * A) p q =
      ∑ r, if S.sub r = S.sub p then 0 else S.sg (S.sub p) (S.sub r) * A p r * A r q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [S.signedCoupling_apply]
  by_cases hr : S.sub r = S.sub p
  · rw [ite_eq_left hr.symm, ite_eq_left hr, zero_mul]
  · rw [ite_eq_right fun e => hr e.symm, ite_eq_right hr]

/-- **The entries of the half-step term, as a sum over the intermediate states.** For `p` in the
subsystem `i` and every state `q`: `(A_ς A) p q` is the sum of `ς(i, sub r) A p r A r q` over the
states `r` outside `i`. -/
theorem signedCoupling_mul_apply_filter (A : Matrix (Fin n) (Fin n) ℝ) {i : κ} {p : Fin n}
    (hp : S.sub p = i) (q : Fin n) :
    (S.signedCoupling A * A) p q =
      ∑ r ∈ Finset.univ.filter (fun r => S.sub r ≠ i), S.sg i (S.sub r) * A p r * A r q := by
  rw [S.signedCoupling_mul_apply, Finset.sum_filter, hp]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = i
  · rw [ite_eq_left hr, ite_eq_right (not_not.2 hr)]
  · rw [ite_eq_right hr, ite_eq_left hr]

/-- **The leg rule.** Let `p` be a state of `i` and `q` a state of `j`, and let `k`, different
from `i` and `j`, be the only subsystem through which they are joined: `A p r * A r q = 0` and
`A q r * A r p = 0` unless `r` is a state of `k`. If the link `i`-`k` has the kind `ε₁` and the
link `k`-`j` the kind `ε₂`, the two entries of the half-step term between `p` and `q` differ by
the factor `ε₁ ε₂ ς_{jk} ς_{ik}`. (`i = j` is allowed.) -/
theorem leg_rule {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ} (hki : k ≠ i)
    (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂) {p q : Fin n}
    (hp : S.sub p = i) (hq : S.sub q = j) (hpq : ∀ r, S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ r, S.sub r ≠ k → A q r * A r p = 0) :
    (S.signedCoupling A * A) q p =
      ε₁ * ε₂ * (S.sg j k * S.sg i k) * (S.signedCoupling A * A) p q := by
  rw [S.signedCoupling_mul_apply, S.signedCoupling_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hp, hq]
  by_cases hr : S.sub r = k
  · have e1 : A r p = ε₁ * A p r := h₁.1 p r hp hr
    have e2 : A q r = ε₂ * A r q := h₂.1 r q hr hq
    have hri : S.sub r ≠ i := by rw [hr]; exact hki
    have hrj : S.sub r ≠ j := by rw [hr]; exact hkj
    have hs := S.sg_mul_self i k
    rw [ite_eq_right hrj, ite_eq_right hri, hr, e1, e2]
    linear_combination (-(ε₁ * ε₂ * S.sg j k * A p r * A r q)) * hs
  · have l : S.sg j (S.sub r) * A q r * A r p = 0 := by rw [mul_assoc, hqp r hr, mul_zero]
    have l' : S.sg i (S.sub r) * A p r * A r q = 0 := by rw [mul_assoc, hpq r hr, mul_zero]
    rw [l, l', ite_self, ite_self, mul_zero]

/-- **Two links of the same kind, the common partner on one side.** If the links `i`-`k` and
`k`-`j` are both conservative or both dissipative (`ε₁ ε₂ = 1`) and `k` runs before both `i` and
`j` or before neither (`ς_{ik} = ς_{jk}`), the two entries of the half-step term between `p` and
`q` are equal: the block is symmetric, a numerical dissipation. -/
theorem leg_rule_like_same_side {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ}
    (hki : k ≠ i) (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hε : ε₁ * ε₂ = 1) (hs : S.sg i k = S.sg j k) {p q : Fin n}
    (hp : S.sub p = i) (hq : S.sub q = j) (hpq : ∀ r, S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ r, S.sub r ≠ k → A q r * A r p = 0) :
    (S.signedCoupling A * A) q p = (S.signedCoupling A * A) p q := by
  rw [S.leg_rule hki hkj h₁ h₂ hp hq hpq hqp, hε, hs]
  linear_combination (S.signedCoupling A * A) p q * S.sg_mul_self j k

/-- **Two links of the same kind, the common partner in between.** If the links `i`-`k` and
`k`-`j` are both conservative or both dissipative (`ε₁ ε₂ = 1`) and `k` runs before exactly one of
`i` and `j` (`ς_{jk} = -ς_{ik}`), the two entries of the half-step term between `p` and `q` are
opposite: the block is skew, a numerical interconnection. -/
theorem leg_rule_like_between {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ}
    (hki : k ≠ i) (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hε : ε₁ * ε₂ = 1) (hs : S.sg j k = -S.sg i k) {p q : Fin n}
    (hp : S.sub p = i) (hq : S.sub q = j) (hpq : ∀ r, S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ r, S.sub r ≠ k → A q r * A r p = 0) :
    (S.signedCoupling A * A) q p = -(S.signedCoupling A * A) p q := by
  rw [S.leg_rule hki hkj h₁ h₂ hp hq hpq hqp, hε, hs]
  linear_combination (-(S.signedCoupling A * A) p q) * S.sg_mul_self i k

/-- **Links of different kinds, the common partner on one side.** If one of the links `i`-`k`,
`k`-`j` is conservative and the other dissipative (`ε₁ ε₂ = -1`) and `k` runs before both `i` and
`j` or before neither (`ς_{ik} = ς_{jk}`), the two entries of the half-step term between `p` and
`q` are opposite: the block is skew, a numerical interconnection. -/
theorem leg_rule_unlike_same_side {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ}
    (hki : k ≠ i) (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hε : ε₁ * ε₂ = -1) (hs : S.sg i k = S.sg j k) {p q : Fin n}
    (hp : S.sub p = i) (hq : S.sub q = j) (hpq : ∀ r, S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ r, S.sub r ≠ k → A q r * A r p = 0) :
    (S.signedCoupling A * A) q p = -(S.signedCoupling A * A) p q := by
  rw [S.leg_rule hki hkj h₁ h₂ hp hq hpq hqp, hε, hs]
  linear_combination (-(S.signedCoupling A * A) p q) * S.sg_mul_self j k

/-- **Links of different kinds, the common partner in between.** If one of the links `i`-`k`,
`k`-`j` is conservative and the other dissipative (`ε₁ ε₂ = -1`) and `k` runs before exactly one
of `i` and `j` (`ς_{jk} = -ς_{ik}`), the two entries of the half-step term between `p` and `q` are
equal: the block is symmetric, a numerical dissipation. -/
theorem leg_rule_unlike_between {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ}
    (hki : k ≠ i) (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hε : ε₁ * ε₂ = -1) (hs : S.sg j k = -S.sg i k) {p q : Fin n}
    (hp : S.sub p = i) (hq : S.sub q = j) (hpq : ∀ r, S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ r, S.sub r ≠ k → A q r * A r p = 0) :
    (S.signedCoupling A * A) q p = (S.signedCoupling A * A) p q := by
  rw [S.leg_rule hki hkj h₁ h₂ hp hq hpq hqp, hε, hs]
  linear_combination (S.signedCoupling A * A) p q * S.sg_mul_self i k

/-- **The leg rule for the blocks.** If `k`, different from `i` and `j`, is the only subsystem
through which `i` and `j` are joined, the link `i`-`k` has the kind `ε₁` and the link `k`-`j` the
kind `ε₂`, then for `x` supported on `i` and `y` on `j`:
`⟪y, A_ς A x⟫ = ε₁ ε₂ ς_{jk} ς_{ik} ⟪x, A_ς A y⟫`, that is
`[A_ς A]_{ji} = ε₁ ε₂ ς_{jk} ς_{ik} [A_ς A]_{ij}ᵀ`. -/
theorem inner_leg_rule {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ} (hki : k ≠ i)
    (hkj : k ≠ j) (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂)
    (hpq : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A p r * A r q = 0)
    (hqp : ∀ p q r, S.sub p = i → S.sub q = j → S.sub r ≠ k → A q r * A r p = 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (hy : ∀ q, S.sub q ≠ j → y q = 0) :
    ⟪y, opE (S.signedCoupling A * A) x⟫ =
      ε₁ * ε₂ * (S.sg j k * S.sg i k) * ⟪x, opE (S.signedCoupling A * A) y⟫ := by
  rw [← OneStep.inner_opE_smul, OneStep.inner_opE_transpose (S.signedCoupling A * A) x y]
  refine inner_opE_congr hx hy fun p q hp hq => ?_
  rw [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  exact S.leg_rule hki hkj h₁ h₂ hp hq (fun r => hpq p q r hp hq) fun r => hqp p q r hp hq

/-! ### Several common partners -/

/-- The leg through the subsystem `k`: `(A mask_k A) p q = Σ_{r ∈ k} A p r A r q`. -/
theorem mul_mask_mul_apply (A : Matrix (Fin n) (Fin n) ℝ) (k : κ) (p q : Fin n) :
    (A * S.mask k * A) p q = ∑ r, if S.sub r = k then A p r * A r q else 0 := by
  rw [mask, mul_diagonal_mul_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = k
  · rw [ite_eq_left hr, ite_eq_left hr, mul_one]
  · rw [ite_eq_right hr, ite_eq_right hr, mul_zero, zero_mul]

/-- The leg through `k` from `p` to `q` vanishes if `A p r = 0` for the states `r` of `k`. -/
theorem mul_mask_mul_apply_eq_zero {A : Matrix (Fin n) (Fin n) ℝ} {k : κ} {p : Fin n}
    (h : ∀ r, S.sub r = k → A p r = 0) (q : Fin n) : (A * S.mask k * A) p q = 0 := by
  rw [S.mul_mask_mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : S.sub r = k
  · rw [ite_eq_left hr, h r hr, zero_mul]
  · rw [ite_eq_right hr]

/-- **A leg in the two directions.** If the link `i`-`k` has the kind `ε₁` and the link `k`-`j`
the kind `ε₂`, then for `p` in `i` and `q` in `j` the leg through `k` from `q` to `p` is `ε₁ ε₂`
times the leg from `p` to `q`: `A_{jk} A_{ki} = ε₁ ε₂ (A_{ik} A_{kj})ᵀ`. -/
theorem leg_swap {A : Matrix (Fin n) (Fin n) ℝ} {i j k : κ} {ε₁ ε₂ : ℝ}
    (h₁ : S.LinkKind A i k ε₁) (h₂ : S.LinkKind A k j ε₂) {p q : Fin n} (hp : S.sub p = i)
    (hq : S.sub q = j) : (A * S.mask k * A) q p = ε₁ * ε₂ * (A * S.mask k * A) p q := by
  rw [S.mul_mask_mul_apply, S.mul_mask_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = k
  · rw [ite_eq_left hr, ite_eq_left hr, h₁.1 p r hp hr, h₂.1 r q hr hq]
    ring
  · rw [ite_eq_right hr, ite_eq_right hr, mul_zero]

/-- **The half-step term as a sum over the subsystems in the middle:**
`(A_ς A) p q = Σ_{k ≠ sub p} ς(sub p, k) (A mask_k A) p q`, for all states `p`, `q` and every
matrix `A`. -/
theorem signedCoupling_mul_apply_sum [Fintype κ] (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    (S.signedCoupling A * A) p q =
      ∑ k, if k = S.sub p then 0 else S.sg (S.sub p) k * (A * S.mask k * A) p q := by
  have e : ∀ k, (if k = S.sub p then 0 else S.sg (S.sub p) k * (A * S.mask k * A) p q) =
      ∑ r, if S.sub r = k then
        (if S.sub r = S.sub p then 0 else S.sg (S.sub p) (S.sub r) * A p r * A r q) else 0 := by
    intro k
    rw [S.mul_mask_mul_apply]
    by_cases hk : k = S.sub p
    · rw [ite_eq_left hk]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : S.sub r = k
      · rw [ite_eq_left hr, ite_eq_left (hr.trans hk)]
      · rw [ite_eq_right hr]
    · rw [ite_eq_right hk, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : S.sub r = k
      · rw [ite_eq_left hr, ite_eq_left hr, ite_eq_right fun e => hk (hr.symm.trans e), hr]
        ring
      · rw [ite_eq_right hr, ite_eq_right hr, mul_zero]
  rw [S.signedCoupling_mul_apply, Finset.sum_congr rfl fun k _ => e k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

/-- **Subsystems without a direct link: the sum over the common partners.** If the block of `A`
from `j` to `i` vanishes (`A a b = 0` for `a` in `i`, `b` in `j`), then for `p` in `i` and `q` in
`j`: `(A_ς A) p q = Σ_{k ≠ i, j} ς_{ik} (A mask_k A) p q`. -/
theorem signedCoupling_mul_apply_partners [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ} {i j : κ}
    (hij : ∀ a b, S.sub a = i → S.sub b = j → A a b = 0) {p q : Fin n} (hp : S.sub p = i) :
    (S.signedCoupling A * A) p q =
      ∑ k, if k = i ∨ k = j then 0 else S.sg i k * (A * S.mask k * A) p q := by
  rw [S.signedCoupling_mul_apply_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp]
  by_cases hki : k = i
  · rw [ite_eq_left hki, ite_eq_left (Or.inl hki)]
  · by_cases hkj : k = j
    · rw [ite_eq_right hki, ite_eq_left (Or.inr hkj),
        S.mul_mask_mul_apply_eq_zero (fun r hr => hij p r hp (hr.trans hkj)) q, mul_zero]
    · rw [ite_eq_right hki, ite_eq_right (not_or.2 ⟨hki, hkj⟩)]

/-- **The leg rule with several common partners.** Let the block of `A` from `i` to `j` vanish
(`A a b = 0` for `a` in `j`, `b` in `i`), and for every other subsystem `k` let the link `i`-`k`
have a kind `ε₁ k` and the link `k`-`j` a kind `ε₂ k`. Then for `p` in `i` and `q` in `j` the
entry of the half-step term from `p` to `q` is the sum of the legs of the opposite entry
(`signedCoupling_mul_apply_partners`), each with its own factor:
`(A_ς A) q p = Σ_{k ≠ i, j} ε₁(k) ε₂(k) ς_{jk} (A mask_k A) p q`. -/
theorem leg_rule_sum [Fintype κ] {A : Matrix (Fin n) (Fin n) ℝ} {i j : κ} (ε₁ ε₂ : κ → ℝ)
    (hkind : ∀ k, k ≠ i → k ≠ j → S.LinkKind A i k (ε₁ k) ∧ S.LinkKind A k j (ε₂ k))
    (hji : ∀ a b, S.sub a = j → S.sub b = i → A a b = 0) {p q : Fin n} (hp : S.sub p = i)
    (hq : S.sub q = j) :
    (S.signedCoupling A * A) q p =
      ∑ k, if k = i ∨ k = j then 0 else
        ε₁ k * ε₂ k * S.sg j k * (A * S.mask k * A) p q := by
  rw [S.signedCoupling_mul_apply_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hq]
  by_cases hkj : k = j
  · rw [ite_eq_left hkj, ite_eq_left (Or.inr hkj)]
  · by_cases hki : k = i
    · rw [ite_eq_right hkj, ite_eq_left (Or.inl hki),
        S.mul_mask_mul_apply_eq_zero (fun r hr => hji q r hq (hr.trans hki)) p, mul_zero]
    · rw [ite_eq_right hkj, ite_eq_right (not_or.2 ⟨hki, hkj⟩),
        S.leg_swap (hkind k hki hkj).1 (hkind k hki hkj).2 hp hq]
      ring

/-! ### The sign of the reaction -/

/-- **The rows of the half-step term of a subsystem, as a sum over the states of the others.**
For `x` supported on `i`, every vector `y` and every matrix `A`:
`⟪x, A_ς A y⟫ = Σ_{r ∉ i} ς(i, sub r) (Σ_p A p r x p) (Σ_q A r q y q)`. -/
theorem inner_signedCoupling_mul_row (A : Matrix (Fin n) (Fin n) ℝ) {i : κ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ p, S.sub p ≠ i → x p = 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ =
      ∑ r, if S.sub r = i then 0 else
        S.sg i (S.sub r) * ((∑ p, A p r * x p) * ∑ q, A r q * y q) := by
  rw [S.inner_signedCoupling_row A hx y, opE_mul_apply, opE_mul_apply,
    OneStep.inner_opE_transpose A (opE (S.osgn i) (opE A y)) x, inner_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [S.opE_osgn_apply, opE_apply, opE_apply]
  by_cases hr : S.sub r = i
  · rw [ite_eq_left hr, ite_eq_left hr, zero_mul, zero_mul]
  · rw [ite_eq_right hr, ite_eq_right hr]
    simp only [Matrix.transpose_apply]
    ring

/-- **The diagonal block of the half-step term for links with a kind.** If every link `i`-`k`
has a kind `ε k`, then for `p`, `q` in `i`:
`(A_ς A) p q = Σ_{r ∉ i} ε(sub r) ς(i, sub r) A p r A q r`. -/
theorem signedCoupling_mul_apply_kind {A : Matrix (Fin n) (Fin n) ℝ} {i : κ} (ε : κ → ℝ)
    (hkind : ∀ k, k ≠ i → S.LinkKind A i k (ε k)) {p q : Fin n} (hp : S.sub p = i)
    (hq : S.sub q = i) :
    (S.signedCoupling A * A) p q =
      ∑ r, if S.sub r = i then 0 else ε (S.sub r) * S.sg i (S.sub r) * (A p r * A q r) := by
  rw [S.signedCoupling_mul_apply, hp]
  refine Finset.sum_congr rfl fun r _ => if_ctx_congr Iff.rfl (fun _ => rfl) fun hr => ?_
  rw [(hkind _ hr).1 q r hq rfl]
  ring

/-- **The reaction for links with a kind, as a bilinear form.** If every link `i`-`k` has a kind
`ε k`, then for `x`, `y` supported on `i`:
`⟪x, A_ς A y⟫ = Σ_{r ∉ i} ε(sub r) ς(i, sub r) (Σ_p A p r x p) (Σ_q A q r y q)`. -/
theorem inner_signedCoupling_mul_kind {A : Matrix (Fin n) (Fin n) ℝ} {i : κ} (ε : κ → ℝ)
    (hkind : ∀ k, k ≠ i → S.LinkKind A i k (ε k)) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) (hy : ∀ q, S.sub q ≠ i → y q = 0) :
    ⟪x, opE (S.signedCoupling A * A) y⟫ =
      ∑ r, if S.sub r = i then 0 else
        ε (S.sub r) * S.sg i (S.sub r) * ((∑ p, A p r * x p) * ∑ q, A q r * y q) := by
  rw [S.inner_signedCoupling_mul_row A hx y]
  refine Finset.sum_congr rfl fun r _ => if_ctx_congr Iff.rfl (fun _ => rfl) fun hr => ?_
  have e : ∑ q, A r q * y q = ε (S.sub r) * ∑ q, A q r * y q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : S.sub q = i
    · rw [(hkind _ hr).1 q r hq rfl]
      ring
    · rw [hy q hq]
      ring
  rw [e]
  ring

/-- **The sign of the reaction.** If every link `i`-`k` has a kind `ε k`, then for `x` supported
on `i`: `⟪x, A_ς A x⟫ = Σ_{r ∉ i} ε(sub r) ς(i, sub r) (Σ_p A p r x p)²`. Each state `r` of a
partner contributes a square with the sign `ε ς`: through a conservative link (`ε = -1`) the
reaction has the sign `-ς`, through a dissipative link (`ε = 1`) the sign `+ς`. -/
theorem inner_signedCoupling_mul_self_kind {A : Matrix (Fin n) (Fin n) ℝ} {i : κ} (ε : κ → ℝ)
    (hkind : ∀ k, k ≠ i → S.LinkKind A i k (ε k)) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) :
    ⟪x, opE (S.signedCoupling A * A) x⟫ =
      ∑ r, if S.sub r = i then 0 else
        ε (S.sub r) * S.sg i (S.sub r) * (∑ p, A p r * x p) ^ 2 := by
  rw [S.inner_signedCoupling_mul_kind ε hkind hx hx]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sq]

/-- **The reaction through conservative links.** If every link of `i` is conservative, then for
`x` supported on `i`: `⟪x, A_ς A x⟫ = -Σ_{r ∉ i} ς(i, sub r) (Σ_p A p r x p)²`. -/
theorem inner_signedCoupling_mul_self_conservative {A : Matrix (Fin n) (Fin n) ℝ} {i : κ}
    (hkind : ∀ k, k ≠ i → S.LinkKind A i k (-1)) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) :
    ⟪x, opE (S.signedCoupling A * A) x⟫ =
      -∑ r, if S.sub r = i then 0 else S.sg i (S.sub r) * (∑ p, A p r * x p) ^ 2 := by
  rw [S.inner_signedCoupling_mul_self_kind (fun _ => -1) hkind hx, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = i
  · rw [ite_eq_left hr, ite_eq_left hr, neg_zero]
  · rw [ite_eq_right hr, ite_eq_right hr]
    ring

/-- **The reaction through dissipative links.** If every link of `i` is dissipative, then for
`x` supported on `i`: `⟪x, A_ς A x⟫ = Σ_{r ∉ i} ς(i, sub r) (Σ_p A p r x p)²`. -/
theorem inner_signedCoupling_mul_self_dissipative {A : Matrix (Fin n) (Fin n) ℝ} {i : κ}
    (hkind : ∀ k, k ≠ i → S.LinkKind A i k 1) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ p, S.sub p ≠ i → x p = 0) :
    ⟪x, opE (S.signedCoupling A * A) x⟫ =
      ∑ r, if S.sub r = i then 0 else S.sg i (S.sub r) * (∑ p, A p r * x p) ^ 2 := by
  rw [S.inner_signedCoupling_mul_self_kind (fun _ => 1) hkind hx]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [one_mul]

/-! ### The trace of the relation -/

/-- **The diagonal of the bracket of the partner samples** is the diagonal of `M`: `N`, `A_c` and
`A₀ A_c` have no diagonal entries. -/
theorem sample_bracket_diag (A : Matrix (Fin n) (Fin n) ℝ) (H : ℝ) (p : Fin n) :
    (S.M + S.N - H • S.coupling A - (H ^ 2 / 2) • (S.blockDiag A * S.coupling A)) p p =
      S.M p p := by
  have hN : S.N p p = 0 := S.hN p p fun h => lt_irrefl _ h.2
  have hc : S.coupling A p p = 0 := by
    rw [S.coupling_apply]
    exact ite_eq_left rfl
  have h2 : (S.blockDiag A * S.coupling A) p p = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [S.blockDiag_apply, S.coupling_apply]
    by_cases hr : S.sub p = S.sub r
    · rw [ite_eq_left hr, ite_eq_left hr.symm, mul_zero]
    · rw [ite_eq_right hr, zero_mul]
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, hN, hc, h2]
  simp

/-- If no subsystem is its own partner, the coefficients of the old samples have no trace. -/
theorem trace_M_eq_zero (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p)) :
    Matrix.trace S.M = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.diag_apply]
  exact S.hM p p fun h => hself p h.1

/-- **The trace of the half-step term for links with a kind.** If every link `s`-`k` between two
different subsystems has a kind `ε s k`:
`tr (A_ς A) = Σ_p Σ_{r ∉ sub p} ε(sub p, sub r) ς(sub p, sub r) (A p r)²`. -/
theorem trace_signedCoupling_mul_kind {A : Matrix (Fin n) (Fin n) ℝ} (ε : κ → κ → ℝ)
    (hkind : ∀ s k, s ≠ k → S.LinkKind A s k (ε s k)) :
    Matrix.trace (S.signedCoupling A * A) =
      ∑ p, ∑ r, if S.sub r = S.sub p then 0 else
        ε (S.sub p) (S.sub r) * S.sg (S.sub p) (S.sub r) * (A p r) ^ 2 := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, S.signedCoupling_mul_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : S.sub r = S.sub p
  · rw [ite_eq_left hr, ite_eq_left hr]
  · rw [ite_eq_right hr, ite_eq_right hr, (hkind _ _ fun e => hr e.symm).1 p r rfl rfl]
    ring

variable {S}

/-- **The trace of the half-step relation, for every coupling.** For a consistent scheme with one
held sample, in any order of execution, and every matrix `A` (no kind of the links is assumed):
`|tr (X - U) - tr (F - 1 - H A₀ - ½H² A₀²) - tr M - ½H² tr (A_ς A)| ≤ n C₃ H³`,
`C₃ = reactionC a b c ‖A‖ H`, `n` the number of states. The bracket of the partner samples
contributes the trace of `M` only (`sample_bracket_diag`). -/
theorem Consistent.half_step_trace_M {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) :
    |Matrix.trace (S.X - U) -
        Matrix.trace (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) -
        Matrix.trace S.M - H ^ 2 / 2 * Matrix.trace (S.signedCoupling A * A)| ≤
      (n : ℝ) * reactionC a b c ‖opE A‖ H * H ^ 3 := by
  have h2 : |Matrix.trace (S.X - U -
        (S.F - 1 - H • S.blockDiag A - (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) -
        S.M - (H ^ 2 / 2) • (S.signedCoupling A * A))| ≤
      (n : ℝ) * (reactionC a b c ‖opE A‖ H * H ^ 3) := by
    refine abs_trace_le_of_diag fun p => ?_
    have h1 := h.half_step_row (S.unitE_support p) (unitE p)
    rw [inner_unitE_opE, inner_unitE_opE, inner_unitE_opE, inner_unitE_opE,
      S.sample_bracket_diag, norm_unitE, mul_one, mul_one] at h1
    exact h1
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul] at h2
  exact h2.trans_eq (by ring)

/-- **The trace of the half-step relation.** For a consistent scheme with one held sample in
which no subsystem is its own partner, in any order of execution, and every matrix `A` (no kind of
the links is assumed):
`|tr (X - U) - tr (F - 1 - H A₀ - ½H² A₀²) - ½H² tr (A_ς A)| ≤ n C₃ H³`,
`C₃ = reactionC a b c ‖A‖ H`, `n` the number of states: the bracket of the partner samples has no
trace. -/
theorem Consistent.half_step_trace {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p)) :
    |Matrix.trace (S.X - U) -
        Matrix.trace (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) -
        H ^ 2 / 2 * Matrix.trace (S.signedCoupling A * A)| ≤
      (n : ℝ) * reactionC a b c ‖opE A‖ H * H ^ 3 := by
  have h1 := h.half_step_trace_M
  rwa [S.trace_M_eq_zero hself, sub_zero] at h1

/-- **The trace of `X - U` with partner weights only.** For a consistent scheme with one held
sample in which no subsystem is its own partner and the local maps are exact,
`F = exp (H A₀)`, in any order of execution and for every matrix `A` (no kind of the links is
assumed): `|tr (X - U) - ½H² tr (A_ς A)| ≤ n (C₃ + ‖A₀‖³/6 · e^{H‖A₀‖}) H³`. The coefficients of
the partner samples do not enter: to leading order the trace of `X - U` is `½H² tr (A_ς A)` for
every such hold. -/
theorem Consistent.trace_partner_weights {A U : Matrix (Fin n) (Fin n) ℝ} {H a b c : ℝ}
    (h : S.Consistent A U H a b c) (hself : ∀ p, ¬ S.partner (S.sub p) (S.sub p))
    (hF : S.F = NormedSpace.exp (H • S.blockDiag A)) :
    |Matrix.trace (S.X - U) - H ^ 2 / 2 * Matrix.trace (S.signedCoupling A * A)| ≤
      (n : ℝ) * (reactionC a b c ‖opE A‖ H +
        ‖opE (S.blockDiag A)‖ ^ 3 / 6 * Real.exp (H * ‖opE (S.blockDiag A)‖)) * H ^ 3 := by
  have h1 := h.half_step_trace hself
  have h2 := (OneStep.abs_trace_le (S.F - 1 - H • S.blockDiag A -
      (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A))).trans
    (mul_le_mul_of_nonneg_left (S.norm_local_bracket_le A h.hH hF) (Nat.cast_nonneg n))
  have e : Matrix.trace (S.X - U) - H ^ 2 / 2 * Matrix.trace (S.signedCoupling A * A) =
      (Matrix.trace (S.X - U) -
        Matrix.trace (S.F - 1 - H • S.blockDiag A -
          (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) -
        H ^ 2 / 2 * Matrix.trace (S.signedCoupling A * A)) +
      Matrix.trace (S.F - 1 - H • S.blockDiag A -
        (H ^ 2 / 2) • (S.blockDiag A * S.blockDiag A)) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
  ring

end Leg

end HeldScheme

end CoSimFoundations
