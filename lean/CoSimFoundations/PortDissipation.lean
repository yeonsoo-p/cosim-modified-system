/-
The numerical dissipation of the half step at the ports (the paper).

**Paper.** With `A_ik = B_i L_ik B_kᵀ` between different subsystems, the outputs
`y_i = B_iᵀ x_i` and their rates `ẏ_k = B_kᵀ Π_k A x`,

  `xᵀ A_ς A x = Σ_i y_iᵀ Σ_{k ≠ i} ς_ik L_ik ẏ_k`,

so that the numerical dissipation of the zero-order hold is
`xᵀ Δ_R x = -(H/2) Σ_i y_iᵀ Σ_k ς_ik L_ik ẏ_k + O(H² |x|²)`.

**Representation of the ports.** A `HeldScheme` carries the products `G C`, not the port
matrices (`OneSided`, `Hidden.of_ports`, takes `B L` and `C` as data). Here the ports are data as
well: `m` ports, `psub a` the subsystem that owns the port `a`, the matrix `B` (`n × m`,
`B = diag(B_i)`: `hB`, the column of a port lives on the states of its owner), the
interconnection `L` (`m × m`), and the hypothesis `hA` that the coupling blocks of `A` are those
of `B L Bᵀ`. With `C = Bᵀ` and `B L` for the matrix `BL` this is the factorisation of
`Hidden.of_ports`.

**Statements.**
* `signedPorts`: `L_ς`, the interconnection with the block `(i, k)` multiplied by `ς_ik` and
  without the blocks inside a subsystem.
* `signedCoupling_eq_ports` (exact): `A_ς = B L_ς Bᵀ`.
* `inner_signedCoupling_mul_self_ports` (**the identity**, exact, every assignment of stages):
  `xᵀ A_ς A x = yᵀ L_ς ẏ`, `y = Bᵀ x` (`portOut B x`), `ẏ = Bᵀ A x`; by `hB` the components of
  `y` at the ports of `i` are `B_iᵀ x_i` and those of `ẏ` at the ports of `k` are `B_kᵀ Π_k A x`.
  `dotProduct_signedPorts` writes the right-hand side as the double sum over the ports,
  `Σ_a Σ_b [psub a ≠ psub b] ς(psub a, psub b) y_a L_ab ẏ_b`.
* `abs_numDissipation_zoh_ports_le` (**the zero-order hold**, every order of execution): for
  `0 < H`, `H ‖A‖ ≤ 1/24`, `σ H ‖A‖ ≤ 1/6`, `σ = √(card κ)`,
  `|xᵀ Δ_R x + (H/2) yᵀ L_ς ẏ| ≤ (37 + 220σ + 53σ² + 54σ³) ‖A‖³ H² ‖x‖²`,
  the remainder of `abs_numDissipation_zoh_sub_le`.
* `skew_of_ports`: a skew interconnection, `L_ba = -L_ab`, gives power-conjugate ports in the
  sense of the library (`A q p = -A p q` between different subsystems), and then
  `sum_drive_sub_eq_ports`: the form of `HalfStepDissipation` with the two rates is the same
  number, `Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) - xᵀ A_ς A₀ x = -yᵀ L_ς ẏ`.

The identity and the statement for the zero-order hold do not use that the ports are
power-conjugate (`L` is arbitrary there).
-/
import CoSimFoundations.HalfStepDissipation

open Matrix
open scoped RealInnerProductSpace

namespace CoSimFoundations

open OneStep

variable {n m : ℕ}

/-- The outputs at the ports, `y = Bᵀ x`: `y_a = Σ_p B p a x_p`. -/
def portOut (B : Matrix (Fin n) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin n)) : Fin m → ℝ :=
  Bᵀ *ᵥ fun p => x p

/-- The components of the outputs. -/
theorem portOut_apply (B : Matrix (Fin n) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (a : Fin m) : portOut B x a = ∑ p, B p a * x p := rfl

namespace HeldScheme

variable {κ : Type*} [DecidableEq κ] (S : HeldScheme n κ)

/-- `L_ς`: the interconnection of the ports signed by the stages of their owners. Between ports
of different subsystems `L_ς a b = ς(psub a, psub b) L a b`, with `+1` if the owner of `b` runs
at an earlier stage than the owner of `a` and `-1` if not; `0` between ports of one subsystem. -/
noncomputable def signedPorts (psub : Fin m → κ) (L : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => if psub a = psub b then 0 else S.sg (psub a) (psub b) * L a b

/-- The entries of the signed interconnection. -/
theorem signedPorts_apply (psub : Fin m → κ) (L : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m) :
    S.signedPorts psub L a b =
      if psub a = psub b then 0 else S.sg (psub a) (psub b) * L a b := rfl

variable {psub : Fin m → κ} {B : Matrix (Fin n) (Fin m) ℝ} {L : Matrix (Fin m) (Fin m) ℝ}
  {A : Matrix (Fin n) (Fin n) ℝ}

/-- **The signed coupling at the ports:** if the column of every port lives on the states of its
owner and the coupling blocks of `A` are those of `B L Bᵀ`, then `A_ς = B L_ς Bᵀ` (all entries;
the blocks inside the subsystems vanish on both sides). -/
theorem signedCoupling_eq_ports (hB : ∀ p a, S.sub p ≠ psub a → B p a = 0)
    (hA : ∀ p q, S.sub p ≠ S.sub q → A p q = (B * L * Bᵀ) p q) :
    S.signedCoupling A = B * S.signedPorts psub L * Bᵀ := by
  ext p r
  rw [S.signedCoupling_apply, Matrix.mul_apply]
  by_cases hpr : S.sub p = S.sub r
  · rw [ite_eq_left hpr]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [S.signedPorts_apply]
    by_cases hab : psub a = psub b
    · rw [ite_eq_left hab, mul_zero, zero_mul]
    · by_cases hpa : S.sub p = psub a
      · have hrb : S.sub r ≠ psub b := fun h => hab (hpa.symm.trans (hpr.trans h))
        rw [hB r b hrb, mul_zero]
      · rw [hB p a hpa, zero_mul, zero_mul]
  · rw [ite_eq_right hpr, hA p r hpr, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S.signedPorts_apply]
    by_cases hpa : S.sub p = psub a
    · by_cases hrb : S.sub r = psub b
      · have hab : psub a ≠ psub b := fun h => hpr (hpa.trans (h.trans hrb.symm))
        rw [ite_eq_right hab, hpa, hrb]
        ring
      · rw [hB r b hrb]
        ring
    · rw [hB p a hpa]
      ring

/-- **The half step at the ports, the identity**, exact, for every `x` and every
assignment of stages: `xᵀ A_ς A x = yᵀ L_ς ẏ` with the outputs `y = Bᵀ x` and their rates
`ẏ = Bᵀ A x`, that is `Σ_i y_iᵀ Σ_{k ≠ i} ς_ik L_ik ẏ_k`. -/
theorem inner_signedCoupling_mul_self_ports (hB : ∀ p a, S.sub p ≠ psub a → B p a = 0)
    (hA : ∀ p q, S.sub p ≠ S.sub q → A p q = (B * L * Bᵀ) p q)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, opE (S.signedCoupling A * A) x⟫ =
      portOut B x ⬝ᵥ (S.signedPorts psub L *ᵥ portOut B (opE A x)) := by
  have h1 : ⟪x, opE (S.signedCoupling A * A) x⟫ =
      (fun p => x p) ⬝ᵥ (S.signedCoupling A *ᵥ fun p => (opE A x) p) := by
    rw [opE_mul_apply, inner_eq_sum]
    exact Finset.sum_congr rfl fun r _ => by
      rw [opE_apply]
      rfl
  rw [h1, S.signedCoupling_eq_ports hB hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dot_mulVec_swap, dotProduct_comm]
  rfl

/-- The right-hand side of the identity as a double sum over the ports:
`yᵀ L_ς z = Σ_a Σ_b [psub a ≠ psub b] ς(psub a, psub b) y_a L_ab z_b`. -/
theorem dotProduct_signedPorts (psub : Fin m → κ) (L : Matrix (Fin m) (Fin m) ℝ)
    (y z : Fin m → ℝ) :
    y ⬝ᵥ (S.signedPorts psub L *ᵥ z) =
      ∑ a, ∑ b, if psub a = psub b then 0 else S.sg (psub a) (psub b) * (y a * L a b * z b) := by
  change ∑ a, y a * ∑ b, S.signedPorts psub L a b * z b = _
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [S.signedPorts_apply]
  by_cases hab : psub a = psub b
  · rw [ite_eq_left hab, ite_eq_left hab, zero_mul, mul_zero]
  · rw [ite_eq_right hab, ite_eq_right hab]
    ring

/-- **The numerical dissipation of the zero-order hold at the ports**, in every
order of execution. If the coupling blocks of `A` are `B_i L_ik B_kᵀ`, then for `0 < H`,
`H ‖A‖ ≤ 1/24` and `√(card κ) · H ‖A‖ ≤ 1/6` the numerical dissipation `Δ_R` of the modified
system of the zero-order hold satisfies, for every `x`,

  `|xᵀ Δ_R x + (H/2) yᵀ L_ς ẏ| ≤ (37 + 220σ + 53σ² + 54σ³) ‖A‖³ · H² ‖x‖²`,   `σ = √(card κ)`,

with `y = Bᵀ x`, `ẏ = Bᵀ A x`: `xᵀ Δ_R x = -(H/2) Σ_i y_iᵀ Σ_k ς_ik L_ik ẏ_k + O(H² |x|²)`. -/
theorem abs_numDissipation_zoh_ports_le [Fintype κ]
    (hA0 : ∀ p q, S.sub p ≠ S.sub q → ¬ S.partner (S.sub p) (S.sub q) → A p q = 0)
    (hB : ∀ p a, S.sub p ≠ psub a → B p a = 0)
    (hA : ∀ p q, S.sub p ≠ S.sub q → A p q = (B * L * Bᵀ) p q) {H : ℝ}
    (hH : 0 < H) (hAH : H * ‖opE A‖ ≤ 1 / 24)
    (hσ : Real.sqrt (Fintype.card κ) * (H * ‖opE A‖) ≤ 1 / 6) (x : EuclideanSpace ℝ (Fin n)) :
    |⟪x, opE (numDissipation A (modifiedSystem H (S.zoh A hA0 H).X)) x⟫ +
        H / 2 * (portOut B x ⬝ᵥ (S.signedPorts psub L *ᵥ portOut B (opE A x)))| ≤
      zohDiffK (Real.sqrt (Fintype.card κ)) ‖opE A‖ * H ^ 2 * ‖x‖ ^ 2 := by
  have h := S.abs_inner_numDissipation_sub_le
    (S.norm_zoh_difference_sub_half_le hA0 hH hAH hσ) x x
  have e : ⟪x, opE (S.halfStepDissipation A H) x⟫ =
      -(H / 2 * (portOut B x ⬝ᵥ (S.signedPorts psub L *ᵥ portOut B (opE A x)))) := by
    rw [halfStepDissipation, inner_opE_smul, inner_opE_sym_eq,
      S.inner_signedCoupling_mul_self_ports hB hA]
    ring
  rwa [e, sub_neg_eq_add, ← sq] at h

/-- **A skew interconnection gives power-conjugate ports:** if `L_ba = -L_ab` and the coupling
blocks of `A` are those of `B L Bᵀ`, then `A q p = -A p q` between different subsystems. -/
theorem skew_of_ports (hA : ∀ p q, S.sub p ≠ S.sub q → A p q = (B * L * Bᵀ) p q)
    (hL : ∀ a b, L b a = -L a b) (p q : Fin n) (hpq : S.sub p ≠ S.sub q) :
    A q p = -A p q := by
  have hLt : Lᵀ = -L := by
    ext a b
    rw [Matrix.transpose_apply, Matrix.neg_apply]
    exact hL a b
  have ht : (B * L * Bᵀ)ᵀ = -(B * L * Bᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hLt,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have h1 : (B * L * Bᵀ) q p = -(B * L * Bᵀ) p q := by
    have h2 := congrFun (congrFun ht p) q
    rwa [Matrix.transpose_apply, Matrix.neg_apply] at h2
  rw [hA q p hpq.symm, hA p q hpq, h1]

/-- **The two forms of the leading numerical dissipation are the same number.** With a skew
interconnection, the form with the two rates of `HalfStepDissipation` is the form at the ports:
`Σ_k (|a_k⁺ x|² - |a_k⁻ x|²) - xᵀ A_ς A₀ x = -yᵀ L_ς ẏ`. -/
theorem sum_drive_sub_eq_ports [Fintype κ] (hB : ∀ p a, S.sub p ≠ psub a → B p a = 0)
    (hA : ∀ p q, S.sub p ≠ S.sub q → A p q = (B * L * Bᵀ) p q)
    (hL : ∀ a b, L b a = -L a b) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ k, (‖opE (S.driveAfter A k) x‖ ^ 2 - ‖opE (S.driveOther A k) x‖ ^ 2) -
        ⟪x, opE (S.signedCoupling A * S.blockDiag A) x⟫ =
      -(portOut B x ⬝ᵥ (S.signedPorts psub L *ᵥ portOut B (opE A x))) := by
  have h1 := S.inner_sym_signedCoupling_mul_self (S.skew_of_ports hA hL) x
  rw [inner_opE_sym_eq, S.inner_signedCoupling_mul_self_ports hB hA] at h1
  linarith

end HeldScheme

end CoSimFoundations
