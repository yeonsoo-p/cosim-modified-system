/-
The rank floor: one statement behind the floors of all one-sample classes.

Finite-dimensional real inner product spaces. `D` the defect, `U` the reference step, `X = D ∘ U`
on the states `E`. A subsystem (or a subsystem together with the samples it is shown) is read out by
`P : E → F` with `‖P‖ ≤ 1`. A set of test directions is given by `Y : G → E` such that the
reference maps them isometrically: `Q = U ∘ Y` with `‖Q‖ ≤ 1` (for instance
`Y = V (Vᵀ Uᵀ U V)^{-1/2}` for a subspace `V` of states the subsystem is not shown). `Z : E → F` is
the part of the scheme's answer that is known beforehand (zero; or the subsystem's own decay if it
has no local gain).

**Rank floor.** If the scheme's answer on the test directions, beyond the known part, has rank at
most `r` (`rank (P ∘ X ∘ Y - Z ∘ Y) ≤ r`), then

  `σ_{r+1} (P ∘ Q - Z ∘ Y) ≤ ‖D - 1‖`.

Instances: `r = 0` is the link floor and the floor from the kernel of an output map (the scheme
answers nothing on directions it is not shown); `r = m` is Gauss–Seidel with `m` new samples;
`r` = the number of samples shown is the count floor; `Z` = the own decay gives the floor of a
scheme without local gains.

Proof: `P ∘ (D - 1) ∘ Q = (P ∘ X ∘ Y - Z ∘ Y) - (P ∘ Q - Z ∘ Y)` because `D ∘ Q = X ∘ Y`; the first
term has rank at most `r`, the left side has norm at most `‖D - 1‖`; apply
`singularValues_le_norm_sub_of_rank_le` (`MemoryFloorSV.lean`).
-/
import CoSimFoundations.MemoryFloorSV

open Module
open scoped RealInnerProductSpace

namespace CoSimFoundations

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The algebra behind the rank floor: `P ∘ (D - 1) ∘ Q = (P ∘ X ∘ Y - Z ∘ Y) - (P ∘ Q - Z ∘ Y)`
when `Q = U ∘ Y`, written as the difference that enters `singularValues_le_norm_sub_of_rank_le`. -/
theorem rank_floor_identity (P : E →L[ℝ] F) (Q Y : G →L[ℝ] E) (D U : E →L[ℝ] E)
    (Z : E →L[ℝ] F) (hUY : U.comp Y = Q) :
    P.comp Q - Z.comp Y - (P.comp ((D.comp U).comp Y) - Z.comp Y) =
      -(P.comp ((D - 1).comp Q)) := by
  subst hUY
  ext x
  simp

/-- Sandwiching between contractions does not increase the operator norm. -/
theorem norm_comp_comp_le_of_le_one (P : E →L[ℝ] F) (T : E →L[ℝ] E) (Q : G →L[ℝ] E)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) : ‖P.comp (T.comp Q)‖ ≤ ‖T‖ :=
  calc ‖P.comp (T.comp Q)‖ ≤ ‖T.comp Q‖ :=
        (P.opNorm_comp_le _).trans (mul_le_of_le_one_left (norm_nonneg _) hP)
    _ ≤ ‖T‖ := (T.opNorm_comp_le Q).trans (mul_le_of_le_one_right (norm_nonneg _) hQ)

/-- **The rank floor.** -/
theorem rank_floor (P : E →L[ℝ] F) (Q Y : G →L[ℝ] E) (D U : E →L[ℝ] E) (Z : E →L[ℝ] F)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hUY : U.comp Y = Q) {r : ℕ}
    (hr : finrank ℝ (LinearMap.range
      ((P.comp ((D.comp U).comp Y) - Z.comp Y : G →L[ℝ] F) : G →ₗ[ℝ] F)) ≤ r) :
    ((P.comp Q - Z.comp Y : G →L[ℝ] F) : G →ₗ[ℝ] F).singularValues r ≤ ‖D - 1‖ := by
  calc ((P.comp Q - Z.comp Y : G →L[ℝ] F) : G →ₗ[ℝ] F).singularValues r
      ≤ ‖P.comp Q - Z.comp Y - (P.comp ((D.comp U).comp Y) - Z.comp Y)‖ :=
        singularValues_le_norm_sub_of_rank_le _ _ hr
    _ = ‖P.comp ((D - 1).comp Q)‖ := by rw [rank_floor_identity P Q Y D U Z hUY, norm_neg]
    _ ≤ ‖D - 1‖ := norm_comp_comp_le_of_le_one P (D - 1) Q hP hQ

/-- **The case `r = 0`: the scheme answers nothing on the test directions** (beyond the known
part): the reference's answer there is a floor under the one-step error. -/
theorem rank_floor_zero (P : E →L[ℝ] F) (Q Y : G →L[ℝ] E) (D U : E →L[ℝ] E) (Z : E →L[ℝ] F)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hUY : U.comp Y = Q)
    (h0 : P.comp ((D.comp U).comp Y) = Z.comp Y) :
    ‖P.comp Q - Z.comp Y‖ ≤ ‖D - 1‖ := by
  have key := rank_floor_identity P Q Y D U Z hUY
  rw [h0, sub_self, sub_zero] at key
  rw [key, norm_neg]
  exact norm_comp_comp_le_of_le_one P (D - 1) Q hP hQ

end CoSimFoundations
