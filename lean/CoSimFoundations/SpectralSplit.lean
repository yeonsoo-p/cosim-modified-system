/-
Real spectral splitting (the real logarithms on the parts,
the trajectory formula, Culver's criterion and eq. (13) are not here). The dominant modified system
needs a split by modulus, which is not built here.

For a linear map `f` on a finite-dimensional real space, the characteristic polynomial factors as
`p = p_c * (p_- * p_0)` with
  p_- = ∏ (X - r) over the negative real roots (with multiplicity),
  p_0 = ∏ (X - 0) over the zero roots, i.e. X^k,
  p_c the cofactor, which has no real root in (-∞, 0],
and the space splits as the direct sum of the kernels
  Z_c = ker p_c(f),  Z_- = ker p_-(f),  Z_0 = ker p_0(f),
each f-invariant. The splitting is unique: any decomposition V_c ⊔ V_- ⊔ V_0 = ⊤ with
V_c ≤ ker q_c(f) (q_c without roots in (-∞, 0]), V_- ≤ ker q_-(f) (q_- a product of X - r, r < 0)
and V_0 ≤ ker q_0(f) (q_0 a product of X - 0) equals it. "Annihilated by a polynomial whose real
roots lie in S" is the real-coefficient form of "the restriction has its spectrum in S" (for S_c,
non-real eigenvalues are allowed; for S_- and S_0 the polynomial splits over ℝ).

Part A is general (any field): splitting by a coprime factorisation of an annihilating polynomial.
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Basic.Real.Basic

open Polynomial LinearMap

namespace CoSimFoundations

/-! ### Part A: splitting by a coprime factorisation -/

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (f : V →ₗ[K] V)

/-- A polynomial in `f` commutes with `f`. -/
theorem aeval_mul_self_comm (q : K[X]) : aeval f q * f = f * aeval f q := by
  have h := congrArg (aeval f) (mul_comm q X)
  simpa only [map_mul, aeval_X] using h

/-- Polynomials in `f` commute. -/
theorem aeval_mul_aeval_comm (p q : K[X]) : aeval f p * aeval f q = aeval f q * aeval f p := by
  rw [← map_mul, ← map_mul, mul_comm]

/-- Kernels of polynomials in `f` are `f`-invariant. -/
theorem map_mem_ker_aeval {q : K[X]} {v : V} (hv : v ∈ ker (aeval f q)) :
    f v ∈ ker (aeval f q) := by
  rw [mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, aeval_mul_self_comm, Module.End.mul_apply, hv, map_zero]

/-- Kernels of polynomials in `f` are invariant under every polynomial in `f`. -/
theorem aeval_mem_ker_aeval {p q : K[X]} {v : V} (hv : v ∈ ker (aeval f q)) :
    aeval f p v ∈ ker (aeval f q) := by
  rw [mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, aeval_mul_aeval_comm, Module.End.mul_apply, hv, map_zero]

variable {f}

/-- **Splitting.** If `a * b` annihilates `f` and `a, b` are coprime, `V = ker a(f) ⊕ ker b(f)`. -/
theorem ker_sup_ker_eq_top {a b : K[X]} (hab : IsCoprime a b) (hann : aeval f (a * b) = 0) :
    ker (aeval f a) ⊔ ker (aeval f b) = ⊤ := by
  rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hab, hann, ker_zero]

theorem disjoint_ker {a b : K[X]} (hab : IsCoprime a b) :
    Disjoint (ker (aeval f a)) (ker (aeval f b)) :=
  disjoint_ker_aeval_of_isCoprime f hab

/-- **Uniqueness, one part.** If `a * b` annihilates `f`, `a, b` coprime, and `W ≤ ker q(f)` with
`q` coprime to `b`, then `W ≤ ker a(f)`. -/
theorem le_ker_of_coprime {a b q : K[X]} (hab : IsCoprime a b) (hann : aeval f (a * b) = 0)
    (hqb : IsCoprime q b) {W : Submodule K V} (hW : W ≤ ker (aeval f q)) :
    W ≤ ker (aeval f a) := by
  intro v hv
  have hall : v ∈ ker (aeval f a) ⊔ ker (aeval f b) := by
    rw [ker_sup_ker_eq_top hab hann]; trivial
  obtain ⟨va, hva, vb, hvb, rfl⟩ := Submodule.mem_sup.1 hall
  have hq : aeval f q va + aeval f q vb = 0 := by
    rw [← map_add]; exact mem_ker.1 (hW hv)
  have hqa : aeval f q va ∈ ker (aeval f a) := aeval_mem_ker_aeval f hva
  have hqb' : aeval f q vb ∈ ker (aeval f b) := aeval_mem_ker_aeval f hvb
  have hzero : aeval f q vb = 0 := by
    have hneg : aeval f q vb = -aeval f q va := eq_neg_of_add_eq_zero_right hq
    have hmem : aeval f q vb ∈ ker (aeval f a) := by rw [hneg]; exact neg_mem hqa
    exact (Submodule.disjoint_def.1 (disjoint_ker hab)) _ hmem hqb'
  have hvb0 : vb = 0 :=
    (Submodule.disjoint_def.1 (disjoint_ker (f := f) hqb)) _ (mem_ker.2 hzero) hvb
  rw [hvb0, add_zero]; exact hva

/-- Two decompositions with `V_i ≤ Z_i`, the `V_i` spanning and the `Z_i` independent, agree. -/
theorem eq_of_le_of_sup {Z₁ Z₂ Z₃ V₁ V₂ V₃ : Submodule K V} (h₁ : V₁ ≤ Z₁) (h₂ : V₂ ≤ Z₂)
    (h₃ : V₃ ≤ Z₃) (hV : V₁ ⊔ (V₂ ⊔ V₃) = ⊤) (hd₁ : Disjoint Z₁ (Z₂ ⊔ Z₃)) (hd₂ : Disjoint Z₂ Z₃) :
    V₁ = Z₁ ∧ V₂ = Z₂ ∧ V₃ = Z₃ := by
  have hdec : ∀ z : V, ∃ v₁ ∈ V₁, ∃ v₂ ∈ V₂, ∃ v₃ ∈ V₃, z = v₁ + (v₂ + v₃) := by
    intro z
    have hz : z ∈ V₁ ⊔ (V₂ ⊔ V₃) := by rw [hV]; trivial
    obtain ⟨v₁, hv₁, w, hw, hzw⟩ := Submodule.mem_sup.1 hz
    obtain ⟨v₂, hv₂, v₃, hv₃, hw'⟩ := Submodule.mem_sup.1 hw
    exact ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, by rw [← hzw, ← hw']⟩
  have hd₁' := Submodule.disjoint_def.1 hd₁
  have hd₂' := Submodule.disjoint_def.1 hd₂
  refine ⟨le_antisymm h₁ ?_, le_antisymm h₂ ?_, le_antisymm h₃ ?_⟩
  · intro z hz
    obtain ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, rfl⟩ := hdec z
    have h23 : v₂ + v₃ ∈ Z₂ ⊔ Z₃ := Submodule.add_mem_sup (h₂ hv₂) (h₃ hv₃)
    have h23' : v₂ + v₃ ∈ Z₁ := by
      have := Z₁.sub_mem hz (h₁ hv₁); simpa using this
    rw [hd₁' _ h23' h23, add_zero]; exact hv₁
  · intro z hz
    obtain ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, rfl⟩ := hdec z
    have hz23 : v₁ + (v₂ + v₃) ∈ Z₂ ⊔ Z₃ := Submodule.mem_sup_left hz
    have hv₁' : v₁ ∈ Z₂ ⊔ Z₃ := by
      have := (Z₂ ⊔ Z₃).sub_mem hz23 (Submodule.add_mem_sup (h₂ hv₂) (h₃ hv₃))
      simpa using this
    have hv₁0 : v₁ = 0 := hd₁' _ (h₁ hv₁) hv₁'
    have hv₃' : v₃ ∈ Z₂ := by
      have := Z₂.sub_mem hz (h₂ hv₂); simpa [hv₁0] using this
    rw [hv₁0, hd₂' _ hv₃' (h₃ hv₃), zero_add, add_zero]; exact hv₂
  · intro z hz
    obtain ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, rfl⟩ := hdec z
    have hz23 : v₁ + (v₂ + v₃) ∈ Z₂ ⊔ Z₃ := Submodule.mem_sup_right hz
    have hv₁' : v₁ ∈ Z₂ ⊔ Z₃ := by
      have := (Z₂ ⊔ Z₃).sub_mem hz23 (Submodule.add_mem_sup (h₂ hv₂) (h₃ hv₃))
      simpa using this
    have hv₁0 : v₁ = 0 := hd₁' _ (h₁ hv₁) hv₁'
    have hv₂' : v₂ ∈ Z₃ := by
      have := Z₃.sub_mem hz (h₃ hv₃); simpa [hv₁0] using this
    rw [hv₁0, hd₂' _ (h₂ hv₂) hv₂', zero_add, zero_add]; exact hv₃

end General

/-! ### Part B: the real root partition of a polynomial -/

section RootPartition

/-- `∏ (X - r)` over a multiset. -/
noncomputable def linProd (s : Multiset ℝ) : ℝ[X] := (s.map fun a => X - C a).prod

theorem linProd_add (s t : Multiset ℝ) : linProd (s + t) = linProd s * linProd t := by
  simp [linProd, Multiset.map_add, Multiset.prod_add]

theorem linProd_monic (s : Multiset ℝ) : (linProd s).Monic :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem roots_linProd (s : Multiset ℝ) : (linProd s).roots = s := roots_multiset_prod_X_sub_C s

/-- A polynomial with no root in `S` is coprime to `∏ (X - r)` over a multiset in `S`. -/
theorem isCoprime_linProd {q : ℝ[X]} {s : Multiset ℝ} {S : Set ℝ} (hq : ∀ r ∈ S, ¬q.IsRoot r)
    (hs : ∀ r ∈ s, r ∈ S) : IsCoprime q (linProd s) := by
  unfold linProd
  induction s using Multiset.induction_on with
  | empty => simpa using isCoprime_one_right
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine IsCoprime.mul_right ?_ (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr))
    refine IsCoprime.symm ((irreducible_X_sub_C a).coprime_iff_not_dvd.2 ?_)
    rw [dvd_iff_isRoot]
    exact hq a (hs a (Multiset.mem_cons_self a s))

theorem not_isRoot_linProd {s : Multiset ℝ} {r : ℝ} (hr : r ∉ s) : ¬(linProd s).IsRoot r := by
  intro h
  have : r ∈ (linProd s).roots := (mem_roots (linProd_monic s).ne_zero).2 h
  rw [roots_linProd] at this
  exact hr this

variable (p : ℝ[X])

/-- The negative real roots, with multiplicity. -/
noncomputable def negRoots : Multiset ℝ := p.roots.filter (· < 0)
/-- The zero roots, with multiplicity. -/
noncomputable def zeroRoots : Multiset ℝ := p.roots.filter (· = 0)

/-- `p_-`. -/
noncomputable def pNeg : ℝ[X] := linProd (negRoots p)
/-- `p_0`. -/
noncomputable def pZero : ℝ[X] := linProd (zeroRoots p)
/-- `p_c = p /ₘ (p_- p_0)`. -/
noncomputable def pCo : ℝ[X] := p /ₘ (pNeg p * pZero p)

theorem negRoots_add_zeroRoots_le : negRoots p + zeroRoots p ≤ p.roots := by
  rw [negRoots, zeroRoots, Multiset.le_iff_count]
  intro a
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
  by_cases h1 : a < 0
  · simp [h1, h1.ne]
  · by_cases h2 : a = 0 <;> simp [h1, h2]

theorem pNeg_mul_pZero : pNeg p * pZero p = linProd (negRoots p + zeroRoots p) := by
  rw [pNeg, pZero, linProd_add]

theorem pNeg_mul_pZero_dvd : pNeg p * pZero p ∣ p := by
  rw [pNeg_mul_pZero]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map (negRoots_add_zeroRoots_le p))).trans
    (prod_multiset_X_sub_C_dvd p)

/-- **The factorisation** `p = p_c * (p_- * p_0)`. -/
theorem factor_eq : p = pCo p * (pNeg p * pZero p) := by
  have hm : (pNeg p * pZero p).Monic := by rw [pNeg_mul_pZero]; exact linProd_monic _
  have h := modByMonic_add_div p (pNeg p * pZero p)
  rw [(modByMonic_eq_zero_iff_dvd hm).2 (pNeg_mul_pZero_dvd p), zero_add] at h
  rw [pCo, mul_comm]; exact h.symm

/-- `p_c` has no real root in `(-∞, 0]`. -/
theorem pCo_not_isRoot (hp : p ≠ 0) {r : ℝ} (hr : r ≤ 0) : ¬(pCo p).IsRoot r := by
  intro hroot
  have hfac := factor_eq p
  have hne : pCo p * (pNeg p * pZero p) ≠ 0 := by rw [← hfac]; exact hp
  have hroots : p.roots = (pCo p).roots + (negRoots p + zeroRoots p) := by
    conv_lhs => rw [hfac]
    rw [roots_mul hne, pNeg_mul_pZero, roots_linProd]
  have hpc0 : pCo p ≠ 0 := left_ne_zero_of_mul hne
  have hmem : r ∈ (pCo p).roots := (mem_roots hpc0).2 hroot
  have hcount := congrArg (Multiset.count r) hroots
  rw [Multiset.count_add, Multiset.count_add, negRoots, zeroRoots, Multiset.count_filter,
    Multiset.count_filter] at hcount
  have hpos : 0 < Multiset.count r (pCo p).roots := Multiset.count_pos.2 hmem
  have hnz : Multiset.count r (negRoots p + zeroRoots p) = Multiset.count r p.roots := by
    rw [Multiset.count_add, negRoots, zeroRoots, Multiset.count_filter, Multiset.count_filter]
    rcases lt_or_eq_of_le hr with h | h
    · simp [h, h.ne]
    · simp [h]
  have hcount := congrArg (Multiset.count r) hroots
  rw [Multiset.count_add, hnz] at hcount
  omega

theorem negRoots_neg {r : ℝ} (hr : r ∈ negRoots p) : r < 0 := (Multiset.mem_filter.1 hr).2
theorem zeroRoots_zero {r : ℝ} (hr : r ∈ zeroRoots p) : r = 0 := (Multiset.mem_filter.1 hr).2

theorem isCoprime_pCo (hp : p ≠ 0) : IsCoprime (pCo p) (pNeg p * pZero p) := by
  rw [pNeg_mul_pZero]
  refine isCoprime_linProd (S := Set.Iic 0) (fun r hr => pCo_not_isRoot p hp hr) ?_
  intro r hr
  rcases Multiset.mem_add.1 hr with h | h
  · exact (negRoots_neg p h).le
  · exact (zeroRoots_zero p h).le

theorem isCoprime_pNeg_pZero : IsCoprime (pNeg p) (pZero p) := by
  refine IsCoprime.symm (isCoprime_linProd (S := Set.Iio 0) (fun r hr => ?_) fun r h => negRoots_neg p h)
  apply not_isRoot_linProd
  intro h0
  exact (ne_of_lt hr) (zeroRoots_zero p h0)

end RootPartition

/-! ### Part C: the splitting of a real linear map

Stated for any nonzero annihilating polynomial `p` of `f` (the characteristic polynomial by
Cayley–Hamilton, or the minimal polynomial), then specialised to the characteristic polynomial. -/

section Split

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (f : V →ₗ[ℝ] V) (p : ℝ[X])

/-- `Z_c`: no eigenvalue in `(-∞, 0]`. -/
noncomputable def Zc : Submodule ℝ V := ker (aeval f (pCo p))
/-- `Z_-`: eigenvalues negative real. -/
noncomputable def Zneg : Submodule ℝ V := ker (aeval f (pNeg p))
/-- `Z_0`: nilpotent part. -/
noncomputable def Zzero : Submodule ℝ V := ker (aeval f (pZero p))

variable {f p}

theorem aeval_factor_eq_zero (hann : aeval f p = 0) :
    aeval f (pCo p * (pNeg p * pZero p)) = 0 := by
  rw [← factor_eq]; exact hann

/-- **Existence.** `V = Z_c ⊕ (Z_- ⊕ Z_0)`. -/
theorem spectral_split (hp : p ≠ 0) (hann : aeval f p = 0) :
    Zc f p ⊔ (Zneg f p ⊔ Zzero f p) = ⊤ ∧ Disjoint (Zc f p) (Zneg f p ⊔ Zzero f p) ∧
      Disjoint (Zneg f p) (Zzero f p) := by
  have hc := isCoprime_pCo p hp
  have hnz := isCoprime_pNeg_pZero p
  have hsplit2 : Zneg f p ⊔ Zzero f p = ker (aeval f (pNeg p * pZero p)) :=
    sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hnz
  refine ⟨?_, ?_, disjoint_ker hnz⟩
  · rw [hsplit2]; exact ker_sup_ker_eq_top hc (aeval_factor_eq_zero hann)
  · rw [hsplit2]; exact disjoint_ker hc

theorem Zc_invariant {v : V} (hv : v ∈ Zc f p) : f v ∈ Zc f p := map_mem_ker_aeval f hv
theorem Zneg_invariant {v : V} (hv : v ∈ Zneg f p) : f v ∈ Zneg f p := map_mem_ker_aeval f hv
theorem Zzero_invariant {v : V} (hv : v ∈ Zzero f p) : f v ∈ Zzero f p := map_mem_ker_aeval f hv

theorem isCoprime_pNeg_rest (hp : p ≠ 0) : IsCoprime (pNeg p) (pCo p * pZero p) :=
  IsCoprime.mul_right (IsCoprime.of_mul_left_left (isCoprime_pCo p hp).symm)
    (isCoprime_pNeg_pZero p)

theorem isCoprime_pZero_rest (hp : p ≠ 0) : IsCoprime (pZero p) (pCo p * pNeg p) :=
  IsCoprime.mul_right (IsCoprime.of_mul_left_right (isCoprime_pCo p hp).symm)
    (isCoprime_pNeg_pZero p).symm

/-- **Uniqueness.** Any splitting `V_c ⊔ (V_- ⊔ V_0) = ⊤` with `V_c` annihilated
by a polynomial without roots in `(-∞, 0]`, `V_-` by a product of `X - r` with `r < 0`, and `V_0`
by a product of `X - 0`, is the splitting of `spectral_split`. -/
theorem spectral_split_unique (hp : p ≠ 0) (hann : aeval f p = 0)
    {Vc Vn V0 : Submodule ℝ V} {qc : ℝ[X]} {sn s0 : Multiset ℝ}
    (hqc : ∀ r ≤ 0, ¬qc.IsRoot r) (hsn : ∀ r ∈ sn, r < 0) (hs0 : ∀ r ∈ s0, r = 0)
    (hVc : Vc ≤ ker (aeval f qc)) (hVn : Vn ≤ ker (aeval f (linProd sn)))
    (hV0 : V0 ≤ ker (aeval f (linProd s0))) (hV : Vc ⊔ (Vn ⊔ V0) = ⊤) :
    Vc = Zc f p ∧ Vn = Zneg f p ∧ V0 = Zzero f p := by
  have hann' := aeval_factor_eq_zero hann
  have h₁ : Vc ≤ Zc f p := by
    refine le_ker_of_coprime (isCoprime_pCo p hp) hann' ?_ hVc
    rw [pNeg_mul_pZero]
    refine isCoprime_linProd (S := Set.Iic 0) (fun r hr => hqc r hr) fun r hr => ?_
    rcases Multiset.mem_add.1 hr with h | h
    · exact (negRoots_neg p h).le
    · exact (zeroRoots_zero p h).le
  have hann_n : aeval f (pNeg p * (pCo p * pZero p)) = 0 := by
    rw [mul_left_comm]; exact hann'
  have hann_0 : aeval f (pZero p * (pCo p * pNeg p)) = 0 := by
    rw [mul_left_comm, mul_comm (pZero p)]; exact hann'
  have h₂ : Vn ≤ Zneg f p := by
    refine le_ker_of_coprime (isCoprime_pNeg_rest hp) hann_n ?_ hVn
    refine IsCoprime.mul_right ?_ ?_
    · exact (isCoprime_linProd (S := Set.Iic 0) (fun r hr => pCo_not_isRoot p hp hr)
        fun r h => (hsn r h).le).symm
    · refine IsCoprime.symm (isCoprime_linProd (S := Set.Iio 0) (fun r hr => ?_) hsn)
      exact not_isRoot_linProd fun h0 => (ne_of_lt hr) (zeroRoots_zero p h0)
  have h₃ : V0 ≤ Zzero f p := by
    refine le_ker_of_coprime (isCoprime_pZero_rest hp) hann_0 ?_ hV0
    refine IsCoprime.mul_right ?_ ?_
    · exact (isCoprime_linProd (S := Set.Iic 0) (fun r hr => pCo_not_isRoot p hp hr)
        fun r h => (hs0 r h).le).symm
    · refine IsCoprime.symm (isCoprime_linProd (S := {0}) (fun r hr => ?_) hs0)
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact not_isRoot_linProd fun h0 => (lt_irrefl _) (negRoots_neg p h0)
  obtain ⟨_, hd₁, hd₂⟩ := spectral_split hp hann
  exact eq_of_le_of_sup h₁ h₂ h₃ hV hd₁ hd₂

/-! #### Eigenvalue reading of the three parts (real eigenvectors; complex eigenvalues are the
roots of the annihilating factors, which `Zneg` and `Zzero` have only on the real axis). -/

theorem aeval_X_sub_C_apply (r : ℝ) (v : V) : aeval f (X - C r) v = f v - r • v := by
  simp [map_sub, aeval_X, aeval_C, Module.algebraMap_end_apply]

theorem eq_zero_of_eigen_of_coprime {q : ℝ[X]} {r : ℝ} (hq : ¬q.IsRoot r) {v : V}
    (hv : v ∈ ker (aeval f q)) (hev : f v = r • v) : v = 0 := by
  have hcop : IsCoprime q (X - C r) :=
    ((irreducible_X_sub_C r).coprime_iff_not_dvd.2 (by rwa [dvd_iff_isRoot])).symm
  refine (Submodule.disjoint_def.1 (disjoint_ker (f := f) hcop)) v hv ?_
  rw [mem_ker, aeval_X_sub_C_apply, hev, sub_self]

/-- On `Z_c` no real eigenvalue lies in `(-∞, 0]`. -/
theorem Zc_eigen (hp : p ≠ 0) {r : ℝ} (hr : r ≤ 0) {v : V} (hv : v ∈ Zc f p)
    (hev : f v = r • v) : v = 0 :=
  eq_zero_of_eigen_of_coprime (pCo_not_isRoot p hp hr) hv hev

/-- On `Z_-` every real eigenvalue is negative. -/
theorem Zneg_eigen {r : ℝ} {v : V} (hv : v ∈ Zneg f p) (hev : f v = r • v) (hv0 : v ≠ 0) :
    r < 0 := by
  by_contra hr
  exact hv0 (eq_zero_of_eigen_of_coprime
    (not_isRoot_linProd fun h => hr (negRoots_neg p h)) hv hev)

/-- On `Z_0` every real eigenvalue is zero. -/
theorem Zzero_eigen {r : ℝ} {v : V} (hv : v ∈ Zzero f p) (hev : f v = r • v) (hv0 : v ≠ 0) :
    r = 0 := by
  by_contra hr
  exact hv0 (eq_zero_of_eigen_of_coprime
    (not_isRoot_linProd fun h => hr (zeroRoots_zero p h)) hv hev)

/-- `p_0 = X ^ k`: `f` is nilpotent on `Z_0`. -/
theorem pZero_eq_X_pow : pZero p = X ^ Multiset.card (zeroRoots p) := by
  have h : zeroRoots p = Multiset.replicate (Multiset.card (zeroRoots p)) 0 :=
    Multiset.eq_replicate_card.2 fun r hr => zeroRoots_zero p hr
  rw [pZero, linProd]
  conv_lhs => rw [h]
  simp

/-- The splitting for the characteristic polynomial (Cayley–Hamilton). -/
theorem spectral_split_charpoly [Module.Free ℝ V] [Module.Finite ℝ V] (f : V →ₗ[ℝ] V) :
    Zc f f.charpoly ⊔ (Zneg f f.charpoly ⊔ Zzero f f.charpoly) = ⊤ ∧
      Disjoint (Zc f f.charpoly) (Zneg f f.charpoly ⊔ Zzero f f.charpoly) ∧
      Disjoint (Zneg f f.charpoly) (Zzero f f.charpoly) :=
  spectral_split (LinearMap.charpoly_monic f).ne_zero (LinearMap.aeval_self_charpoly f)

end Split

end CoSimFoundations
