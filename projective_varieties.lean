import Mathlib

open scoped LinearAlgebra.Projectivization
open MvPolynomial Set Ideal Projectivization Finset

/-!
# Projective Varieties — Hassett Chapter 7

Formalises projective algebraic geometry over a field `k`:
- Projective n-space `P^n(k)` and homogeneous coordinates (§7.1)
- Homogeneous polynomials and the scaling lemma (§7.2)
- Projective varieties and Zariski topology on `P^n(k)` (§7.3–7.4)
- Standard affine open charts and affine-projective correspondence (§7.5)
- Projective Nullstellensatz (§7.6)

References: Hassett, *Introduction to Algebraic Geometry*, Chapter 7.
-/

namespace ProjectiveVarieties

variable {k : Type*} [Field k]

/-! ## §7.1  Projective Space (Hassett §7.1) -/

section ProjectiveSpace

/-- *Projective n-space* over `k`: lines through the origin in `k^{n+1}`.
Uses Mathlib's `Projectivization` (notation `ℙ k V`). -/
abbrev Pn (k : Type*) [Field k] (n : ℕ) := ℙ k (Fin (n+1) → k)

/-- Two nonzero vectors represent the same projective point iff one is a nonzero scalar multiple
of the other.  `mk K u hu = mk K v hv ↔ ∃ a : Kˣ, a • v = u`. -/
theorem projMk_eq_iff {n : ℕ} {u v : Fin (n+1) → k} (hu : u ≠ 0) (hv : v ≠ 0) :
    Projectivization.mk k u hu = Projectivization.mk k v hv ↔ ∃ a : kˣ, a • v = u :=
  Projectivization.mk_eq_mk_iff k u v hu hv

/-- The canonical representative satisfies `mk k p.rep p.rep_nonzero = p`. -/
theorem mk_rep' {n : ℕ} (p : Pn k n) :
    Projectivization.mk k p.rep p.rep_nonzero = p :=
  Projectivization.mk_rep p

/-- Any `v` representing `mk k v hv` is a nonzero scalar multiple of the canonical `rep`.
`K` is explicit in `exists_smul_eq_mk_rep` (per `variable (K)` in Mathlib). -/
theorem exists_unit_smul_rep {n : ℕ} (v : Fin (n+1) → k) (hv : v ≠ 0) :
    ∃ a : kˣ, a • v = (Projectivization.mk k v hv).rep :=
  Projectivization.exists_smul_eq_mk_rep k v hv

end ProjectiveSpace

/-! ## §7.2  Homogeneous Polynomials (Hassett §7.2) -/

section HomogeneousPolynomials

variable {σ : Type*}

/-- **Hassett §7.2** — Scaling property: `f(r · v) = r^d · f(v)` for `f` homogeneous of degree `d`.
This ensures vanishing at a projective point is independent of the chosen representative. -/
theorem homogeneous_eval_smul {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (r : k) (v : σ → k) :
    MvPolynomial.eval (r • v) f = r ^ d * MvPolynomial.eval v f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.mem_support_iff] at hm
  -- hf hm : Finsupp.weight 1 m = d (since IsHomogeneous = IsWeightedHomogeneous 1)
  have hdm : ∑ i ∈ m.support, m i = d := by
    have h := hf hm
    rw [Finsupp.weight_apply] at h
    simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
    exact (show Finsupp.sum m (fun _ c => c) = ∑ i ∈ m.support, m i from rfl).symm.trans h
  simp only [Finsupp.prod]
  have hprod : ∏ i ∈ m.support, (r * v i) ^ m i = r ^ d * ∏ i ∈ m.support, v i ^ m i :=
    calc ∏ i ∈ m.support, (r * v i) ^ m i
        = ∏ i ∈ m.support, (r ^ m i * v i ^ m i) :=
          Finset.prod_congr rfl fun i _ => mul_pow r (v i) (m i)
      _ = (∏ i ∈ m.support, r ^ m i) * ∏ i ∈ m.support, v i ^ m i :=
          Finset.prod_mul_distrib
      _ = r ^ (∑ i ∈ m.support, m i) * ∏ i ∈ m.support, v i ^ m i := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = r ^ d * ∏ i ∈ m.support, v i ^ m i := by rw [hdm]
  rw [hprod]; ring

/-- For homogeneous `f` of degree `d` and `r ≠ 0`: `f(r · v) = 0 ↔ f(v) = 0`. -/
theorem homogeneous_eval_smul_eq_zero_iff {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) {r : k} (hr : r ≠ 0) (v : σ → k) :
    MvPolynomial.eval (r • v) f = 0 ↔ MvPolynomial.eval v f = 0 := by
  rw [homogeneous_eval_smul hf]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero d hr)
  · intro h; rw [h, mul_zero]

/-- An ideal `I ⊆ k[x₀,...,xₙ]` is *homogeneous* if every homogeneous component of
every element of `I` also lies in `I`. -/
def IsHomogeneousIdeal {n : ℕ} (I : Ideal (MvPolynomial (Fin (n+1)) k)) : Prop :=
  ∀ f ∈ I, ∀ d, MvPolynomial.homogeneousComponent d f ∈ I

theorem IsHomogeneousIdeal.bot {n : ℕ} :
    IsHomogeneousIdeal (⊥ : Ideal (MvPolynomial (Fin (n+1)) k)) := fun f hf d => by
  simp [Ideal.mem_bot.mp hf]

theorem IsHomogeneousIdeal.top {n : ℕ} :
    IsHomogeneousIdeal (⊤ : Ideal (MvPolynomial (Fin (n+1)) k)) :=
  fun _ _ _ => Submodule.mem_top

theorem IsHomogeneousIdeal.sup {n : ℕ} {I J : Ideal (MvPolynomial (Fin (n+1)) k)}
    (hI : IsHomogeneousIdeal I) (hJ : IsHomogeneousIdeal J) :
    IsHomogeneousIdeal (I ⊔ J) := fun f hf d => by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, hI a ha d, _, hJ b hb d, rfl⟩

theorem IsHomogeneousIdeal.inf {n : ℕ} {I J : Ideal (MvPolynomial (Fin (n+1)) k)}
    (hI : IsHomogeneousIdeal I) (hJ : IsHomogeneousIdeal J) :
    IsHomogeneousIdeal (I ⊓ J) := fun f hf d =>
  Ideal.mem_inf.mpr ⟨hI f (Ideal.mem_inf.mp hf).1 d, hJ f (Ideal.mem_inf.mp hf).2 d⟩

/-- Bridge: the project's `IsHomogeneousIdeal` is equivalent to Mathlib's graded-algebra
  notion `Ideal.IsHomogeneous (homogeneousSubmodule ...)`. -/
private theorem isHomogeneousIdeal_iff {n : ℕ} (I : Ideal (MvPolynomial (Fin (n+1)) k)) :
    IsHomogeneousIdeal I ↔
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n+1)) (R := k)
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) k) I := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (n+1)) (R := k)
  -- With gradedAlgebra, (DirectSum.decompose (homogeneousSubmodule _) r i : _) = homogeneousComponent i r.
  have heq : ∀ (r : MvPolynomial (Fin (n+1)) k) (i : ℕ),
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n+1)) k) r i :
        MvPolynomial (Fin (n+1)) k) = MvPolynomial.homogeneousComponent i r :=
    fun r i => MvPolynomial.decomposition.decompose'_apply r i
  -- Ideal.IsHomogeneous unfolds to SetLike.IsHomogeneous which unfolds to ∀ i m ∈ I, decompose m i ∈ I
  unfold IsHomogeneousIdeal Ideal.IsHomogeneous Submodule.IsHomogeneous
  constructor
  · intro hI i m hm
    rw [heq]
    exact hI m hm i
  · intro hI m hm i
    have h := hI (i := i) hm
    rw [heq] at h
    exact h

theorem IsHomogeneousIdeal.mul {n : ℕ} {I J : Ideal (MvPolynomial (Fin (n+1)) k)}
    (hI : IsHomogeneousIdeal I) (hJ : IsHomogeneousIdeal J) :
    IsHomogeneousIdeal (I * J) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (n+1)) (R := k)
  rw [isHomogeneousIdeal_iff] at hI hJ ⊢
  exact Ideal.IsHomogeneous.mul hI hJ

end HomogeneousPolynomials

/-! ## §7.3  Projective Varieties (Hassett §7.3) -/

section ProjectiveVarieties

variable {n : ℕ}

/-- The *projective zero locus* of an ideal `I ⊆ k[x₀,...,xₙ]`:
`p ∈ V_proj(I)` iff every `f ∈ I` vanishes at `p`'s canonical representative. -/
def projectiveZeroLocus (I : Ideal (MvPolynomial (Fin (n+1)) k)) : Set (Pn k n) :=
  {p | ∀ f ∈ I, MvPolynomial.eval p.rep f = 0}

/-- `V_proj(0) = P^n(k)`. -/
theorem projectiveZeroLocus_bot :
    projectiveZeroLocus (⊥ : Ideal (MvPolynomial (Fin (n+1)) k)) = Set.univ := by
  ext p; simp [projectiveZeroLocus]

/-- `V_proj(⊤) = ∅`. -/
theorem projectiveZeroLocus_top :
    projectiveZeroLocus (⊤ : Ideal (MvPolynomial (Fin (n+1)) k)) = ∅ := by
  ext p
  simp only [projectiveZeroLocus, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
             exists_prop]
  exact ⟨1, Submodule.mem_top, by simp⟩

/-- `V_proj` is anti-monotone: `I ≤ J → V_proj(J) ⊆ V_proj(I)`. -/
theorem projectiveZeroLocus_anti_mono {I J : Ideal (MvPolynomial (Fin (n+1)) k)} (h : I ≤ J) :
    projectiveZeroLocus J ⊆ projectiveZeroLocus I :=
  fun p hp f hf => hp f (h hf)

/-- `V_proj(I ∩ J) = V_proj(I) ∪ V_proj(J)` (uses that k is an integral domain). -/
theorem projectiveZeroLocus_inf {I J : Ideal (MvPolynomial (Fin (n+1)) k)} :
    projectiveZeroLocus (I ⊓ J) = projectiveZeroLocus I ∪ projectiveZeroLocus J := by
  ext p
  simp only [projectiveZeroLocus, Set.mem_setOf_eq, Ideal.mem_inf, Set.mem_union]
  constructor
  · intro hp
    by_contra hc
    simp only [not_or, not_forall, exists_prop] at hc
    obtain ⟨⟨f, hfI, hfp⟩, ⟨g, hgJ, hgp⟩⟩ := hc
    have hfgIJ : f * g ∈ I ⊓ J :=
      Ideal.mem_inf.mpr ⟨I.mul_mem_right g hfI, J.mul_mem_left f hgJ⟩
    have := hp (f * g) hfgIJ
    rw [map_mul] at this
    exact absurd this (mul_ne_zero hfp hgp)
  · rintro (hI | hJ) f ⟨hfI, hfJ⟩
    · exact hI f hfI
    · exact hJ f hfJ

/-- `V_proj(I · J) = V_proj(I) ∪ V_proj(J)`. -/
theorem projectiveZeroLocus_mul {I J : Ideal (MvPolynomial (Fin (n+1)) k)} :
    projectiveZeroLocus (I * J) = projectiveZeroLocus I ∪ projectiveZeroLocus J := by
  ext p
  simp only [projectiveZeroLocus, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro hp
    by_contra hc
    simp only [not_or, not_forall, exists_prop] at hc
    obtain ⟨⟨f, hfI, hfp⟩, ⟨g, hgJ, hgp⟩⟩ := hc
    have := hp (f * g) (Ideal.mul_mem_mul hfI hgJ)
    rw [map_mul] at this
    exact absurd this (mul_ne_zero hfp hgp)
  · rintro (hI | hJ) f hf
    · exact hI f (Ideal.mul_le_right hf)
    · exact hJ f (Ideal.mul_le_left hf)

/-- `V_proj(⨆ i, Iᵢ) = ⋂ i, V_proj(Iᵢ)`. -/
theorem projectiveZeroLocus_iSup {ι : Type*} (I : ι → Ideal (MvPolynomial (Fin (n+1)) k)) :
    projectiveZeroLocus (⨆ i, I i) = ⋂ i, projectiveZeroLocus (I i) := by
  ext p
  simp only [projectiveZeroLocus, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hp i f hf; exact hp f (le_iSup I i hf)
  · intro hp f hf
    -- Use that ker(eval p.rep) is an ideal containing each I i
    have hker : ⨆ i, I i ≤ RingHom.ker (MvPolynomial.eval p.rep) := by
      apply iSup_le; intro i g hg
      rw [RingHom.mem_ker]; exact hp i g hg
    exact RingHom.mem_ker.mp (hker hf)

end ProjectiveVarieties

/-! ## §7.4  Zariski Topology on P^n (Hassett §7.4) -/

section ZariskiTopologyPn

variable {n : ℕ}

/-- The *Zariski topology* on `P^n(k)`: closed sets are projective zero loci of homogeneous ideals.
We give the topology via `TopologicalSpace.ofClosed`. -/
@[reducible]
noncomputable def zariskiTopologyPn (k : Type*) [Field k] (n : ℕ) : TopologicalSpace (Pn k n) :=
  TopologicalSpace.ofClosed
    {C | ∃ I : Ideal (MvPolynomial (Fin (n+1)) k), IsHomogeneousIdeal I ∧
        C = projectiveZeroLocus I}
    -- ∅ = V_proj(⊤)
    ⟨⊤, IsHomogeneousIdeal.top, projectiveZeroLocus_top.symm⟩
    -- Arbitrary intersections of projective varieties
    (fun A hA => by
      classical
      -- Each C ∈ A is some V_proj(I_C)
      let I : ↑A → Ideal (MvPolynomial (Fin (n+1)) k) :=
        fun ⟨C, hC⟩ => (hA hC).choose
      have hIeq : ∀ C : ↑A, (C : Set (Pn k n)) = projectiveZeroLocus (I C) :=
        fun ⟨C, hC⟩ => (hA hC).choose_spec.2
      have hIhom : ∀ C : ↑A, IsHomogeneousIdeal (I C) :=
        fun ⟨C, hC⟩ => (hA hC).choose_spec.1
      -- ⋂₀ A = V_proj(⨆ I_C)
      refine ⟨⨆ C : ↑A, I C, ?_, ?_⟩
      · -- Sup of homogeneous ideals is homogeneous
        letI := MvPolynomial.gradedAlgebra (σ := Fin (n+1)) (R := k)
        rw [isHomogeneousIdeal_iff]
        have hIhom' : ∀ C : ↑A, Ideal.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Fin (n+1)) k) (I C) :=
          fun C => (isHomogeneousIdeal_iff (I C)).mp (hIhom C)
        exact Ideal.IsHomogeneous.iSup hIhom'
      · -- ⋂₀ A = ⋂ C, V_proj(I_C) = V_proj(⨆ I_C) by iSup lemma
        rw [projectiveZeroLocus_iSup]
        ext x
        simp only [Set.mem_sInter, Set.mem_iInter]
        constructor
        · intro hx ⟨C, hC⟩
          rw [← hIeq ⟨C, hC⟩]; exact hx C hC
        · intro hx C hC
          have := hx ⟨C, hC⟩
          rw [← hIeq ⟨C, hC⟩] at this; exact this)
    -- Finite union: V_proj(I) ∪ V_proj(J) = V_proj(I · J)
    (fun A ⟨I, hIhom, hI⟩ B ⟨J, hJhom, hJ⟩ =>
      ⟨I * J, IsHomogeneousIdeal.mul hIhom hJhom,
       by rw [hI, hJ, ← projectiveZeroLocus_mul]⟩)

/-- Projective zero loci of homogeneous ideals are Zariski-closed. -/
theorem isClosed_projectiveZeroLocus {I : Ideal (MvPolynomial (Fin (n+1)) k)}
    (hI : IsHomogeneousIdeal I) :
    @IsClosed _ (zariskiTopologyPn k n) (projectiveZeroLocus I) := by
  letI : TopologicalSpace (Pn k n) := zariskiTopologyPn k n
  refine ⟨?_⟩
  exact ⟨I, hI, compl_compl _⟩

/-- Every projective hypersurface `{f = 0}` for homogeneous `f` is Zariski-closed. -/
theorem isClosed_projectiveHypersurface {d : ℕ} (f : MvPolynomial (Fin (n+1)) k)
    (hf : f.IsHomogeneous d) :
    @IsClosed _ (zariskiTopologyPn k n) (projectiveZeroLocus (Ideal.span {f})) := by
  apply isClosed_projectiveZeroLocus
  letI := MvPolynomial.gradedAlgebra (σ := Fin (n+1)) (R := k)
  rw [isHomogeneousIdeal_iff]
  apply Ideal.homogeneous_span
  rintro x (rfl : x = f)
  exact ⟨d, hf⟩

end ZariskiTopologyPn

/-! ## §7.5  Standard Affine Charts (Hassett §7.5) -/

section AffineCharts

variable {n : ℕ}

/-- The `i`-th standard affine open of `P^n(k)`: `Uᵢ = {[v] | vᵢ ≠ 0}`.
We use the canonical representative `p.rep`. -/
def standardAffineOpen (i : Fin (n+1)) : Set (Pn k n) :=
  {p | p.rep i ≠ 0}

/-- The affine coordinate map on `Uᵢ`: `[v₀:...:vₙ] ↦ (vⱼ/vᵢ)_{j≠i}`. -/
noncomputable def affineCoord (i : Fin (n+1)) : standardAffineOpen (k := k) (n := n) i → Fin n → k :=
  fun ⟨p, _⟩ j => p.rep (i.succAbove j) / p.rep i

/-- The inverse map: embed `𝔸ⁿ(k)` into `Uᵢ ⊆ P^n(k)` via
`(u₀,...,u_{n-1}) ↦ [u₀:...:u_{i-1}:1:uᵢ:...:u_{n-1}]`. -/
noncomputable def homogenizeAt (i : Fin (n+1)) (u : Fin n → k) : Pn k n :=
  Projectivization.mk k (Fin.insertNth i 1 u) (by
    intro h; have := congr_fun h i
    simp [Fin.insertNth_apply_same] at this)

theorem homogenizeAt_mem (i : Fin (n+1)) (u : Fin n → k) :
    homogenizeAt i u ∈ standardAffineOpen i := by
  show (homogenizeAt i u).rep i ≠ 0
  obtain ⟨a, ha⟩ := exists_unit_smul_rep (Fin.insertNth i 1 u) (by
    intro h; have := congr_fun h i; simp [Fin.insertNth_apply_same] at this)
  have hdef : homogenizeAt i u =
      Projectivization.mk k (Fin.insertNth i 1 u) (by
        intro h; have := congr_fun h i; simp [Fin.insertNth_apply_same] at this) := rfl
  rw [hdef, ← ha, Pi.smul_apply, Fin.insertNth_apply_same, Units.smul_def, smul_eq_mul, mul_one]
  exact Units.ne_zero a

/-- `affineCoord` after `homogenizeAt` is the identity. -/
theorem affineCoord_homogenizeAt (i : Fin (n+1)) (u : Fin n → k) :
    affineCoord i ⟨homogenizeAt i u, homogenizeAt_mem i u⟩ = u := by
  ext j
  simp only [affineCoord]
  obtain ⟨a, ha⟩ := exists_unit_smul_rep (Fin.insertNth i 1 u) (by
    intro h; have := congr_fun h i; simp [Fin.insertNth_apply_same] at this)
  show (homogenizeAt i u).rep (i.succAbove j) / (homogenizeAt i u).rep i = u j
  have hdef : homogenizeAt i u =
      Projectivization.mk k (Fin.insertNth i 1 u) (by
        intro h; have := congr_fun h i; simp [Fin.insertNth_apply_same] at this) := rfl
  rw [hdef, ← ha]
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, Fin.insertNth_apply_succAbove,
             Fin.insertNth_apply_same, mul_one]
  exact mul_div_cancel_left₀ (u j) (Units.ne_zero a)

/-- `homogenizeAt` after `affineCoord` is the identity. -/
theorem homogenizeAt_affineCoord (i : Fin (n+1)) (p : standardAffineOpen i) :
    homogenizeAt i (affineCoord (k := k) i p) = p.1 := by
  simp only [homogenizeAt]
  have hvi : p.1.rep i ≠ 0 := p.2
  -- The coordinate vector with 1 at position i equals (1/vᵢ) • v
  have hvec : Fin.insertNth i 1 (affineCoord (k := k) i p) = (p.1.rep i)⁻¹ • p.1.rep := by
    ext j
    induction j using Fin.succAboveCases i with
    | x => simp [Fin.insertNth_apply_same, inv_mul_cancel₀ hvi]
    | p j' => simp [Fin.insertNth_apply_succAbove, affineCoord, div_eq_mul_inv, mul_comm]
  -- mk k (insertNth 1 (affineCoord i p)) = mk k p.rep = p
  conv_rhs => rw [← Projectivization.mk_rep p.1]
  exact Iff.mpr (Projectivization.mk_eq_mk_iff' k _ _ _ _) ⟨(p.1.rep i)⁻¹, hvec.symm⟩

/-- **Hassett Prop 7.10** — `Uᵢ ≅ 𝔸ⁿ(k)` as sets. -/
theorem standardAffineOpen_bijective (i : Fin (n+1)) :
    Function.Bijective (affineCoord (k := k) (n := n) i) := by
  constructor
  · intro ⟨p, hp⟩ ⟨q, hq⟩ heq
    exact Subtype.ext ((homogenizeAt_affineCoord i ⟨p, hp⟩).symm.trans
      (by rw [heq]; exact homogenizeAt_affineCoord i ⟨q, hq⟩))
  · intro u; exact ⟨⟨homogenizeAt i u, homogenizeAt_mem i u⟩, affineCoord_homogenizeAt i u⟩

/-- **Hassett §7.5** — Dehomogenization of `f ∈ k[x₀,...,xₙ]` at `xᵢ`:
set `xᵢ = 1`, giving `f(x₀,...,x_{i-1},1,x_{i+1},...,xₙ) ∈ k[y₀,...,y_{n-1}]`. -/
noncomputable def dehomogenizeHom (i : Fin (n+1)) :
    MvPolynomial (Fin (n+1)) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (Fin.insertNth i 1 MvPolynomial.X)

/-- Dehomogenization: `Xᵢ ↦ 1`. -/
theorem dehomogenizeHom_X_same (i : Fin (n+1)) :
    dehomogenizeHom (k := k) i (MvPolynomial.X i) = 1 := by
  simp [dehomogenizeHom, Fin.insertNth_apply_same]

/-- Dehomogenization: `X_{succAbove i j} ↦ Xⱼ`. -/
theorem dehomogenizeHom_X_succAbove (i : Fin (n+1)) (j : Fin n) :
    dehomogenizeHom (k := k) i (MvPolynomial.X (i.succAbove j)) = MvPolynomial.X j := by
  simp [dehomogenizeHom, Fin.insertNth_apply_succAbove]

/-- Evaluating a dehomogenized polynomial at `u` equals evaluating the original at
`Fin.insertNth i 1 u`. -/
private lemma dehomogenize_eval_eq (i : Fin (n+1)) (u : Fin n → k)
    (f : MvPolynomial (Fin (n+1)) k) :
    MvPolynomial.eval u (dehomogenizeHom i f) =
    MvPolynomial.eval (Fin.insertNth i 1 u) f := by
  have key : ((MvPolynomial.aeval u).comp (dehomogenizeHom i) :
      MvPolynomial (Fin (n+1)) k →ₐ[k] k) = MvPolynomial.aeval (Fin.insertNth i 1 u) := by
    apply MvPolynomial.algHom_ext; intro j
    simp only [AlgHom.comp_apply, dehomogenizeHom, MvPolynomial.aeval_X]
    induction j using Fin.succAboveCases i with
    | x => simp [Fin.insertNth_apply_same]
    | p j' => simp [Fin.insertNth_apply_succAbove, MvPolynomial.aeval_X]
  have := AlgHom.congr_fun key f
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] at this
  exact this

/-- For a homogeneous ideal `I`, evaluation vanishes at `r • v` whenever it vanishes at `v`. -/
private lemma eval_smul_zero_of_homog {σ : Type*}
    (I : Ideal (MvPolynomial σ k))
    (hI : ∀ f ∈ I, ∀ d, MvPolynomial.homogeneousComponent d f ∈ I)
    {v : σ → k} (hv : ∀ f ∈ I, MvPolynomial.eval v f = 0)
    {f : MvPolynomial σ k} (hf : f ∈ I) (r : k) :
    MvPolynomial.eval (r • v) f = 0 := by
  rw [← MvPolynomial.sum_homogeneousComponent f]
  simp only [map_sum]
  apply Finset.sum_eq_zero; intro d _
  rw [homogeneous_eval_smul (MvPolynomial.homogeneousComponent_isHomogeneous d f)]
  exact mul_eq_zero_of_right _ (hv _ (hI f hf d))

/-- The affine zero locus of a dehomogenized ideal equals the affine chart of the
projective zero locus (for a homogeneous ideal). -/
theorem proj_chart_eq_affine {I : Ideal (MvPolynomial (Fin (n+1)) k)}
    (hI : IsHomogeneousIdeal I) (i : Fin (n+1)) :
    affineCoord (k := k) i '' (Subtype.val ⁻¹' projectiveZeroLocus I : Set (standardAffineOpen i)) =
    MvPolynomial.zeroLocus k (I.map (dehomogenizeHom i).toRingHom) := by
  ext u
  simp only [Set.mem_image, Set.mem_preimage, MvPolynomial.mem_zeroLocus_iff,
             MvPolynomial.aeval_eq_eval]
  constructor
  · -- LHS → RHS: given [p] ∈ projective zero locus with affineCoord = u, show u ∈ affine locus
    rintro ⟨⟨p, hp⟩, hpI, rfl⟩ g hg
    -- g ∈ I.map (dehomogenizeHom i); show eval (affineCoord i ⟨p,hp⟩) g = 0
    -- Key: comap the kernel of eval (affineCoord i ...) back through dehomogenizeHom i
    have hker : I.map (dehomogenizeHom i).toRingHom ≤
        RingHom.ker (MvPolynomial.eval (affineCoord i ⟨p, hp⟩)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      show MvPolynomial.eval (affineCoord i ⟨p, hp⟩) (dehomogenizeHom i f) = 0
      rw [dehomogenize_eval_eq]
      -- insertNth i 1 (affineCoord i ⟨p,hp⟩) = (p.rep i)⁻¹ • p.rep
      have hvec : Fin.insertNth i 1 (affineCoord i ⟨p, hp⟩) = (p.rep i)⁻¹ • p.rep := by
        ext j; induction j using Fin.succAboveCases i with
        | x => simp [Fin.insertNth_apply_same, inv_mul_cancel₀ hp]
        | p j' => simp [Fin.insertNth_apply_succAbove, affineCoord, div_eq_mul_inv, mul_comm]
      rw [hvec]
      exact eval_smul_zero_of_homog I hI hpI hf _
    exact RingHom.mem_ker.mp (hker hg)
  · -- RHS → LHS: given u ∈ affine locus, lift to homogenizeAt i u ∈ projective locus
    intro h
    refine ⟨⟨homogenizeAt i u, homogenizeAt_mem i u⟩, ?_, affineCoord_homogenizeAt i u⟩
    -- Show homogenizeAt i u ∈ projectiveZeroLocus I
    intro f hf
    obtain ⟨a, ha⟩ := exists_unit_smul_rep (Fin.insertNth i 1 u) (by
      intro hh; have := congr_fun hh i; simp [Fin.insertNth_apply_same] at this)
    -- rep = a • (insertNth i 1 u)
    have hrep : (homogenizeAt i u).rep = a • (Fin.insertNth i 1 u : Fin (n+1) → k) := by
      conv_lhs =>
        rw [show homogenizeAt i u = Projectivization.mk k (Fin.insertNth i 1 u) _ from rfl]
      exact ha.symm
    rw [hrep]
    -- Convert kˣ-smul to k-smul, then use scaling lemma
    rw [show a • (Fin.insertNth i 1 u : Fin (n+1) → k) =
        (a : k) • (Fin.insertNth i 1 u : Fin (n+1) → k) from by simp [Units.smul_def]]
    apply eval_smul_zero_of_homog I hI _ hf
    -- ∀ g ∈ I, eval (insertNth i 1 u) g = 0 follows from u ∈ affine locus
    intro g hg
    have hmem : (dehomogenizeHom i) g ∈ I.map (dehomogenizeHom i).toRingHom :=
      Ideal.mem_map_of_mem _ hg
    have := h _ hmem
    rwa [dehomogenize_eval_eq] at this

end AffineCharts

/-! ## §7.6  Projective Nullstellensatz (Hassett §7.6) -/

section ProjectiveNullstellensatz

variable {n : ℕ}

/-- The *irrelevant ideal* `𝔪+ = ⟨x₀,...,xₙ⟩ ⊆ k[x₀,...,xₙ]`.
A homogeneous ideal `I` has `V_proj(I) = ∅` iff `√I ⊇ 𝔪+^N` for some `N`. -/
noncomputable def irrelevantIdeal (k : Type*) [Field k] (n : ℕ) :
    Ideal (MvPolynomial (Fin (n+1)) k) :=
  Ideal.span (Set.range MvPolynomial.X)

/-- The irrelevant ideal is homogeneous. -/
theorem IsHomogeneousIdeal.irrelevant {n : ℕ} :
    IsHomogeneousIdeal (irrelevantIdeal k n) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (n+1)) (R := k)
  rw [isHomogeneousIdeal_iff]
  apply Ideal.homogeneous_span
  rintro x ⟨i, rfl⟩
  exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩

/-- **Projective Nullstellensatz** (Hassett Thm 7.16) — For algebraically closed `k`:
`V_proj(I) = ∅ ↔ ∃ N, (𝔪+)^N ≤ I` (for `I` homogeneous, not ⊤). -/
theorem projective_nullstellensatz [IsAlgClosed k]
    {I : Ideal (MvPolynomial (Fin (n+1)) k)} (hI : IsHomogeneousIdeal I) (hI' : I ≠ ⊤) :
    projectiveZeroLocus I = ∅ ↔ ∃ N : ℕ, (irrelevantIdeal k n) ^ N ≤ I :=
  sorry

/-- **Projective Nullstellensatz** (variety form, Hassett Thm 7.18) — For algebraically closed `k`:
`I(V_proj(I)) = √I` (for `I` homogeneous). -/
theorem projective_vanishingIdeal_eq_radical [IsAlgClosed k]
    {I : Ideal (MvPolynomial (Fin (n+1)) k)} (hI : IsHomogeneousIdeal I)
    (hne : projectiveZeroLocus I ≠ ∅) (f : MvPolynomial (Fin (n+1)) k) :
    (∀ p ∈ projectiveZeroLocus I, MvPolynomial.eval p.rep f = 0) ↔ f ∈ I.radical :=
  sorry

end ProjectiveNullstellensatz

/-! ## §7.7  Key Examples (Hassett §7.7) -/

section Examples

variable {n : ℕ}

/-- A *projective hypersurface* in `P^n(k)` defined by a single homogeneous polynomial. -/
noncomputable def projectiveHypersurface (f : MvPolynomial (Fin (n+1)) k) : Set (Pn k n) :=
  projectiveZeroLocus (Ideal.span {f})

/-- The smooth conic `{x₀x₂ = x₁²} ⊆ P²(k)`. -/
noncomputable def conicCurve : Set (Pn k 2) :=
  projectiveHypersurface (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2)

/-- A *projective variety* is (by definition) a Zariski-closed subset of some `P^n(k)`. -/
def IsProjectiveVariety (V : Set (Pn k n)) : Prop :=
  @IsClosed _ (zariskiTopologyPn k n) V

/-- Every projective hypersurface (for a homogeneous polynomial) is a projective variety. -/
theorem isProjectiveVariety_hypersurface {d : ℕ} (f : MvPolynomial (Fin (n+1)) k)
    (hf : f.IsHomogeneous d) :
    IsProjectiveVariety (projectiveHypersurface f) :=
  isClosed_projectiveHypersurface f hf

/-- **Hassett Def 7.22** — The Veronese embedding `νₐ : P^n → P^N` sends `[v]` to all
degree-`a` monomials. Its image is a projective variety called the *Veronese variety*. -/
theorem veronese_image_isProjectiveVariety (a : ℕ) :
    ∃ (N : ℕ) (ν : Pn k n → Pn k N) (_ : Function.Injective ν),
      IsProjectiveVariety (Set.range ν) :=
  sorry

/-- **Hassett Def 7.25** — The Segre embedding `σ_{m,n} : P^m × P^n → P^{mn+m+n}` is
injective and its image is a projective variety called the *Segre variety*. -/
theorem segre_image_isProjectiveVariety (m : ℕ) :
    ∃ (seg : Pn k m × Pn k n → Pn k (m * n + m + n)) (_ : Function.Injective seg),
      IsProjectiveVariety (Set.range seg) :=
  sorry

end Examples

/-! ## §7.8  Morphisms of Projective Varieties (Hassett §7.8) -/

section Morphisms

variable {m n : ℕ}

/-- A *morphism of projective varieties* `V → W` is locally given by a tuple of homogeneous
polynomials of equal degree that do not simultaneously vanish on `V`. -/
structure IsProjMorphism (V : Set (Pn k m)) (W : Set (Pn k n))
    (φ : {p : Pn k m // p ∈ V} → Pn k n) : Prop where
  /-- φ is given (on each point) by homogeneous polynomials of equal degree. -/
  is_poly : ∃ (d : ℕ) (f : Fin (n+1) → MvPolynomial (Fin (m+1)) k),
    (∀ j, (f j).IsHomogeneous d) ∧
    ∀ (p : {q : Pn k m // q ∈ V}),
      (∃ j, MvPolynomial.eval p.1.rep (f j) ≠ 0) ∧
      ∃ (hne : (fun j => MvPolynomial.eval p.1.rep (f j)) ≠ 0),
        φ p = Projectivization.mk k (fun j => MvPolynomial.eval p.1.rep (f j)) hne
  /-- φ maps V into W. -/
  maps_into : ∀ p : {q : Pn k m // q ∈ V}, φ p ∈ W

/-- The identity is a morphism. -/
theorem isProjMorphism_id (V : Set (Pn k n)) :
    IsProjMorphism V V (fun p => p.1) := by
  refine ⟨⟨1, MvPolynomial.X, fun j => MvPolynomial.isHomogeneous_X k j, fun p => ?_⟩,
         fun p => p.2⟩
  refine ⟨?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply p.1.rep_nonzero
    ext j
    have := hall j
    rwa [MvPolynomial.eval_X] at this
  · refine ⟨by intro h; apply p.1.rep_nonzero; ext j;
               have := congr_fun h j; simp [MvPolynomial.eval_X] at this; exact this, ?_⟩
    simp only [MvPolynomial.eval_X, Projectivization.mk_rep]

/-- Evaluating a polynomial obtained by substituting `fφ` into `fψl`
equals evaluating `fψl` at the values `eval v (fφ j)`. -/
private lemma eval_aeval_eq {p q : ℕ}
    (fφ : Fin (q+1) → MvPolynomial (Fin (p+1)) k)
    (fψl : MvPolynomial (Fin (q+1)) k) (v : Fin (p+1) → k) :
    MvPolynomial.eval v (MvPolynomial.aeval fφ fψl) =
    MvPolynomial.eval (fun j => MvPolynomial.eval v (fφ j)) fψl := by
  have key : ((MvPolynomial.aeval v).comp (MvPolynomial.aeval fφ) :
      MvPolynomial (Fin (q+1)) k →ₐ[k] k) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval v (fφ j)) := by
    apply MvPolynomial.algHom_ext; intro j
    simp [MvPolynomial.aeval_X, MvPolynomial.aeval_eq_eval]
  exact_mod_cast AlgHom.congr_fun key fψl

/-- Composition of morphisms is a morphism. -/
theorem isProjMorphism_comp {p q : ℕ}
    {U : Set (Pn k p)} {V : Set (Pn k q)} {W : Set (Pn k n)}
    {φ : {x : Pn k p // x ∈ U} → Pn k q} {ψ : {x : Pn k q // x ∈ V} → Pn k n}
    (hφ : IsProjMorphism U V φ) (hψ : IsProjMorphism V W ψ)
    (hcomp : ∀ p : {x : Pn k p // x ∈ U}, φ p ∈ V) :
    IsProjMorphism U W (fun p => ψ ⟨φ p, hcomp p⟩) := by
  refine ⟨?_, fun p => hψ.maps_into ⟨φ p, hcomp p⟩⟩
  -- Obtain polynomial data for φ and ψ
  obtain ⟨dφ, fφ, hfφ_hom, hfφ_pt⟩ := hφ.is_poly
  obtain ⟨dψ, fψ, hfψ_hom, hfψ_pt⟩ := hψ.is_poly
  -- Composition polynomials: substitute fφ into fψ
  refine ⟨dφ * dψ, fun l => MvPolynomial.aeval fφ (fψ l), fun l => ?_, fun pt => ?_⟩
  · -- Homogeneity of degree dφ * dψ
    exact (hfψ_hom l).aeval fφ hfφ_hom
  · -- Point-wise data: existence, nonvanishing, and equality
    obtain ⟨⟨j_φ, hj_φ⟩, hne_φ, hrep_φ⟩ := hfφ_pt pt
    obtain ⟨⟨j_ψ, hj_ψ⟩, hne_ψ, hrep_ψ⟩ := hfψ_pt ⟨φ pt, hcomp pt⟩
    -- (φ pt).rep = (c : k) • (fun j => eval pt.rep (fφ j)) for some unit c
    obtain ⟨c, hc⟩ := exists_unit_smul_rep (fun j => MvPolynomial.eval pt.1.rep (fφ j)) hne_φ
    have hrep : (φ pt).rep = (c : k) • fun j => MvPolynomial.eval pt.1.rep (fφ j) := by
      rw [hrep_φ]; simp only [← hc, Units.smul_def]
    -- Key: eval (φ pt).rep (fψ l) = c^dψ * eval pt.rep (aeval fφ (fψ l))
    have key_eval : ∀ l, MvPolynomial.eval (φ pt).rep (fψ l) =
        (c : k) ^ dψ * MvPolynomial.eval pt.1.rep (MvPolynomial.aeval fφ (fψ l)) := fun l => by
      rw [hrep, homogeneous_eval_smul (hfψ_hom l), eval_aeval_eq]
    -- The composition evaluations are nonzero
    have hne_comp : (fun l => MvPolynomial.eval pt.1.rep (MvPolynomial.aeval fφ (fψ l))) ≠ 0 := by
      intro heq
      apply hne_ψ
      funext l; simp only [Pi.zero_apply]
      rw [key_eval l, show MvPolynomial.eval pt.1.rep (MvPolynomial.aeval fφ (fψ l)) = 0 from
        congr_fun heq l, mul_zero]
    refine ⟨⟨j_ψ, ?_⟩, hne_comp, ?_⟩
    · -- ∃ j, eval pt.rep (aeval fφ (fψ j)) ≠ 0
      intro heq
      apply hj_ψ
      rw [key_eval j_ψ, heq, mul_zero]
    · -- ψ ⟨φ pt, _⟩ = mk k (fun l => eval pt.rep (aeval fφ (fψ l))) hne_comp
      rw [hrep_ψ, Projectivization.mk_eq_mk_iff k]
      exact ⟨Units.mk0 ((c : k) ^ dψ) (pow_ne_zero _ (Units.ne_zero c)), by
        ext l
        simp only [Units.smul_def, Units.val_mk0, Pi.smul_apply, smul_eq_mul]
        exact (key_eval l).symm⟩

end Morphisms

end ProjectiveVarieties
