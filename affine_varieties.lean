import Mathlib

open MvPolynomial Set Ideal

/-!
# Affine Varieties — Hassett Chapter 3 (§3.1–3.4)

Formalises the basic theory of affine algebraic varieties over a field `k`:
the Galois connection between ideals and zero loci, the Zariski topology,
coordinate rings, and morphisms of varieties.

References: Hassett, *Introduction to Algebraic Geometry*, §3.1–3.4.

## Already in Mathlib (`Mathlib.RingTheory.Nullstellensatz`)

- `MvPolynomial.zeroLocus K I`  — `{x : σ → K | ∀ p ∈ I, aeval x p = 0}`
- `MvPolynomial.vanishingIdeal k V` — `{p | ∀ x ∈ V, aeval x p = 0}`
- `zeroLocus_bot` — `V(0) = Set.univ`
- `zeroLocus_top` — `V(1) = ∅`
- `vanishingIdeal_empty` — `I(∅) = ⊤`
- `zeroLocus_anti_mono`, `vanishingIdeal_anti_mono`
- `le_vanishingIdeal_zeroLocus`, `zeroLocus_vanishingIdeal_le`
- `zeroLocus_span`, `mem_zeroLocus_iff`, `mem_vanishingIdeal_iff`
-/

namespace AffineVarieties

/-! ## §3.1  Lattice of Ideals and Varieties (Hassett Props 3.4–3.14) -/

section VarietyLattice

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {σ ι : Type*}

/-- **Hassett Prop 3.4** — `V(⨆ i, Fᵢ) = ⋂ i, V(Fᵢ)`.

The zero locus of a join of ideals equals the intersection of zero loci. -/
theorem zeroLocus_iSup (F : ι → Ideal (MvPolynomial σ k)) :
    zeroLocus K (⨆ i, F i) = ⋂ i, zeroLocus K (F i) := by
  ext x
  simp only [mem_zeroLocus_iff, Set.mem_iInter]
  constructor
  · intro hx i p hp
    exact hx p (le_iSup F i hp)
  · intro hx
    have hle : ⨆ i, F i ≤
        RingHom.ker ((aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom) := by
      apply iSup_le; intro i p hp
      rw [RingHom.mem_ker]; exact hx i p hp
    intro p hp
    have := hle hp; rwa [RingHom.mem_ker] at this

/-- **Hassett Prop 3.10** — `V(I ⊔ J) = V(I) ∩ V(J)`. -/
theorem zeroLocus_sup (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus K (I ⊔ J) = zeroLocus K I ∩ zeroLocus K J := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    exact ⟨zeroLocus_anti_mono le_sup_left hx, zeroLocus_anti_mono le_sup_right hx⟩
  · intro x ⟨hI, hJ⟩
    rw [mem_zeroLocus_iff]
    have hle : I ⊔ J ≤
        RingHom.ker ((aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom) := by
      rw [sup_le_iff]
      exact ⟨fun p hp => by rw [RingHom.mem_ker]; exact (mem_zeroLocus_iff.mp hI) p hp,
             fun p hp => by rw [RingHom.mem_ker]; exact (mem_zeroLocus_iff.mp hJ) p hp⟩
    intro p hp; have := hle hp; rwa [RingHom.mem_ker] at this

/-- **Hassett Prop 3.6** — `I(⋃ i, Sᵢ) = ⨅ i, I(Sᵢ)`. -/
theorem vanishingIdeal_iUnion (S : ι → Set (σ → K)) :
    vanishingIdeal k (⋃ i, S i) = ⨅ i, vanishingIdeal k (S i) := by
  apply le_antisymm
  · apply le_iInf; intro i
    exact vanishingIdeal_anti_mono (Set.subset_iUnion S i)
  · intro p hp
    rw [Submodule.mem_iInf] at hp
    rw [mem_vanishingIdeal_iff]
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact (mem_vanishingIdeal_iff.mp (hp i)) x hi

/-- **Hassett Prop 3.12 (part 1)** — `V(I ⊓ J) = V(I) ∪ V(J)`.

Uses that `K` is an integral domain (automatic from `[Field K]`). -/
theorem zeroLocus_inf (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus K (I ⊓ J) = zeroLocus K I ∪ zeroLocus K J := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    rw [mem_zeroLocus_iff] at hx
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨hcI, hcJ⟩ := hc
    rw [mem_zeroLocus_iff] at hcI hcJ
    push Not at hcI hcJ
    obtain ⟨p, hp, hpx⟩ := hcI
    obtain ⟨q, hq, hqx⟩ := hcJ
    have hpq : p * q ∈ I ⊓ J := Ideal.mem_inf.mpr
      ⟨Ideal.mul_mem_right q I hp, J.mul_mem_left p hq⟩
    have hzero := hx (p * q) hpq
    rw [map_mul] at hzero
    exact absurd hzero (mul_ne_zero hpx hqx)
  · apply Set.union_subset
    · exact zeroLocus_anti_mono inf_le_left
    · exact zeroLocus_anti_mono inf_le_right

/-- **Hassett Prop 3.12 (part 2)** — `V(I · J) = V(I) ∪ V(J)`. -/
theorem zeroLocus_mul (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus K (I * J) = zeroLocus K I ∪ zeroLocus K J := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    rw [mem_zeroLocus_iff] at hx
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨hcI, hcJ⟩ := hc
    rw [mem_zeroLocus_iff] at hcI hcJ
    push Not at hcI hcJ
    obtain ⟨p, hp, hpx⟩ := hcI
    obtain ⟨q, hq, hqx⟩ := hcJ
    have hpq : p * q ∈ I * J := Ideal.mul_mem_mul hp hq
    have hzero := hx (p * q) hpq
    rw [map_mul] at hzero
    exact absurd hzero (mul_ne_zero hpx hqx)
  · apply Set.union_subset
    · intro x hx; rw [mem_zeroLocus_iff] at hx ⊢
      intro p hp; exact hx p (Ideal.mul_le_right hp)
    · intro x hx; rw [mem_zeroLocus_iff] at hx ⊢
      intro p hp; exact hx p (Ideal.mul_le_left hp)

/-- **Hassett Prop 3.14** — Every affine variety is cut out by finitely many equations.
Follows from the Hilbert Basis Theorem (Noetherianity of `MvPolynomial σ k` for finite `σ`). -/
theorem zeroLocus_finiteGen [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    ∃ (S : Finset (MvPolynomial σ k)),
      zeroLocus K I = zeroLocus K (Ideal.span (S : Set (MvPolynomial σ k))) := by
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨S, ?_⟩
  have hS' : Ideal.span (S : Set (MvPolynomial σ k)) = I := hS
  rw [← hS']

end VarietyLattice

/-! ## §3.2  The Zariski Topology (Hassett §3.2) -/

section ZariskiTopology

variable {k : Type*} [Field k] {σ τ : Type*}

/-- The Zariski topology on `σ → k`: closed sets are zero loci of polynomial ideals. -/
@[implicit_reducible] noncomputable def zariskiTopology (k σ : Type*) [Field k] : TopologicalSpace (σ → k) :=
  TopologicalSpace.ofClosed
    -- Closed sets = zero loci of ideals
    {C | ∃ I : Ideal (MvPolynomial σ k), C = zeroLocus k I}
    -- ∅ is closed: ∅ = V(⊤)
    ⟨⊤, by simp⟩
    -- Arbitrary intersections of closed sets are closed
    (fun A hA => by
      classical
      -- For each C ∈ A, choose an ideal I_C with C = V(I_C)
      let I : ↑A → Ideal (MvPolynomial σ k) :=
        fun ⟨C, hC⟩ => (hA hC).choose
      have hI : ∀ C : ↑A, (C : Set (σ → k)) = zeroLocus k (I C) :=
        fun ⟨C, hC⟩ => (hA hC).choose_spec
      -- ⋂₀ A = V(⨆ C, I C) by zeroLocus_iSup
      refine ⟨⨆ C : ↑A, I C, ?_⟩
      rw [zeroLocus_iSup]
      ext x
      simp only [Set.mem_sInter, Set.mem_iInter]
      constructor
      · intro hx ⟨C, hC⟩
        rw [← hI ⟨C, hC⟩]
        exact hx C hC
      · intro hx C hC
        have h : C = zeroLocus k (I ⟨C, hC⟩) := hI ⟨C, hC⟩
        rw [h]
        exact hx ⟨C, hC⟩)
    -- Finite unions of closed sets are closed: V(I) ∪ V(J) = V(I · J)
    (fun A ⟨I, hI⟩ B ⟨J, hJ⟩ =>
      ⟨I * J, by rw [hI, hJ, ← zeroLocus_mul]⟩)

lemma zariskiTopology_isOpen_iff (s : Set (σ → k)) :
    @IsOpen _ (zariskiTopology k σ) s ↔
    sᶜ ∈ ({C | ∃ I : Ideal (MvPolynomial σ k), C = zeroLocus k I} : Set (Set (σ → k))) := by
  unfold zariskiTopology TopologicalSpace.ofClosed
  exact Iff.rfl

/-- A set is Zariski-closed iff it is a zero locus of some ideal. -/
theorem zariskiTopology_isClosed_iff (C : Set (σ → k)) :
    @IsClosed _ (zariskiTopology k σ) C ↔
    ∃ I : Ideal (MvPolynomial σ k), C = zeroLocus k I := by
  constructor
  · intro hC
    -- Extract the openness of the complement
    have hOpen : @IsOpen _ (zariskiTopology k σ) Cᶜ := hC.isOpen_compl
    rw [zariskiTopology_isOpen_iff, compl_compl, Set.mem_setOf_eq] at hOpen
    exact hOpen
  · intro ⟨I, hI⟩
    -- Build the IsOpen witness, then wrap it as IsClosed
    have h : @IsOpen _ (zariskiTopology k σ) Cᶜ := by
      rw [zariskiTopology_isOpen_iff, compl_compl, Set.mem_setOf_eq]
      exact ⟨I, hI⟩
    exact @IsClosed.mk _ (zariskiTopology k σ) C h

/-- Zero loci are Zariski-closed. -/
theorem isClosed_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    @IsClosed _ (zariskiTopology k σ) (zeroLocus k I) :=
  (zariskiTopology_isClosed_iff _).mpr ⟨I, rfl⟩

/-- **Hassett Prop 3.22** — Polynomial maps between affine spaces are continuous with respect
to the Zariski topology. -/
theorem polynomialMap_continuous (f : τ → MvPolynomial σ k) :
    @Continuous _ _ (zariskiTopology k σ) (zariskiTopology k τ)
      (fun v : σ → k => (fun j => aeval v (f j))) := by
  letI : TopologicalSpace (σ → k) := zariskiTopology k σ
  letI : TopologicalSpace (τ → k) := zariskiTopology k τ
  rw [continuous_def]
  intro s hs
  rw [zariskiTopology_isOpen_iff] at hs ⊢
  obtain ⟨J, hJ⟩ := hs
  rw [← Set.preimage_compl, hJ, Set.mem_setOf_eq]
  refine ⟨J.map (aeval f).toRingHom, ?_⟩
  ext v
  simp only [Set.mem_preimage, mem_zeroLocus_iff]
  -- Composition: (aeval v) ∘ (aeval f) = aeval (fun j => aeval v (f j))
  have hcomp : (aeval v : MvPolynomial σ k →ₐ[k] k).comp (aeval f) =
               aeval (fun j => aeval v (f j)) :=
    MvPolynomial.algHom_ext (fun j => by simp [AlgHom.comp_apply, aeval_X])
  constructor
  · intro hv p hp
    -- Strategy: J.map (aeval f) ≤ ker(aeval v), so hp gives aeval v p = 0
    have hle : J.map (aeval f).toRingHom ≤
        RingHom.ker ((aeval v : MvPolynomial σ k →ₐ[k] k).toRingHom) := by
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      exact (AlgHom.congr_fun hcomp q).trans (hv q hq)
    exact RingHom.mem_ker.mp (hle hp)
  · intro hv p hp
    -- aeval f p ∈ J.map (aeval f), so aeval v (aeval f p) = 0
    rw [← AlgHom.congr_fun hcomp p]
    exact hv (aeval f p) (Ideal.mem_map_of_mem _ hp)

end ZariskiTopology

/-! ## §3.3  Coordinate Rings and Morphisms (Hassett §3.3) -/

section CoordinateRings

variable {k : Type*} [Field k] {σ τ : Type*}

/-- **Hassett §3.3** — The coordinate ring `k[V]` of an affine variety `V ⊆ σ → k`.
This is the ring of polynomial functions on `V`: `k[σ] / I(V)`. -/
noncomputable abbrev coordinateRing (V : Set (σ → k)) :=
  MvPolynomial σ k ⧸ vanishingIdeal k V

namespace coordinateRing

noncomputable instance commRing (V : Set (σ → k)) : CommRing (coordinateRing V) :=
  inferInstanceAs (CommRing (MvPolynomial σ k ⧸ vanishingIdeal k V))

noncomputable instance algebra (V : Set (σ → k)) : Algebra k (coordinateRing V) :=
  inferInstanceAs (Algebra k (MvPolynomial σ k ⧸ vanishingIdeal k V))

/-- The quotient map `k[σ] → k[V]`. -/
noncomputable def mk (V : Set (σ → k)) : MvPolynomial σ k →ₐ[k] coordinateRing V :=
  Ideal.Quotient.mkₐ k (vanishingIdeal k V)

theorem mk_surjective (V : Set (σ → k)) : Function.Surjective (mk V) :=
  Ideal.Quotient.mkₐ_surjective k _

theorem mk_zero_iff {V : Set (σ → k)} {p : MvPolynomial σ k} :
    mk V p = 0 ↔ ∀ v ∈ V, aeval v p = 0 := by
  show Ideal.Quotient.mk (vanishingIdeal k V) p = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_vanishingIdeal_iff]

/-- Two polynomials give the same element of `k[V]` iff they agree at every point of `V`. -/
theorem mk_eq_mk_iff {V : Set (σ → k)} {p q : MvPolynomial σ k} :
    mk V p = mk V q ↔ ∀ v ∈ V, aeval v p = aeval v q := by
  rw [← sub_eq_zero, ← map_sub, mk_zero_iff]
  simp [map_sub, sub_eq_zero]

/-- `mk V p = 0` iff `p ∈ vanishingIdeal k V`. -/
private theorem mk_eq_zero_iff_mem {V : Set (σ → k)} {p : MvPolynomial σ k} :
    mk V p = 0 ↔ p ∈ vanishingIdeal k V := by
  rw [mk_zero_iff, mem_vanishingIdeal_iff]

end coordinateRing

/-- A **morphism of affine varieties** `φ : V → W` is a polynomial map: there exist polynomials
`fⱼ ∈ k[σ]` such that `φ(v)ⱼ = fⱼ(v)` for all `v ∈ V`, with `φ(V) ⊆ W`. -/
structure IsMorphism (V : Set (σ → k)) (W : Set (τ → k))
    (φ : (σ → k) → (τ → k)) : Prop where
  is_poly : ∃ f : τ → MvPolynomial σ k, ∀ v, φ v = fun j => aeval v (f j)
  maps_into : ∀ v ∈ V, φ v ∈ W

/-- **Hassett §3.3** — Every morphism of varieties `φ : V → W` induces a pullback
algebra homomorphism `φ* : k[W] → k[V]` sending `p ↦ p ∘ φ`. -/
noncomputable def morphismPullback {V : Set (σ → k)} {W : Set (τ → k)}
    {φ : (σ → k) → (τ → k)} (hφ : IsMorphism V W φ) :
    coordinateRing W →ₐ[k] coordinateRing V :=
  let f := Classical.choose hφ.is_poly
  let hf : ∀ v, φ v = fun j => aeval v (f j) := Classical.choose_spec hφ.is_poly
  -- Lift the map k[τ] → k[V] sending X_j ↦ class of f_j
  Ideal.Quotient.liftₐ (vanishingIdeal k W) ((coordinateRing.mk V).comp (aeval f)) (by
    intro p hp
    simp only [AlgHom.comp_apply]
    rw [coordinateRing.mk_zero_iff]
    intro v hv
    -- aeval v (aeval f p) = aeval (φ v) p (by composition)
    have hcomp : (aeval v : MvPolynomial σ k →ₐ[k] k).comp (aeval f) =
                 aeval (fun j => aeval v (f j)) :=
      MvPolynomial.algHom_ext (fun j => by simp [AlgHom.comp_apply, aeval_X])
    have key : aeval v (aeval f p) = aeval (fun j => aeval v (f j)) p :=
      AlgHom.congr_fun hcomp p
    rw [key, ← hf v]
    exact (mem_vanishingIdeal_iff.mp hp) (φ v) (hφ.maps_into v hv))

/-!
### Auxiliary: liftₐ computation

For any ideal `I` of an algebra and any `k`-algebra hom `f : A →ₐ[k] B` with `f` vanishing on
`I`, the lift through `A ⧸ I` computes as `(liftₐ I f hf) (mkₐ k I p) = f p`.
-/

private lemma liftₐ_mk_eq {A B : Type*} {k : Type*} [CommRing A] [CommRing B] [CommRing k]
    [Algebra k A] [Algebra k B] (I : Ideal A) (f : A →ₐ[k] B)
    (hf : ∀ a ∈ I, f a = 0) (p : A) :
    Ideal.Quotient.liftₐ I f hf (Ideal.Quotient.mkₐ k I p) = f p :=
  AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I f hf) p

/-- **Hassett Cor 3.32** — `k`-algebra homomorphisms `k[W] → k[V]` biject canonically with
tuples `(g_j)_{j:τ}` in `k[V]` satisfying all polynomial relations of `I(W)`.

This is the universal property of the coordinate ring `k[W] = k[τ]/I(W)`: it represents
the functor `A ↦ {g : τ → A | ∀ p ∈ I(W), aeval g p = 0}` on `k`-algebras.
The geometric pullback construction is `morphismPullback`. -/
noncomputable def morphism_algHom_equiv (V : Set (σ → k)) (W : Set (τ → k)) :
    (coordinateRing W →ₐ[k] coordinateRing V) ≃
    {g : τ → coordinateRing V //
      ∀ p ∈ vanishingIdeal k W, (MvPolynomial.aeval g p : coordinateRing V) = 0} where
  toFun ψ :=
    ⟨fun j => ψ (coordinateRing.mk W (X j)), fun p hp => by
      -- aeval (fun j => ψ (mk W (X j))) = ψ.comp (mk W) as AlgHoms (agree on generators)
      have heq : (MvPolynomial.aeval fun j => ψ (coordinateRing.mk W (MvPolynomial.X j))) =
                 ψ.comp (coordinateRing.mk W) :=
        MvPolynomial.algHom_ext (fun j => by simp [MvPolynomial.aeval_X])
      rw [heq, AlgHom.comp_apply]
      -- mk W p = 0 since p ∈ vanishingIdeal k W
      have hpW : coordinateRing.mk W p = 0 :=
        coordinateRing.mk_eq_zero_iff_mem.mpr hp
      rw [hpW, map_zero]⟩
  invFun g :=
    Ideal.Quotient.liftₐ (vanishingIdeal k W) (MvPolynomial.aeval g.1) g.2
  left_inv ψ := AlgHom.ext fun q => by
    obtain ⟨p, rfl⟩ := coordinateRing.mk_surjective W q
    -- liftₐ I f hf (mkₐ k I p) = f p definitionally (Quotient.lift computes)
    -- so goal reduces to: aeval (fun j => ψ (mk W (X j))) p = ψ (mk W p)
    change (MvPolynomial.aeval fun j => ψ (coordinateRing.mk W (MvPolynomial.X j))) p =
           ψ (coordinateRing.mk W p)
    have heq : (MvPolynomial.aeval fun j => ψ (coordinateRing.mk W (MvPolynomial.X j))) =
               ψ.comp (coordinateRing.mk W) :=
      MvPolynomial.algHom_ext (fun j => by simp [MvPolynomial.aeval_X])
    rw [heq, AlgHom.comp_apply]
  right_inv g := Subtype.ext (funext fun j => by
    -- liftₐ I (aeval g.1) g.2 (mk W (X j)) = (aeval g.1) (X j) = g.1 j definitionally
    change MvPolynomial.aeval g.1 (MvPolynomial.X j) = g.1 j
    exact MvPolynomial.aeval_X g.1 j)

end CoordinateRings

/-! ## §3.4  Rational Maps (Hassett §3.4) -/

section RationalMaps

variable {k : Type*} [Field k] {σ τ : Type*}

/-- A **rational map** from `V` to `W` is a tuple of elements of `k(V) = Frac(k[V])`
satisfying all polynomial relations of `I(W)`, i.e., the tuple defines a well-formed algebraic
map into `W`. This is the algebraic content of Hassett's rational maps (§3.4). -/
def IsRationalMap (V : Set (σ → k)) (W : Set (τ → k))
    (ρ : τ → FractionRing (coordinateRing V)) : Prop :=
  ∀ p ∈ vanishingIdeal k W, (MvPolynomial.aeval ρ p : FractionRing (coordinateRing V)) = 0

/-- **Hassett Cor 3.46** — When `V` is irreducible (`coordinateRing V` is a domain), rational
maps `V ⇢ W` (tuples in `k(V)` satisfying the ideal relations of `W`) correspond bijectively
to `k`-algebra homomorphisms `k[W] → k(V) = Frac(k[V])`. -/
noncomputable def rationalMap_algHom_equiv
    (V : Set (σ → k)) (W : Set (τ → k))
    [IsDomain (coordinateRing V)] :
    {ρ : τ → FractionRing (coordinateRing V) // IsRationalMap V W ρ} ≃
    (coordinateRing W →ₐ[k] FractionRing (coordinateRing V)) where
  toFun ρ :=
    -- Lift aeval ρ.1 : k[τ] → k(V) through the quotient k[W] = k[τ]/I(W)
    Ideal.Quotient.liftₐ (vanishingIdeal k W) (MvPolynomial.aeval ρ.1) ρ.2
  invFun ψ :=
    ⟨fun j => ψ (coordinateRing.mk W (X j)), fun p hp => by
      -- aeval (fun j => ψ (mk W (X j))) = ψ.comp (mk W) as AlgHoms
      have heq : (MvPolynomial.aeval fun j => ψ (coordinateRing.mk W (MvPolynomial.X j))) =
                 ψ.comp (coordinateRing.mk W) :=
        MvPolynomial.algHom_ext (fun j => by simp [MvPolynomial.aeval_X])
      rw [heq, AlgHom.comp_apply]
      have hpW : coordinateRing.mk W p = 0 :=
        coordinateRing.mk_eq_zero_iff_mem.mpr hp
      rw [hpW, map_zero]⟩
  left_inv ρ := Subtype.ext (funext fun j => by
    -- liftₐ I (aeval ρ.1) ρ.2 (mk W (X j)) = (aeval ρ.1) (X j) = ρ.1 j definitionally
    change MvPolynomial.aeval ρ.1 (MvPolynomial.X j) = ρ.1 j
    exact MvPolynomial.aeval_X ρ.1 j)
  right_inv ψ := AlgHom.ext fun q => by
    obtain ⟨p, rfl⟩ := coordinateRing.mk_surjective W q
    -- liftₐ I f hf (mkₐ k I p) = f p definitionally
    change (MvPolynomial.aeval fun j => ψ (coordinateRing.mk W (MvPolynomial.X j))) p =
           ψ (coordinateRing.mk W p)
    have heq : (MvPolynomial.aeval fun j => ψ (coordinateRing.mk W (MvPolynomial.X j))) =
               ψ.comp (coordinateRing.mk W) :=
      MvPolynomial.algHom_ext (fun j => by simp [MvPolynomial.aeval_X])
    rw [heq, AlgHom.comp_apply]

end RationalMaps

/-! ## §3.5  Principal Affine Open Subsets (Hassett §3.5) -/

section PrincipalAffineOpen

variable {k : Type*} [Field k] {σ : Type*}

/-- `aeval f (rename g q) = aeval (f ∘ g) q`. -/
private lemma aeval_rename_comp {M : Type*} [CommSemiring M] [Algebra k M]
    {α β : Type*} (f : β → M) (g : α → β) (q : MvPolynomial α k) :
    aeval f (MvPolynomial.rename g q) = aeval (f ∘ g) q :=
  MvPolynomial.aeval_rename g f q

/-- **Hassett §3.5** — The *principal affine open* `V_g = {(v, z) ∈ (σ ⊕ Unit) → k : v ∈ V, z·g(v) = 1}`.
The extra coordinate `z` is the formal inverse of `g`, so `V_g ≅ {v ∈ V : g(v) ≠ 0}`. -/
def principalAffineOpen (V : Set (σ → k)) (g : MvPolynomial σ k) :
    Set ((σ ⊕ Unit) → k) :=
  {p | p ∘ Sum.inl ∈ V ∧ p (Sum.inr ()) * aeval (p ∘ Sum.inl) g = 1}

/-- The projection `(v, z) ↦ v` maps `V_g` bijectively onto `{v ∈ V : g(v) ≠ 0}`. -/
theorem principalAffineOpen_proj_eq (V : Set (σ → k)) (g : MvPolynomial σ k) :
    (· ∘ Sum.inl) '' principalAffineOpen V g = {v ∈ V | aeval v g ≠ 0} := by
  ext v
  constructor
  · rintro ⟨p, ⟨hpV, hpg⟩, rfl⟩
    exact ⟨hpV, fun h => by simp [h] at hpg⟩
  · rintro ⟨hv, hg⟩
    refine ⟨Sum.elim v (fun _ => (aeval v g)⁻¹), ⟨?_, ?_⟩, funext fun i => Sum.elim_inl v _ i⟩
    · rwa [show Sum.elim v (fun _ => (aeval v g)⁻¹) ∘ Sum.inl = v from
          funext fun i => Sum.elim_inl v _ i]
    · rw [show Sum.elim v (fun _ => (aeval v g)⁻¹) ∘ Sum.inl = v from
              funext fun i => Sum.elim_inl v _ i,
          show Sum.elim v (fun _ => (aeval v g)⁻¹) (Sum.inr ()) = (aeval v g)⁻¹ from
              Sum.elim_inr v _ ()]
      exact inv_mul_cancel₀ hg

/-- `V_g` is Zariski-closed: it is the zero locus of the ideal
`I.map (rename inl) + ⟨z·g - 1⟩` in `k[σ ⊕ Unit]`. -/
theorem principalAffineOpen_eq_zeroLocus (I : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k) :
    principalAffineOpen (zeroLocus k I) g =
    zeroLocus k (I.map (MvPolynomial.rename Sum.inl).toRingHom ⊔
      Ideal.span {MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl g - 1}) := by
  ext p
  simp only [principalAffineOpen, Set.mem_setOf_eq, mem_zeroLocus_iff]
  constructor
  · intro ⟨hpI, hpg⟩ q hq
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hq
    rw [← hab, map_add]
    have ha0 : aeval p a = 0 := by
      have hle : I.map (MvPolynomial.rename Sum.inl).toRingHom ≤
          Ideal.comap (aeval p : MvPolynomial (σ ⊕ Unit) k →ₐ[k] k).toRingHom ⊥ :=
        Ideal.map_le_iff_le_comap.mpr fun r hr => by
          simp only [Ideal.mem_comap, Submodule.mem_bot, AlgHom.toRingHom_eq_coe,
                     AlgHom.coe_toRingHom, aeval_rename_comp]
          exact hpI r hr
      have := hle ha
      simp only [Ideal.mem_comap, Submodule.mem_bot, AlgHom.toRingHom_eq_coe,
                 AlgHom.coe_toRingHom] at this
      exact this
    have hb0 : aeval p b = 0 := by
      have hle : Ideal.span {MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl g - 1} ≤
          Ideal.comap (aeval p : MvPolynomial (σ ⊕ Unit) k →ₐ[k] k).toRingHom ⊥ := by
        apply Ideal.span_le.mpr
        simp only [Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, Submodule.mem_bot,
                   AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, map_mul,
                   MvPolynomial.aeval_X, aeval_rename_comp, map_one, sub_eq_zero]
        exact hpg
      have := hle hb
      simp only [Ideal.mem_comap, Submodule.mem_bot, AlgHom.toRingHom_eq_coe,
                 AlgHom.coe_toRingHom] at this
      exact this
    simp [ha0, hb0]
  · intro hp
    refine ⟨fun r hr => ?_, ?_⟩
    · have hmem : MvPolynomial.rename Sum.inl r ∈
          I.map (MvPolynomial.rename Sum.inl).toRingHom ⊔
          Ideal.span {MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl g - 1} :=
        Submodule.mem_sup.mpr ⟨_, Ideal.mem_map_of_mem _ hr, 0, zero_mem _, add_zero _⟩
      have h := hp _ hmem
      rwa [aeval_rename_comp] at h
    · have hmem : MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl g - 1 ∈
          I.map (MvPolynomial.rename Sum.inl).toRingHom ⊔
          Ideal.span {MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl g - 1} :=
        Submodule.mem_sup.mpr ⟨0, zero_mem _, _,
          Ideal.subset_span (by simp), zero_add _⟩
      have h := hp _ hmem
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, aeval_rename_comp, map_one] at h
      exact sub_eq_zero.mp h

/-- **Hassett §3.5** — The coordinate ring of `V_g` is isomorphic to the localization `k[V][1/g̅]`
where `g̅ = mk V g ∈ k[V]`. -/
theorem principalAffineOpen_coordinateRing (V : Set (σ → k)) (g : MvPolynomial σ k) :
    Nonempty (coordinateRing (principalAffineOpen V g) ≃ₐ[k]
      Localization.Away (coordinateRing.mk V g)) := by
  -- ψ₀ : k[V] →ₐ[k] k[principalAffineOpen V g], sending mk V f ↦ mk (pao V g) (rename inl f)
  let ψ₀ : coordinateRing V →ₐ[k] coordinateRing (principalAffineOpen V g) :=
    Ideal.Quotient.liftₐ (vanishingIdeal k V)
      ((coordinateRing.mk (principalAffineOpen V g)).comp (MvPolynomial.rename Sum.inl)) (by
        intro f hf
        simp only [AlgHom.comp_apply]
        rw [coordinateRing.mk_zero_iff]
        intro p ⟨hpV, _⟩
        rw [aeval_rename_comp]
        exact mem_vanishingIdeal_iff.mp hf _ hpV)
  -- Computation rule for ψ₀
  have hψ₀ : ∀ f : MvPolynomial σ k,
      ψ₀ (coordinateRing.mk V f) =
      coordinateRing.mk (principalAffineOpen V g) (MvPolynomial.rename Sum.inl f) :=
    fun f => rfl
  -- z = mk (pao V g) (X (inr ())) is the inverse of ψ₀(g̅)
  have hzg : coordinateRing.mk (principalAffineOpen V g) (MvPolynomial.X (Sum.inr ())) *
      ψ₀ (coordinateRing.mk V g) = 1 := by
    rw [hψ₀, ← map_mul, ← map_one (coordinateRing.mk (principalAffineOpen V g)),
        ← sub_eq_zero, ← map_sub]
    apply (coordinateRing.mk_zero_iff).mpr
    intro p ⟨_, hpg⟩
    simp only [map_sub, map_mul, MvPolynomial.aeval_X, aeval_rename_comp, map_one]
    linear_combination hpg
  -- Algebra structure on k[principalAffineOpen V g] over k[V] via ψ₀
  letI algPAO : Algebra (coordinateRing V) (coordinateRing (principalAffineOpen V g)) :=
    ψ₀.toAlgebra
  set_option synthInstance.maxHeartbeats 400000 in
  haveI sclTow : IsScalarTower k (coordinateRing V) (coordinateRing (principalAffineOpen V g)) :=
    IsScalarTower.of_algebraMap_eq fun r => (ψ₀.commutes r).symm
  -- k[principalAffineOpen V g] is the localization of k[V] away from g̅
  haveI isLoc : IsLocalization.Away (coordinateRing.mk V g)
      (coordinateRing (principalAffineOpen V g)) := by
    apply IsLocalization.Away.mk
    · -- map_unit: ψ₀(g̅) is a unit
      show IsUnit (ψ₀ (coordinateRing.mk V g))
      exact ⟨⟨ψ₀ (coordinateRing.mk V g),
               coordinateRing.mk (principalAffineOpen V g) (MvPolynomial.X (Sum.inr ())),
               by rw [mul_comm]; exact hzg,
               hzg⟩, rfl⟩
    · -- surj: every element s satisfies s * ψ₀(g̅)^n = ψ₀(a) for some n, a
      intro s
      obtain ⟨p, rfl⟩ := coordinateRing.mk_surjective (principalAffineOpen V g) s
      -- Prove by induction on the polynomial p
      suffices ∀ p : MvPolynomial (σ ⊕ Unit) k,
          ∃ (n : ℕ) (a : coordinateRing V),
          coordinateRing.mk (principalAffineOpen V g) p *
            ψ₀ (coordinateRing.mk V g) ^ n = ψ₀ a by
        exact this p
      intro p
      induction p using MvPolynomial.induction_on with
      | C c =>
        exact ⟨0, algebraMap k (coordinateRing V) c, by
          simp only [pow_zero, mul_one, hψ₀]
          exact (ψ₀.commutes c).symm⟩
      | add p q ihp ihq =>
        obtain ⟨n₁, a₁, h₁⟩ := ihp
        obtain ⟨n₂, a₂, h₂⟩ := ihq
        exact ⟨n₁ + n₂,
          a₁ * coordinateRing.mk V g ^ n₂ + a₂ * coordinateRing.mk V g ^ n₁, by
          simp only [map_add, map_mul, map_pow, pow_add]
          calc (coordinateRing.mk (principalAffineOpen V g) p +
                  coordinateRing.mk (principalAffineOpen V g) q) *
                (ψ₀ (coordinateRing.mk V g) ^ n₁ * ψ₀ (coordinateRing.mk V g) ^ n₂)
              = coordinateRing.mk (principalAffineOpen V g) p *
                  ψ₀ (coordinateRing.mk V g) ^ n₁ * ψ₀ (coordinateRing.mk V g) ^ n₂ +
                coordinateRing.mk (principalAffineOpen V g) q *
                  ψ₀ (coordinateRing.mk V g) ^ n₂ * ψ₀ (coordinateRing.mk V g) ^ n₁ := by ring
            _ = ψ₀ a₁ * ψ₀ (coordinateRing.mk V g) ^ n₂ +
                ψ₀ a₂ * ψ₀ (coordinateRing.mk V g) ^ n₁ := by rw [h₁, h₂]⟩
      | mul_X p i ih =>
        obtain ⟨n, a, h⟩ := ih
        rcases i with i | ⟨⟩
        · -- X (inl i): n stays, a multiplies by mk V (X i)
          have hxi : coordinateRing.mk (principalAffineOpen V g) (MvPolynomial.X (Sum.inl i)) =
              ψ₀ (coordinateRing.mk V (MvPolynomial.X i)) := by
            rw [hψ₀, MvPolynomial.rename_X]
          exact ⟨n, a * coordinateRing.mk V (MvPolynomial.X i), by
            rw [map_mul, hxi]
            have hrearr : coordinateRing.mk (principalAffineOpen V g) p *
                ψ₀ (coordinateRing.mk V (MvPolynomial.X i)) * ψ₀ (coordinateRing.mk V g) ^ n =
                coordinateRing.mk (principalAffineOpen V g) p * ψ₀ (coordinateRing.mk V g) ^ n *
                ψ₀ (coordinateRing.mk V (MvPolynomial.X i)) := by ring
            rw [hrearr, h, ← map_mul]⟩
        · -- X (inr ()): n increases by 1, a stays
          exact ⟨n + 1, a, by
            rw [pow_succ, map_mul]
            calc coordinateRing.mk (principalAffineOpen V g) p *
                    coordinateRing.mk (principalAffineOpen V g) (MvPolynomial.X (Sum.inr ())) *
                    (ψ₀ (coordinateRing.mk V g) ^ n * ψ₀ (coordinateRing.mk V g))
                = coordinateRing.mk (principalAffineOpen V g) p *
                    ψ₀ (coordinateRing.mk V g) ^ n *
                    (coordinateRing.mk (principalAffineOpen V g) (MvPolynomial.X (Sum.inr ())) *
                      ψ₀ (coordinateRing.mk V g)) := by ring
              _ = ψ₀ a * 1 := by rw [h, hzg]
              _ = ψ₀ a := mul_one _⟩
    · -- exists_of_eq: ψ₀(a) = ψ₀(b) implies mk V g * a = mk V g * b
      intro a b hab
      use 1
      rw [pow_one, ← sub_eq_zero, ← mul_sub]
      obtain ⟨rep, hrep⟩ := coordinateRing.mk_surjective V (a - b)
      rw [← hrep, ← map_mul, coordinateRing.mk_zero_iff]
      intro v hv
      simp only [map_mul]
      by_cases hg : aeval v g = 0
      · simp [hg]
      · -- Construct point (v, 1/g(v)) ∈ principalAffineOpen V g
        have hmem : Sum.elim v (fun _ => (aeval v g)⁻¹) ∈ principalAffineOpen V g :=
          ⟨show Sum.elim v _ ∘ Sum.inl ∈ V by
              rwa [show Sum.elim v (fun _ => (aeval v g)⁻¹) ∘ Sum.inl = v from
                funext fun i => Sum.elim_inl v _ i],
           show Sum.elim v _ (Sum.inr ()) * aeval (Sum.elim v _ ∘ Sum.inl) g = 1 by
              rw [show Sum.elim v (fun _ => (aeval v g)⁻¹) ∘ Sum.inl = v from
                    funext fun i => Sum.elim_inl v _ i, Sum.elim_inr]
              exact inv_mul_cancel₀ hg⟩
        -- From hab, ψ₀(a - b) = 0, so ψ₀(mk V rep) = 0
        have h0 : ψ₀ (coordinateRing.mk V rep) = 0 := by
          rw [hrep, map_sub]; exact sub_eq_zero.mpr hab
        -- So rename inl rep ∈ vanishingIdeal k (principalAffineOpen V g)
        have hvan : MvPolynomial.rename Sum.inl rep ∈
            vanishingIdeal k (principalAffineOpen V g) := by
          apply mem_vanishingIdeal_iff.mpr
          rw [← coordinateRing.mk_zero_iff, ← hψ₀]
          exact h0
        -- Evaluate at (v, 1/g(v)) to get aeval v rep = 0
        have key : aeval v rep = 0 := by
          have := mem_vanishingIdeal_iff.mp hvan _ hmem
          rwa [aeval_rename_comp,
            show Sum.elim v (fun _ => (aeval v g)⁻¹) ∘ Sum.inl = v from
              funext fun i => Sum.elim_inl v _ i] at this
        simp [key]
  -- Conclude: k[principalAffineOpen V g] ≃ₐ[k] Localization.Away (mk V g)
  exact ⟨(Localization.algEquiv (Submonoid.powers (coordinateRing.mk V g))
      (coordinateRing (principalAffineOpen V g))).symm.restrictScalars k⟩

end PrincipalAffineOpen

/-! ## §3.6  Rational and Unirational Varieties (Hassett §3.6) -/

section RationalVarieties

variable {k : Type*} [Field k] {τ : Type*}

/-- **Hassett Def 3.55 / Prop 3.57** — `W` is *unirational* if there exists a `k`-algebra injection
`k[W] ↪ k(σ)` for some type `σ` in `Type 0`. Geometrically, `W` admits a rational parametrization
`𝔸ⁿ(k) ⇢ W` whose image is Zariski-dense in `W`.
We use `Type 0` so that the same witness can be shared in `IsRational.isUnirational`. -/
def IsUnirational (W : Set (τ → k)) : Prop :=
  ∃ (σ : Type),
    ∃ ψ : coordinateRing W →ₐ[k] FractionRing (MvPolynomial σ k),
      Function.Injective ψ

/-- **Hassett Def 3.59** — `W` is *rational* if the function field `k(W)` is purely transcendental:
`k(W) ≅ k(x₁,...,xₙ)` for some `n`. -/
def IsRational (W : Set (τ → k)) : Prop :=
  ∃ (σ : Type),
    Nonempty (FractionRing (coordinateRing W) ≃ₐ[k] FractionRing (MvPolynomial σ k))

/-- **Hassett Cor 3.60** — Every rational variety is unirational.

Proof: compose the algebra map `k[W] → Frac(k[W])` (injective, since localizing at
`nonZeroDivisors` is always injective) with the isomorphism `φ : Frac(k[W]) ≅ k(σ)`. -/
theorem IsRational.isUnirational {W : Set (τ → k)} (h : IsRational W) : IsUnirational W := by
  obtain ⟨σ, ⟨φ⟩⟩ := h
  exact ⟨σ, φ.toAlgHom.comp (IsScalarTower.toAlgHom k (coordinateRing W)
      (FractionRing (coordinateRing W))),
    φ.injective.comp (IsLocalization.injective (FractionRing (coordinateRing W)) le_rfl)⟩

end RationalVarieties

/-! ## §4.1  Projections and Graphs (Hassett §4.1) -/

section ProjectionsAndGraphs

variable {k : Type*} [Field k] {σ τ : Type*}

/-- The *product variety* `V × W` embedded as a subvariety of `(σ ⊕ τ) → k`. -/
def productVariety (V : Set (σ → k)) (W : Set (τ → k)) : Set ((σ ⊕ τ) → k) :=
  {p | p ∘ Sum.inl ∈ V ∧ p ∘ Sum.inr ∈ W}

/-- The *graph ideal* of a polynomial map `f : τ → k[σ]` over the zero locus `V(I)`.
Generators: the pullback of `I` along `inl : σ → σ ⊕ τ`, plus the equations `y_j = f_j(x)`. -/
noncomputable def graphIdeal (I : Ideal (MvPolynomial σ k)) (f : τ → MvPolynomial σ k) :
    Ideal (MvPolynomial (σ ⊕ τ) k) :=
  I.map (MvPolynomial.rename Sum.inl).toRingHom ⊔
  Ideal.span (Set.range fun j : τ =>
    MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (f j))

/-- The *graph* `Γf` of the polynomial map `v ↦ fun j => aeval v (f j)` on `V(I)`. -/
def graphOf (I : Ideal (MvPolynomial σ k)) (f : τ → MvPolynomial σ k) :
    Set ((σ ⊕ τ) → k) :=
  {p | p ∘ Sum.inl ∈ zeroLocus k I ∧ ∀ j : τ, p (Sum.inr j) = aeval (p ∘ Sum.inl) (f j)}

/-- **Hassett Prop 4.5** — The graph `Γf` equals the zero locus of `graphIdeal I f`,
confirming it is an affine variety. -/
theorem graphOf_eq_zeroLocus (I : Ideal (MvPolynomial σ k)) (f : τ → MvPolynomial σ k) :
    graphOf I f = zeroLocus k (graphIdeal I f) := by
  ext p
  simp only [graphOf, graphIdeal, Set.mem_setOf_eq, mem_zeroLocus_iff]
  constructor
  · intro ⟨hpI, hpf⟩ q hq
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hq
    rw [← hab, map_add]
    have ha0 : aeval p a = 0 := by
      have hle : I.map (MvPolynomial.rename Sum.inl).toRingHom ≤
          Ideal.comap (aeval p : MvPolynomial (σ ⊕ τ) k →ₐ[k] k).toRingHom ⊥ :=
        Ideal.map_le_iff_le_comap.mpr fun r hr => by
          simp only [Ideal.mem_comap, Submodule.mem_bot, AlgHom.toRingHom_eq_coe,
                     AlgHom.coe_toRingHom, aeval_rename_comp]
          exact hpI r hr
      have := hle ha
      simp only [Ideal.mem_comap, Submodule.mem_bot, AlgHom.toRingHom_eq_coe,
                 AlgHom.coe_toRingHom] at this
      exact this
    have hb0 : aeval p b = 0 := by
      have hle : Ideal.span (Set.range fun j : τ =>
              MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (f j)) ≤
          Ideal.comap (aeval p : MvPolynomial (σ ⊕ τ) k →ₐ[k] k).toRingHom ⊥ := by
        apply Ideal.span_le.mpr
        rintro x ⟨j, rfl⟩
        simp only [SetLike.mem_coe, Ideal.mem_comap, Submodule.mem_bot, AlgHom.toRingHom_eq_coe,
                   AlgHom.coe_toRingHom, map_sub, MvPolynomial.aeval_X, aeval_rename_comp,
                   sub_eq_zero]
        exact hpf j
      have := hle hb
      simp only [Ideal.mem_comap, Submodule.mem_bot, AlgHom.toRingHom_eq_coe,
                 AlgHom.coe_toRingHom] at this
      exact this
    simp [ha0, hb0]
  · intro hp
    refine ⟨fun r hr => ?_, fun j => ?_⟩
    · have hmem : MvPolynomial.rename Sum.inl r ∈
          I.map (MvPolynomial.rename Sum.inl).toRingHom ⊔
          Ideal.span (Set.range fun j : τ =>
            MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (f j)) :=
        Submodule.mem_sup.mpr ⟨_, Ideal.mem_map_of_mem _ hr, 0, zero_mem _, add_zero _⟩
      have h := hp _ hmem
      rwa [aeval_rename_comp] at h
    · have hmem : MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (f j) ∈
          I.map (MvPolynomial.rename Sum.inl).toRingHom ⊔
          Ideal.span (Set.range fun j : τ =>
            MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (f j)) :=
        Submodule.mem_sup.mpr ⟨0, zero_mem _, _,
          Ideal.subset_span (Set.mem_range_self j), zero_add _⟩
      have h := hp _ hmem
      simp only [map_sub, MvPolynomial.aeval_X, aeval_rename_comp] at h
      exact sub_eq_zero.mp h

/-- The graph of a polynomial map is Zariski-closed. -/
theorem isClosed_graphOf (I : Ideal (MvPolynomial σ k)) (f : τ → MvPolynomial σ k) :
    @IsClosed _ (zariskiTopology k (σ ⊕ τ)) (graphOf I f) := by
  rw [graphOf_eq_zeroLocus]; exact isClosed_zeroLocus _

/-- **Hassett Thm 4.3** (Projection / Elimination Theorem) — For `V(J) ⊆ 𝔸^(σ⊕τ)(k)`,
the Zariski closure of the projection `π(V(J))` onto `τ → k` equals `V(J ∩ k[τ])`,
where `J ∩ k[τ]` is the elimination ideal `J.comap (rename inr)`.

Requires `k` algebraically closed (for the Nullstellensatz `I(V(I)) = √I`) and
`σ`, `τ` finite (to apply the Mathlib Nullstellensatz). -/
theorem closure_projection_eq [IsAlgClosed k] [Finite σ] [Finite τ]
    (J : Ideal (MvPolynomial (σ ⊕ τ) k)) :
    @closure _ (zariskiTopology k τ) ((· ∘ Sum.inr) '' zeroLocus k J) =
    zeroLocus k (J.comap (MvPolynomial.rename Sum.inr).toRingHom) := by
  letI : TopologicalSpace (τ → k) := zariskiTopology k τ
  apply Set.eq_of_subset_of_subset
  · -- Forward: closure(π(V(J))) ⊆ V(R)
    apply closure_minimal _ (isClosed_zeroLocus _)
    rintro q ⟨x, hx, rfl⟩
    rw [mem_zeroLocus_iff]
    intro f hf
    rw [Ideal.mem_comap] at hf
    have h := mem_zeroLocus_iff.mp hx _ hf
    rw [← MvPolynomial.aeval_rename]
    exact h
  · -- Backward: V(R) ⊆ closure(π(V(J)))
    -- For q ∈ V(R) and any Zariski open U = V(J')ᶜ ∋ q:
    -- rename Sum.inr f ∉ √J (else aeval q f = 0 contradicting f(q) ≠ 0).
    -- Nullstellensatz then gives x ∈ V(J) with (rename Sum.inr f)(x) ≠ 0,
    -- so x ∘ Sum.inr ∈ π(V(J)) ∩ U.
    intro q hq
    rw [mem_closure_iff]
    intro U hU hqU
    rw [zariskiTopology_isOpen_iff] at hU
    simp only [Set.mem_setOf_eq] at hU
    obtain ⟨J', hJ'⟩ := hU
    -- U = (zeroLocus k J')ᶜ
    have hU_eq : U = (zeroLocus k J')ᶜ := by
      rw [← compl_compl U, hJ']
    have hqnotV : q ∉ zeroLocus k J' := by
      intro hq'; rw [← hJ'] at hq'; exact absurd hqU hq'
    rw [mem_zeroLocus_iff] at hqnotV
    push Not at hqnotV
    obtain ⟨f, hfJ', hfq⟩ := hqnotV
    -- rename Sum.inr f ∉ J.radical
    have hf_not_rad : MvPolynomial.rename Sum.inr f ∉ J.radical := fun hrad => by
      have hfrad_comap : f ∈ (J.comap (MvPolynomial.rename Sum.inr).toRingHom).radical := by
        rw [← Ideal.comap_radical]; exact Ideal.mem_comap.mpr hrad
      exact hfq (MvPolynomial.mem_vanishingIdeal_iff.mp
        (MvPolynomial.radical_le_vanishingIdeal_zeroLocus (K := k) _ hfrad_comap) q hq)
    -- Nullstellensatz: ∃ x ∈ V(J), aeval x (rename Sum.inr f) ≠ 0
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)] at hf_not_rad
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hf_not_rad
    push Not at hf_not_rad
    obtain ⟨x, hxJ, hfx⟩ := hf_not_rad
    rw [MvPolynomial.aeval_rename] at hfx
    -- x ∘ Sum.inr ∈ π(V(J)) ∩ U
    have hxnotV : x ∘ Sum.inr ∉ zeroLocus k J' := by
      rw [mem_zeroLocus_iff]; push Not; exact ⟨f, hfJ', hfx⟩
    refine ⟨x ∘ Sum.inr, ?_, ⟨x, hxJ, rfl⟩⟩
    rw [hU_eq]; exact hxnotV

end ProjectionsAndGraphs

/-! ## §4.2  Images of Polynomial Maps (Hassett §4.2) -/

section ImagesOfMaps

variable {k : Type*} [Field k] {σ τ : Type*}

/-- A *Zariski-constructible* set in `σ → k` is a finite union of sets of the form
`V(I) \ V(J)` (locally closed sets in the Zariski topology).  By Chevalley's theorem,
images of polynomial maps between affine varieties are constructible. -/
def IsZariskiConstructible (S : Set (σ → k)) : Prop :=
  ∃ (n : ℕ) (Is Js : Fin n → Ideal (MvPolynomial σ k)),
    S = ⋃ i, (zeroLocus k (Is i) \ zeroLocus k (Js i))

/-- Every Zariski-closed set is constructible (take a single locally closed piece `V(I) \ ∅`). -/
theorem isClosed_isZariskiConstructible {S : Set (σ → k)}
    (h : @IsClosed _ (zariskiTopology k σ) S) : IsZariskiConstructible S := by
  obtain ⟨I, rfl⟩ := (zariskiTopology_isClosed_iff _).mp h
  refine ⟨1, fun _ => I, fun _ => ⊤, ?_⟩
  simp [Set.iUnion_const, zeroLocus_top]

/-- Every Zariski-open set is constructible (take a single locally closed piece `𝔸^σ \ V(I)`). -/
theorem isOpen_isZariskiConstructible {S : Set (σ → k)}
    (h : @IsOpen _ (zariskiTopology k σ) S) : IsZariskiConstructible S := by
  rw [zariskiTopology_isOpen_iff] at h
  obtain ⟨I, hI⟩ := h
  refine ⟨1, fun _ => ⊥, fun _ => I, ?_⟩
  rw [Set.iUnion_const, zeroLocus_bot, top_sdiff, ← hI, compl_compl]

/-- The image of the polynomial map `v ↦ (fun j => aeval v (f j))` on `V(I)` equals the
projection of the graph `Γ_f ⊆ (σ ⊕ τ) → k` onto the `τ`-coordinates. -/
theorem image_polynomial_eq_proj_graph (I : Ideal (MvPolynomial σ k))
    (f : τ → MvPolynomial σ k) :
    (fun v : σ → k => fun j => aeval v (f j)) '' zeroLocus k I =
    (· ∘ Sum.inr) '' graphOf I f := by
  ext q
  simp only [Set.mem_image, graphOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Sum.elim v (fun j => aeval v (f j)), ⟨?_, ?_⟩, ?_⟩
    · simpa [Function.comp, Sum.elim_comp_inl] using hv
    · intro j; simp [Sum.elim_comp_inl]
    · funext j; simp
  · rintro ⟨p, ⟨hpI, hpf⟩, rfl⟩
    exact ⟨p ∘ Sum.inl, hpI, funext fun j => (hpf j).symm⟩

/-- **Hassett §4.2 / Chevalley's Theorem** — The image of `V(I)` under the polynomial map
`v ↦ (fun j => aeval v (f j))` is Zariski-constructible.

*Proof sketch*: The graph `Γ_f = graphOf I f` is Zariski-closed in `(σ ⊕ τ) → k`
(by `graphOf_eq_zeroLocus`).  Chevalley's theorem (proved via Noether normalization)
then implies the projection `π(Γ_f)` is constructible; and `π(Γ_f)` equals the image
by `image_polynomial_eq_proj_graph`. -/
theorem chevalley_constructible (I : Ideal (MvPolynomial σ k))
    (f : τ → MvPolynomial σ k) :
    IsZariskiConstructible ((fun v : σ → k => fun j => aeval v (f j)) '' zeroLocus k I) :=
  sorry

/-- The image of all of affine space `𝔸^σ(k)` under a polynomial map is constructible. -/
theorem image_polynomial_isConstructible (f : τ → MvPolynomial σ k) :
    IsZariskiConstructible (Set.range (fun v : σ → k => fun j => aeval v (f j))) := by
  rw [← Set.image_univ,
    show (Set.univ : Set (σ → k)) = zeroLocus k (⊥ : Ideal (MvPolynomial σ k)) by simp]
  exact chevalley_constructible ⊥ f

/-- The closure of the image of `V(I)` under a polynomial map is a zero locus.
This combines `image_polynomial_eq_proj_graph` with `isClosed_graphOf`. -/
theorem closure_image_polynomial_isClosed (I : Ideal (MvPolynomial σ k))
    (f : τ → MvPolynomial σ k) :
    @IsClosed _ (zariskiTopology k τ)
      (@closure _ (zariskiTopology k τ)
        ((fun v : σ → k => fun j => aeval v (f j)) '' zeroLocus k I)) :=
  @isClosed_closure _ (zariskiTopology k τ) _

end ImagesOfMaps

/-! ## §4.3  Secant Varieties, Joins, and Scrolls (Hassett §4.3) -/

section SecantVarieties

variable {k : Type*} [Field k] {σ : Type*}

/-- The standard affine `N`-simplex: `Δ_N = {t : Fin N → k | ∑ i, t i = 1}`.
Points represent barycentric coordinates for affine combinations of `N` points. -/
def affineSimplex (k : Type*) [Field k] (N : ℕ) : Set (Fin N → k) :=
  {t | ∑ i, t i = 1}

/-- The affine `N`-simplex is Zariski-closed: it is the zero locus of `∑ i, X i - 1`. -/
theorem affineSimplex_isClosed (k : Type*) [Field k] (N : ℕ) :
    @IsClosed _ (zariskiTopology k (Fin N)) (affineSimplex k N) := by
  apply (zariskiTopology_isClosed_iff _).mpr
  exact ⟨Ideal.span {∑ i : Fin N, MvPolynomial.X i - 1}, by
    ext t
    simp only [affineSimplex, Set.mem_setOf_eq, mem_zeroLocus_iff]
    constructor
    · intro ht q hq
      rw [Ideal.mem_span_singleton] at hq
      obtain ⟨c, hc⟩ := hq
      simp only [hc, map_mul, map_sub, map_sum, MvPolynomial.aeval_X, map_one]
      rw [ht, sub_self, zero_mul]
    · intro ht
      have h := ht _ (Ideal.mem_span_singleton.mpr (dvd_refl _))
      simp only [map_sub, map_sum, MvPolynomial.aeval_X, map_one] at h
      exact sub_eq_zero.mp h⟩

/-- The *N-secant map*: takes `N` points and barycentric weights, returns their affine combination.
`secantMap N vs ts = fun s => ∑ i, ts i · vs i s`. -/
def secantMap (N : ℕ) (vs : Fin N → σ → k) (ts : Fin N → k) : σ → k :=
  fun s => ∑ i : Fin N, ts i * vs i s

/-- **Hassett §4.3** — The *N-secant variety* `Sec_N(V)` of `V`: the Zariski closure of all
weighted affine sums `∑ tᵢ · vᵢ` with `vᵢ ∈ V` and barycentric weights `∑ tᵢ = 1`. -/
noncomputable def secantVariety (N : ℕ) (V : Set (σ → k)) : Set (σ → k) :=
  @closure _ (zariskiTopology k σ)
    (Set.image2 (secantMap N)
      {vs : Fin N → σ → k | ∀ i, vs i ∈ V}
      (affineSimplex k N))

/-- The N-secant variety is Zariski-closed (it is defined as a topological closure). -/
theorem isClosed_secantVariety (N : ℕ) (V : Set (σ → k)) :
    @IsClosed _ (zariskiTopology k σ) (secantVariety N V) :=
  @isClosed_closure _ (zariskiTopology k σ) _

/-- `secantVariety` is monotone: enlarging `V` enlarges `Sec_N(V)`. -/
theorem secantVariety_mono {N : ℕ} {V W : Set (σ → k)} (h : V ⊆ W) :
    secantVariety N V ⊆ secantVariety N W :=
  @closure_mono _ (zariskiTopology k σ) _ _
    (Set.image2_subset (fun _ hvs i => h (hvs i)) (le_refl _))

/-- The *join* `J(V, W)` of two sets: Zariski closure of all affine line segments
`{t · v + (1 - t) · w | v ∈ V, w ∈ W, t ∈ k}`. -/
noncomputable def joinVariety (V W : Set (σ → k)) : Set (σ → k) :=
  @closure _ (zariskiTopology k σ)
    { p | ∃ (t : k) (v w : σ → k), v ∈ V ∧ w ∈ W ∧
          p = fun s => t * v s + (1 - t) * w s }

/-- The join of two sets is Zariski-closed. -/
theorem isClosed_joinVariety (V W : Set (σ → k)) :
    @IsClosed _ (zariskiTopology k σ) (joinVariety V W) :=
  @isClosed_closure _ (zariskiTopology k σ) _

/-- `V` is contained in `Sec_1(V)` (the secant variety with one point is the Zariski closure of V). -/
theorem subset_secantVariety_one (V : Set (σ → k)) :
    V ⊆ secantVariety 1 V := by
  intro v hv
  apply @subset_closure _ (zariskiTopology k σ)
  refine Set.mem_image2.mpr ⟨![v], ?_, ![1], ?_, ?_⟩
  · exact fun i => by fin_cases i; exact hv
  · simp [affineSimplex]
  · funext s; simp [secantMap]

/-- The 1-secant variety of a closed set equals the set itself. -/
theorem secantVariety_one_of_isClosed {V : Set (σ → k)}
    (hV : @IsClosed _ (zariskiTopology k σ) V) : secantVariety 1 V = V :=
  le_antisymm
    (@closure_minimal _ (zariskiTopology k σ) _ V (by
      intro p hp
      obtain ⟨vs, hvs, ts, hts, rfl⟩ := Set.mem_image2.mp hp
      have hts0 : ts 0 = 1 := by
        simp only [affineSimplex, Set.mem_setOf_eq, Fin.sum_univ_one] at hts; exact hts
      have heq : secantMap 1 vs ts = vs 0 := funext fun s => by
        simp [secantMap, hts0]
      rw [heq]; exact hvs 0) hV)
    (subset_secantVariety_one V)

end SecantVarieties

/-! ## §4.4  Tangent Spaces and Smooth Points (Hassett §6.1) -/

section TangentSpaces

variable {k : Type*} [Field k] {σ : Type*} [Fintype σ]

/-- The *directional derivative* of `f ∈ k[σ]` at `p ∈ k^σ` in direction `v ∈ k^σ`,
as a `k`-linear map in `v`. -/
noncomputable def linearizationAt (f : MvPolynomial σ k) (p : σ → k) :
    (σ → k) →ₗ[k] k where
  toFun v := ∑ i : σ, aeval p (MvPolynomial.pderiv i f) * v i
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring

/-- Computation rule for `linearizationAt`. -/
@[simp] theorem linearizationAt_apply (f : MvPolynomial σ k) (p v : σ → k) :
    linearizationAt f p v = ∑ i : σ, aeval p (MvPolynomial.pderiv i f) * v i :=
  rfl

/-- The *tangent space* `T_p V(I)` at `p ∈ V(I)` is the subspace of `k^σ` cut out by the
linearizations of all `f ∈ I`.  Geometrically, it is the kernel of the Jacobian matrix of
generators of `I` evaluated at `p`. -/
noncomputable def tangentSpace (I : Ideal (MvPolynomial σ k)) (p : σ → k) :
    Submodule k (σ → k) :=
  ⨅ f : I, LinearMap.ker (linearizationAt f.1 p)

theorem mem_tangentSpace {I : Ideal (MvPolynomial σ k)} {p v : σ → k} :
    v ∈ tangentSpace I p ↔
    ∀ f ∈ I, ∑ i : σ, aeval p (MvPolynomial.pderiv i f) * v i = 0 := by
  simp only [tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker,
             linearizationAt_apply, Subtype.forall]

/-- `T_p 𝔸^σ = 𝔸^σ`: the tangent space to affine space at any point is everything. -/
theorem tangentSpace_bot (p : σ → k) :
    tangentSpace (⊥ : Ideal (MvPolynomial σ k)) p = ⊤ := by
  ext v
  simp only [mem_tangentSpace, Submodule.mem_top, iff_true]
  intro f hf
  rw [Ideal.mem_bot.mp hf]
  simp

/-- The tangent space is anti-monotone in the ideal: `I ≤ J → T_p V(J) ≤ T_p V(I)`. -/
theorem tangentSpace_anti {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) (p : σ → k) :
    tangentSpace J p ≤ tangentSpace I p := by
  intro v hv
  rw [mem_tangentSpace] at *
  exact fun f hf => hv f (h hf)

/-- A closed embedding `V(J) ⊆ V(I)` (i.e., `I ⊆ J`) gives a containment
of tangent spaces: `T_p V(J) ≤ T_p V(I)`. -/
theorem tangentSpace_le_of_le {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) (p : σ → k) :
    tangentSpace J p ≤ tangentSpace I p :=
  tangentSpace_anti h p

/-- The linearization of the zero polynomial is identically zero. -/
@[simp] theorem linearizationAt_zero (p : σ → k) : linearizationAt (0 : MvPolynomial σ k) p = 0 := by
  ext v; simp [linearizationAt]

/-- The linearization is additive in `f`. -/
theorem linearizationAt_add (f g : MvPolynomial σ k) (p : σ → k) :
    linearizationAt (f + g) p = linearizationAt f p + linearizationAt g p := by
  ext v
  simp only [linearizationAt, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add,
             add_mul, Finset.sum_add_distrib]

/-- A point `p ∈ V(I)` is *smooth* (or *regular*) of (tangent) dimension `d` if the tangent
space `T_p V(I)` has `k`-dimension `d`. -/
def IsRegularPoint (I : Ideal (MvPolynomial σ k)) (p : σ → k) (d : ℕ) : Prop :=
  p ∈ zeroLocus k I ∧ Module.finrank k (tangentSpace I p) = d

/-- A point `p ∈ V(I)` is *singular* if it fails to be regular of the expected dimension. -/
def IsSingularPoint (I : Ideal (MvPolynomial σ k)) (p : σ → k) (d : ℕ) : Prop :=
  p ∈ zeroLocus k I ∧ Module.finrank k (tangentSpace I p) > d

/-- The *singular locus* of `V(I)` of expected dimension `d`. -/
def singularLocus (I : Ideal (MvPolynomial σ k)) (d : ℕ) : Set (σ → k) :=
  {p ∈ zeroLocus k I | IsSingularPoint I p d}

/-- A smooth point has a tangent space of the smallest possible dimension. -/
theorem IsRegularPoint.tangentSpace_dim {I : Ideal (MvPolynomial σ k)} {p : σ → k} {d : ℕ}
    (h : IsRegularPoint I p d) :
    Module.finrank k (tangentSpace I p) = d :=
  h.2

/-- At a smooth point, the tangent space is the "expected" one (contained in `k^σ`). -/
theorem tangentSpace_le_top (I : Ideal (MvPolynomial σ k)) (p : σ → k) :
    tangentSpace I p ≤ ⊤ :=
  le_top

/-- The tangent space of `V(I ⊔ J) = V(I) ∩ V(J)` equals the intersection of tangent spaces. -/
theorem tangentSpace_sup (I J : Ideal (MvPolynomial σ k)) (p : σ → k) :
    tangentSpace (I ⊔ J) p = tangentSpace I p ⊓ tangentSpace J p := by
  ext v
  simp only [mem_tangentSpace, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun f hf => h f (Submodule.mem_sup_left hf),
           fun g hg => h g (Submodule.mem_sup_right hg)⟩
  · intro ⟨hI, hJ⟩ g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
    have h1 := hI a ha
    have h2 := hJ b hb
    simp only [map_add, add_mul, Finset.sum_add_distrib, h1, h2, add_zero]

/-- The *gradient* of `f ∈ k[σ]` at `p ∈ k^σ`: the coefficient vector of the derivative. -/
noncomputable def gradient (f : MvPolynomial σ k) (p : σ → k) : σ → k :=
  fun i => aeval p (MvPolynomial.pderiv i f)

theorem linearizationAt_eq_dotProduct (f : MvPolynomial σ k) (p v : σ → k) :
    linearizationAt f p v = ∑ i : σ, gradient f p i * v i :=
  rfl

/-- **Jacobian criterion for hypersurfaces** — The tangent space of the hypersurface `V({f})`
at a point `p ∈ V({f})` equals the kernel of the gradient linear form `∇f(p) · –`.

Proof: `⊆` follows immediately from definition.  `⊇` uses the Leibniz rule:
for `g = c · f ∈ ⟨f⟩`, `∂g/∂xᵢ(p) = c(p) · ∂f/∂xᵢ(p)` (since `f(p) = 0`). -/
theorem tangentSpace_span_singleton_eq {f : MvPolynomial σ k} {p : σ → k}
    (hp : aeval p f = 0) :
    tangentSpace (Ideal.span {f}) p = LinearMap.ker (linearizationAt f p) := by
  apply le_antisymm
  · intro v hv
    simp only [LinearMap.mem_ker, linearizationAt_apply]
    exact (mem_tangentSpace.mp hv) f (Ideal.subset_span (Set.mem_singleton f))
  · intro v hv
    rw [mem_tangentSpace]
    intro g hg
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg
    simp only [LinearMap.mem_ker, linearizationAt_apply] at hv
    calc ∑ i : σ, aeval p (MvPolynomial.pderiv i (f * c)) * v i
        = ∑ i : σ, aeval p c * (aeval p (MvPolynomial.pderiv i f) * v i) :=
          Finset.sum_congr rfl (fun i _ => by
            have hpd : MvPolynomial.pderiv i (f * c) =
                MvPolynomial.pderiv i f * c + f * MvPolynomial.pderiv i c :=
              MvPolynomial.pderiv_mul
            rw [hpd, map_add, map_mul, map_mul, hp, zero_mul, add_zero]; ring)
      _ = aeval p c * ∑ i : σ, aeval p (MvPolynomial.pderiv i f) * v i := by
          rw [← Finset.mul_sum]
      _ = 0 := by rw [hv, mul_zero]

/-- **Jacobian criterion for hypersurfaces** (Hassett §6.2) — `p ∈ V({f})` is a regular point
of expected dimension `Fintype.card σ - 1` if and only if the gradient `∇f(p) ≠ 0`.
The kernel of a nonzero linear form on `k^σ` has dimension `|σ| - 1` by rank-nullity. -/
theorem isRegularPoint_iff_gradient_ne_zero {f : MvPolynomial σ k} {p : σ → k}
    (hp : aeval p f = 0) [Nonempty σ] :
    IsRegularPoint (Ideal.span {f}) p (Fintype.card σ - 1) ↔ gradient f p ≠ 0 := by
  rw [IsRegularPoint, tangentSpace_span_singleton_eq hp]
  have hmem : p ∈ zeroLocus k (Ideal.span {f}) := by
    rw [mem_zeroLocus_iff]
    intro g hg
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg
    simp only [map_mul, hp, zero_mul]
  rw [and_iff_right hmem]
  -- Reduce: gradient ≠ 0 ↔ linearizationAt ≠ 0
  have hgrad_iff : gradient f p ≠ 0 ↔ linearizationAt f p ≠ 0 := by
    constructor
    · intro hg hlin
      apply hg; ext j
      haveI : DecidableEq σ := Classical.decEq σ
      have key : linearizationAt f p (Pi.single j 1) = gradient f p j := by
        rw [linearizationAt_eq_dotProduct,
          Finset.sum_eq_single j
            (fun i _ hji => by simp only [Pi.single_apply, if_neg hji, mul_zero])
            (fun h => absurd (Finset.mem_univ j) h),
          Pi.single_apply, if_pos rfl, mul_one]
      simp only [Pi.zero_apply]
      exact key.symm.trans (DFunLike.congr_fun hlin _)
    · intro hlin hg
      apply hlin; ext v
      simp only [LinearMap.zero_apply, linearizationAt_eq_dotProduct]
      simp [show gradient f p = 0 from hg]
  rw [hgrad_iff]
  -- Rank-nullity: finrank ker φ = card σ - 1 ↔ φ ≠ 0
  have hpos : 0 < Fintype.card σ := Fintype.card_pos
  constructor
  · intro hfin hzero
    have hker_top : LinearMap.ker (linearizationAt f p) = ⊤ :=
      LinearMap.ker_eq_top.mpr hzero
    rw [hker_top, finrank_top, Module.finrank_pi] at hfin
    omega
  · intro hne
    have hrange_ne : LinearMap.range (linearizationAt f p) ≠ ⊥ :=
      fun h => hne (LinearMap.range_eq_bot.mp h)
    have hrange1 : Module.finrank k (LinearMap.range (linearizationAt f p)) = 1 := by
      have h_le : Module.finrank k (LinearMap.range (linearizationAt f p)) ≤ 1 := by
        have := Submodule.finrank_le (R := k) (LinearMap.range (linearizationAt f p))
        rwa [Module.finrank_self] at this
      have h_ge : 1 ≤ Module.finrank k (LinearMap.range (linearizationAt f p)) :=
        Submodule.one_le_finrank_iff.mpr hrange_ne
      omega
    have hrn : Module.finrank k (LinearMap.range (linearizationAt f p)) +
        Module.finrank k (LinearMap.ker (linearizationAt f p)) = Fintype.card σ := by
      have := LinearMap.finrank_range_add_finrank_ker (linearizationAt f p)
      rwa [Module.finrank_pi] at this
    omega

/-- **Leibniz rule** for the linearization: `∇(fg)(p) = g(p)∇f(p) + f(p)∇g(p)`. -/
theorem linearizationAt_mul (f g : MvPolynomial σ k) (p : σ → k) :
    linearizationAt (f * g) p =
    aeval p g • linearizationAt f p + aeval p f • linearizationAt g p := by
  ext v
  simp only [linearizationAt_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show ∑ i : σ, aeval p (MvPolynomial.pderiv i (f * g)) * v i =
      aeval p g * ∑ i : σ, aeval p (MvPolynomial.pderiv i f) * v i +
      aeval p f * ∑ i : σ, aeval p (MvPolynomial.pderiv i g) * v i from by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have h : MvPolynomial.pderiv i (f * g) =
        MvPolynomial.pderiv i f * g + f * MvPolynomial.pderiv i g := MvPolynomial.pderiv_mul
    rw [h, map_add, map_mul, map_mul]; ring]

/-- The linearization of a scalar constant is the zero map. -/
@[simp] theorem linearizationAt_C (c : k) (p : σ → k) :
    linearizationAt (C c : MvPolynomial σ k) p = 0 := by
  ext v; simp [linearizationAt_apply, MvPolynomial.pderiv_C]

/-- The linearization of the `i`-th coordinate function `X i` is the `i`-th projection. -/
@[simp] theorem linearizationAt_X [DecidableEq σ] (i : σ) (p : σ → k) :
    linearizationAt (X i : MvPolynomial σ k) p = LinearMap.proj i := by
  apply LinearMap.ext; intro v
  rw [linearizationAt_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i
    (fun j _ hji => by simp only [MvPolynomial.pderiv_X_of_ne hji.symm, map_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)]
  have hd : MvPolynomial.pderiv i (X i : MvPolynomial σ k) = 1 := by
    rw [MvPolynomial.pderiv_X, Pi.single_apply, if_pos rfl]
  rw [hd, map_one, one_mul]

/-- The tangent space at a complete intersection of two hypersurfaces. -/
theorem tangentSpace_span_pair_eq {f g : MvPolynomial σ k} {p : σ → k}
    (hf : aeval p f = 0) (hg : aeval p g = 0) :
    tangentSpace (Ideal.span {f, g}) p =
    LinearMap.ker (linearizationAt f p) ⊓ LinearMap.ker (linearizationAt g p) := by
  have hset : ({f, g} : Set (MvPolynomial σ k)) = {f} ∪ {g} := by
    ext; simp [or_comm]
  rw [hset, Ideal.span_union, tangentSpace_sup,
      tangentSpace_span_singleton_eq hf, tangentSpace_span_singleton_eq hg]

/-- The *tangent dimension* of a variety `V(I)` at `p`: `finrank k (T_p V(I))`. -/
noncomputable def tangentDim (I : Ideal (MvPolynomial σ k)) (p : σ → k) : ℕ :=
  Module.finrank k (tangentSpace I p)

/-- The tangent dimension is at most the number of variables (the ambient dimension). -/
theorem tangentDim_le_card (I : Ideal (MvPolynomial σ k)) (p : σ → k) :
    tangentDim I p ≤ Fintype.card σ := by
  have h := Submodule.finrank_le (tangentSpace I p)
  rwa [Module.finrank_pi] at h

end TangentSpaces

/-! ## §4.5  Krull Dimension of Affine Varieties (Hassett §5.1) -/

section VarietyDimension

variable {k : Type*} [Field k] {σ : Type*}

/-- The *Krull dimension* of an affine variety `V ⊆ k^σ`: the Krull dimension of its
coordinate ring, equivalently the maximal length of a chain of irreducible closed subvarieties. -/
noncomputable def varietyDim (V : Set (σ → k)) : WithBot ℕ∞ :=
  ringKrullDim (coordinateRing V)

/-- A field has Krull dimension 0; hence a point variety (coordinate ring ≅ k) has dimension 0. -/
theorem varietyDim_point [IsAlgClosed k] [Finite σ] (p : σ → k) :
    varietyDim ({p} : Set (σ → k)) = 0 := by
  have hmaximal : (vanishingIdeal k {p} : Ideal (MvPolynomial σ k)).IsMaximal :=
    isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨p, rfl⟩
  show ringKrullDim (coordinateRing ({p} : Set (σ → k))) = 0
  exact ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaximal)

/-- The empty variety has Krull dimension `⊥` (its coordinate ring is the zero ring). -/
theorem varietyDim_empty :
    varietyDim (∅ : Set (σ → k)) = ⊥ := by
  simp only [varietyDim]
  haveI : Subsingleton (coordinateRing (∅ : Set (σ → k))) :=
    Ideal.Quotient.subsingleton_iff.mpr vanishingIdeal_empty
  exact ringKrullDim_eq_bot_of_subsingleton

/-- Affine space `𝔸^σ(k)` has Krull dimension `|σ|` when `σ` is finite and `k` is infinite.
Proof: for infinite `k`, `vanishingIdeal k Set.univ = ⊥` (by `MvPolynomial.funext_iff`), so
`coordinateRing Set.univ ≅ MvPolynomial σ k`, and
`ringKrullDim (MvPolynomial σ k) = ringKrullDim k + Nat.card σ = 0 + |σ| = |σ|`. -/
theorem varietyDim_affineSpace [Fintype σ] [Infinite k] :
    varietyDim (Set.univ : Set (σ → k)) = Fintype.card σ := by
  simp only [varietyDim]
  have hvan : vanishingIdeal k (Set.univ : Set (σ → k)) = ⊥ := by
    ext p
    simp only [mem_vanishingIdeal_iff, Set.mem_univ, forall_true_left,
               Ideal.mem_bot, MvPolynomial.aeval_eq_eval]
    constructor
    · intro h
      exact MvPolynomial.funext (fun x => by rw [map_zero]; exact h x)
    · rintro rfl; simp
  have heq : coordinateRing (Set.univ : Set (σ → k)) ≃+* MvPolynomial σ k :=
    (Ideal.quotEquivOfEq hvan).trans (RingEquiv.quotientBot _)
  rw [ringKrullDim_eq_of_ringEquiv heq, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp [Nat.card_eq_fintype_card]

/-- Dimension is monotone: if `V ⊆ W` (as closed sets), then `dim V ≤ dim W`.
Proof: the inclusion `W ↪ V` induces a surjection `k[V] ↠ k[W]` on coordinate rings,
which gives a monotone map on prime spectra. -/
theorem varietyDim_mono {V W : Set (σ → k)} (h : V ⊆ W) :
    varietyDim V ≤ varietyDim W := by
  simp only [varietyDim]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (vanishingIdeal_anti_mono h))
    (Ideal.Quotient.factor_surjective _)

end VarietyDimension

end AffineVarieties
