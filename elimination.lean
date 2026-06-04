import Mathlib
import affine_varieties

open MvPolynomial Set Ideal Finset AffineVarieties

/-!
# Elimination Theory — Hassett Chapter 4

Formalises elimination theory over a field `k`:
- Projections and elimination ideals (§4.1)
- Graphs of polynomial maps (§4.1)
- Closure Theorem for projections (Theorem 4.3)
- Elimination Theorem via Gröbner bases (Theorem 4.8, sorry'd)
- Secant varieties and joins (§4.3)

References: Hassett, *Introduction to Algebraic Geometry*, Chapter 4.
-/

namespace Elimination

variable {k : Type*} [Field k]

-- ---------------------------------------------------------------------------
-- §4.1  Projections
-- ---------------------------------------------------------------------------

/-- The projection π : kⁿ⁺ᵐ → kᵐ forgetting the first n coordinates. -/
def projection (n m : ℕ) : (Fin (n + m) → k) → (Fin m → k) :=
  fun v j => v (Fin.natAdd n j)

/-- The n-th elimination ideal of J ⊆ k[x₁,…,xₙ,y₁,…,yₘ] is
    J ∩ k[y₁,…,yₘ], realised as the preimage under the renaming
    yⱼ ↦ x_{n+j}. -/
noncomputable def eliminationIdeal (n : ℕ) {m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + m)) k)) :
    Ideal (MvPolynomial (Fin m) k) :=
  J.comap (MvPolynomial.rename (Fin.natAdd n))

/-- A polynomial f ∈ k[y] lies in the elimination ideal iff rename(f) ∈ J. -/
theorem mem_eliminationIdeal_iff (n : ℕ) {m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + m)) k))
    (f : MvPolynomial (Fin m) k) :
    f ∈ eliminationIdeal n J ↔
    MvPolynomial.rename (Fin.natAdd n) f ∈ J :=
  Ideal.mem_comap

-- ---------------------------------------------------------------------------
-- §4.1  Graphs of polynomial maps
-- ---------------------------------------------------------------------------

/-- The graph ideal of a polynomial map φ : kⁿ → kᵐ (given component-wise
    as φⱼ ∈ k[x₁,…,xₙ]) inside k[x₁,…,xₙ,y₁,…,yₘ].

    I(Γ_φ) = π₁*(I) + ⟨y₁ - φ₁(x), …, yₘ - φₘ(x)⟩

    where π₁* : k[x] → k[x,y] renames xᵢ ↦ xᵢ (via castAdd). -/
noncomputable def graphIdeal (n m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (φ : Fin m → MvPolynomial (Fin n) k) :
    Ideal (MvPolynomial (Fin (n + m)) k) :=
  I.map (MvPolynomial.rename (Fin.castAdd m)) ⊔
  span (⋃ j : Fin m,
    {MvPolynomial.X (Fin.natAdd n j) -
      MvPolynomial.rename (Fin.castAdd m) (φ j)})

-- ---------------------------------------------------------------------------
-- §4.1  Forward direction of Theorem 4.3
-- ---------------------------------------------------------------------------

/-- Forward inclusion: the image of V(J) under projection is contained in
    V(J_n), the zero locus of the elimination ideal.

    Proof: if f ∈ J_n then rename(natAdd n)(f) ∈ J, so it vanishes on
    every v ∈ V(J); but aeval v (rename f) = aeval (v ∘ natAdd n) f =
    aeval (π(v)) f by the aeval_rename lemma. -/
theorem projection_image_subset_eliminationLocus
    (n m : ℕ) (J : Ideal (MvPolynomial (Fin (n + m)) k)) :
    projection n m '' MvPolynomial.zeroLocus k J ⊆
    MvPolynomial.zeroLocus k (eliminationIdeal n J) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_zeroLocus_iff]
  intro f hf
  rw [mem_eliminationIdeal_iff] at hf
  have heval : MvPolynomial.aeval v (MvPolynomial.rename (Fin.natAdd n) f) = 0 :=
    mem_zeroLocus_iff.mp hv _ hf
  rw [MvPolynomial.aeval_rename] at heval
  exact heval

-- ---------------------------------------------------------------------------
-- §4.1  Closure Theorem (Theorem 4.3)
-- ---------------------------------------------------------------------------

/-- Closure Theorem (Hassett Theorem 4.3).

    With the Zariski topology on affine space, the closure of π(V(J)) equals
    V(J_n).  The forward inclusion is proved above; the reverse inclusion
    requires the Nullstellensatz and that J = I(V(J)) (which holds when k is
    algebraically closed), so we sorry this direction. -/
theorem closure_projection_eq_eliminationLocus [IsAlgClosed k]
    (n m : ℕ) (J : Ideal (MvPolynomial (Fin (n + m)) k)) :
    @closure _ (zariskiTopology k (Fin m)) (projection n m '' MvPolynomial.zeroLocus k J) =
    MvPolynomial.zeroLocus k (eliminationIdeal n J) := by
  letI : TopologicalSpace (Fin m → k) := zariskiTopology k (Fin m)
  -- projection n m = (· ∘ Fin.natAdd n), eliminationIdeal n J = J.comap(rename(Fin.natAdd n))
  apply Set.eq_of_subset_of_subset
  · -- Forward: closure(π(V(J))) ⊆ V(eliminationIdeal n J)
    apply closure_minimal _ (isClosed_zeroLocus _)
    rintro _ ⟨x, hx, rfl⟩
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro f hf
    rw [mem_eliminationIdeal_iff] at hf
    have h := MvPolynomial.mem_zeroLocus_iff.mp hx _ hf
    show aeval (x ∘ Fin.natAdd n) f = 0
    rw [← MvPolynomial.aeval_rename]
    exact h
  · -- Backward: V(eliminationIdeal n J) ⊆ closure(π(V(J)))
    intro q hq
    rw [mem_closure_iff]
    intro U hU hqU
    rw [zariskiTopology_isOpen_iff] at hU
    simp only [Set.mem_setOf_eq] at hU
    obtain ⟨J', hJ'⟩ := hU
    have hU_eq : U = (MvPolynomial.zeroLocus k J')ᶜ := by
      rw [← compl_compl U, hJ']
    have hqnotV : q ∉ MvPolynomial.zeroLocus k J' := by
      intro hq'; rw [← hJ'] at hq'; exact absurd hqU hq'
    rw [MvPolynomial.mem_zeroLocus_iff] at hqnotV
    push Not at hqnotV
    obtain ⟨f, hfJ', hfq⟩ := hqnotV
    -- rename (Fin.natAdd n) f ∉ J.radical
    have hf_not_rad : MvPolynomial.rename (Fin.natAdd n) f ∉ J.radical := fun hrad => by
      have hfrad_comap : f ∈ (eliminationIdeal n J).radical := by
        rw [eliminationIdeal, ← Ideal.comap_radical]
        exact Ideal.mem_comap.mpr hrad
      exact hfq (MvPolynomial.mem_vanishingIdeal_iff.mp
        (MvPolynomial.radical_le_vanishingIdeal_zeroLocus (K := k) _ hfrad_comap) q hq)
    -- Nullstellensatz: ∃ x ∈ V(J), aeval x (rename (Fin.natAdd n) f) ≠ 0
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)] at hf_not_rad
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hf_not_rad
    push Not at hf_not_rad
    obtain ⟨x, hxJ, hfx⟩ := hf_not_rad
    rw [MvPolynomial.aeval_rename] at hfx
    -- x ∘ Fin.natAdd n ∈ π(V(J)) ∩ U
    have hxnotV : x ∘ Fin.natAdd n ∉ MvPolynomial.zeroLocus k J' := by
      rw [MvPolynomial.mem_zeroLocus_iff]; push Not; exact ⟨f, hfJ', hfx⟩
    refine ⟨x ∘ Fin.natAdd n, ?_, ⟨x, hxJ, rfl⟩⟩
    rw [hU_eq]; exact hxnotV

-- ---------------------------------------------------------------------------
-- §4.1  Proposition 4.5 — the variety of the graph ideal is the graph
-- ---------------------------------------------------------------------------

/-- The variety of the graph ideal equals the graph of φ over V(I).

    Γ_φ = {(v, φ(v)) : v ∈ V(I)} ⊆ kⁿ × kᵐ ≅ kⁿ⁺ᵐ. -/
theorem graphIdeal_zeroLocus_eq
    (n m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (φ : Fin m → MvPolynomial (Fin n) k) :
    MvPolynomial.zeroLocus k (graphIdeal n m I φ) =
    {v : Fin (n + m) → k |
      (fun i => v (Fin.castAdd m i)) ∈ MvPolynomial.zeroLocus k I ∧
      ∀ j : Fin m, v (Fin.natAdd n j) =
        MvPolynomial.aeval (fun i => v (Fin.castAdd m i)) (φ j)} := by
  have vcomp_eq : ∀ v : Fin (n + m) → k,
      (fun i => v (Fin.castAdd m i)) = v ∘ Fin.castAdd m := fun v => rfl
  ext v
  simp only [Set.mem_setOf_eq]
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · -- Forward: if v vanishes on graphIdeal, extract the two conditions
    intro h
    simp only [graphIdeal] at h
    have hA : ∀ f ∈ I.map (MvPolynomial.rename (Fin.castAdd m)), MvPolynomial.aeval v f = 0 :=
      fun f hf => h f (Ideal.mem_sup_left hf)
    have hB : ∀ f ∈ span (⋃ j : Fin m,
        {MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.rename (Fin.castAdd m) (φ j)}),
        MvPolynomial.aeval v f = 0 :=
      fun f hf => h f (Ideal.mem_sup_right hf)
    refine ⟨?_, ?_⟩
    · -- Condition 1: (fun i => v (castAdd m i)) ∈ zeroLocus k I
      rw [MvPolynomial.mem_zeroLocus_iff, vcomp_eq]
      intro g hg
      have hmem : MvPolynomial.rename (Fin.castAdd m) g ∈
          I.map (MvPolynomial.rename (Fin.castAdd m)) :=
        Ideal.mem_map_of_mem _ hg
      have hval := hA _ hmem
      rwa [MvPolynomial.aeval_rename] at hval
    · -- Condition 2: v (natAdd n j) = aeval (fun i => v (castAdd m i)) (φ j)
      intro j
      rw [vcomp_eq]
      have hgen : MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.rename (Fin.castAdd m) (φ j) ∈
          span (⋃ j : Fin m,
            {MvPolynomial.X (Fin.natAdd n j) -
              MvPolynomial.rename (Fin.castAdd m) (φ j)}) := by
        apply Ideal.subset_span
        simp only [Set.mem_iUnion, Set.mem_singleton_iff]
        exact ⟨j, rfl⟩
      have hval := hB _ hgen
      simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_rename] at hval
      exact sub_eq_zero.mp hval
  · -- Backward: if v satisfies both conditions, it vanishes on graphIdeal
    rintro ⟨h1, h2⟩
    simp only [graphIdeal]
    rw [MvPolynomial.mem_zeroLocus_iff, vcomp_eq] at h1
    have h2' : ∀ j : Fin m, v (Fin.natAdd n j) = MvPolynomial.aeval (v ∘ Fin.castAdd m) (φ j) :=
      fun j => by rw [← vcomp_eq]; exact h2 j
    intro f hf
    -- f ∈ A ⊔ B, write f = a + b
    rw [Submodule.mem_sup] at hf
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    simp only [map_add]
    -- Show aeval v a = 0
    have hva : MvPolynomial.aeval v a = 0 := by
      suffices hle : I.map (MvPolynomial.rename (Fin.castAdd m)) ≤
          RingHom.ker (MvPolynomial.aeval v) by
        exact hle ha
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp only [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.aeval_rename]
      exact h1 g hg
    -- Show aeval v b = 0
    have hvb : MvPolynomial.aeval v b = 0 := by
      have hvanish : ∀ j : Fin m, MvPolynomial.aeval v
          (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.rename (Fin.castAdd m) (φ j)) = 0 := by
        intro j
        simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_rename]
        exact sub_eq_zero.mpr (h2' j)
      have hle : span (⋃ j : Fin m,
          {MvPolynomial.X (Fin.natAdd n j) -
            MvPolynomial.rename (Fin.castAdd m) (φ j)}) ≤
          RingHom.ker (MvPolynomial.aeval v) := by
        rw [Ideal.span_le]
        intro x hx
        simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
        obtain ⟨j, rfl⟩ := hx
        exact hvanish j
      exact hle hb
    simp [hva, hvb]

-- ---------------------------------------------------------------------------
-- §4.1  Theorem 4.8 — Elimination Theorem (Gröbner basis version)
-- ---------------------------------------------------------------------------

/-- Elimination Theorem (Hassett Theorem 4.8).

    If G is a Gröbner basis of J with respect to a lex elimination order
    (x₁ > … > xₙ > y₁ > … > yₘ), then G ∩ k[y₁,…,yₘ] is a Gröbner
    basis of the elimination ideal J_n.

    This is a deep result requiring Buchberger theory and monomial orders.
    The statement as formalised here only asserts finite generation of the
    elimination ideal, which follows from Noetherianness of `k[y₁,…,yₘ]`. -/
theorem elimination_theorem
    (n m : ℕ) (J : Ideal (MvPolynomial (Fin (n + m)) k)) :
    ∃ (G : Finset (MvPolynomial (Fin m) k)),
      span (G : Set (MvPolynomial (Fin m) k)) = eliminationIdeal n J := by
  have hfg : (eliminationIdeal n J).FG := IsNoetherian.noetherian _
  obtain ⟨S, hS⟩ := hfg
  exact ⟨S, hS⟩

-- ---------------------------------------------------------------------------
-- §4.3  Secant varieties and joins
-- ---------------------------------------------------------------------------

section SecantVarieties

variable {n : ℕ} [TopologicalSpace (Fin n → k)]

variable (k) in
/-- The standard N-simplex Δ_N: affine combinations with non-negative
    weights summing to 1.  Here we work purely algebraically, so the
    condition is just ∑ tᵢ = 1. -/
def standardSimplex (N : ℕ) : Set (Fin N → k) :=
  {t : Fin N → k | ∑ i, t i = 1}

/-- Affine combination of N points with weights t ∈ Δ_N. -/
def affineCombination (N : ℕ) (pts : Fin N → Fin n → k) (t : Fin N → k) :
    Fin n → k :=
  fun j => ∑ i : Fin N, t i * pts i j

/-- The N-th secant variety of V: closure of all affine combinations of
    N points of V with weights in Δ_N. -/
noncomputable def secantVariety (N : ℕ) (V : Set (Fin n → k)) :
    Set (Fin n → k) :=
  closure (⋃ (pts : Fin N → Fin n → k) (_ : ∀ i, pts i ∈ V)
             (t : Fin N → k) (_ : t ∈ standardSimplex k N),
    {affineCombination N pts t})

/-- The join of varieties V₁,…,V_N: closure of all affine combinations
    of one point from each. -/
noncomputable def joinVarieties (N : ℕ) (Vs : Fin N → Set (Fin n → k)) :
    Set (Fin n → k) :=
  closure (⋃ (pts : Fin N → Fin n → k) (_ : ∀ i, pts i ∈ Vs i)
             (t : Fin N → k) (_ : t ∈ standardSimplex k N),
    {affineCombination N pts t})

/-- The cone over V with apex p: the join of V and the single point {p}. -/
noncomputable def coneOver (V : Set (Fin n → k)) (p : Fin n → k) :
    Set (Fin n → k) :=
  joinVarieties 2 ![V, {p}]

-- The secant variety is the join of N copies of V.
theorem secantVariety_eq_join (N : ℕ) (V : Set (Fin n → k)) :
    secantVariety N V = joinVarieties N (fun _ => V) := by
  simp [secantVariety, joinVarieties]

-- The join of one variety is the closure of that variety.
theorem joinVarieties_one (V : Set (Fin n → k)) :
    joinVarieties 1 (fun _ => V) = closure V := by
  simp only [joinVarieties]
  congr 1
  ext v
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨pts, hpts, t, ht, rfl⟩
    have ht0 : t 0 = 1 := by
      have := ht
      simp only [standardSimplex, Set.mem_setOf_eq] at this
      simpa using this
    have heq : affineCombination 1 pts t = pts 0 := by
      ext j; simp [affineCombination, ht0]
    rw [heq]; exact hpts 0
  · intro hv
    refine ⟨fun _ => v, fun _ => hv, fun _ => 1, ?_, ?_⟩
    · simp [standardSimplex]
    · ext j; simp [affineCombination]

-- V is contained in its first secant variety.
theorem subset_secantVariety_one (V : Set (Fin n → k)) :
    V ⊆ secantVariety 1 V := by
  intro v hv
  apply subset_closure
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  refine ⟨fun _ => v, fun _ => hv, fun _ => 1, ?_, ?_⟩
  · simp [standardSimplex]
  · ext j; simp [affineCombination]

-- V is contained in Sec_N(V) for any N ≥ 1.
theorem subset_secantVariety (N : ℕ) (hN : 0 < N) (V : Set (Fin n → k)) :
    V ⊆ secantVariety N V := by
  intro v hv
  apply subset_closure
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  refine ⟨fun _ => v, fun _ => hv,
          fun i => if i = ⟨0, hN⟩ then 1 else 0, ?_, ?_⟩
  · simp only [standardSimplex, Set.mem_setOf_eq]
    simp
  · ext j
    simp only [affineCombination]
    rw [show ∑ i : Fin N, (if i = ⟨0, hN⟩ then (1 : k) else 0) * v j =
          (∑ i : Fin N, if i = ⟨0, hN⟩ then (1 : k) else 0) * v j from
      (Finset.sum_mul ..).symm]
    simp

end SecantVarieties

end Elimination
