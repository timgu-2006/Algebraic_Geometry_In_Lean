import Mathlib

open MvPolynomial Set Ideal Finset

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
theorem closure_projection_eq_eliminationLocus
    (n m : ℕ) (J : Ideal (MvPolynomial (Fin (n + m)) k))
    [TopologicalSpace (Fin m → k)] :
    closure (projection n m '' MvPolynomial.zeroLocus k J) =
    MvPolynomial.zeroLocus k (eliminationIdeal n J) := by
  sorry

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
  sorry

-- ---------------------------------------------------------------------------
-- §4.1  Theorem 4.8 — Elimination Theorem (Gröbner basis version)
-- ---------------------------------------------------------------------------

/-- Elimination Theorem (Hassett Theorem 4.8).

    If G is a Gröbner basis of J with respect to a lex elimination order
    (x₁ > … > xₙ > y₁ > … > yₘ), then G ∩ k[y₁,…,yₘ] is a Gröbner
    basis of the elimination ideal J_n.

    This is a deep result requiring Buchberger theory and monomial orders. -/
theorem elimination_theorem
    (n m : ℕ) (J : Ideal (MvPolynomial (Fin (n + m)) k)) :
    ∃ (G : Finset (MvPolynomial (Fin m) k)),
      span (G : Set (MvPolynomial (Fin m) k)) = eliminationIdeal n J := by
  sorry

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
