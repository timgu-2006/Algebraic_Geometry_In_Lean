import Mathlib

open Polynomial MvPolynomial Set Ideal Matrix Finset

/-!
# Resultants — Hassett Chapter 5

Formalises the theory of resultants over a field `k`:
- Common roots and coprimality (§5.1, Proposition 5.1)
- The Sylvester matrix and resultant (§5.1, Definition 5.4)
- Resultant vanishes iff common factor (Theorem 5.5)
- Discriminant as special resultant (§5.1.1)
- Resultant as a function of roots (§5.2, sorry'd)
- Resultants and elimination theory (§5.3, Theorem 5.13)

References: Hassett, *Introduction to Algebraic Geometry*, Chapter 5.
-/

namespace Resultants

-- The Sylvester matrix and resultant make sense over any commutative ring.
variable {R : Type*} [CommRing R]

-- ---------------------------------------------------------------------------
-- §5.1  The Sylvester matrix and resultant (Definition 5.4)
-- ---------------------------------------------------------------------------

/-- The Sylvester matrix of f (degree m) and g (degree n) is the
    (m+n)×(m+n) matrix whose determinant is Res(f,g).

    Rows 0..n-1 are the n shifts of f; rows n..m+n-1 are the m shifts of g. -/
noncomputable def sylvesterMatrix (m n : ℕ) (f g : Polynomial R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  fun i j =>
    if (i : ℕ) < n then
      if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + m then
        f.coeff ((i : ℕ) + m - (j : ℕ))
      else 0
    else
      if (i : ℕ) - n ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) then
        g.coeff ((i : ℕ) - (j : ℕ))
      else 0

/-- The resultant Res(f,g) is the determinant of the Sylvester matrix. -/
noncomputable def resultant (m n : ℕ) (f g : Polynomial R) : R :=
  (sylvesterMatrix m n f g).det

/-- The (0,0) entry of the Sylvester matrix (when n > 0) is the leading
    coefficient of f, i.e., f.coeff m. -/
theorem sylvesterMatrix_zero_zero (m n : ℕ) (hmn : 0 < m + n) (hn : 0 < n)
    (f g : Polynomial R) :
    sylvesterMatrix m n f g ⟨0, hmn⟩ ⟨0, hmn⟩ = f.coeff m := by
  simp [sylvesterMatrix, hn]

-- The g-block: entry (n, 0) is the leading coefficient of g.
theorem sylvesterMatrix_n_zero (m n : ℕ) (hmn : 0 < m + n) (hm : 0 < m)
    (f g : Polynomial R) :
    sylvesterMatrix m n f g ⟨n, by omega⟩ ⟨0, hmn⟩ = g.coeff n := by
  simp [sylvesterMatrix]

-- ---------------------------------------------------------------------------
-- §5.1  Common roots and coprimality
-- ---------------------------------------------------------------------------

-- Field-specific results use a field variable.
section FieldResults

universe u

variable {k : Type u} [Field k]

/-!
### Proposition 5.1

For nonconstant f, g ∈ k[x], the following are equivalent:
1. f and g have a common root over some extension of k;
2. f and g share a common nonconstant factor in k[x];
3. ¬ IsCoprime f g;
4. ⟨f, g⟩ ⊊ k[x].

Conditions 3–4 are equivalent because k[x] is a PID.
-/

/-- Conditions 3 and 4 of Proposition 5.1 are equivalent.

    In k[x], `IsCoprime f g` iff `span {f, g} = ⊤`. -/
theorem isCoprime_iff_span_eq_top (f g : Polynomial k) :
    IsCoprime f g ↔ (span {f, g} : Ideal (Polynomial k)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, h⟩

/-- Proposition 5.1: common root over an extension ↔ not coprime. -/
theorem common_root_iff_not_isCoprime (f g : Polynomial k)
    (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
    (∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
       ∃ α : L, aeval α (f.map (algebraMap k L)) = 0 ∧
                aeval α (g.map (algebraMap k L)) = 0) ↔
    ¬ IsCoprime f g := by
  simp_rw [Polynomial.aeval_map_algebraMap]
  constructor
  -- (→) A common root kills any Bézout combination, contradicting IsCoprime.
  · rintro ⟨L, _, _, α, hfα, hgα⟩ ⟨a, b, h⟩
    have : aeval α (a * f + b * g : Polynomial k) = 1 := by rw [h]; simp
    simp [map_add, map_mul, hfα, hgα] at this
  -- (←) If f, g are not coprime, their gcd d has an irreducible factor p.
  --     The field AdjoinRoot p (same universe u) contains a common root.
  · intro hcop
    classical
    set d := EuclideanDomain.gcd f g
    have hf_ne : f ≠ 0 := by intro h; simp [h] at hf
    have hd_ne : d ≠ 0 := by
      intro h; apply hf_ne
      have hd : d ∣ f := EuclideanDomain.gcd_dvd_left f g
      simp only [h, zero_dvd_iff] at hd; exact hd
    have hd_not_unit : ¬ IsUnit d :=
      fun hu => hcop (EuclideanDomain.gcd_isUnit_iff.mp hu)
    obtain ⟨p, hp_irred, hp_dvd_d⟩ :=
      WfDvdMonoid.exists_irreducible_factor hd_not_unit hd_ne
    have hp_dvd_f : p ∣ f := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_left f g)
    have hp_dvd_g : p ∣ g := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_right f g)
    haveI : Fact (Irreducible p) := ⟨hp_irred⟩
    -- AdjoinRoot p is a field (p irreducible over a field) in Type u.
    refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
    · obtain ⟨r, hr⟩ := hp_dvd_f
      have hroot : aeval (AdjoinRoot.root p) p = 0 := by
        rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
      rw [hr, map_mul, hroot, zero_mul]
    · obtain ⟨r, hr⟩ := hp_dvd_g
      have hroot : aeval (AdjoinRoot.root p) p = 0 := by
        rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
      rw [hr, map_mul, hroot, zero_mul]

-- ---------------------------------------------------------------------------
-- §5.1  Theorem 5.5 — Res(f,g) = 0 ↔ common factor
-- ---------------------------------------------------------------------------

/-- Theorem 5.5: f, g have a common factor iff Res(f,g) = 0.

    Proof: The Sylvester matrix δ₀(m+n-1) is invertible iff 1 ∈ image(δ₀) iff
    ⟨f,g⟩ = k[x] iff f and g are coprime (Lemma 5.6). -/
theorem resultant_eq_zero_iff_not_isCoprime (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f g : Polynomial k)
    (hfdeg : f.natDegree = m) (hgdeg : g.natDegree = n)
    (hflc : f.leadingCoeff ≠ 0) (hglc : g.leadingCoeff ≠ 0) :
    resultant m n f g = 0 ↔ ¬ IsCoprime f g := by
  sorry

/-- Lemma 5.6: Coprime f (deg m), g (deg n) have Bezout coefficients with
    degree bounds: deg A ≤ n-1 and deg B ≤ m-1. -/
theorem bezout_bounded_degrees (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f g : Polynomial k)
    (hfdeg : f.natDegree = m) (hgdeg : g.natDegree = n)
    (hcop : IsCoprime f g) :
    ∃ A B : Polynomial k,
      A.natDegree ≤ n - 1 ∧ B.natDegree ≤ m - 1 ∧ A * f + B * g = 1 := by
  obtain ⟨a₀, b₀, hab⟩ := hcop
  have hg_ne : g ≠ 0 := by intro h; simp [h] at hgdeg; omega
  have hf_ne : f ≠ 0 := by intro h; simp [h] at hfdeg; omega
  have hdiv : g * (a₀ / g) + a₀ % g = a₀ := EuclideanDomain.div_add_mod a₀ g
  -- A = a₀ % g, B = b₀ + (a₀ / g) * f
  have hBez : (a₀ % g) * f + (b₀ + (a₀ / g) * f) * g = 1 := by
    linear_combination f * hdiv + hab
  refine ⟨a₀ % g, b₀ + (a₀ / g) * f, ?_, ?_, hBez⟩
  · -- Degree bound on A = a₀ % g: since deg(A) < deg(g) = n, we get deg(A) ≤ n - 1
    by_cases hA : a₀ % g = 0
    · simp [hA]
    · have hd : (a₀ % g).degree < g.degree := EuclideanDomain.mod_lt a₀ hg_ne
      have : (a₀ % g).natDegree < g.natDegree := Polynomial.natDegree_lt_natDegree hA hd
      omega
  · -- Degree bound on B: if deg(B) ≥ m then deg(B*g) ≥ m+n, but A*f+B*g = 1 has degree 0
    set B := b₀ + (a₀ / g) * f with hB_def
    by_cases hB : B = 0
    · simp [hB]
    · by_contra hBd
      have hBdeg : m ≤ B.natDegree := by omega
      have hBg_deg : m + n ≤ (B * g).natDegree := by
        rw [Polynomial.natDegree_mul hB hg_ne, hgdeg]; omega
      by_cases hA : a₀ % g = 0
      · -- If A = 0, then B * g = 1, so natDegree (B * g) = 0, contradiction
        simp [hA] at hBez
        have : (B * g).natDegree = 0 := by rw [hBez]; exact Polynomial.natDegree_one
        omega
      · -- If A ≠ 0, bound natDegree(A*f) ≤ m+n-1 < natDegree(B*g), so the leading
        -- term of B*g cannot cancel, giving natDegree(A*f+B*g) = natDegree(B*g) ≥ m+n
        -- but A*f+B*g = 1 has natDegree 0, contradiction
        have hA_ndeg : (a₀ % g).natDegree ≤ n - 1 := by
          have hd : (a₀ % g).degree < g.degree := EuclideanDomain.mod_lt a₀ hg_ne
          have : (a₀ % g).natDegree < g.natDegree := Polynomial.natDegree_lt_natDegree hA hd
          omega
        have hAf_deg : (a₀ % g * f).natDegree ≤ m + n - 1 := by
          rw [Polynomial.natDegree_mul hA hf_ne, hfdeg]; omega
        have hstrict : (a₀ % g * f).natDegree < (B * g).natDegree := by omega
        have hsum_deg : (a₀ % g * f + B * g).natDegree = (B * g).natDegree :=
          Polynomial.natDegree_add_eq_right_of_natDegree_lt hstrict
        have hone : (a₀ % g * f + B * g).natDegree = 0 := by
          rw [hBez]; exact Polynomial.natDegree_one
        omega

-- ---------------------------------------------------------------------------
-- §5.1.1  Discriminant
-- ---------------------------------------------------------------------------

/-- The discriminant of a degree-m polynomial f:
    disc(f) = (-1)^(m(m-1)/2) · aₘ⁻¹ · Res(f, f').

    A polynomial has a repeated root iff its discriminant vanishes. -/
noncomputable def discriminant (m : ℕ) (f : Polynomial k) : k :=
  (-1 : k) ^ (m * (m - 1) / 2) * f.leadingCoeff⁻¹ * resultant m (m - 1) f f.derivative

/-- f has a multiple root iff disc(f) = 0. -/
theorem hasMultipleRoot_iff_discriminant_zero (m : ℕ) (hm : 1 < m) (f : Polynomial k)
    (hfdeg : f.natDegree = m) (hflc : f.leadingCoeff ≠ 0) :
    (∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (α : L),
       (f.map (algebraMap k L)).IsRoot α ∧
       (f.map (algebraMap k L)).derivative.IsRoot α) ↔
    discriminant m f = 0 := by
  sorry

-- ---------------------------------------------------------------------------
-- §5.1.2  Homogeneous resultant (Theorem 5.8)
-- ---------------------------------------------------------------------------

/-- Theorem 5.8: For nonconstant homogeneous F, G ∈ k[x₀,x₁], Res(F,G) = 0
    iff F and G have a common nonconstant homogeneous factor. -/
theorem homogeneous_resultant_eq_zero_iff (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (F G : MvPolynomial (Fin 2) k)
    (hFhom : IsHomogeneous F m) (hGhom : IsHomogeneous G n) :
    resultant m n (F.eval₂ (algebraMap k (Polynomial k)) (![Polynomial.X, 1]))
                  (G.eval₂ (algebraMap k (Polynomial k)) (![Polynomial.X, 1])) = 0 ↔
    ∃ H : MvPolynomial (Fin 2) k, H.totalDegree ≥ 1 ∧ H ∣ F ∧ H ∣ G := by
  sorry

-- ---------------------------------------------------------------------------
-- §5.2  The resultant as a function of the roots
-- ---------------------------------------------------------------------------

/-- Proposition 5.10 / Product formula.

    If f = aₘ ∏(x - αᵢ) and g = bₙ ∏(x - βⱼ) over an algebraically
    closed extension L, then Res(f,g) = aₘⁿ · bₙᵐ · ∏_{i,j} (αᵢ - βⱼ). -/
theorem resultant_eq_prod_diff (m n : ℕ)
    (f g : Polynomial k) (hfdeg : f.natDegree = m) (hgdeg : g.natDegree = n)
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L]
    (α : Fin m → L) (β : Fin n → L)
    (hf : f.map (algebraMap k L) =
          Polynomial.C ((algebraMap k L) f.leadingCoeff) *
          ∏ i, (Polynomial.X - Polynomial.C (α i)))
    (hg : g.map (algebraMap k L) =
          Polynomial.C ((algebraMap k L) g.leadingCoeff) *
          ∏ j, (Polynomial.X - Polynomial.C (β j))) :
    (algebraMap k L) (resultant m n f g) =
    (algebraMap k L) f.leadingCoeff ^ n *
    (algebraMap k L) g.leadingCoeff ^ m *
    ∏ i : Fin m, ∏ j : Fin n, (α i - β j) := by
  sorry

/-- Proposition 5.12: Res(f,g) is irreducible as a polynomial in the
    coefficients of f and g. -/
theorem resultant_irreducible (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let S := MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) k
    let f : Polynomial S := ∑ i : Fin (m+1),
      Polynomial.C (X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)
    let g : Polynomial S := ∑ j : Fin (n+1),
      Polynomial.C (X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)
    Irreducible (resultant m n f g) := by
  sorry

-- ---------------------------------------------------------------------------
-- §5.3  Resultants and elimination theory
-- ---------------------------------------------------------------------------

/-- The incidence variety of §5.3: pairs (x, coefficients) where
    f(x) = g(x) = 0. -/
noncomputable def commonRootVariety (m n : ℕ) :
    Set (k × (Fin (m+1) → k) × (Fin (n+1) → k)) :=
  {p | let x := p.1; let a := p.2.1; let b := p.2.2
       (∑ i : Fin (m+1), a i * x ^ (i : ℕ)) = 0 ∧
       (∑ j : Fin (n+1), b j * x ^ (j : ℕ)) = 0}

/-- Theorem 5.13: The elimination ideal of ⟨f,g⟩ is generated by Res(f,g).

    Let S = k[a₀,...,aₘ,b₀,...,bₙ] and f = aₘxᵐ+…+a₀, g = bₙxⁿ+…+b₀ in S[x].
    Then ⟨f,g⟩ ∩ S = ⟨Res(f,g)⟩.

    Proof sketch:
    - Res(f,g) ∈ ⟨f,g⟩ by Cramer's rule applied to the Sylvester matrix.
    - Any P ∈ ⟨f,g⟩ ∩ S vanishes when αᵢ = βⱼ, so the product formula
      shows Res(f,g) | P in the UFD S[α,β]. Since aₘ,bₙ do not divide
      Res(f,g), we conclude Res(f,g) | P in S. -/
theorem elimination_ideal_eq_resultant_span (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let S := MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) k
    let f : Polynomial S := ∑ i : Fin (m+1),
      Polynomial.C (X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)
    let g : Polynomial S := ∑ j : Fin (n+1),
      Polynomial.C (X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)
    (span {f, g} : Ideal (Polynomial S)).comap Polynomial.C =
    span {resultant m n f g} := by
  sorry

-- ---------------------------------------------------------------------------
-- §5.3  Cramer's rule lemma
-- ---------------------------------------------------------------------------

/-- Cramer's rule: for any square matrix M and vector v, det(M) • v ∈ image(M.mulVec).

    Proof: M · (adj(M) · v) = (M · adj(M)) · v = det(M) · Id · v = det(M) · v,
    using the classical adjoint identity M · adj(M) = det(M) · Id. -/
theorem det_smul_mem_range_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    M.det • v ∈ Set.range (M.mulVec) :=
  ⟨M.cramer v, M.mulVec_cramer v⟩

/-- Res(f,g) · 1 ∈ ⟨f,g⟩ ⊆ S[x] (the easy direction of Theorem 5.13). -/
theorem resultant_C_mem_span (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let S := MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) k
    let f : Polynomial S := ∑ i : Fin (m+1),
      Polynomial.C (X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)
    let g : Polynomial S := ∑ j : Fin (n+1),
      Polynomial.C (X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)
    Polynomial.C (resultant m n f g) ∈ (span {f, g} : Ideal (Polynomial S)) := by
  sorry

end FieldResults

end Resultants
