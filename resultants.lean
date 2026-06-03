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

-- Helper: coefficient of ∑_{k : Fin mn} C(v k) * X^{mn-1-k} at position e
-- equals v[mn-1-e] when e < mn, else 0.
private lemma descPolyCoeff {R : Type*} [CommRing R] (mn : ℕ) (v : Fin mn → R) (e : ℕ) :
    (∑ k : Fin mn, Polynomial.C (v k) * Polynomial.X ^ (mn - 1 - (k : ℕ))).coeff e =
    if h : e < mn then v ⟨mn - 1 - e, by omega⟩ else 0 := by
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  -- Sum = ∑_k (if e = mn-1-k then v k else 0)
  -- Rewrite the condition: e = mn-1-k iff k = ⟨mn-1-e, _⟩ (when e < mn).
  split_ifs with he
  · -- e < mn: exactly one k (namely ⟨mn-1-e, _⟩) satisfies e = mn-1-k.
    -- Rewrite condition e = mn-1-k as ⟨mn-1-e,_⟩ = k, then use sum_ite_eq'.
    have heq : ∀ k : Fin mn,
        (e = mn - 1 - (k : ℕ)) ↔ ((⟨mn - 1 - e, by omega⟩ : Fin mn) = k) :=
      fun k => ⟨fun h => Fin.ext (by simp only [Fin.val_mk]; omega),
               fun h => by have := congr_arg Fin.val h; simp only [Fin.val_mk] at this; omega⟩
    simp_rw [heq]
    -- Now: ∑ k, (if ⟨mn-1-e,_⟩ = k then v k else 0) = v ⟨mn-1-e,_⟩
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  · -- e ≥ mn: no k in Fin mn satisfies mn-1-k = e
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    omega

-- Key row identity for f-rows of the Sylvester matrix (descending polynomial = X^{n-1-j} * f).
-- Requires that f.coeff d = 0 for d > m (i.e., natDegree f ≤ m).
private lemma sylvester_f_row_desc {R : Type*} [CommRing R] (m n : ℕ) (hn : 0 < n)
    (f g : Polynomial R) (hf : ∀ d, m < d → f.coeff d = 0)
    (j : Fin (m + n)) (hj : (j : ℕ) < n) :
    ∑ k : Fin (m + n), Polynomial.C (sylvesterMatrix m n f g j k) *
      Polynomial.X ^ (m + n - 1 - (k : ℕ)) =
    Polynomial.X ^ (n - 1 - (j : ℕ)) * f := by
  apply Polynomial.ext; intro e
  rw [descPolyCoeff]
  split_ifs with he
  · -- Compute: sylvesterMatrix j ⟨m+n-1-e, _⟩
    simp only [sylvesterMatrix, hj, ↓reduceIte]
    -- Check Sylvester condition: j ≤ m+n-1-e ≤ j+m?
    rw [Polynomial.coeff_X_pow_mul']
    by_cases h1 : n - 1 - (j : ℕ) ≤ e
    · -- n-1-j ≤ e: upper Sylvester condition (m+n-1-e ≤ j+m) holds
      rw [if_pos h1]
      by_cases h2 : (j : ℕ) ≤ m + n - 1 - e
      · -- Lower condition holds too: full match
        have hcond : (j : ℕ) ≤ m + n - 1 - e ∧ m + n - 1 - e ≤ (j : ℕ) + m := ⟨h2, by omega⟩
        rw [if_pos hcond]
        -- Goal: f.coeff(j+m-(m+n-1-e)) = f.coeff(e-(n-1-j))
        -- Both sides equal j + e - (n-1) in ℤ. Use zify.
        have heq : (j : ℕ) + m - (m + n - 1 - e) = e - (n - 1 - (j : ℕ)) := by
          have hjn : (j : ℕ) < n := hj
          have h2' : m + n - 1 - e ≤ m + (j : ℕ) := by omega
          zify [h2, h2', h1, hjn.le]
          omega
        rw [heq]
      · -- Lower condition fails: j > m+n-1-e, so Sylvester = 0
        push Not at h2
        have hnotcond : ¬ ((j : ℕ) ≤ m + n - 1 - e ∧ m + n - 1 - e ≤ (j : ℕ) + m) := by
          push Not; intro h; omega
        rw [if_neg hnotcond]
        -- f.coeff(e-(n-1-j)) = 0 since j > m+n-1-e implies e+j ≥ m+n implies e-(n-1-j) > m
        refine (hf _ ?_).symm
        have hjn : (j : ℕ) < n := hj
        have h1' : n - 1 - (j : ℕ) ≤ e := h1
        have hn1j : n - 1 - (j : ℕ) + (j : ℕ) = n - 1 := by omega
        -- h2 : m+n-1-e < j (after push Not)
        -- hsum : m+n ≤ j+e (from h2 : m+n-1-e < j and he : e < m+n)
        have hsum : m + n ≤ (j : ℕ) + e := by
          have he' : e ≤ m + n - 1 := by omega
          zify [he'] at h2 ⊢; omega
        omega
    · -- n-1-j > e: Sylvester condition fails (upper: m+n-1-e > j+m), RHS = 0
      push Not at h1  -- h1 : e < n-1-j
      rw [if_neg (by omega : ¬(n - 1 - (j : ℕ) ≤ e))]
      have hnotcond : ¬ ((j : ℕ) ≤ m + n - 1 - e ∧ m + n - 1 - e ≤ (j : ℕ) + m) := by
        have hjn : (j : ℕ) < n := hj
        rintro ⟨_, h⟩; zify [hjn.le] at *; omega
      rw [if_neg hnotcond]
  · -- e ≥ m+n: both sides are 0 (both LHS and RHS).
    -- LHS: descPolyCoeff gives 0 (since ¬(e < m+n)).
    -- RHS: (X^{n-1-j} * f).coeff e: n-1-j ≤ e (since n-1-j < n ≤ m+n ≤ e).
    --      So coeff = f.coeff(e-(n-1-j)) = 0 since e-(n-1-j) ≥ m+1 > m.
    rw [Polynomial.coeff_X_pow_mul']
    -- n-1-j ≤ n-1 < n ≤ m+n ≤ e, so condition n-1-j ≤ e holds.
    have h1 : n - 1 - (j : ℕ) ≤ e := by omega
    rw [if_pos h1]
    -- f.coeff(e-(n-1-j)) = 0 since e-(n-1-j) ≥ m+n-n+1 = m+1 > m
    symm; apply hf; zify [h1, hj.le] at *; omega

-- Key row identity for g-rows of the Sylvester matrix.
-- Requires that g.coeff d = 0 for d > n.
private lemma sylvester_g_row_desc {R : Type*} [CommRing R] (m n : ℕ) (hm : 0 < m)
    (f g : Polynomial R) (hg : ∀ d, n < d → g.coeff d = 0)
    (s : Fin m) :
    ∑ k : Fin (m + n), Polynomial.C (sylvesterMatrix m n f g ⟨n + (s : ℕ), by omega⟩ k) *
      Polynomial.X ^ (m + n - 1 - (k : ℕ)) =
    Polynomial.X ^ (m - 1 - (s : ℕ)) * g := by
  apply Polynomial.ext; intro e
  rw [descPolyCoeff]
  split_ifs with he
  · simp only [sylvesterMatrix]
    -- Evaluate the row selector: n+s ≥ n, so we take the g-row branch.
    have hge : ¬ (n + (s : ℕ) < n) := by omega
    rw [if_neg hge]
    -- Simplify n+s-n = s in the column condition.
    rw [show n + (s : ℕ) - n = (s : ℕ) from Nat.add_sub_cancel_left n s]
    -- Now goal: (if (s:ℕ) ≤ m+n-1-e ∧ m+n-1-e ≤ n+(s:ℕ) then g.coeff(n+(s:ℕ)-(m+n-1-e)) else 0)
    --         = (X^{m-1-s} * g).coeff e
    rw [Polynomial.coeff_X_pow_mul']
    by_cases h1 : m - 1 - (s : ℕ) ≤ e
    · rw [if_pos h1]
      -- When m-1-s ≤ e, the upper condition always holds: m+n-1-e ≤ n+s.
      have hs_le : (s : ℕ) ≤ m - 1 := by omega
      have h_hi : m + n - 1 - e ≤ n + (s : ℕ) := by zify [h1, hs_le]; omega
      -- Case split on lower condition: s ≤ m+n-1-e?
      by_cases h_lo : (s : ℕ) ≤ m + n - 1 - e
      · -- Both conditions hold: Sylvester = g.coeff(n+s-(m+n-1-e)) = g.coeff(e-(m-1-s))
        rw [if_pos (show (s : ℕ) ≤ m + n - 1 - e ∧ m + n - 1 - e ≤ n + (s : ℕ) from ⟨h_lo, h_hi⟩)]
        have heq : n + (s : ℕ) - (m + n - 1 - e) = e - (m - 1 - (s : ℕ)) := by
          zify [h_lo, h1, hs_le]; omega
        rw [heq]
      · -- Lower fails (s > m+n-1-e): Sylvester = 0 and g.coeff(e-(m-1-s)) = 0
        rw [if_neg (show ¬((s : ℕ) ≤ m + n - 1 - e ∧ m + n - 1 - e ≤ n + (s : ℕ)) from by
          rintro ⟨h, _⟩; exact h_lo h)]
        -- e-(m-1-s) > n: s > m+n-1-e means s+e > m+n-1 means e-m+1+s > n
        symm
        apply hg
        push Not at h_lo
        zify [h1, hs_le] at *; omega
    · -- h1 : ¬(m - 1 - ↑s ≤ e), i.e. e < m - 1 - ↑s
      push Not at h1  -- h1 : e < m - 1 - ↑s
      rw [if_neg (by omega : ¬(m - 1 - (s : ℕ) ≤ e))]
      -- Upper condition fails: m+n-1-e > n+s (since m-1 > s+e)
      have hs_le : (s : ℕ) ≤ m - 1 := by omega
      rw [if_neg (show ¬((s : ℕ) ≤ m + n - 1 - e ∧ m + n - 1 - e ≤ n + (s : ℕ)) from by
        rintro ⟨_, h⟩; zify [hs_le] at *; omega)]
  · rw [Polynomial.coeff_X_pow_mul']
    -- e ≥ m+n: m-1-s ≤ m-1 < m ≤ m+n ≤ e, so m-1-s ≤ e holds.
    have hs_lt : (s : ℕ) < m := s.isLt
    have hs_le : (s : ℕ) ≤ m - 1 := by omega
    have h1 : m - 1 - (s : ℕ) ≤ e := by omega
    rw [if_pos h1]
    symm; apply hg
    zify [h1, hs_le] at *; omega

/-- Res(f,g) · 1 ∈ ⟨f,g⟩ ⊆ S[x] (the easy direction of Theorem 5.13). -/
theorem resultant_C_mem_span (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let S := MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) k
    let f : Polynomial S := ∑ i : Fin (m+1),
      Polynomial.C (X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)
    let g : Polynomial S := ∑ j : Fin (n+1),
      Polynomial.C (X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)
    Polynomial.C (resultant m n f g) ∈ (span {f, g} : Ideal (Polynomial S)) := by
  -- Strategy: exhibit Bezout multipliers A and B from the last row of adj(M).
  -- A * f + B * g = C(Res) follows from:
  --   ∑_j adj[last,j] * (row_desc j) = C(Res)
  -- where row_desc j = ∑_k C(M[j,k]) * X^{m+n-1-k} = X^{n-1-j}*f or X^{m-1-(j-n)}*g.
  intro S f g
  letI : CommRing S := inferInstance
  letI : Semiring S := inferInstance
  rw [Ideal.mem_span_pair]
  set M := sylvesterMatrix m n f g with hM_def
  have hmn : 0 < m + n := by omega
  let last : Fin (m + n) := ⟨m + n - 1, by omega⟩
  -- Multipliers from the last row of adj(M):
  --   A = ∑_{j<n}   C(adj[last,j]) * X^{n-1-j}
  --   B = ∑_{j=n}^{m+n-1} C(adj[last,j]) * X^{m-1-(j-n)}
  refine ⟨
    ∑ j : Fin (m + n), if (j : ℕ) < n then
      Polynomial.C (M.adjugate last j) * Polynomial.X ^ (n - 1 - (j : ℕ))
    else 0,
    ∑ j : Fin (m + n), if n ≤ (j : ℕ) then
      Polynomial.C (M.adjugate last j) * Polynomial.X ^ (m - 1 - ((j : ℕ) - n))
    else 0,
    ?_⟩
  -- Prove A * f + B * g = C(Res).
  -- Step 1: Replace X^{n-1-j}*f and X^{m-1-s}*g using the row identities (helper lemmas).
  -- This gives A*f = ∑_j<n C(adj[last,j]) * ∑_k C(M[j,k]) * X^{m+n-1-k}
  --            B*g = ∑_j≥n C(adj[last,j]) * ∑_k C(M[j,k]) * X^{m+n-1-k}
  -- Step 2: Combine and swap sums:
  --   A*f + B*g = ∑_j C(adj[last,j]) * ∑_k C(M[j,k])*X^{m+n-1-k}
  --             = ∑_k (∑_j adj[last,j] * M[j,k]) * X^{m+n-1-k}    (C-linear)
  --             = ∑_k (adj*M)[last,k] * X^{m+n-1-k}                (matrix mult)
  --             = ∑_k Res * δ(last=k) * X^{m+n-1-k}                (adjugate_mul)
  --             = Res * X^0 = C(Res).
  --
  -- Prove degree bounds: f.coeff d = 0 for d > m, and g.coeff d = 0 for d > n.
  -- These follow from the explicit form of f and g.
  have hf_deg : ∀ d, m < d → f.coeff d = 0 := by
    intro d hd
    simp only [f, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    apply Finset.sum_eq_zero
    intro i _
    simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro heq
    have := i.isLt; omega
  have hg_deg : ∀ d, n < d → g.coeff d = 0 := by
    intro d hd
    simp only [g, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    apply Finset.sum_eq_zero
    intro i _
    simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro heq
    have := i.isLt; omega
  -- Row identity helpers.
  have row_f : ∀ j : Fin (m + n), (j : ℕ) < n →
      Polynomial.X ^ (n - 1 - (j : ℕ)) * f =
      ∑ k : Fin (m + n), Polynomial.C (M j k) * Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
    intro j hj
    rw [hM_def]
    exact (sylvester_f_row_desc (R := S) m n hn f g hf_deg j hj).symm
  have row_g : ∀ s : Fin m,
      Polynomial.X ^ (m - 1 - (s : ℕ)) * g =
      ∑ k : Fin (m + n), Polynomial.C (M ⟨n + (s : ℕ), by omega⟩ k) *
        Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
    intro s
    rw [hM_def]
    exact (sylvester_g_row_desc (R := S) m n hm f g hg_deg s).symm
  -- Now compute A * f + B * g.
  -- First, rewrite A * f using row_f.
  have hAf : (∑ j : Fin (m + n), if (j : ℕ) < n then
        Polynomial.C (M.adjugate last j) * Polynomial.X ^ (n - 1 - (j : ℕ))
      else 0) * f =
      ∑ j : Fin (m + n), if (j : ℕ) < n then
        Polynomial.C (M.adjugate last j) *
          ∑ k : Fin (m + n), Polynomial.C (M j k) * Polynomial.X ^ (m + n - 1 - (k : ℕ))
      else 0 := by
    rw [Finset.sum_mul]
    congr 1; ext j
    split_ifs with hj
    · rw [mul_assoc, row_f j hj]
    · simp
  -- Second, rewrite B * g using row_g.
  have hBg : (∑ j : Fin (m + n), if n ≤ (j : ℕ) then
        Polynomial.C (M.adjugate last j) * Polynomial.X ^ (m - 1 - ((j : ℕ) - n))
      else 0) * g =
      ∑ j : Fin (m + n), if n ≤ (j : ℕ) then
        Polynomial.C (M.adjugate last j) *
          ∑ k : Fin (m + n), Polynomial.C (M j k) * Polynomial.X ^ (m + n - 1 - (k : ℕ))
      else 0 := by
    rw [Finset.sum_mul]
    congr 1; ext j
    split_ifs with hj
    · -- j ≥ n, let s = j - n : Fin m
      have hs_lt : (j : ℕ) - n < m := by omega
      let s : Fin m := ⟨(j : ℕ) - n, hs_lt⟩
      have hj_eq : j = ⟨n + (s : ℕ), by omega⟩ := by ext; simp [s]; omega
      rw [mul_assoc]
      -- X^{m-1-(j-n)} * g = X^{m-1-s} * g = row_g s (with M j = M ⟨n+s,_⟩ from hj_eq)
      have hexpeq : m - 1 - ((j : ℕ) - n) = m - 1 - (s : ℕ) := rfl
      have hrow : Polynomial.X ^ (m - 1 - (s : ℕ)) * g =
          ∑ k : Fin (m + n), Polynomial.C (M j k) * Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
        rw [row_g s]; congr 1; ext k; simp only [hj_eq]
      rw [hexpeq, hrow]
    · simp
  rw [hAf, hBg]
  -- Now combine: (∑_j if j<n then ... else 0) + (∑_j if n≤j then ... else 0)
  --           = ∑_j C(adj[last,j]) * ∑_k C(M[j,k]) * X^{m+n-1-k}
  have hcombine : (∑ j : Fin (m + n), if (j : ℕ) < n then
            Polynomial.C (M.adjugate last j) *
              ∑ k : Fin (m + n), Polynomial.C (M j k) * Polynomial.X ^ (m + n - 1 - (k : ℕ))
          else 0) +
        (∑ j : Fin (m + n), if n ≤ (j : ℕ) then
            Polynomial.C (M.adjugate last j) *
              ∑ k : Fin (m + n), Polynomial.C (M j k) * Polynomial.X ^ (m + n - 1 - (k : ℕ))
          else 0) =
      ∑ j : Fin (m + n), Polynomial.C (M.adjugate last j) *
        ∑ k : Fin (m + n), Polynomial.C (M j k) * Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
    rw [← Finset.sum_add_distrib]
    congr 1; ext j
    by_cases hj : (j : ℕ) < n
    · simp [hj, show ¬ n ≤ (j : ℕ) from by omega]
    · push Not at hj
      simp [show ¬ (j : ℕ) < n from by omega, hj]
  rw [hcombine]
  -- Swap the two sums:
  --   ∑_j C(adj[last,j]) * ∑_k C(M[j,k]) * X^{m+n-1-k}
  -- = ∑_k (∑_j adj[last,j] * M[j,k]) * X^{m+n-1-k}
  -- = ∑_k C((adj*M)[last,k]) * X^{m+n-1-k}
  -- = ∑_k C(Res * δ(last=k)) * X^{m+n-1-k}
  -- = C(Res) * X^{m+n-1-(m+n-1)} = C(Res) * 1 = C(Res)
  simp_rw [Finset.mul_sum, ← mul_assoc, ← Polynomial.C_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply]
  -- Now: ∑_k C((adj*M)[last, k]) * X^{m+n-1-k}
  rw [Matrix.adjugate_mul]
  -- (Res • 1)[last, k] = Res * δ(last = k)
  simp_rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  -- ∑_k C(if last = k then Res else 0) * X^{m+n-1-k}
  -- Simplify C(if ... then x else 0) = if ... then C(x) else 0
  simp_rw [apply_ite Polynomial.C, map_zero]
  -- Pull the if out of the product: (if last=k then C(Res) else 0) * X^... = if last=k then ... else 0
  simp_rw [ite_mul, zero_mul]
  -- Now: ∑_k (if last = k then C(Res)*X^{m+n-1-k} else 0) = C(Res)*X^{m+n-1-last}
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte, last, Fin.val_mk]
  -- X^{m+n-1-(m+n-1)} = X^0 = 1
  simp only [Nat.sub_self, pow_zero, mul_one]
  -- C(M.det) = C(resultant m n f g)
  simp only [resultant, ← hM_def]

end FieldResults

end Resultants
