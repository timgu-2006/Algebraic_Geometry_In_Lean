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

-- Key polynomial identity: for any v : Fin(m+n) → R,
-- let A = ∑_{j:Fin n} C(v[j]) * X^{n-1-j}  and  B = ∑_{j:Fin m} C(v[n+j]) * X^{m-1-j}.
-- Then A * f + B * g = ∑_k C((v ᵥ* sylvesterMatrix m n f g)[k]) * X^{m+n-1-k}.
-- (This uses the row identities above and a sum-swap.)
private lemma sylvester_vecMul_poly_eq {R : Type*} [CommRing R]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f g : Polynomial R)
    (hf : ∀ d, m < d → f.coeff d = 0) (hg : ∀ d, n < d → g.coeff d = 0)
    (v : Fin (m + n) → R) :
    let A : Polynomial R := ∑ j : Fin n,
        Polynomial.C (v ⟨j, by omega⟩) * Polynomial.X ^ (n - 1 - (j : ℕ))
    let B : Polynomial R := ∑ j : Fin m,
        Polynomial.C (v ⟨n + (j : ℕ), by omega⟩) * Polynomial.X ^ (m - 1 - (j : ℕ))
    A * f + B * g =
    ∑ k : Fin (m + n), Polynomial.C ((v ᵥ* sylvesterMatrix m n f g) k) *
      Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
  intro A B
  set M := sylvesterMatrix m n f g
  -- Row identities: ∑_k C(M[j,k]) * X^{m+n-1-k} = X^{n-1-j} * f  (for j<n)
  --                 ∑_k C(M[n+s,k]) * X^{m+n-1-k} = X^{m-1-s} * g  (for s<m)
  have row_f : ∀ j : Fin n,
      Polynomial.X ^ (n - 1 - (j : ℕ)) * f =
      ∑ k : Fin (m + n), Polynomial.C (M ⟨j, by omega⟩ k) *
        Polynomial.X ^ (m + n - 1 - (k : ℕ)) :=
    fun j => (sylvester_f_row_desc (R := R) m n hn f g hf ⟨j, by omega⟩ j.isLt).symm
  have row_g : ∀ s : Fin m,
      Polynomial.X ^ (m - 1 - (s : ℕ)) * g =
      ∑ k : Fin (m + n), Polynomial.C (M ⟨n + (s : ℕ), by omega⟩ k) *
        Polynomial.X ^ (m + n - 1 - (k : ℕ)) :=
    fun s => (sylvester_g_row_desc (R := R) m n hm f g hg s).symm
  -- Expand A * f: each term C(v[j]) * X^{n-1-j} * f → ∑_k C(v[j]) * C(M[j,k]) * X^{m+n-1-k}
  have hAf : A * f = ∑ j : Fin n, ∑ k : Fin (m + n),
      Polynomial.C (v ⟨j, by omega⟩) * Polynomial.C (M ⟨j, by omega⟩ k) *
        Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
    simp only [A, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [mul_assoc, row_f j, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    ring
  -- Expand B * g similarly
  have hBg : B * g = ∑ j : Fin m, ∑ k : Fin (m + n),
      Polynomial.C (v ⟨n + (j : ℕ), by omega⟩) * Polynomial.C (M ⟨n + (j : ℕ), by omega⟩ k) *
        Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
    simp only [B, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [mul_assoc, row_g j, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    -- Need: C(v[n+j]) * (C(M[n+j,k]) * X^{m+n-1-k}) = C(v[n+j]) * C(M[n+j,k]) * X^{m+n-1-k}
    ring
  rw [hAf, hBg]
  -- Goal: ∑_{j:Fin n} ∑_k C(v[j])*C(M[j,k])*X^{m+n-1-k}
  --     + ∑_{j:Fin m} ∑_k C(v[n+j])*C(M[n+j,k])*X^{m+n-1-k}
  --     = ∑_k C((v ᵥ* M)[k]) * X^{m+n-1-k}
  -- Combine C(a)*C(b) = C(a*b)
  simp_rw [← Polynomial.C_mul]
  -- The goal is now:
  -- ∑_{j:Fin n} ∑_k C(v[j]*M[j,k]) * X^{...} + ∑_{j:Fin m} ∑_k C(v[n+j]*M[n+j,k]) * X^{...}
  -- = ∑_k C((v ᵥ* M)[k]) * X^{...}
  apply Polynomial.ext; intro e
  simp only [Polynomial.coeff_add, Polynomial.finset_sum_coeff,
             Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  -- At coefficient e, we have:
  -- ∑_j ∑_k v[j]*M[j,k] * (if e = m+n-1-k then 1 else 0)
  -- + ∑_j ∑_k v[n+j]*M[n+j,k] * (if e = m+n-1-k then 1 else 0)
  -- = ∑_k (v ᵥ* M)[k] * (if e = m+n-1-k then 1 else 0)
  -- Swap inner and outer sums
  rw [Finset.sum_comm (γ := Fin n), Finset.sum_comm (γ := Fin m)]
  rw [← Finset.sum_add_distrib]
  congr 1; ext k
  -- Goal: ∑_{j:Fin n} v[j]*M[j,k] * c + ∑_{j:Fin m} v[n+j]*M[n+j,k] * c = (v ᵥ* M)[k] * c
  -- where c = if e = m+n-1-k then 1 else 0
  -- Factor out c using Finset.sum_mul
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
  congr 1
  -- ∑_{j:Fin n} v[j]*M[j,k] + ∑_{j:Fin m} v[n+j]*M[n+j,k] = ∑_{x:Fin(m+n)} v[x]*M[x,k]
  simp only [Matrix.vecMul, dotProduct]
  -- Partition Fin (m+n) into {x | x < n} and {x | n ≤ x}, biject each part to Fin n / Fin m.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Fin (m + n) => (x : ℕ) < n) (fun x => v x * M x k)]
  congr 1
  · symm
    -- After symm: ∑ x ∈ filter(x<n) univ, v x * M x k  =  ∑ j : Fin n, v ⟨j,_⟩ * M ⟨j,_⟩ k
    -- i : Fin(m+n) → Fin n,  j : Fin n → Fin(m+n)
    exact Finset.sum_nbij'
      (fun x : Fin (m + n) => (if h : (x : ℕ) < n then (⟨x.val, h⟩ : Fin n) else ⟨0, hn⟩))
      (fun j : Fin n => (⟨↑j, by omega⟩ : Fin (m + n)))
      (fun _ _ => Finset.mem_univ _)
      (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩)
      (fun x hx => by simp [dif_pos (Finset.mem_filter.mp hx).2])
      (fun j _ => by simp [dif_pos j.isLt])
      (fun x hx => by simp [dif_pos (Finset.mem_filter.mp hx).2])
  · symm
    -- After symm: ∑ x ∈ filter(x≥n) univ, v x * M x k  =  ∑ j : Fin m, v ⟨n+j,_⟩ * M ⟨n+j,_⟩ k
    exact Finset.sum_nbij'
      (fun x : Fin (m + n) => (if h : n ≤ (x : ℕ) then (⟨x.val - n, by omega⟩ : Fin m) else ⟨0, hm⟩))
      (fun j : Fin m => (⟨n + ↑j, by omega⟩ : Fin (m + n)))
      (fun _ _ => Finset.mem_univ _)
      (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [not_lt]⟩)
      (fun x hx => by
        have h : n ≤ (x : ℕ) := by simpa [not_lt] using (Finset.mem_filter.mp hx).2
        apply Fin.ext; simp only [dif_pos h]
        show n + ((x : ℕ) - n) = (x : ℕ); omega)
      (fun j _ => by
        apply Fin.ext; simp only [dif_pos (by omega : n ≤ n + (j : ℕ))]
        show n + (j : ℕ) - n = (j : ℕ); omega)
      (fun x hx => by
        have h : n ≤ (x : ℕ) := by simpa [not_lt] using (Finset.mem_filter.mp hx).2
        have heq : (⟨n + ((x : ℕ) - n), by omega⟩ : Fin (m + n)) = x := by
          apply Fin.ext; show n + ((x : ℕ) - n) = (x : ℕ); omega
        simp only [dif_pos h, heq])

theorem resultant_eq_zero_iff_not_isCoprime (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f g : Polynomial k)
    (hfdeg : f.natDegree = m) (hgdeg : g.natDegree = n)
    (hflc : f.leadingCoeff ≠ 0) (hglc : g.leadingCoeff ≠ 0) :
    resultant m n f g = 0 ↔ ¬ IsCoprime f g := by
  have hf_ne : f ≠ 0 := by intro h; simp [h] at hflc
  have hg_ne : g ≠ 0 := by intro h; simp [h] at hglc
  set M := sylvesterMatrix m n f g with hM_def
  have hf_deg : ∀ d, m < d → f.coeff d = 0 := fun d hd =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hg_deg : ∀ d, n < d → g.coeff d = 0 := fun d hd =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  -- The key correspondence: v ᵥ* M = 0 ↔ A*f + B*g = 0
  -- where A = ∑_{j<n} C(v[j]) * X^{n-1-j}, B = ∑_{j<m} C(v[n+j]) * X^{m-1-j}.
  -- Use exists_vecMul_eq_zero_iff: det M = 0 ↔ ∃ v ≠ 0, v ᵥ* M = 0.
  rw [resultant, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · -- (→): ∃ v ≠ 0, v ᵥ* M = 0  →  ¬ IsCoprime f g
    rintro ⟨v, hv_ne, hv_mul⟩ hcop
    -- Define A and B from v.
    set A_v : Polynomial k := ∑ j : Fin n,
        Polynomial.C (v ⟨j, by omega⟩) * Polynomial.X ^ (n - 1 - (j : ℕ))
    set B_v : Polynomial k := ∑ j : Fin m,
        Polynomial.C (v ⟨n + (j : ℕ), by omega⟩) * Polynomial.X ^ (m - 1 - (j : ℕ))
    -- A_v * f + B_v * g = 0 because v ᵥ* M = 0.
    have hAfBg : A_v * f + B_v * g = 0 := by
      -- Apply the polynomial identity lemma; the let-bindings in heq are def-eq to A_v, B_v
      have hraw := sylvester_vecMul_poly_eq (R := k) m n hm hn f g hf_deg hg_deg v
      -- hraw : (let A := ...; let B := ...; A * f + B * g) = ∑_k C((v ᵥ* M)[k]) * X^{...}
      -- Evaluate the lets (definitionally equal to A_v, B_v)
      simp only [] at hraw
      -- Now hraw : A_v * f + B_v * g = ∑_k C((v ᵥ* M)[k]) * X^{...}
      -- (This works because A_v = ∑ j : Fin n, ... and B_v = ∑ j : Fin m, ... by definition)
      -- v ᵥ* M = 0 (M = sylvesterMatrix m n f g)
      have hvm : v ᵥ* sylvesterMatrix m n f g = 0 := hM_def ▸ hv_mul
      simp only [hvm, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at hraw
      exact hraw
    -- v ≠ 0 implies A_v ≠ 0 or B_v ≠ 0.
    -- If A_v = 0: A_v.coeff(n-1-j) = v[j] = 0 for all j<n (from descPolyCoeff).
    -- If B_v = 0: B_v.coeff(m-1-j) = v[n+j] = 0 for all j<m.
    -- Both = 0 ↔ v = 0. Contradiction.
    have hAB_ne : A_v ≠ 0 ∨ B_v ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨hA0, hB0⟩ := h
      apply hv_ne
      ext ⟨i, hi⟩
      simp only [Pi.zero_apply]
      by_cases h_i : i < n
      · -- v[i] = A_v.coeff(n-1-i) = 0
        have hcoeff : A_v.coeff (n - 1 - i) = 0 := by rw [hA0]; simp
        -- A_v = ∑_j C(v[j]) * X^{n-1-j}, so coeff(n-1-i) = v[i] by descPolyCoeff
        simp only [A_v, descPolyCoeff, dif_pos (show n - 1 - i < n from by omega),
            show n - 1 - (n - 1 - i) = i from by omega] at hcoeff
        exact hcoeff
      · -- i = n + j for some j < m
        have h_ge : n ≤ i := Nat.le_of_not_lt h_i
        have hj_lt : i - n < m := by omega
        have hcoeff : B_v.coeff (m - 1 - (i - n)) = 0 := by rw [hB0]; simp
        simp only [B_v, descPolyCoeff, dif_pos (show m - 1 - (i - n) < m from by omega),
            show m - 1 - (m - 1 - (i - n)) = i - n from by omega,
            show n + (i - n) = i from by omega] at hcoeff
        exact hcoeff
    -- From hcop and A_v*f + B_v*g = 0, derive contradiction via degree bounds.
    -- A_v*f + B_v*g = 0 means A_v*f = -B_v*g.
    -- So f | B_v*g. By IsCoprime f g: f | B_v.
    -- But B_v.natDegree ≤ m-1 < m = f.natDegree (if B_v ≠ 0). Contradiction.
    -- If B_v = 0: then A_v*f = 0, so A_v = 0 (k[X] domain), contradicting hAB_ne.
    have hBv_ne : B_v ≠ 0 := by
      rcases hAB_ne with hA | hB
      · -- B_v = 0 → A_v*f = 0 → A_v = 0 (contradiction)
        intro hB0
        rw [hB0, zero_mul, add_zero] at hAfBg
        -- A_v * f = 0 and f ≠ 0 in a domain → A_v = 0
        exact hA (mul_eq_zero.mp hAfBg |>.resolve_right hf_ne)
      · exact hB
    -- B_v.natDegree ≤ m - 1
    have hBv_deg : B_v.natDegree ≤ m - 1 := by
      simp only [B_v]
      apply (Polynomial.natDegree_sum_le _ _).trans
      apply Finset.sup_le
      intro j _
      calc (Polynomial.C (v ⟨n + (j : ℕ), by omega⟩) * Polynomial.X ^ (m - 1 - (j : ℕ))).natDegree
          ≤ (Polynomial.X (R := k) ^ (m - 1 - (j : ℕ))).natDegree := by
            apply Polynomial.natDegree_C_mul_le
        _ = m - 1 - (j : ℕ) := Polynomial.natDegree_X_pow _
        _ ≤ m - 1 := by omega
    -- f | B_v from hcop and hAfBg.
    have hf_dvd_Bv : f ∣ B_v := by
      have hf_dvd_Bvg : f ∣ B_v * g := by
        use -A_v
        linear_combination hAfBg
      exact hcop.dvd_of_dvd_mul_right hf_dvd_Bvg
    -- But f.natDegree = m > m-1 ≥ B_v.natDegree, so f cannot divide B_v (since B_v ≠ 0).
    have := Polynomial.natDegree_le_of_dvd hf_dvd_Bv hBv_ne
    omega
  · -- (←): ¬ IsCoprime f g  →  ∃ v ≠ 0, v ᵥ* M = 0
    intro hncop
    classical
    -- Get a common irreducible factor p.
    set d := EuclideanDomain.gcd f g
    have hd_ne : d ≠ 0 := by
      intro h; apply hf_ne
      have hdvd : d ∣ f := EuclideanDomain.gcd_dvd_left f g
      rw [h] at hdvd
      exact (zero_dvd_iff.mp hdvd)
    have hd_not_unit : ¬ IsUnit d :=
      fun hu => hncop (EuclideanDomain.gcd_isUnit_iff.mp hu)
    obtain ⟨p, hp_irred, hp_dvd_d⟩ :=
      WfDvdMonoid.exists_irreducible_factor hd_not_unit hd_ne
    have hp_dvd_f : p ∣ f := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_left f g)
    have hp_dvd_g : p ∣ g := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_right f g)
    have hp_ne : p ≠ 0 := hp_irred.ne_zero
    -- A = g/p (degree n - deg(p) < n), B = -(f/p) (degree m - deg(p) < m).
    -- A*f + B*g = (g/p)*f - (f/p)*g = 0.
    set A : Polynomial k := g / p
    set B : Polynomial k := -(f / p)
    have hgp : p * (g / p) = g := EuclideanDomain.mul_div_cancel' hp_ne hp_dvd_g
    have hfp : p * (f / p) = f := EuclideanDomain.mul_div_cancel' hp_ne hp_dvd_f
    have hgp_ne : g / p ≠ 0 := by
      intro h; rw [h, mul_zero] at hgp; exact hg_ne hgp.symm
    have hfp_ne : f / p ≠ 0 := by
      intro h; rw [h, mul_zero] at hfp; exact hf_ne hfp.symm
    have hA_ne : A ≠ 0 := hgp_ne
    have hAfBg_zero : A * f + B * g = 0 := by
      simp only [A, B]
      -- (g/p)*f + (-(f/p))*g = (g/p)*f - (f/p)*g
      -- p * ((g/p)*f - (f/p)*g) = (p*(g/p))*f - (p*(f/p))*g = g*f - f*g = 0
      have key : (g / p) * f - (f / p) * g = 0 := by
        have h1 : p * ((g / p) * f - (f / p) * g) = 0 := by
          linear_combination f * hgp - g * hfp
        exact mul_left_cancel₀ hp_ne (h1.trans (mul_zero p).symm)
      linear_combination key
    -- A.natDegree < n and B.natDegree < m.
    have hp_deg_pos : 0 < p.natDegree := hp_irred.natDegree_pos
    have hA_deg : A.natDegree < n := by
      simp only [A]
      have h := Polynomial.natDegree_mul hp_ne hgp_ne
      rw [hgp, hgdeg] at h; omega
    have hB_deg : B.natDegree < m := by
      simp only [B, Polynomial.natDegree_neg]
      have h := Polynomial.natDegree_mul hp_ne hfp_ne
      rw [hfp, hfdeg] at h; omega
    -- Construct v from A and B coefficients in descending order.
    -- v[j] = A.coeff(n-1-j)  for j < n
    -- v[n+j] = B.coeff(m-1-j)  for j < m
    -- This is the "reverse" encoding of A and B.
    set v : Fin (m + n) → k := fun i =>
      if h : (i : ℕ) < n then A.coeff (n - 1 - (i : ℕ))
      else B.coeff (m - 1 - ((i : ℕ) - n))
    -- v ≠ 0 (since A ≠ 0, some coefficient of A is nonzero).
    have hv_ne : v ≠ 0 := by
      intro hv_eq
      apply hA_ne
      ext e
      by_cases he : e < n
      · have := congr_fun hv_eq ⟨n - 1 - e, by omega⟩
        simp only [v, Fin.val_mk, dif_pos (show n - 1 - e < n from by omega)] at this
        rw [show n - 1 - (n - 1 - e) = e from by omega] at this
        exact this
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    -- v ᵥ* M = 0 because A*f + B*g = 0.
    have hv_mul : v ᵥ* M = 0 := by
      -- The key: sylvester_vecMul_poly_eq with v' := the "standard" encoding of A and B.
      -- But our v uses reversed ordering. We need to connect v to A and B.
      -- Note: v[j] = A.coeff(n-1-j) for j < n means
      --   A = ∑_{j<n} C(A.coeff(n-1-j)) * X^{n-1-j}  ... wait, no.
      -- Let w[j] = A.coeff(n-1-j). Then v[j] = w[j] for j < n.
      -- And ∑_{j<n} C(v[j]) * X^{n-1-j} = ∑_{j<n} C(A.coeff(n-1-j)) * X^{n-1-j} = A (if A.natDegree < n).
      -- So: A = ∑_{j:Fin n} C(v[j]) * X^{n-1-j}  (when A.natDegree < n)
      -- and: B = ∑_{j:Fin m} C(v[n+j]) * X^{m-1-j}  (when B.natDegree < m).
      -- Then by sylvester_vecMul_poly_eq:
      --   A*f + B*g = ∑_k C((v ᵥ* M)[k]) * X^{m+n-1-k}
      -- Since A*f+B*g = 0, all coefficients of (v ᵥ* M) are 0.
      -- First verify: ∑_{j<n} C(v[j]) * X^{n-1-j} = A
      have hA_eq : (∑ j : Fin n, Polynomial.C (v ⟨j, by omega⟩) *
          Polynomial.X ^ (n - 1 - (j : ℕ))) = A := by
        apply Polynomial.ext; intro e
        rw [descPolyCoeff]
        split_ifs with he
        · -- v ⟨n-1-e, _⟩ = A.coeff e, since n-1-e < n so dif_pos applies
          simp only [v, dif_pos (show n - 1 - e < n from by omega)]
          rw [show n - 1 - (n - 1 - e) = e from by omega]
        · -- e ≥ n: LHS = 0, RHS = A.coeff e = 0 since A.natDegree < n
          exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
      -- And: ∑_{j<m} C(v[n+j]) * X^{m-1-j} = B
      have hB_eq : (∑ j : Fin m, Polynomial.C (v ⟨n + (j : ℕ), by omega⟩) *
          Polynomial.X ^ (m - 1 - (j : ℕ))) = B := by
        apply Polynomial.ext; intro e
        rw [descPolyCoeff]
        split_ifs with he
        · -- v ⟨n + (m-1-e), _⟩ = B.coeff e
          -- v is defined with dif: since n + (m-1-e) ≥ n, dif_neg applies
          simp only [v, dif_neg (show ¬ (n + (m - 1 - e) < n) from by omega)]
          -- Now B = -(f/p), B.coeff e = -(f/p).coeff e
          simp only [B, Polynomial.coeff_neg]
          rw [show n + (m - 1 - e) - n = m - 1 - e from by omega]
          rw [show m - 1 - (m - 1 - e) = e from by omega]
        · -- e ≥ m: LHS = 0, RHS = B.coeff e = 0 since B.natDegree < m
          exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
      -- Now apply sylvester_vecMul_poly_eq
      -- The lemma gives: (∑_{j<n} C(v[j])*X^{n-1-j})*f + (∑_{j<m} C(v[n+j])*X^{m-1-j})*g
      --                = ∑_k C((v ᵥ* M)[k]) * X^{m+n-1-k}
      -- We know the LHS equals A*f + B*g by hA_eq and hB_eq.
      have heq : A * f + B * g =
          ∑ k : Fin (m + n), Polynomial.C ((v ᵥ* sylvesterMatrix m n f g) k) *
            Polynomial.X ^ (m + n - 1 - (k : ℕ)) := by
        have hraw := sylvester_vecMul_poly_eq (R := k) m n hm hn f g hf_deg hg_deg v
        rw [hA_eq, hB_eq] at hraw
        exact hraw
      rw [hAfBg_zero] at heq
      -- Now: 0 = ∑_k C((v ᵥ* M)[k]) * X^{m+n-1-k}
      -- This implies all (v ᵥ* M)[k] = 0.
      ext c
      simp only [Pi.zero_apply]
      have hcoeff := congr_arg (Polynomial.coeff · (m + n - 1 - (c : ℕ))) heq.symm
      simp only [Polynomial.coeff_zero] at hcoeff
      rw [Polynomial.finset_sum_coeff] at hcoeff
      simp only [Polynomial.coeff_C_mul_X_pow] at hcoeff
      -- hcoeff: ∑_k (if m+n-1-c = m+n-1-k then (v ᵥ* M)[k] else 0) = 0
      -- The condition m+n-1-c = m+n-1-k is equivalent to k = c (for k, c : Fin (m+n))
      simp only [← hM_def] at hcoeff
      -- Convert: if m+n-1-c = m+n-1-k then ... to if k = c then ...
      have hconv : ∀ x : Fin (m + n), (m + n - 1 - (c : ℕ) = m + n - 1 - (x : ℕ)) ↔ x = c := by
        intro x; constructor
        · intro h; exact Fin.ext (by omega)
        · intro h; rw [h]
      simp_rw [hconv] at hcoeff
      rw [Finset.sum_ite_eq'] at hcoeff
      simp only [Finset.mem_univ, if_true] at hcoeff
      exact hcoeff
    exact ⟨v, hv_ne, hv_mul⟩

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
  simp only [Polynomial.IsRoot, Polynomial.derivative_map]
  have hf_ne : f ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hflc
  have hm_pos : 0 < m := by omega
  have hn_pos : 0 < m - 1 := by omega
  have hf_deg : ∀ d, m < d → f.coeff d = 0 :=
    fun d hd => Polynomial.coeff_eq_zero_of_natDegree_lt (hfdeg ▸ hd)
  have hg_bound : ∀ d, m - 1 < d → f.derivative.coeff d = 0 := fun d hd => by
    rw [Polynomial.coeff_derivative]
    have hc : f.coeff (d + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hc]
  -- Step 1: disc = 0 ↔ Res(f, f') = 0.
  have hc_ne : (-1 : k) ^ (m * (m - 1) / 2) * f.leadingCoeff⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (inv_ne_zero hflc)
  rw [show discriminant m f = 0 ↔ resultant m (m - 1) f f.derivative = 0 from
    ⟨fun h => (mul_eq_zero.mp h).resolve_left hc_ne,
     fun h => by simp [discriminant, h]⟩]
  -- Step 2: Res = 0 ↔ ∃ v ≠ 0, v ᵥ* M = 0.
  set g := f.derivative with hg_def
  set M := sylvesterMatrix m (m - 1) f g with hM_def
  rw [resultant, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · -- (→): ∃ common root → ∃ v ≠ 0, v ᵥ* M = 0
    rintro ⟨L, _, _, α, hfα, hgα⟩
    -- Common root → ¬ IsCoprime f f.derivative
    have hncop : ¬ IsCoprime f g := by
      intro ⟨a, b, hab⟩
      have h : ((a * f + b * g).map (algebraMap k L)).eval α = 1 := by
        rw [hab, Polynomial.map_one, Polynomial.eval_one]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
                 Polynomial.eval_mul, hfα, hgα, mul_zero, add_zero] at h
      exact one_ne_zero h.symm
    classical
    by_cases hg_zero : g = 0
    · -- f' = 0: Sylvester matrix has zero rows → det = 0 → ∃ v ≠ 0, v ᵥ* M = 0
      rw [Matrix.exists_vecMul_eq_zero_iff]
      apply Matrix.det_eq_zero_of_row_eq_zero ⟨m - 1, by omega⟩
      intro j
      simp only [hM_def, sylvesterMatrix, Fin.val_mk,
                 show ¬ (m - 1 < m - 1) from lt_irrefl _]
      simp only [↓reduceIte, hg_zero, Polynomial.coeff_zero]
      split_ifs <;> rfl
    · -- f' ≠ 0: use common irreducible factor to build kernel vector
      set d := EuclideanDomain.gcd f g
      have hd_ne : d ≠ 0 := by
        intro h; apply hf_ne
        have : d ∣ f := EuclideanDomain.gcd_dvd_left f g
        rw [h] at this; exact zero_dvd_iff.mp this
      have hd_not_unit : ¬ IsUnit d := fun hu => hncop (EuclideanDomain.gcd_isUnit_iff.mp hu)
      obtain ⟨p, hp_irred, hp_dvd_d⟩ := WfDvdMonoid.exists_irreducible_factor hd_not_unit hd_ne
      have hp_dvd_f : p ∣ f := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_left f g)
      have hp_dvd_g : p ∣ g := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_right f g)
      have hp_ne : p ≠ 0 := hp_irred.ne_zero
      have hgp_ne : g / p ≠ 0 := by
        intro h
        have hgp : p * (g / p) = g := EuclideanDomain.mul_div_cancel' hp_ne hp_dvd_g
        rw [h, mul_zero] at hgp; exact hg_zero hgp.symm
      have hfp_ne : f / p ≠ 0 := by
        intro h
        have hfp : p * (f / p) = f := EuclideanDomain.mul_div_cancel' hp_ne hp_dvd_f
        rw [h, mul_zero] at hfp; exact hf_ne hfp.symm
      set A := g / p
      set B := -(f / p)
      have hgp : p * A = g := EuclideanDomain.mul_div_cancel' hp_ne hp_dvd_g
      have hfp : p * (f / p) = f := EuclideanDomain.mul_div_cancel' hp_ne hp_dvd_f
      have hAfBg_zero : A * f + B * g = 0 := by
        simp only [A, B]
        have key : g / p * f - f / p * g = 0 := by
          have h1 : p * (g / p * f - f / p * g) = 0 := by
            linear_combination f * hgp - g * hfp
          exact mul_left_cancel₀ hp_ne (h1.trans (mul_zero p).symm)
        linear_combination key
      have hp_deg_pos : 0 < p.natDegree := hp_irred.natDegree_pos
      have hA_deg : A.natDegree < m - 1 := by
        have h := Polynomial.natDegree_mul hp_ne hgp_ne
        rw [hgp] at h
        have hg_nd : g.natDegree ≤ m - 1 := by
          by_contra h; push_neg at h
          exact absurd (hg_bound g.natDegree h) (Polynomial.leadingCoeff_ne_zero.mpr hg_zero)
        omega
      have hB_deg : B.natDegree < m := by
        simp only [B, Polynomial.natDegree_neg]
        have h := Polynomial.natDegree_mul hp_ne hfp_ne
        rw [hfp, hfdeg] at h; omega
      -- Construct v from descending coefficients of A and B
      -- Use (m-1)-1 = m-2 so that descPolyCoeff (with mn=m-1) pattern-matches directly.
      let v : Fin (m + (m - 1)) → k := fun i =>
        if h : (i : ℕ) < m - 1 then A.coeff ((m - 1) - 1 - (i : ℕ))
        else B.coeff (m - 1 - ((i : ℕ) - (m - 1)))
      have hv_ne : v ≠ 0 := by
        intro hv_eq; apply hgp_ne
        ext e
        by_cases he : e < m - 1
        · have := congr_fun hv_eq ⟨(m - 1) - 1 - e, by omega⟩
          simp only [v, Fin.val_mk, dif_pos (by omega : (m - 1) - 1 - e < m - 1)] at this
          rw [show (m - 1) - 1 - ((m - 1) - 1 - e) = e from by omega] at this
          simpa using this
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hv_mul : v ᵥ* M = 0 := by
        have hA_eq : (∑ j : Fin (m - 1), Polynomial.C (v ⟨j, by omega⟩) *
            Polynomial.X ^ ((m - 1) - 1 - (j : ℕ))) = A := by
          apply Polynomial.ext; intro e
          rw [descPolyCoeff]
          split_ifs with he
          · simp only [v, dif_pos (by omega : (m - 1) - 1 - e < m - 1)]
            congr 1; omega
          · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
        have hB_eq : (∑ j : Fin m, Polynomial.C (v ⟨(m - 1) + (j : ℕ), by omega⟩) *
            Polynomial.X ^ (m - 1 - (j : ℕ))) = B := by
          apply Polynomial.ext; intro e
          rw [descPolyCoeff]
          split_ifs with he
          · simp only [v, dif_neg (by omega : ¬((m - 1) + (m - 1 - e) < m - 1))]
            simp only [B, Polynomial.coeff_neg]
            rw [show (m - 1) + (m - 1 - e) - (m - 1) = m - 1 - e from by omega,
                show m - 1 - (m - 1 - e) = e from by omega]
          · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
        have heq : A * f + B * g = ∑ k : Fin (m + (m - 1)),
            Polynomial.C ((v ᵥ* sylvesterMatrix m (m - 1) f g) k) *
              Polynomial.X ^ (m + (m - 1) - 1 - (k : ℕ)) := by
          have hraw := sylvester_vecMul_poly_eq (R := k) m (m - 1) hm_pos hn_pos
              f g hf_deg hg_bound v
          rw [hA_eq, hB_eq] at hraw; exact hraw
        rw [hAfBg_zero] at heq
        ext c; simp only [Pi.zero_apply]
        have hcoeff := congr_arg (Polynomial.coeff · (m + (m - 1) - 1 - (c : ℕ))) heq.symm
        simp only [Polynomial.coeff_zero] at hcoeff
        rw [Polynomial.finset_sum_coeff] at hcoeff
        simp only [Polynomial.coeff_C_mul_X_pow] at hcoeff
        have hconv : ∀ x : Fin (m + (m - 1)),
            (m + (m - 1) - 1 - (c : ℕ) = m + (m - 1) - 1 - (x : ℕ)) ↔ x = c :=
          fun x => ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
        simp_rw [hconv] at hcoeff
        rw [Finset.sum_ite_eq'] at hcoeff
        simp only [Finset.mem_univ, if_true] at hcoeff
        rw [hM_def]; exact hcoeff
      exact ⟨v, hv_ne, hv_mul⟩
  · -- (←): ∃ v ≠ 0, v ᵥ* M = 0 → ∃ common root in some extension
    rintro ⟨v, hv_ne, hv_mul⟩
    -- Extract A_v and B_v from v, show A_v * f + B_v * g = 0
    set A_v := ∑ j : Fin (m - 1), Polynomial.C (v ⟨j, by omega⟩) *
        Polynomial.X ^ ((m - 1) - 1 - (j : ℕ)) with hAv_def
    set B_v := ∑ j : Fin m, Polynomial.C (v ⟨(m - 1) + (j : ℕ), by omega⟩) *
        Polynomial.X ^ (m - 1 - (j : ℕ)) with hBv_def
    have hAfBg : A_v * f + B_v * g = 0 := by
      have hraw := sylvester_vecMul_poly_eq (R := k) m (m - 1) hm_pos hn_pos
          f g hf_deg hg_bound v
      simp only [] at hraw
      simp only [hv_mul, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at hraw
      exact hraw
    -- Derive ¬ IsCoprime f g from the kernel vector
    have hncop : ¬ IsCoprime f g := by
      have hAB_ne : A_v ≠ 0 ∨ B_v ≠ 0 := by
        by_contra h; push Not at h; obtain ⟨hA0, hB0⟩ := h
        apply hv_ne; ext ⟨i, hi⟩; simp only [Pi.zero_apply]
        by_cases hlt : i < m - 1
        · have : A_v.coeff ((m - 1) - 1 - i) = 0 := by rw [hA0]; simp
          simp only [hAv_def, descPolyCoeff, dif_pos (by omega : (m - 1) - 1 - i < m - 1),
                     show (m - 1) - 1 - ((m - 1) - 1 - i) = i from by omega] at this
          exact this
        · have hge : m - 1 ≤ i := Nat.le_of_not_lt hlt
          have : B_v.coeff (m - 1 - (i - (m - 1))) = 0 := by rw [hB0]; simp
          simp only [hBv_def, descPolyCoeff, dif_pos (by omega : m - 1 - (i - (m-1)) < m),
                     show m - 1 - (m - 1 - (i - (m-1))) = i - (m-1) from by omega,
                     show (m - 1) + (i - (m-1)) = i from by omega] at this
          exact this
      have hBv_ne : B_v ≠ 0 := by
        rcases hAB_ne with hA | hB
        · intro hB0; rw [hB0, zero_mul, add_zero] at hAfBg
          exact hA (mul_eq_zero.mp hAfBg |>.resolve_right hf_ne)
        · exact hB
      have hBv_deg : B_v.natDegree ≤ m - 1 := by
        simp only [hBv_def]
        apply (Polynomial.natDegree_sum_le _ _).trans
        apply Finset.sup_le; intro j _
        calc (Polynomial.C _ * Polynomial.X ^ _).natDegree
            ≤ (Polynomial.X (R := k) ^ (m - 1 - (j : ℕ))).natDegree :=
              Polynomial.natDegree_C_mul_le _ _
          _ = m - 1 - (j : ℕ) := Polynomial.natDegree_X_pow _
          _ ≤ m - 1 := by omega
      intro hcop
      exact absurd
        (Polynomial.natDegree_le_of_dvd
          (hcop.dvd_of_dvd_mul_right ⟨-A_v, by linear_combination hAfBg⟩) hBv_ne)
        (by omega)
    -- ¬ IsCoprime f g → produce a common root via AdjoinRoot
    classical
    by_cases hg_zero : g = 0
    · -- g = f' = 0: any root of f works; use AlgebraicClosure
      haveI : IsAlgClosed (AlgebraicClosure k) := AlgebraicClosure.isAlgClosed k
      -- Find a root of f in the algebraic closure (f has positive degree)
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure k) f
          (by rw [Polynomial.degree_eq_natDegree hf_ne, hfdeg]; norm_cast; omega)
      refine ⟨AlgebraicClosure k, inferInstance, inferInstance, α, ?_, ?_⟩
      · -- f(α) = 0: aeval α f = (f.map φ).eval α
        rw [Polynomial.eval_map, ← Polynomial.aeval_def]; exact hα
      · simp [hg_zero]
    · -- g ≠ 0: get common irreducible factor p, use L = AdjoinRoot p
      set d := EuclideanDomain.gcd f g
      have hd_ne : d ≠ 0 := by
        intro h; apply hf_ne
        have : d ∣ f := EuclideanDomain.gcd_dvd_left f g
        rw [h] at this; exact zero_dvd_iff.mp this
      have hd_not_unit : ¬ IsUnit d := fun hu => hncop (EuclideanDomain.gcd_isUnit_iff.mp hu)
      obtain ⟨p, hp_irred, hp_dvd_d⟩ := WfDvdMonoid.exists_irreducible_factor hd_not_unit hd_ne
      have hp_dvd_f : p ∣ f := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_left f g)
      have hp_dvd_g : p ∣ g := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_right f g)
      haveI : Fact (Irreducible p) := ⟨hp_irred⟩
      set φ := algebraMap k (AdjoinRoot p)
      have hroot : (p.map φ).eval (AdjoinRoot.root p) = 0 := by
        rw [Polynomial.eval_map, ← Polynomial.aeval_def]
        rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
      refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
      · obtain ⟨r, hr⟩ := hp_dvd_f
        rw [hr, Polynomial.map_mul, Polynomial.eval_mul, hroot, zero_mul]
      · obtain ⟨r, hr⟩ := hp_dvd_g
        rw [hr, Polynomial.map_mul, Polynomial.eval_mul, hroot, zero_mul]

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
  set φ := algebraMap k (Polynomial k)
  set ι : Fin 2 → Polynomial k := ![Polynomial.X, 1]
  set f := F.eval₂ φ ι with hf_def
  set g := G.eval₂ φ ι with hg_def
  set M := sylvesterMatrix m n f g with hM_def
  -- For d > m and e ∈ F.support, IsHomogeneous F m gives weight 1 e = m, i.e. e 0 + e 1 = m,
  -- so e 0 ≤ m < d. The monomial e evaluates to C(F.coeff e) * X^(e 0), which has coeff 0 at d.
  have hf_natdeg : f.natDegree ≤ m := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    show (F.eval₂ (algebraMap k (Polynomial k)) (![Polynomial.X, (1 : Polynomial k)])).coeff d = 0
    rw [F.as_sum, MvPolynomial.eval₂_sum, Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro e he
    have he_coeff : F.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have he_01 : e 0 + e 1 = m := by
      have h := hFhom he_coeff
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
          Fin.sum_univ_two] at h
      simpa [smul_eq_mul] using h
    rw [MvPolynomial.eval₂_monomial,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    -- coeff_X_pow gives `if d = e 0 then 1 else 0`, and d ≠ e 0 since e 0 ≤ m < d
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               one_pow, mul_one, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul,
               Polynomial.coeff_X_pow, if_neg (show d ≠ e 0 from by omega), mul_zero]
  have hg_natdeg : g.natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    show (G.eval₂ (algebraMap k (Polynomial k)) (![Polynomial.X, (1 : Polynomial k)])).coeff d = 0
    rw [G.as_sum, MvPolynomial.eval₂_sum, Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro e he
    have he_coeff : G.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have he_01 : e 0 + e 1 = n := by
      have h := hGhom he_coeff
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
          Fin.sum_univ_two] at h
      simpa [smul_eq_mul] using h
    rw [MvPolynomial.eval₂_monomial,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               one_pow, mul_one, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul,
               Polynomial.coeff_X_pow, if_neg (show d ≠ e 0 from by omega), mul_zero]
  have hf_bound : ∀ d, m < d → f.coeff d = 0 := fun d hd =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hg_bound : ∀ d, n < d → g.coeff d = 0 := fun d hd =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  constructor
  · -- (→): resultant = 0 → ∃ common factor of totalDegree ≥ 1
    -- Strategy:
    -- • Extract null vector v ≠ 0 with v ᵥ* M = 0; build A_v, B_v with A_v*f + B_v*g = 0.
    -- • If F=0 or G=0: trivial (take H = G or F or X 0).
    -- • If both natDeg < bound: X₁ divides both F and G; take H = X 1.
    -- • Otherwise (at least one natDeg = bound): prove ¬IsCoprime(f,g) via degree argument,
    --   get irreducible common factor p, take H = p.homogenize(p.natDeg).
    intro hres
    -- Extract null vector
    rw [resultant, ← Matrix.exists_vecMul_eq_zero_iff] at hres
    obtain ⟨v, hv_ne, hv_mul⟩ := hres
    -- Build Bézout polynomials A_v, B_v from v
    set A_v : Polynomial k :=
      ∑ j : Fin n, Polynomial.C (v ⟨(j : ℕ), by omega⟩) * Polynomial.X ^ (n - 1 - (j : ℕ))
    set B_v : Polynomial k :=
      ∑ j : Fin m, Polynomial.C (v ⟨n + (j : ℕ), by omega⟩) * Polynomial.X ^ (m - 1 - (j : ℕ))
    -- A_v * f + B_v * g = 0
    have hAfBg : A_v * f + B_v * g = 0 := by
      have hraw := sylvester_vecMul_poly_eq (R := k) m n hm hn f g hf_bound hg_bound v
      simp only [] at hraw
      have hvm : v ᵥ* sylvesterMatrix m n f g = 0 := hM_def ▸ hv_mul
      simp only [hvm, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at hraw
      exact hraw
    -- Degree bounds on A_v and B_v
    have hAv_deg : A_v.natDegree ≤ n - 1 := by
      simp only [A_v]
      apply (Polynomial.natDegree_sum_le _ _).trans
      apply Finset.sup_le; intro j _
      calc (Polynomial.C (v ⟨(j : ℕ), by omega⟩) *
              Polynomial.X ^ (n - 1 - (j : ℕ))).natDegree
          ≤ (Polynomial.X (R := k) ^ (n - 1 - (j : ℕ))).natDegree :=
            Polynomial.natDegree_C_mul_le _ _
        _ = n - 1 - (j : ℕ) := Polynomial.natDegree_X_pow _
        _ ≤ n - 1 := Nat.sub_le _ _
    have hBv_deg : B_v.natDegree ≤ m - 1 := by
      simp only [B_v]
      apply (Polynomial.natDegree_sum_le _ _).trans
      apply Finset.sup_le; intro j _
      calc (Polynomial.C (v ⟨n + (j : ℕ), by omega⟩) *
              Polynomial.X ^ (m - 1 - (j : ℕ))).natDegree
          ≤ (Polynomial.X (R := k) ^ (m - 1 - (j : ℕ))).natDegree :=
            Polynomial.natDegree_C_mul_le _ _
        _ = m - 1 - (j : ℕ) := Polynomial.natDegree_X_pow _
        _ ≤ m - 1 := Nat.sub_le _ _
    -- A_v ≠ 0 or B_v ≠ 0 (from v ≠ 0)
    have hAB_ne : A_v ≠ 0 ∨ B_v ≠ 0 := by
      by_contra h; push_neg at h; obtain ⟨hA0, hB0⟩ := h
      apply hv_ne; ext ⟨i, hi⟩; simp only [Pi.zero_apply]
      by_cases h_i : i < n
      · have hcoeff : A_v.coeff (n - 1 - i) = 0 := by rw [hA0]; simp
        simp only [A_v, descPolyCoeff,
                   dif_pos (show n - 1 - i < n from by omega),
                   show n - 1 - (n - 1 - i) = i from by omega] at hcoeff
        exact hcoeff
      · have h_ge : n ≤ i := Nat.le_of_not_lt h_i
        have hcoeff : B_v.coeff (m - 1 - (i - n)) = 0 := by rw [hB0]; simp
        simp only [B_v, descPolyCoeff,
                   dif_pos (show m - 1 - (i - n) < m from by omega),
                   show m - 1 - (m - 1 - (i - n)) = i - n from by omega,
                   show n + (i - n) = i from by omega] at hcoeff
        exact hcoeff
    -- Homogenization identities: f.homogenize m = F and g.homogenize n = G
    have heval_F : MvPolynomial.aeval ι F = f := hf_def.symm
    have hF_eq : f.homogenize m = F :=
      Polynomial.homogenize_eq_of_isHomogeneous hFhom heval_F
    have heval_G : MvPolynomial.aeval ι G = g := hg_def.symm
    have hG_eq : g.homogenize n = G :=
      Polynomial.homogenize_eq_of_isHomogeneous hGhom heval_G
    -- Factorization: f.homogenize m = X₁^(m-d_f) * f.homogenize(d_f), and similarly for g
    have hfact_F : f.homogenize m =
        MvPolynomial.X 1 ^ (m - f.natDegree) * f.homogenize f.natDegree := by
      have key := Polynomial.homogenize_mul (1 : Polynomial k) f
          (show (1 : Polynomial k).natDegree ≤ m - f.natDegree from by simp)
          le_rfl
      simp only [one_mul, Polynomial.homogenize_one] at key
      rwa [Nat.sub_add_cancel hf_natdeg] at key
    have hfact_G : g.homogenize n =
        MvPolynomial.X 1 ^ (n - g.natDegree) * g.homogenize g.natDegree := by
      have key := Polynomial.homogenize_mul (1 : Polynomial k) g
          (show (1 : Polynomial k).natDegree ≤ n - g.natDegree from by simp)
          le_rfl
      simp only [one_mul, Polynomial.homogenize_one] at key
      rwa [Nat.sub_add_cancel hg_natdeg] at key
    -- Case: F = 0
    by_cases hFz : F = 0
    · by_cases hGz : G = 0
      · exact ⟨MvPolynomial.X 0, by simp [MvPolynomial.totalDegree_X],
                 by rw [hFz]; exact dvd_zero _,
                 by rw [hGz]; exact dvd_zero _⟩
      · exact ⟨G, by linarith [hGhom.totalDegree hGz],
                   by rw [hFz]; exact dvd_zero _,
                   dvd_refl G⟩
    -- Case: G = 0 (F ≠ 0)
    by_cases hGz : G = 0
    · exact ⟨F, by linarith [hFhom.totalDegree hFz],
                 dvd_refl F,
                 by rw [hGz]; exact dvd_zero _⟩
    -- F ≠ 0, G ≠ 0 ⟹ f ≠ 0, g ≠ 0
    have hfne : f ≠ 0 := by
      intro hf0; apply hFz
      rw [← hF_eq]; exact (Polynomial.homogenize_eq_zero_iff hf_natdeg).mpr hf0
    have hgne : g ≠ 0 := by
      intro hg0; apply hGz
      rw [← hG_eq]; exact (Polynomial.homogenize_eq_zero_iff hg_natdeg).mpr hg0
    -- Case: both natDegrees strictly below their bounds → X₁ divides F and G
    by_cases hbothlt : f.natDegree < m ∧ g.natDegree < n
    · obtain ⟨hfd, hgd⟩ := hbothlt
      have hX1F : MvPolynomial.X 1 ∣ F := by
        rw [← hF_eq, hfact_F]
        exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
      have hX1G : MvPolynomial.X 1 ∣ G := by
        rw [← hG_eq, hfact_G]
        exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
      exact ⟨MvPolynomial.X 1, by simp [MvPolynomial.totalDegree_X], hX1F, hX1G⟩
    -- At least one natDegree equals its bound: prove ¬IsCoprime f g
    have hncop : ¬ IsCoprime f g := by
      intro hcop
      have hAv_ne : A_v ≠ 0 := by
        rcases hAB_ne with hA | hB
        · exact hA
        · intro hA0; rw [hA0, zero_mul, zero_add] at hAfBg
          exact hB (mul_eq_zero.mp hAfBg |>.resolve_right hgne)
      have hBv_ne : B_v ≠ 0 := by
        rcases hAB_ne with hA | hB
        · intro hB0; rw [hB0, zero_mul, add_zero] at hAfBg
          exact hA (mul_eq_zero.mp hAfBg |>.resolve_right hfne)
        · exact hB
      by_cases hgn : g.natDegree = n
      · -- g ∣ A_v via IsCoprime; then g.natDeg ≤ A_v.natDeg ≤ n-1 < n: contradiction
        have hg_dvd_Avf : g ∣ A_v * f := ⟨-B_v, by linear_combination hAfBg⟩
        have hgA : g ∣ A_v := hcop.symm.dvd_of_dvd_mul_right hg_dvd_Avf
        have := Polynomial.natDegree_le_of_dvd hgA hAv_ne
        omega
      · -- g.natDeg < n, so f.natDeg = m; f ∣ B_v; f.natDeg ≤ B_v.natDeg ≤ m-1: contradiction
        have hgd : g.natDegree < n := Nat.lt_of_le_of_ne hg_natdeg hgn
        have hfd : ¬ f.natDegree < m := fun hlt => hbothlt ⟨hlt, hgd⟩
        have hfm : f.natDegree = m := Nat.le_antisymm hf_natdeg (Nat.le_of_not_lt hfd)
        have hf_dvd_Bvg : f ∣ B_v * g := ⟨-A_v, by linear_combination hAfBg⟩
        have hfB : f ∣ B_v := hcop.dvd_of_dvd_mul_right hf_dvd_Bvg
        have := Polynomial.natDegree_le_of_dvd hfB hBv_ne
        omega
    -- Get common irreducible factor p of f and g
    classical
    set d_fg := EuclideanDomain.gcd f g
    have hd_ne : d_fg ≠ 0 := by
      intro h; apply hfne
      have : d_fg ∣ f := EuclideanDomain.gcd_dvd_left f g
      rw [h] at this; exact zero_dvd_iff.mp this
    have hd_not_unit : ¬ IsUnit d_fg :=
      fun hu => hncop (EuclideanDomain.gcd_isUnit_iff.mp hu)
    obtain ⟨p, hp_irred, hp_dvd_d⟩ :=
      WfDvdMonoid.exists_irreducible_factor hd_not_unit hd_ne
    have hp_dvd_f : p ∣ f := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_left f g)
    have hp_dvd_g : p ∣ g := dvd_trans hp_dvd_d (EuclideanDomain.gcd_dvd_right f g)
    -- Take H = p.homogenize p.natDegree
    refine ⟨p.homogenize p.natDegree, ?_, ?_, ?_⟩
    · -- H.totalDegree ≥ 1
      have hpH_ne : p.homogenize p.natDegree ≠ 0 :=
        fun h => hp_irred.ne_zero ((Polynomial.homogenize_eq_zero_iff le_rfl).mp h)
      have := (Polynomial.isHomogeneous_homogenize p).totalDegree hpH_ne
      linarith [hp_irred.natDegree_pos]
    · -- H ∣ F: via H ∣ f.homogenize(f.natDeg) ∣ X₁^(m-d_f) * f.homogenize(d_f) = F
      have h1 : p.homogenize p.natDegree ∣ f.homogenize f.natDegree :=
        Polynomial.homogenize_dvd hp_dvd_f
      have h2 : f.homogenize f.natDegree ∣ F := by
        rw [← hF_eq, hfact_F]; exact dvd_mul_left _ _
      exact dvd_trans h1 h2
    · -- H ∣ G: symmetrically
      have h3 : p.homogenize p.natDegree ∣ g.homogenize g.natDegree :=
        Polynomial.homogenize_dvd hp_dvd_g
      have h4 : g.homogenize g.natDegree ∣ G := by
        rw [← hG_eq, hfact_G]; exact dvd_mul_left _ _
      exact dvd_trans h3 h4
  · -- (←): ∃ H dividing both → resultant = 0
    rintro ⟨H, htd, ⟨Q, hFQ⟩, ⟨R, hGR⟩⟩
    set h := H.eval₂ φ ι
    set q := Q.eval₂ φ ι
    set r := R.eval₂ φ ι
    -- f = h * q and g = h * r (ring hom applied to F = H*Q, G = H*R)
    have hfhq : f = h * q := by
      show F.eval₂ φ ι = H.eval₂ φ ι * Q.eval₂ φ ι
      rw [hFQ, MvPolynomial.eval₂_mul]
    have hghr : g = h * r := by
      show G.eval₂ φ ι = H.eval₂ φ ι * R.eval₂ φ ι
      rw [hGR, MvPolynomial.eval₂_mul]
    rw [resultant]
    -- Case f = 0: row 0 of the Sylvester matrix is all zeros
    by_cases hfz : f = 0
    · apply Matrix.det_eq_zero_of_row_eq_zero ⟨0, by omega⟩
      intro ⟨j, hj⟩
      simp only [M, sylvesterMatrix, Fin.val_zero, show (0 : ℕ) < n from hn, ↓reduceIte,
                 hfz, Polynomial.coeff_zero]
      split_ifs <;> rfl
    -- Case g = 0: row n is all zeros
    · by_cases hgz : g = 0
      · apply Matrix.det_eq_zero_of_row_eq_zero ⟨n, by omega⟩
        intro ⟨j, hj⟩
        simp only [M, sylvesterMatrix, show ¬ ((n : ℕ) < n) from lt_irrefl n, ↓reduceIte,
                   hgz, Polynomial.coeff_zero]
        split_ifs <;> rfl
      -- Main case: f ≠ 0 and g ≠ 0
      · have hh_ne : h ≠ 0 := fun h0 => hfz (by rw [hfhq, h0, zero_mul])
        have hq_ne : q ≠ 0 := fun q0 => hfz (by rw [hfhq, q0, mul_zero])
        have hr_ne : r ≠ 0 := fun r0 => hgz (by rw [hghr, r0, mul_zero])
        -- Sub-case h.natDegree = 0 (h is a nonzero constant):
        -- Since F = H*Q is homogeneous of degree m and H.totalDegree ≥ 1, we get
        -- totalDegree(Q) = m - totalDegree(H) ≤ m - 1, so q = Q(X,1) has natDegree ≤ m-1.
        -- Combined with f = h*q (h constant), f.natDegree ≤ m-1, so f.coeff m = 0.
        -- Similarly g.coeff n = 0. Hence column 0 of M is all zeros.
        by_cases hh_const : h.natDegree = 0
        · have hFne : F ≠ 0 := fun hF => hfz
              (show f = 0 from by rw [hf_def, hF]; exact MvPolynomial.eval₂_zero φ ι)
          have hGne : G ≠ 0 := fun hG => hgz
              (show g = 0 from by rw [hg_def, hG]; exact MvPolynomial.eval₂_zero φ ι)
          have hHne : H ≠ 0 := fun hH => hFne (hFQ.trans (hH ▸ zero_mul Q))
          have hQne : Q ≠ 0 := fun hQ => hFne (hFQ.trans (hQ ▸ mul_zero H))
          have hRne : R ≠ 0 := fun hR => hGne (hGR.trans (hR ▸ mul_zero H))
          -- totalDegree(H) + totalDegree(Q) = m, so totalDegree(Q) ≤ m - 1
          have htdF : F.totalDegree = m := hFhom.totalDegree hFne
          have htdG : G.totalDegree = n := hGhom.totalDegree hGne
          have htdQ : Q.totalDegree ≤ m - 1 := by
            have := MvPolynomial.totalDegree_mul_of_isDomain hHne hQne
            rw [← hFQ, htdF] at this; omega
          have htdR : R.totalDegree ≤ n - 1 := by
            have := MvPolynomial.totalDegree_mul_of_isDomain hHne hRne
            rw [← hGR, htdG] at this; omega
          -- q.natDegree ≤ Q.totalDegree: for d > Q.totalDegree, each monomial e of Q
          -- has e 0 ≤ e.sum ≤ Q.totalDegree < d, so it contributes 0 to q.coeff d
          have hq_td : q.natDegree ≤ Q.totalDegree := by
            apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            intro d hd
            show (Q.eval₂ (algebraMap k (Polynomial k)) (![Polynomial.X, (1 : Polynomial k)])).coeff d = 0
            rw [Q.as_sum, MvPolynomial.eval₂_sum, Polynomial.finset_sum_coeff]
            apply Finset.sum_eq_zero
            intro e he
            rw [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
                Fin.prod_univ_two]
            have he_e0 : e 0 ≤ Q.totalDegree := by
              have htd : e.sum (fun _ v => v) ≤ Q.totalDegree := MvPolynomial.le_totalDegree he
              have hsum : e.sum (fun _ v => v) = e 0 + e 1 := by
                rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
              omega
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                       one_pow, mul_one, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul,
                       Polynomial.coeff_X_pow, if_neg (show d ≠ e 0 from by omega), mul_zero]
          have hr_td : r.natDegree ≤ R.totalDegree := by
            apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            intro d hd
            show (R.eval₂ (algebraMap k (Polynomial k)) (![Polynomial.X, (1 : Polynomial k)])).coeff d = 0
            rw [R.as_sum, MvPolynomial.eval₂_sum, Polynomial.finset_sum_coeff]
            apply Finset.sum_eq_zero
            intro e he
            rw [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
                Fin.prod_univ_two]
            have he_e0 : e 0 ≤ R.totalDegree := by
              have htd : e.sum (fun _ v => v) ≤ R.totalDegree := MvPolynomial.le_totalDegree he
              have hsum : e.sum (fun _ v => v) = e 0 + e 1 := by
                rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
              omega
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                       one_pow, mul_one, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul,
                       Polynomial.coeff_X_pow, if_neg (show d ≠ e 0 from by omega), mul_zero]
          -- f.coeff m = 0: f.natDegree = h.natDeg + q.natDeg = 0 + q.natDeg ≤ m-1 < m
          have hfm : f.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
            have hfn := hfhq ▸ Polynomial.natDegree_mul hh_ne hq_ne
            omega)
          have hgn : g.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
            have hgn := hghr ▸ Polynomial.natDegree_mul hh_ne hr_ne
            omega)
          -- Column 0 of the Sylvester matrix is all zeros → det M = 0
          apply Matrix.det_eq_zero_of_column_eq_zero ⟨0, by omega⟩
          intro ⟨i, hi⟩
          simp only [M, sylvesterMatrix]
          split_ifs with h1 h2 h3
          · -- i < n, i ≤ 0 ∧ 0 ≤ i + m: so i = 0, entry = f.coeff m = 0
            have hi0 : i = 0 := by omega
            simp [hi0, hfm]
          · rfl
          · -- ¬(i < n), i - n ≤ 0 ∧ 0 ≤ i: so i = n, entry = g.coeff n = 0
            have hin : i = n := by omega
            simp [hin, hgn]
          · rfl
        -- Sub-case h.natDegree ≥ 1: Bézout-vector argument
        · have hh_pos : 1 ≤ h.natDegree := Nat.one_le_iff_ne_zero.mpr hh_const
          have hfhq_ndeg : f.natDegree = h.natDegree + q.natDegree := by
            rw [hfhq]; exact Polynomial.natDegree_mul hh_ne hq_ne
          have hghr_ndeg : g.natDegree = h.natDegree + r.natDegree := by
            rw [hghr]; exact Polynomial.natDegree_mul hh_ne hr_ne
          have hq_natdeg : q.natDegree ≤ m - 1 := by
            have := hfhq_ndeg ▸ hf_natdeg; omega
          have hr_natdeg : r.natDegree ≤ n - 1 := by
            have := hghr_ndeg ▸ hg_natdeg; omega
          -- Define the Bézout vector w from (r, -q):
          --   w[j]   = r.coeff(n-1-j)       for j < n
          --   w[n+j] = (-q).coeff(m-1-j)    for j < m
          -- This yields A*f + B*g = r*(h*q) + (-q)*(h*r) = 0.
          let w : Fin (m + n) → k := fun ⟨i, _⟩ =>
            if h_i : i < n then r.coeff (n - 1 - i) else (-q).coeff (m - 1 - (i - n))
          have hw_r : ∀ j : Fin n, w ⟨(j : ℕ), by omega⟩ = r.coeff (n - 1 - (j : ℕ)) :=
            fun j => dif_pos j.isLt
          have hw_negq : ∀ j : Fin m,
              w ⟨n + (j : ℕ), by omega⟩ = (-q).coeff (m - 1 - (j : ℕ)) := by
            intro ⟨j, hj⟩
            simp only [w, show ¬ (n + j < n) from by omega, dif_neg, not_false_eq_true,
                       Nat.add_sub_cancel_left]
          -- A := ∑_{j<n} C(w[j]) * X^{n-1-j} = r  (since w[j]=r.coeff(n-1-j) and natDeg r ≤ n-1)
          have hA_eq_r : (∑ j : Fin n,
              Polynomial.C (w ⟨(j : ℕ), by omega⟩) * Polynomial.X ^ (n - 1 - (j : ℕ))) = r := by
            simp_rw [hw_r]
            apply Polynomial.ext; intro e
            have key := descPolyCoeff n (fun j : Fin n => r.coeff (n - 1 - (j : ℕ))) e
            rw [key]
            split_ifs with he
            · show r.coeff (n - 1 - (n - 1 - e)) = r.coeff e; congr 1; omega
            · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
          -- B := ∑_{j<m} C(w[n+j]) * X^{m-1-j} = -q  (natDeg q ≤ m-1)
          have hB_eq_negq : (∑ j : Fin m,
              Polynomial.C (w ⟨n + (j : ℕ), by omega⟩) * Polynomial.X ^ (m - 1 - (j : ℕ))) =
              -q := by
            simp_rw [hw_negq]
            apply Polynomial.ext; intro e
            have key := descPolyCoeff m (fun j : Fin m => (-q).coeff (m - 1 - (j : ℕ))) e
            rw [key]
            split_ifs with he
            · show (-q).coeff (m - 1 - (m - 1 - e)) = (-q).coeff e; congr 1; omega
            · simp only [Polynomial.coeff_neg]
              exact (neg_eq_zero.mpr (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))).symm
          -- A * f + B * g = r * f + (-q) * g = r*(h*q) + (-q)*(h*r) = 0
          have hAfBg : r * f + -q * g = 0 := by rw [hfhq, hghr]; ring
          -- Apply sylvester_vecMul_poly_eq: A*f + B*g = ∑_k C((w ᵥ* M)[k]) * X^{m+n-1-k}
          have hraw := sylvester_vecMul_poly_eq (R := k) m n hm hn f g hf_bound hg_bound w
          simp only [] at hraw
          rw [hA_eq_r, hB_eq_negq, hAfBg] at hraw
          -- hraw : 0 = ∑_k C((w ᵥ* M)[k]) * X^{m+n-1-k}
          -- Extract: (w ᵥ* M)[k] = 0 for all k, using descPolyCoeff
          have hvM_zero : w ᵥ* M = 0 := by
            funext ⟨k', hk'⟩
            have hcoeff := congr_arg
              (fun p : Polynomial k => p.coeff (m + n - 1 - k')) hraw.symm
            simp only [Polynomial.coeff_zero] at hcoeff
            have key2 :=
              descPolyCoeff (m + n)
                (fun k : Fin (m + n) => (w ᵥ* sylvesterMatrix m n f g) k)
                (m + n - 1 - k')
            rw [key2, dif_pos (by omega)] at hcoeff
            simp only [show m + n - 1 - (m + n - 1 - k') = k' from by omega] at hcoeff
            exact hcoeff
          -- w ≠ 0 since r ≠ 0 (r.coeff of some index is nonzero)
          have hw_ne : w ≠ 0 := by
            intro heq
            apply hr_ne
            ext e
            by_cases he : e < n
            · have hwe := congr_fun heq ⟨n - 1 - e, by omega⟩
              simp only [Pi.zero_apply] at hwe
              rw [hw_r ⟨n - 1 - e, by omega⟩] at hwe
              simpa [show n - 1 - (n - 1 - e) = e from by omega] using hwe
            · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          -- Conclude: det M = 0
          rw [← hM_def, ← Matrix.exists_vecMul_eq_zero_iff]
          exact ⟨w, hw_ne, hvM_zero⟩

-- ---------------------------------------------------------------------------
-- §5.2  The resultant as a function of the roots
-- ---------------------------------------------------------------------------

/-- Our `resultant` equals Mathlib's `Polynomial.resultant`.

    The two Sylvester matrix conventions differ by a transpose and reversal of
    indices: `Polynomial.sylvester f g m n = (sylvesterMatrix m n f g)ᵀ.submatrix rev rev`
    where `rev i = m+n-1-i`.  Transposing and applying the index permutation
    both preserve the determinant, so the determinants agree. -/
private lemma resultant_eq_polynomial_resultant (m n : ℕ) (f g : Polynomial k) :
    resultant m n f g = Polynomial.resultant f g m n := by
  simp only [resultant, Polynomial.resultant]
  -- The reversal involution on Fin (m+n)
  let rev : Fin (m + n) ≃ Fin (m + n) :=
    Function.Involutive.toPerm (fun i : Fin (m + n) => ⟨m + n - 1 - i.val, by omega⟩)
      (fun i => by ext; simp; omega)
  -- Key matrix equality: Polynomial.sylvester = (sylvesterMatrix)ᵀ.submatrix rev rev
  suffices h : Polynomial.sylvester f g m n =
      (sylvesterMatrix m n f g)ᵀ.submatrix rev rev by
    calc (sylvesterMatrix m n f g).det
        = ((sylvesterMatrix m n f g)ᵀ).det := (Matrix.det_transpose _).symm
      _ = (((sylvesterMatrix m n f g)ᵀ).submatrix rev rev).det :=
            (Matrix.det_submatrix_equiv_self _ _).symm
      _ = (Polynomial.sylvester f g m n).det := by rw [← h]
  ext ⟨i, hi⟩ j
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply,
             Polynomial.sylvester, Matrix.of_apply]
  simp only [rev, Function.Involutive.toPerm, Equiv.coe_fn_mk]
  induction j using Fin.addCases with
  | left j =>
    -- Column j.val < m: g-block in sylvesterMatrix (row m+n-1-j.val ≥ n)
    simp only [Fin.addCases_left, Set.mem_Icc, Fin.val_castAdd, sylvesterMatrix]
    rw [if_neg (by omega : ¬ (m + n - 1 - j.val < n))]
    split_ifs with h1 h2
    · congr 1; omega
    · exfalso; push Not at h2; omega
    · exfalso; push Not at h1; omega
    · rfl
  | right j =>
    -- Column m+j.val ≥ m: f-block in sylvesterMatrix (row n-1-j.val < n)
    simp only [Fin.addCases_right, Set.mem_Icc, Fin.val_natAdd, sylvesterMatrix]
    rw [if_pos (by omega : m + n - 1 - (m + j.val) < n)]
    split_ifs with h1 h2
    · congr 1; omega
    · exfalso; push Not at h2; omega
    · exfalso; push Not at h1; omega
    · rfl

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
  -- Step 1: Relate our resultant to Polynomial.resultant, then use map naturality
  rw [resultant_eq_polynomial_resultant]
  simp only [← Polynomial.resultant_map_map]
  -- Step 2: Substitute the factorizations of f.map φ and g.map φ
  rw [hf, hg]
  -- Step 3: Factor out leading coefficients using C-mul lemmas
  rw [Polynomial.resultant_C_mul_right, Polynomial.resultant_C_mul_left]
  -- Step 4: Expand the product over F' = ∏ i, (X - C (α i))
  set G' : L[X] := ∏ j : Fin n, (Polynomial.X - Polynomial.C (β j)) with hG'_def
  have hG'deg : G'.natDegree = n := by
    simp only [G']; rw [Polynomial.natDegree_prod_of_monic]; simp
    intro i _; exact Polynomial.monic_X_sub_C _
  have hF'deg : (∏ i : Fin m, (Polynomial.X - Polynomial.C (α i) : L[X])).natDegree = m := by
    rw [Polynomial.natDegree_prod_of_monic]; simp
    intro i _; exact Polynomial.monic_X_sub_C _
  have hprod := Polynomial.resultant_prod_left Finset.univ
      (fun i => Polynomial.X - Polynomial.C (α i)) G' n
      (by simp [Polynomial.leadingCoeff_X_sub_C]) hG'deg.le
  simp only [Polynomial.natDegree_X_sub_C] at hprod
  rw [hF'deg] at hprod
  rw [hprod]
  -- Step 5: Apply resultant_X_sub_C_left: (X - C (α i)).resultant G' 1 n = G'.eval (α i)
  simp only [Polynomial.resultant_X_sub_C_left G' n _ hG'deg.le]
  -- Step 6: Evaluate G' = ∏ j, (X - C (β j)) at α i
  have heval : ∀ i : Fin m, G'.eval (α i) = ∏ j : Fin n, (α i - β j) := fun i => by
    simp [G', Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  simp only [heval]
  ring

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
