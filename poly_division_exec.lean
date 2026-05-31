import Mathlib

/-!
# Executable Multivariate Polynomial Division

A runnable implementation of the multivariate division algorithm over ℚ
(Cox–Little–O'Shea §2.3, Hassett Thm 2.1.3).

## Representation
- **Exponent vectors** `Exp = List ℕ` — index `i` holds the exponent of variable `xᵢ`.
- **Terms** `Term` — a nonzero rational coefficient paired with an exponent vector.
- **Polynomials** `Poly = List Term` — terms in *strictly decreasing* graded-lex order,
  no zero-coefficient terms.

## Monomial order
Graded lex (grlex): compare total degrees first, then lex left-to-right.
-/

namespace ExecPolyDiv

/-! ### Exponent vectors -/

abbrev Exp := List ℕ

def expTotalDeg (e : Exp) : ℕ := e.sum

def expLexOrd : Exp → Exp → Ordering
  | [],      []      => .eq
  | _ :: _,  []      => .gt
  | [],      _ :: _  => .lt
  | a :: as, b :: bs =>
    if a < b then .lt else if b < a then .gt else expLexOrd as bs

/-- Graded-lex comparison. -/
def expCmp (a b : Exp) : Ordering :=
  let da := expTotalDeg a; let db := expTotalDeg b
  if da < db then .lt else if db < da then .gt else expLexOrd a b

def expBlt (a b : Exp) : Bool := expCmp a b == .lt

/-- `a` divides `b` pointwise: `a[i] ≤ b[i]` for all `i`. -/
def expDivides (a b : Exp) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => x ≤ y

/-- Monomial quotient `b - a` (assumes `expDivides a b`). -/
def expMdiv (b a : Exp) : Exp := b.zipWith (· - ·) a

/-- Monomial product `a + b`. -/
def expMmul (a b : Exp) : Exp := a.zipWith (· + ·) b

/-! ### Polynomial representation -/

structure Term where
  coeff : ℚ
  exp   : Exp
  deriving Repr, Inhabited

abbrev Poly := List Term

/-- Merge a single term into an accumulator, combining like exponents. -/
private def mergeTerm (acc : Poly) (t : Term) : Poly :=
  match acc.findIdx? (fun s => s.exp == t.exp) with
  | some i =>
    let c := acc[i]!.coeff + t.coeff
    if c == 0 then acc.eraseIdx i
    else acc.set i { acc[i]! with coeff := c }
  | none => t :: acc

/-- Insert into a decreasing-grlex-sorted list. -/
private def insertSorted (t : Term) : Poly → Poly
  | []      => [t]
  | h :: tl =>
    if expBlt h.exp t.exp then t :: h :: tl   -- t > h, so t goes first
    else h :: insertSorted t tl

/-- Combine like terms, drop zeros, and sort in decreasing grlex order. -/
def normalize (p : Poly) : Poly :=
  (p.foldl mergeTerm []).foldl (fun acc t => insertSorted t acc) []

/-! ### Arithmetic -/

def padd (p q : Poly) : Poly := normalize (p ++ q)
def pneg (p : Poly)   : Poly := p.map fun t => { t with coeff := -t.coeff }
def psub (p q : Poly) : Poly := padd p (pneg q)

/-- Multiply every term of `p` by the monomial term `t`. -/
def mulTerm (t : Term) (p : Poly) : Poly :=
  if t.coeff == 0 then []
  else normalize (p.map fun s =>
    { coeff := t.coeff * s.coeff, exp := expMmul t.exp s.exp })

def pmul (p q : Poly) : Poly := normalize (p.flatMap (mulTerm · q))

/-- Leading term of a normalised polynomial. -/
def leadingTerm? (p : Poly) : Option Term := p.head?

/-! ### Division algorithm -/

/-- One reduction step: if `LT(g)` divides `LT(f)`, subtract the appropriate multiple.
    Returns `(quotient_term, reduced_f)`. -/
def tryDivStep (f g : Poly) : Option (Term × Poly) := do
  let lf ← leadingTerm? f
  let lg ← leadingTerm? g
  guard (expDivides lg.exp lf.exp)
  let qt : Term := { coeff := lf.coeff / lg.coeff, exp := expMdiv lf.exp lg.exp }
  return (qt, psub f (mulTerm qt g))

/-! ### Termination infrastructure for `divAux`

The termination argument: at every recursive call the grlex rank of `LT(p)` strictly
decreases.  We represent the rank as a `ℕ × ℕ` pair

  `polyGrlexPair p = (expTotalDeg LT(p), expLexCode LT(p))`

ordered lexicographically.  `ℕ × ℕ` with `Prod.lt` already has a
`WellFoundedRelation` instance in Lean 4, so no additional proof of well-foundedness
is needed.

**Why `expLexCode` works for same-length exponents**: grlex restricts to lex within
a fixed total degree `d`.  For length-`n` lists summing to `d`, `expLexCode` evaluates
the list as a base-`(d+1)` numeral, which is strictly monotone w.r.t. lex (each
coefficient is ≤ d < d+1, so the most-significant digit dominates).

Note: grlex on *variable-length* `List ℕ` is **not** a well-order — the chain
`[4,1] >_grlex [4,0,1] >_grlex [4,0,0,1] > …` is infinite.  All exponent vectors
produced by this algorithm have the **same** length (operations `expMmul`/`expMdiv`
use `zipWith`, preserving length when both inputs share a length), so the same-length
restriction is satisfied in every actual execution.
-/

/-- Base-`(d+1)` lexicographic code of an exponent vector with total degree `d`.
    Evaluates the list as a numeral in base `expTotalDeg e + 1`.  Strictly monotone
    with respect to `expLexOrd` within same-length, same-sum lists. -/
private def expLexCode (e : Exp) : ℕ :=
  e.foldl (fun acc x => acc * (expTotalDeg e + 1) + x) 0

/-- Termination measure: `(total degree of LT(p), lex code of LT(p))`.
    Ordered lexicographically by `Prod.lt`; well-founded since both components are `ℕ`. -/
private def polyGrlexPair (p : Poly) : ℕ × ℕ :=
  match leadingTerm? p with
  | none   => (0, 0)
  | some t => (expTotalDeg t.exp + 1, expLexCode t.exp)

/-! ### `expLexCode` monotonicity infrastructure -/

/-- Evaluates `l` as a base-`B` numeral starting from accumulator `init`. -/
private def lexCodeFrom (B init : ℕ) (l : List ℕ) : ℕ :=
  l.foldl (fun acc x => acc * B + x) init

private lemma expLexCode_eq_from (e : Exp) :
    expLexCode e = lexCodeFrom (expTotalDeg e + 1) 0 e := rfl

private lemma lexCodeFrom_nil (B init : ℕ) : lexCodeFrom B init [] = init := rfl

private lemma lexCodeFrom_cons (B init h : ℕ) (t : List ℕ) :
    lexCodeFrom B init (h :: t) = lexCodeFrom B (init * B + h) t := rfl

/-- Split the initial accumulator out of a `lexCodeFrom` computation. -/
private lemma lexCodeFrom_split (B init : ℕ) (l : List ℕ) :
    lexCodeFrom B init l = init * B ^ l.length + lexCodeFrom B 0 l := by
  induction l generalizing init with
  | nil => simp [lexCodeFrom_nil]
  | cons h t ih =>
    rw [lexCodeFrom_cons, ih (init * B + h), lexCodeFrom_cons, ih (0 * B + h)]
    simp only [List.length_cons, pow_succ, Nat.zero_mul, Nat.zero_add]; ring

/-- `lexCodeFrom B 0 l < B ^ l.length` when every digit satisfies `< B`. -/
private lemma lexCodeFrom_lt_pow {B : ℕ} (hB : 0 < B) {l : List ℕ}
    (hel : ∀ x ∈ l, x < B) : lexCodeFrom B 0 l < B ^ l.length := by
  induction l with
  | nil => simp [lexCodeFrom_nil]
  | cons h t ih =>
    rw [lexCodeFrom_cons, lexCodeFrom_split]
    simp only [List.length_cons, pow_succ, Nat.zero_mul, Nat.zero_add]
    have hh : h < B := hel h (List.mem_cons.mpr (Or.inl rfl))
    have ht : ∀ x ∈ t, x < B := fun x hx => hel x (List.mem_cons.mpr (Or.inr hx))
    nlinarith [ih ht, pow_pos hB t.length, Nat.zero_le (lexCodeFrom B 0 t)]

private lemma nat_mem_le_sum {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left_of_le (ih ht)

/-- `lexCodeFrom` is strictly monotone w.r.t. `expLexOrd` for equal-length lists
    with bounded digits. -/
private lemma lexCodeFrom_strictMono {B : ℕ} (hB : 0 < B) {a b : List ℕ}
    (hlen : a.length = b.length) (hBa : ∀ x ∈ a, x < B) (hBb : ∀ x ∈ b, x < B)
    (hlex : expLexOrd a b = .lt) (init : ℕ) :
    lexCodeFrom B init a < lexCodeFrom B init b := by
  induction a generalizing b init with
  | nil =>
    cases b with
    | nil => simp [expLexOrd] at hlex
    | cons _ _ => simp at hlen
  | cons ha ta iha =>
    cases b with
    | nil => simp at hlen
    | cons hb tb =>
      rw [lexCodeFrom_cons, lexCodeFrom_cons]
      have hlen' : ta.length = tb.length := by simpa using hlen
      rcases Nat.lt_trichotomy ha hb with h | h | h
      · -- ha < hb: the most-significant digit already determines the order
        rw [lexCodeFrom_split B (init * B + ha) ta, lexCodeFrom_split B (init * B + hb) tb, ← hlen']
        have hca := lexCodeFrom_lt_pow hB (fun x hx => hBa x (List.mem_cons.mpr (Or.inr hx)))
        nlinarith [pow_pos hB ta.length, Nat.zero_le (lexCodeFrom B 0 tb)]
      · -- ha = hb: recurse on tails
        subst h
        have hlex' : expLexOrd ta tb = .lt := by
          simp only [expLexOrd, lt_irrefl, if_false] at hlex; exact hlex
        exact iha hlen'
          (fun x hx => hBa x (List.mem_cons.mpr (Or.inr hx)))
          (fun x hx => hBb x (List.mem_cons.mpr (Or.inr hx)))
          hlex' (init * B + ha)
      · -- ha > hb: expLexOrd returns .gt, contradicts hlex = .lt
        exfalso
        have hgt : expLexOrd (ha :: ta) (hb :: tb) = .gt := by
          simp only [expLexOrd, show ¬ha < hb from Nat.not_lt.mpr (Nat.le_of_lt h),
                     if_false, show hb < ha from h, if_true]
        rw [hgt] at hlex; exact absurd hlex (by decide)

/-- `expLexCode` is strictly monotone for equal-length, equal-sum exponent vectors. -/
private lemma expLexCode_strictMono {a b : Exp}
    (hlen : a.length = b.length) (hsum : expTotalDeg a = expTotalDeg b)
    (hlex : expLexOrd a b = .lt) : expLexCode a < expLexCode b := by
  rw [expLexCode_eq_from a, expLexCode_eq_from b, ← hsum]
  apply lexCodeFrom_strictMono (Nat.succ_pos _) hlen
  · intro x hx
    have hle : x ≤ expTotalDeg a := by simp only [expTotalDeg]; exact nat_mem_le_sum hx
    omega
  · intro x hx
    have hle : x ≤ b.sum := nat_mem_le_sum hx
    simp only [expTotalDeg] at hsum ⊢; omega
  · exact hlex

/-! ### Ordering lemmas needed for well-formedness proofs -/

private lemma expLexOrd_lt_trans {a b c : Exp}
    (hab : expLexOrd a b = .lt) (hbc : expLexOrd b c = .lt) : expLexOrd a c = .lt := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => simp [expLexOrd] at hab
    | cons _ _ => cases c with
      | nil => simp [expLexOrd] at hbc
      | cons _ _ => simp [expLexOrd]
  | cons ha ta iha =>
    cases b with
    | nil => simp [expLexOrd] at hab
    | cons hb tb =>
      cases c with
      | nil => simp [expLexOrd] at hbc
      | cons hc tc =>
        simp only [expLexOrd] at *
        rcases Nat.lt_trichotomy ha hb with h | h | h
        · simp only [h, if_true] at hab
          rcases Nat.lt_trichotomy hb hc with h2 | h2 | h2
          · simp only [show ha < hc from Nat.lt_trans h h2, if_true]
          · subst h2; simp only [h, if_true]
          · simp only [show ¬ hb < hc from Nat.not_lt.mpr (Nat.le_of_lt h2), if_false,
                       show hc < hb from h2, if_true] at hbc
            exact absurd hbc (by decide)
        · subst h; simp only [Nat.lt_irrefl, if_false] at hab hbc ⊢
          rcases Nat.lt_trichotomy ha hc with h2 | h2 | h2
          · simp only [h2, if_true]
          · subst h2; simp only [Nat.lt_irrefl, if_false] at hab hbc ⊢; exact iha hab hbc
          · simp only [show ¬ ha < hc from Nat.not_lt.mpr (Nat.le_of_lt h2), if_false,
                       show hc < ha from h2, if_true] at hbc
            exact absurd hbc (by decide)
        · simp only [show ¬ ha < hb from Nat.not_lt.mpr (Nat.le_of_lt h), if_false,
                     show hb < ha from h, if_true] at hab
          exact absurd hab (by decide)

private lemma expCmp_lt_trans {a b c : Exp}
    (hab : expCmp a b = .lt) (hbc : expCmp b c = .lt) : expCmp a c = .lt := by
  simp only [expCmp, expTotalDeg] at *
  split_ifs at hab hbc ⊢ with h1 h2 h3 h4 h5 h6 <;> simp_all <;> try omega
  exact expLexOrd_lt_trans hab hbc

private lemma expBlt_trans {a b c : Exp}
    (hab : expBlt a b = true) (hbc : expBlt b c = true) : expBlt a c = true := by
  simp only [expBlt, beq_iff_eq] at *; exact expCmp_lt_trans hab hbc

private lemma expLexOrd_eq_imp_eq {a b : Exp} (h : expLexOrd a b = .eq) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => simp [expLexOrd] at h
  | cons ha ta iha =>
    cases b with
    | nil => simp [expLexOrd] at h
    | cons hb tb =>
      simp only [expLexOrd] at h
      by_cases h1 : ha < hb
      · simp [h1] at h
      · by_cases h2 : hb < ha
        · simp [show ¬ ha < hb from h1, h2] at h
        · have heq : ha = hb := Nat.le_antisymm (Nat.le_of_not_lt h2) (Nat.le_of_not_lt h1)
          subst heq; simp [Nat.lt_irrefl] at h; exact congrArg (ha :: ·) (iha h)

private lemma expLexOrd_gt_iff_lt_swap {a b : Exp} :
    expLexOrd a b = .gt ↔ expLexOrd b a = .lt := by
  induction a generalizing b with
  | nil => cases b <;> simp [expLexOrd]
  | cons ha ta iha =>
    cases b with
    | nil => simp [expLexOrd]
    | cons hb tb =>
      simp only [expLexOrd]
      rcases Nat.lt_trichotomy ha hb with h | h | h
      · simp [h, show ¬ hb < ha from Nat.not_lt.mpr (Nat.le_of_lt h)]
      · subst h; simp [Nat.lt_irrefl, iha]
      · simp [show ¬ ha < hb from Nat.not_lt.mpr (Nat.le_of_lt h), h]

private lemma expCmp_gt_iff_lt_swap {a b : Exp} :
    expCmp a b = .gt ↔ expCmp b a = .lt := by
  unfold expCmp expTotalDeg
  by_cases h1 : a.sum < b.sum
  · have h2 : ¬ b.sum < a.sum := Nat.not_lt.mpr (Nat.le_of_lt h1)
    simp [h1, h2]
  · by_cases h2 : b.sum < a.sum
    · have h3 : ¬ a.sum < b.sum := h1
      simp [h3, h2]
    · have heq : a.sum = b.sum := by omega
      simp [h1, h2, expLexOrd_gt_iff_lt_swap]

/-! ### Well-formedness invariant for polynomials -/

/-- A polynomial is in canonical form: terms sorted in strictly-decreasing grlex order,
    all exponents distinct, all coefficients nonzero. -/
private def WellFormed : Poly → Prop
  | []       => True
  | h :: rest =>
    h.coeff ≠ 0 ∧
    (∀ s ∈ rest, s.exp.length = h.exp.length) ∧
    (∀ s ∈ rest, s.exp ≠ h.exp) ∧
    (∀ s ∈ rest, expCmp s.exp h.exp = .lt) ∧
    WellFormed rest

private lemma WellFormed.tail {h : Term} {t : Poly} (hw : WellFormed (h :: t)) :
    WellFormed t := hw.2.2.2.2

private lemma WellFormed.head_ne_zero {h : Term} {t : Poly} (hw : WellFormed (h :: t)) :
    h.coeff ≠ 0 := hw.1

private lemma WellFormed.head_exp_length {h : Term} {t : Poly} (hw : WellFormed (h :: t)) :
    ∀ s ∈ t, s.exp.length = h.exp.length := hw.2.1

private lemma WellFormed.head_exp_nodup {h : Term} {t : Poly} (hw : WellFormed (h :: t)) :
    ∀ s ∈ t, s.exp ≠ h.exp := hw.2.2.1

private lemma WellFormed.head_exp_max {h : Term} {t : Poly} (hw : WellFormed (h :: t)) :
    ∀ s ∈ t, expCmp s.exp h.exp = .lt := hw.2.2.2.1

private lemma WellFormed.all_coeff_ne_zero {p : Poly} (hw : WellFormed p) :
    ∀ t ∈ p, t.coeff ≠ 0 := by
  induction p with
  | nil => simp
  | cons h t ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hw.head_ne_zero
    · exact ih hw.tail s hs

private lemma WellFormed.pairwise_exp_ne {p : Poly} (hw : WellFormed p) :
    p.Pairwise (fun a b => a.exp ≠ b.exp) := by
  induction p with
  | nil => exact List.Pairwise.nil
  | cons h t ih =>
    rw [List.pairwise_cons]
    exact ⟨fun s hs => (hw.head_exp_nodup s hs).symm, ih hw.tail⟩

private lemma WellFormed.exp_length_eq {p : Poly} (hw : WellFormed p) :
    ∀ a ∈ p, ∀ b ∈ p, a.exp.length = b.exp.length := by
  induction p with
  | nil => simp
  | cons h t ih =>
    intro a ha b hb
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (hw.head_exp_length b hb).symm
    · exact hw.head_exp_length a ha
    · exact ih hw.tail a ha b hb

/-! ### `insertSorted` and `foldl mergeTerm` lemmas -/

private lemma mem_insertSorted {t : Term} {p : Poly} {s : Term} :
    s ∈ insertSorted t p ↔ s = t ∨ s ∈ p := by
  induction p with
  | nil => simp [insertSorted]
  | cons h rest ih =>
    simp only [insertSorted]
    by_cases hlt : expBlt h.exp t.exp = true
    · simp [hlt, List.mem_cons]
    · rw [if_neg hlt, List.mem_cons, ih, List.mem_cons]
      tauto

/-- When every element of `p` is grlex-smaller than `t`, inserting `t` prepends it. -/
private lemma insertSorted_of_all_lt {t : Term} {p : Poly}
    (hall : ∀ s ∈ p, expBlt s.exp t.exp = true) :
    insertSorted t p = t :: p := by
  cases p with
  | nil => simp [insertSorted]
  | cons h rest =>
    simp only [insertSorted, if_pos (hall h (List.mem_cons.mpr (Or.inl rfl)))]

/-- `insertSorted` preserves `WellFormed` when the inserted element has a fresh exponent
    and matching exponent length. -/
private lemma insertSorted_wf {t : Term} {p : Poly}
    (ht : t.coeff ≠ 0)
    (hp : WellFormed p)
    (hfresh : ∀ s ∈ p, s.exp ≠ t.exp)
    (hlen : ∀ s ∈ p, s.exp.length = t.exp.length) :
    WellFormed (insertSorted t p) := by
  match p with
  | [] => exact ⟨ht, fun s hs => absurd hs List.not_mem_nil,
                     fun s hs => absurd hs List.not_mem_nil,
                     fun s hs => absurd hs List.not_mem_nil, trivial⟩
  | h :: rest =>
    simp only [insertSorted]
    by_cases hlt : expBlt h.exp t.exp = true
    · simp only [hlt, if_true]
      have hh_lt : expCmp h.exp t.exp = .lt := by
        simp only [expBlt, beq_iff_eq] at hlt; exact hlt
      refine ⟨ht, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, hp⟩
      · exact hlen s hs
      · exact hfresh s hs
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact hh_lt
        · exact expCmp_lt_trans (hp.head_exp_max s hs) hh_lt
    · have hlt_f : expBlt h.exp t.exp = false := by
        revert hlt; cases expBlt h.exp t.exp <;> simp
      simp only [hlt_f, if_false]
      have hins := insertSorted_wf ht hp.tail
        (fun s hs => hfresh s (List.mem_cons.mpr (Or.inr hs)))
        (fun s hs => hlen s (List.mem_cons.mpr (Or.inr hs)))
      have hne : t.exp ≠ h.exp :=
        fun heq => hfresh h (List.mem_cons.mpr (Or.inl rfl)) heq.symm
      refine ⟨hp.head_ne_zero, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, hins⟩
      · rw [mem_insertSorted] at hs
        rcases hs with rfl | hs
        · exact (hlen h (List.mem_cons.mpr (Or.inl rfl))).symm
        · exact hp.head_exp_length s hs
      · rw [mem_insertSorted] at hs
        rcases hs with rfl | hs
        · exact hne
        · exact hp.head_exp_nodup s hs
      · rw [mem_insertSorted] at hs
        rcases hs with hs | hs
        · -- hs : s = t; rewrite s.exp → t.exp without substituting t
          simp only [hs, ← expCmp_gt_iff_lt_swap]
          have hne_lt : expCmp h.exp t.exp ≠ .lt := by
            simp only [expBlt, beq_eq_false_iff_ne] at hlt_f; exact hlt_f
          have hne_eq : expCmp h.exp t.exp ≠ .eq := by
            intro heq
            simp only [expCmp, expTotalDeg] at heq
            by_cases h1 : h.exp.sum < t.exp.sum
            · simp only [h1, ↓reduceIte] at heq; exact absurd heq (by decide)
            · simp only [show ¬ h.exp.sum < t.exp.sum from h1, if_false] at heq
              by_cases h2 : t.exp.sum < h.exp.sum
              · simp only [h2, ↓reduceIte] at heq; exact absurd heq (by decide)
              · simp only [show ¬ t.exp.sum < h.exp.sum from h2, if_false] at heq
                exact hne (expLexOrd_eq_imp_eq heq).symm
          rcases hcmp : expCmp h.exp t.exp with _ | _ | _
          · exact absurd hcmp hne_lt
          · exact absurd hcmp hne_eq
          · rfl
        · exact hp.head_exp_max s hs

/-- `foldl insertSorted []` of a reversed `WellFormed` polynomial recovers the original. -/
private lemma foldl_insertSorted_reverse_wf {p : Poly} (hw : WellFormed p) :
    p.reverse.foldl (fun acc t => insertSorted t acc) [] = p := by
  induction p with
  | nil => simp
  | cons h t ih =>
    rw [List.reverse_cons, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih hw.tail]
    exact insertSorted_of_all_lt (fun s hs => by
      simp only [expBlt, beq_iff_eq]; exact hw.head_exp_max s hs)

private lemma findIdx?_go_eq_none_aux {α : Type*} {p : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = false) (i : ℕ) : List.findIdx?.go p l i = none := by
  induction l generalizing i with
  | nil => rfl
  | cons hd tl ih =>
    unfold List.findIdx?.go
    simp [h hd (List.mem_cons.mpr (Or.inl rfl)),
          ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

private lemma findIdx?_eq_none_aux {α : Type*} {p : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = false) : l.findIdx? p = none := by
  simp only [List.findIdx?]
  exact findIdx?_go_eq_none_aux h 0

/-- When all exponents in `l` are fresh w.r.t. `acc` and pairwise distinct,
    `foldl mergeTerm acc l = l.reverse ++ acc`. -/
private lemma foldl_mergeTerm_fresh {acc l : Poly}
    (hdisjoint : ∀ s ∈ l, ∀ a ∈ acc, s.exp ≠ a.exp)
    (hnodup : l.Pairwise (fun a b => a.exp ≠ b.exp)) :
    l.foldl mergeTerm acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    have h_fresh : ∀ a ∈ acc, h.exp ≠ a.exp :=
      fun a ha => hdisjoint h (List.mem_cons.mpr (Or.inl rfl)) a ha
    have hmt : mergeTerm acc h = h :: acc := by
      simp only [mergeTerm]
      have hno : acc.findIdx? (fun s => s.exp == h.exp) = none :=
        findIdx?_eq_none_aux (fun a ha => beq_eq_false_iff_ne.mpr (h_fresh a ha).symm)
      simp [hno]
    rw [hmt, ih]
    · simp [List.reverse_cons, List.append_assoc]
    · intro s hs a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ((List.pairwise_cons.mp hnodup).1 s hs).symm
      · exact hdisjoint s (List.mem_cons.mpr (Or.inr hs)) a ha
    · exact (List.pairwise_cons.mp hnodup).2

/-- `foldl mergeTerm []` of a `WellFormed` polynomial gives the reverse. -/
private lemma foldl_mergeTerm_wf_rev {p : Poly} (hw : WellFormed p) :
    p.foldl mergeTerm [] = p.reverse := by
  cases p with
  | nil => simp [mergeTerm]
  | cons h t =>
    simp only [List.foldl_cons]
    have hmt : mergeTerm [] h = [h] := by simp [mergeTerm]
    rw [hmt, foldl_mergeTerm_fresh]
    · simp [List.reverse_cons]
    · intro s hs a ha
      simp only [List.mem_singleton] at ha; subst ha
      exact hw.head_exp_nodup s hs
    · exact hw.pairwise_exp_ne.tail

/-- If `findIdx?.go` returns none, all elements fail the predicate (converse of `findIdx?_go_eq_none_aux`). -/
private lemma findIdx?_go_none_all_false {α : Type*} {p : α → Bool} {l : List α} {n : ℕ}
    (hnone : List.findIdx?.go p l n = none) : ∀ x ∈ l, p x = false := by
  induction l generalizing n with
  | nil => simp
  | cons hd tl ih =>
    intro x hx
    have hphd : p hd = false := by
      by_contra h
      simp only [ne_eq, Bool.not_eq_false] at h
      exact absurd hnone (by simp [List.findIdx?.go, h])
    have hnone' : List.findIdx?.go p tl (n + 1) = none := by
      simpa [List.findIdx?.go, hphd] using hnone
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hphd
    · exact ih hnone' x hx

private lemma findIdx?_none_all_false {α : Type*} {p : α → Bool} {l : List α}
    (hnone : l.findIdx? p = none) : ∀ x ∈ l, p x = false := by
  simp only [List.findIdx?] at hnone; exact findIdx?_go_none_all_false hnone

/-- Setting only the coefficient of an element doesn't change the exponent map. -/
private lemma map_exp_set_coeff (acc : Poly) (i : ℕ) (c : ℚ) :
    (acc.set i { acc[i]! with coeff := c }).map (·.exp) = acc.map (·.exp) := by
  induction acc generalizing i with
  | nil => simp
  | cons h t ih =>
    cases i with
    | zero => rfl
    | succ n =>
      show h.exp :: (t.set n { t[n]! with coeff := c }).map (·.exp) = h.exp :: t.map (·.exp)
      exact congrArg (h.exp :: ·) (ih n)

/-- A universal property is preserved by `List.set` when the replacement also satisfies it. -/
private lemma forall_mem_set {α : Type*} {l : List α} {i : ℕ} {a : α} {p : α → Prop}
    (hl : ∀ x ∈ l, p x) (ha : p a) : ∀ x ∈ l.set i a, p x := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    intro x hx
    cases i with
    | zero =>
      simp only [List.set, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact hl x (List.mem_cons.mpr (Or.inr hx))
    | succ n =>
      simp only [List.set, List.mem_cons] at hx
      rcases hx with rfl | hx
      · apply hl; exact List.mem_cons.mpr (Or.inl rfl)
      · exact ih (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx))) x hx

/-- Pairwise exp-distinctness is preserved by a coeff-only `set`. -/
private lemma pairwise_ne_set_coeff {acc : Poly} {i : ℕ} {c : ℚ}
    (hacc : acc.Pairwise (fun a b => a.exp ≠ b.exp)) :
    (acc.set i { acc[i]! with coeff := c }).Pairwise (fun a b => a.exp ≠ b.exp) := by
  induction acc generalizing i with
  | nil => simp
  | cons h t ih =>
    cases i with
    | zero =>
      simp only [List.set]
      exact List.Pairwise.cons (List.pairwise_cons.mp hacc).1 (List.pairwise_cons.mp hacc).2
    | succ n =>
      simp only [List.set]
      refine List.Pairwise.cons (fun s hs heq => ?_) (ih (List.pairwise_cons.mp hacc).2)
      have hmem : s.exp ∈ (t.set n { t[n]! with coeff := c }).map (·.exp) :=
        List.mem_map.mpr ⟨s, hs, rfl⟩
      rw [map_exp_set_coeff] at hmem
      obtain ⟨a, ha, ha_eq⟩ := List.mem_map.mp hmem
      exact (List.pairwise_cons.mp hacc).1 a ha (heq.trans ha_eq.symm)

/-- Pairwise exp-distinctness is preserved by a single `mergeTerm` step. -/
private lemma mergeTerm_pairwise_ne {acc : Poly} {t : Term}
    (hacc : acc.Pairwise (fun a b => a.exp ≠ b.exp)) :
    (mergeTerm acc t).Pairwise (fun a b => a.exp ≠ b.exp) := by
  simp only [mergeTerm]
  split
  · rename_i i
    split
    · exact hacc.sublist (List.eraseIdx_sublist _ _)
    · rename_i c _; exact pairwise_ne_set_coeff hacc
  · rename_i hnone
    refine List.Pairwise.cons (fun s hs heq => ?_) hacc
    have hall := findIdx?_none_all_false hnone s hs
    simp [heq.symm] at hall

/-- Pairwise exp-distinctness is maintained across `foldl mergeTerm`. -/
private lemma foldl_mergeTerm_pairwise_ne {acc l : Poly}
    (hacc : acc.Pairwise (fun a b => a.exp ≠ b.exp)) :
    (l.foldl mergeTerm acc).Pairwise (fun a b => a.exp ≠ b.exp) := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons h t ih => exact ih (mergeTerm_pairwise_ne hacc)

/-- Nonzero coefficients are maintained by a single `mergeTerm` step. -/
private lemma mergeTerm_coeff_ne {acc : Poly} {t : Term}
    (hacc : ∀ s ∈ acc, s.coeff ≠ 0) (ht : t.coeff ≠ 0) :
    ∀ s ∈ mergeTerm acc t, s.coeff ≠ 0 := by
  simp only [mergeTerm]
  split
  · rename_i i
    split
    · intro s hs; exact hacc s (List.mem_of_mem_eraseIdx hs)
    · rename_i c hc; exact forall_mem_set hacc (by simpa using hc)
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ht
    · exact hacc s hs

/-- Nonzero coefficients are maintained across `foldl mergeTerm`. -/
private lemma foldl_mergeTerm_coeff_ne {acc l : Poly}
    (hacc : ∀ s ∈ acc, s.coeff ≠ 0) (hl : ∀ s ∈ l, s.coeff ≠ 0) :
    ∀ s ∈ l.foldl mergeTerm acc, s.coeff ≠ 0 := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons h t ih =>
    exact ih (mergeTerm_coeff_ne hacc (hl h (List.mem_cons.mpr (Or.inl rfl))))
              (fun s hs => hl s (List.mem_cons.mpr (Or.inr hs)))

/-- Exp lengths are maintained by a single `mergeTerm` step. -/
private lemma mergeTerm_exp_len {acc : Poly} {t : Term} {n : ℕ}
    (hacc : ∀ s ∈ acc, s.exp.length = n) (ht : t.exp.length = n) :
    ∀ s ∈ mergeTerm acc t, s.exp.length = n := by
  intro s hs
  simp only [mergeTerm] at hs
  cases h_find : acc.findIdx? (fun x => x.exp == t.exp) with
  | none =>
    simp only [h_find] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ht
    · exact hacc s hs
  | some i =>
    simp only [h_find] at hs
    split_ifs at hs with h_zero
    · exact hacc s (List.mem_of_mem_eraseIdx hs)
    · have hmem : s.exp ∈ acc.map (·.exp) := by
        have : s.exp ∈ (acc.set i _).map (·.exp) := List.mem_map.mpr ⟨s, hs, rfl⟩
        rwa [map_exp_set_coeff] at this
      obtain ⟨a, ha, ha_eq⟩ := List.mem_map.mp hmem
      exact ha_eq ▸ hacc a ha

/-- Exp lengths are maintained across `foldl mergeTerm`. -/
private lemma foldl_mergeTerm_exp_len {acc l : Poly} {n : ℕ}
    (hacc : ∀ s ∈ acc, s.exp.length = n) (hl : ∀ s ∈ l, s.exp.length = n) :
    ∀ s ∈ l.foldl mergeTerm acc, s.exp.length = n := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons h t ih =>
    exact ih (mergeTerm_exp_len hacc (hl h (List.mem_cons.mpr (Or.inl rfl))))
              (fun s hs => hl s (List.mem_cons.mpr (Or.inr hs)))

/-- `foldl insertSorted` with generalized accumulator: inserts fresh, same-length,
    nonzero-coeff, pairwise-distinct elements into a WF list, producing a WF list. -/
private lemma foldl_insertSorted_wf_aux {acc q : Poly}
    (hacc : WellFormed acc)
    (hcoeff : ∀ t ∈ q, t.coeff ≠ 0)
    (hfresh : ∀ t ∈ q, ∀ s ∈ acc, t.exp ≠ s.exp)
    (hlen_qa : ∀ t ∈ q, ∀ s ∈ acc, t.exp.length = s.exp.length)
    (hlen_qq : ∀ a ∈ q, ∀ b ∈ q, a.exp.length = b.exp.length)
    (hne : q.Pairwise (fun a b => a.exp ≠ b.exp)) :
    WellFormed (q.foldl (fun acc t => insertSorted t acc) acc) := by
  induction q generalizing acc with
  | nil => exact hacc
  | cons h t ih =>
    simp only [List.foldl_cons]
    have h_ins_wf : WellFormed (insertSorted h acc) := insertSorted_wf
      (hcoeff h (List.mem_cons.mpr (Or.inl rfl))) hacc
      (fun s hs => (hfresh h (List.mem_cons.mpr (Or.inl rfl)) s hs).symm)
      (fun s hs => (hlen_qa h (List.mem_cons.mpr (Or.inl rfl)) s hs).symm)
    apply ih h_ins_wf
    · exact fun x hx => hcoeff x (List.mem_cons.mpr (Or.inr hx))
    · intro x hx s hs
      rw [mem_insertSorted] at hs
      rcases hs with heq | hs
      · rw [heq]; exact ((List.pairwise_cons.mp hne).1 x hx).symm
      · exact hfresh x (List.mem_cons.mpr (Or.inr hx)) s hs
    · intro x hx s hs
      rw [mem_insertSorted] at hs
      rcases hs with heq | hs
      · rw [heq]; exact hlen_qq x (List.mem_cons.mpr (Or.inr hx)) h (List.mem_cons.mpr (Or.inl rfl))
      · exact hlen_qa x (List.mem_cons.mpr (Or.inr hx)) s hs
    · intro a ha b hb
      exact hlen_qq a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb))
    · exact (List.pairwise_cons.mp hne).2

/-- `normalize` is the identity on `WellFormed` polynomials. -/
private lemma normalize_wf_id {p : Poly} (hw : WellFormed p) : normalize p = p := by
  unfold normalize
  rw [foldl_mergeTerm_wf_rev hw, foldl_insertSorted_reverse_wf hw]

/-- The output of `normalize` is `WellFormed` when the input has nonzero coefficients
    and uniform exponent length. -/
private lemma normalize_wf (p : Poly)
    (hcoeff : ∀ t ∈ p, t.coeff ≠ 0)
    (hlen : ∀ a ∈ p, ∀ b ∈ p, a.exp.length = b.exp.length) :
    WellFormed (normalize p) := by
  unfold normalize
  have hq_coeff : ∀ t ∈ p.foldl mergeTerm [], t.coeff ≠ 0 :=
    foldl_mergeTerm_coeff_ne (by simp) hcoeff
  have hq_pairwise : (p.foldl mergeTerm []).Pairwise (fun a b => a.exp ≠ b.exp) :=
    foldl_mergeTerm_pairwise_ne List.Pairwise.nil
  have hq_len : ∀ a ∈ p.foldl mergeTerm [], ∀ b ∈ p.foldl mergeTerm [], a.exp.length = b.exp.length := by
    cases p with
    | nil => simp
    | cons h t =>
      have hfix : ∀ s ∈ (h :: t).foldl mergeTerm [], s.exp.length = h.exp.length :=
        foldl_mergeTerm_exp_len (by simp) (fun s hs => hlen s hs h (List.mem_cons.mpr (Or.inl rfl)))
      exact fun a ha b hb => (hfix a ha).trans (hfix b hb).symm
  exact foldl_insertSorted_wf_aux (hacc := trivial) hq_coeff
    (fun _ _ _ hs => by simp at hs)
    (fun _ _ _ hs => by simp at hs)
    hq_len hq_pairwise

/-- `normalize` is idempotent when the input has nonzero coefficients and uniform exp length. -/
private lemma normalize_idempotent (p : Poly)
    (hcoeff : ∀ t ∈ p, t.coeff ≠ 0)
    (hlen : ∀ a ∈ p, ∀ b ∈ p, a.exp.length = b.exp.length) :
    normalize (normalize p) = normalize p :=
  normalize_wf_id (normalize_wf p hcoeff hlen)

/-- `psub p q` is WF when both inputs are WF and have the same exponent length. -/
private lemma psub_wf_of_wf {p q : Poly} (hwp : WellFormed p) (hwq : WellFormed q)
    (hlen : ∀ a ∈ p, ∀ b ∈ q, a.exp.length = b.exp.length) :
    WellFormed (psub p q) := by
  simp only [psub, padd]
  apply normalize_wf
  · intro t ht
    simp only [List.mem_append, pneg, List.mem_map] at ht
    rcases ht with ht | ⟨s, hs, rfl⟩
    · exact hwp.all_coeff_ne_zero t ht
    · exact neg_ne_zero.mpr (hwq.all_coeff_ne_zero s hs)
  · intro a ha b hb
    simp only [List.mem_append, pneg, List.mem_map] at ha hb
    rcases ha with ha | ⟨sa, hsa, rfl⟩ <;> rcases hb with hb | ⟨sb, hsb, rfl⟩
    · exact hwp.exp_length_eq a ha b hb
    · exact hlen a ha sb hsb
    · exact (hlen b hb sa hsa).symm
    · exact hwq.exp_length_eq sa hsa sb hsb

/-! ### Head-cancellation lemma: `psub (lt :: rest) [lt] = rest` -/

private lemma findIdx?_eq_none_of_mem_false {α : Type*} {p : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = false) : l.findIdx? p = none :=
  findIdx?_eq_none_aux h

private lemma findIdx?_go_append_last {α : Type*} {p : α → Bool} (x : α)
    (hx : p x = true) : ∀ (l : List α), (∀ s ∈ l, p s = false) →
    ∀ (i : ℕ), List.findIdx?.go p (l ++ [x]) i = some (i + l.length) := by
  intro l hnone
  induction l with
  | nil => intro i; simp only [List.nil_append, List.length_nil, Nat.add_zero]
           unfold List.findIdx?.go; simp [hx]
  | cons hd tl ih =>
    intro i
    simp only [List.cons_append, List.length_cons]
    unfold List.findIdx?.go
    have hd_false : p hd = false := hnone hd (List.mem_cons.mpr (Or.inl rfl))
    simp only [hd_false, Bool.false_eq_true, ↓reduceIte]
    rw [ih (fun s hs => hnone s (List.mem_cons.mpr (Or.inr hs))) (i + 1)]
    congr 1; omega

private lemma findIdx?_append_last {α : Type*} {p : α → Bool} {l : List α} {x : α}
    (hnone : ∀ s ∈ l, p s = false) (hx : p x = true) :
    (l ++ [x]).findIdx? p = some l.length := by
  simp only [List.findIdx?]
  rw [findIdx?_go_append_last x hx l hnone 0]
  simp

private lemma eraseIdx_append_last {α : Type*} (l : List α) (x : α) :
    (l ++ [x]).eraseIdx l.length = l := by
  induction l with
  | nil => simp [List.eraseIdx]
  | cons h t ih => simp [List.eraseIdx, ih]

private lemma getElem!_append_last (l : List Term) (x : Term) :
    (l ++ [x])[l.length]! = x := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

private lemma mergeTerm_cancel {t : Term} (l : List Term)
    (hfresh : ∀ s ∈ l, s.exp ≠ t.exp) :
    mergeTerm (l ++ [t]) { t with coeff := -t.coeff } = l := by
  simp only [mergeTerm]
  rw [show (l ++ [t]).findIdx? (fun s => s.exp == t.exp) = some l.length from
    findIdx?_append_last
      (fun s hs => beq_eq_false_iff_ne.mpr (hfresh s hs))
      (beq_self_eq_true _)]
  simp only
  have hget : (l ++ [t])[l.length]! = t := getElem!_append_last l t
  simp only [hget, add_neg_cancel, beq_self_eq_true, ↓reduceIte]
  exact eraseIdx_append_last l t

/-- When `p` is `WellFormed` with head `lt`, subtracting `[lt]` yields `p.tail`. -/
private lemma psub_head_cancel {p : Poly} {lt : Term}
    (hhead : p.head? = some lt) (hw : WellFormed p) :
    psub p [lt] = p.tail := by
  obtain ⟨rest, rfl⟩ : ∃ rest, p = lt :: rest := by
    cases p with
    | nil => simp at hhead
    | cons h t => exact ⟨t, by simp at hhead; subst hhead; rfl⟩
  -- psub (lt :: rest) [lt] = normalize ((lt :: rest) ++ pneg [lt])
  --                        = normalize ((lt :: rest) ++ [{coeff := -lt.coeff, exp := lt.exp}])
  simp only [psub, padd, pneg, List.map]
  -- After foldl mergeTerm: lt and its negation cancel → result is rest.reverse
  -- After foldl insertSorted: rest.reverse → rest (since rest is WF)
  unfold normalize
  have hfresh_rest : ∀ s ∈ rest, ∀ a ∈ ([lt] : Poly), s.exp ≠ a.exp :=
    fun s hs a ha => by
      simp only [List.mem_singleton] at ha; subst ha
      exact hw.head_exp_nodup s hs
  -- Step 1: foldl mergeTerm [] ((lt :: rest) ++ [{coeff := -lt.coeff, exp := lt.exp}])
  -- = foldl mergeTerm [lt] (rest ++ [{coeff := -lt.coeff, exp := lt.exp}])
  -- After processing rest (all fresh w.r.t. [lt] and each other): rest.reverse ++ [lt]
  -- After processing neg_lt: lt cancels → rest.reverse
  have hstep1 : ((lt :: rest) ++ [{ lt with coeff := -lt.coeff }]).foldl mergeTerm [] =
      rest.reverse := by
    rw [List.cons_append, List.foldl_cons]
    -- mergeTerm [] lt = [lt]
    have hmt_lt : mergeTerm [] lt = [lt] := by simp [mergeTerm]
    rw [hmt_lt]
    -- foldl mergeTerm [lt] (rest ++ [neg_lt])
    rw [List.foldl_append]
    -- foldl mergeTerm [lt] rest = rest.reverse ++ [lt]  (all fresh)
    rw [foldl_mergeTerm_fresh (acc := [lt]) (l := rest)]
    · -- mergeTerm (rest.reverse ++ [lt]) neg_lt = rest.reverse
      simp only [List.foldl_cons, List.foldl_nil]
      exact mergeTerm_cancel rest.reverse (fun s hs => by
        rw [List.mem_reverse] at hs
        exact hw.head_exp_nodup s hs)
    · exact hfresh_rest
    · exact hw.tail.pairwise_exp_ne
  rw [hstep1, foldl_insertSorted_reverse_wf hw.tail]
  rfl

/-- `psub p [lt]` is WF when `lt = LT(p)` and `p` is WF. -/
private lemma psub_head_wf {p : Poly} {lt : Term}
    (h : p.head? = some lt) (hw : WellFormed p) : WellFormed (psub p [lt]) := by
  cases p with
  | nil => simp at h
  | cons hd tl =>
    rw [psub_head_cancel h hw]
    exact hw.tail

/-- The length of `expMdiv b a` equals `b.length` when `expDivides a b`. -/
private lemma expMdiv_length {a b : Exp} (hdiv : expDivides a b = true) :
    (expMdiv b a).length = b.length := by
  simp only [expDivides, Bool.and_eq_true, beq_iff_eq] at hdiv
  simp only [expMdiv, List.length_zipWith]; omega

/-- The length of `expMmul a b` equals `a.length` when lengths match. -/
private lemma expMmul_length_eq {a b : Exp} (h : a.length = b.length) :
    (expMmul a b).length = a.length := by
  simp only [expMmul, List.length_zipWith]; omega

/-- `mulTerm qt g` is WF when `g` is WF and `qt.coeff ≠ 0`. -/
private lemma mulTerm_wf {qt : Term} {g : Poly} (hw : WellFormed g) (hqt : qt.coeff ≠ 0) :
    WellFormed (mulTerm qt g) := by
  simp only [mulTerm, beq_iff_eq, ne_eq, hqt, not_false_eq_true, ↓reduceIte]
  apply normalize_wf
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact mul_ne_zero hqt (hw.all_coeff_ne_zero s hs)
  · intro a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨sa, hsa, rfl⟩ := ha
    obtain ⟨sb, hsb, rfl⟩ := hb
    have := hw.exp_length_eq sa hsa sb hsb
    simp only [expMmul, List.length_zipWith]; omega

/-- Exps in `mergeTerm acc t` come from `acc` or `t.exp`. -/
private lemma mergeTerm_exp_mem {acc : Poly} {t s : Term}
    (hs : s ∈ mergeTerm acc t) : (∃ a ∈ acc, a.exp = s.exp) ∨ s.exp = t.exp := by
  simp only [mergeTerm] at hs
  cases h_find : acc.findIdx? (fun x => x.exp == t.exp) with
  | none =>
    simp only [h_find] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Or.inr rfl
    · exact Or.inl ⟨s, hs, rfl⟩
  | some i =>
    simp only [h_find] at hs
    split_ifs at hs with h_zero
    · exact Or.inl ⟨s, List.mem_of_mem_eraseIdx hs, rfl⟩
    · have hmem : s.exp ∈ (acc.set i _).map (·.exp) := List.mem_map.mpr ⟨s, hs, rfl⟩
      rw [map_exp_set_coeff] at hmem
      obtain ⟨a, ha, ha_eq⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨a, ha, ha_eq⟩

/-- Exps in `l.foldl mergeTerm acc` come from `acc` or `l`. -/
private lemma foldl_mergeTerm_exp_mem {acc l : Poly} {t : Term}
    (ht : t ∈ l.foldl mergeTerm acc) :
    (∃ s ∈ acc, s.exp = t.exp) ∨ (∃ s ∈ l, s.exp = t.exp) := by
  induction l generalizing acc with
  | nil => exact Or.inl ⟨t, ht, rfl⟩
  | cons h rest ih =>
    simp only [List.foldl_cons] at ht
    rcases ih ht with ⟨s, hs, heq_st⟩ | ⟨s, hs, heq_st⟩
    · rcases mergeTerm_exp_mem hs with ⟨a, ha, heq_sa⟩ | heq_sh
      · exact Or.inl ⟨a, ha, heq_sa.trans heq_st⟩
      · exact Or.inr ⟨h, List.mem_cons.mpr (Or.inl rfl), heq_sh.symm.trans heq_st⟩
    · exact Or.inr ⟨s, List.mem_cons.mpr (Or.inr hs), heq_st⟩

/-- Exps in `q.foldl (insertSorted ·) acc` come from `acc` or `q`. -/
private lemma foldl_insertSorted_exp_mem_aux {acc q : Poly} {t : Term}
    (ht : t ∈ q.foldl (fun acc x => insertSorted x acc) acc) :
    (∃ s ∈ acc, s.exp = t.exp) ∨ (∃ s ∈ q, s.exp = t.exp) := by
  induction q generalizing acc with
  | nil => exact Or.inl ⟨t, ht, rfl⟩
  | cons qh rest ih =>
    simp only [List.foldl_cons] at ht
    rcases ih ht with ⟨s, hs, heq_exp⟩ | ⟨s, hs, heq_exp⟩
    · rw [mem_insertSorted] at hs
      rcases hs with heq_s | hs
      · exact Or.inr ⟨s, by rw [heq_s]; exact List.mem_cons.mpr (Or.inl rfl), heq_exp⟩
      · exact Or.inl ⟨s, hs, heq_exp⟩
    · exact Or.inr ⟨s, List.mem_cons.mpr (Or.inr hs), heq_exp⟩

/-- Exps in `normalize l` come from `l`. -/
private lemma normalize_exp_mem {l : Poly} {t : Term} (ht : t ∈ normalize l) :
    ∃ s ∈ l, s.exp = t.exp := by
  unfold normalize at ht
  rcases foldl_insertSorted_exp_mem_aux ht with ⟨_, h, _⟩ | ⟨s, hs, heq⟩
  · simp at h
  · rcases (foldl_mergeTerm_exp_mem hs).resolve_left
        (fun ⟨_, h, _⟩ => by simp at h) with ⟨a, ha, heq'⟩
    exact ⟨a, ha, heq'.trans heq⟩

/-! ### Sub-lemmas for `psub_mulTerm_lt` -/

private lemma expTotalDeg_expMmul {a b : Exp} (h : a.length = b.length) :
    expTotalDeg (expMmul a b) = expTotalDeg a + expTotalDeg b := by
  simp only [expTotalDeg, expMmul]
  induction a generalizing b with
  | nil => cases b with | nil => simp | cons _ _ => simp at h
  | cons a0 a' ih =>
    cases b with
    | nil => simp at h
    | cons b0 b' =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have := ih (Nat.succ_injective h); omega

private lemma expLexOrd_expMmul_left {c a b : Exp}
    (hca : c.length = a.length) (hab : a.length = b.length) :
    expLexOrd (expMmul c a) (expMmul c b) = expLexOrd a b := by
  simp only [expMmul]
  induction c generalizing a b with
  | nil =>
    cases a with
    | nil => cases b with | nil => simp [expLexOrd] | cons _ _ => simp at hab
    | cons _ _ => simp at hca
  | cons c0 c' ih =>
    cases a with | nil => simp at hca | cons a0 a' =>
    cases b with | nil => simp at hab | cons b0 b' =>
    simp only [List.zipWith_cons_cons, expLexOrd]
    rcases Nat.lt_trichotomy a0 b0 with h | h | h
    · simp [show c0 + a0 < c0 + b0 from by omega, show ¬(c0+b0<c0+a0) from by omega,
            h, show ¬(b0<a0) from by omega]
    · subst h; simp [Nat.lt_irrefl]
      exact ih (Nat.succ_injective hca) (Nat.succ_injective hab)
    · simp [show ¬(c0+a0<c0+b0) from by omega, show c0+b0<c0+a0 from by omega,
            show ¬(a0<b0) from by omega, h]

private lemma expCmp_expMmul_left {c a b : Exp}
    (hca : c.length = a.length) (hab : a.length = b.length) :
    expCmp (expMmul c a) (expMmul c b) = expCmp a b := by
  simp only [expCmp, expTotalDeg_expMmul hca,
             expTotalDeg_expMmul (show c.length = b.length from by omega),
             Nat.add_lt_add_iff_left]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact expLexOrd_expMmul_left hca hab

private lemma expMdiv_cancel {a b : Exp} (hdiv : expDivides a b = true) :
    expMmul (expMdiv b a) a = b := by
  simp only [expDivides, Bool.and_eq_true, beq_iff_eq] at hdiv
  obtain ⟨hlen, hall⟩ := hdiv
  simp only [expMmul, expMdiv]
  induction a generalizing b with
  | nil => cases b with | nil => simp | cons _ _ => simp at hlen
  | cons a0 a' ih =>
    cases b with
    | nil => simp at hlen
    | cons b0 b' =>
      simp only [List.zipWith_cons_cons]
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
                 decide_eq_true_iff] at hall
      obtain ⟨h0, hall'⟩ := hall
      congr 1
      · exact Nat.sub_add_cancel h0
      · exact ih (Nat.succ_injective hlen) hall'

private lemma expCmp_self (a : Exp) : expCmp a a = .eq := by
  simp only [expCmp, lt_irrefl, if_false]
  induction a with
  | nil => simp [expLexOrd]
  | cons h t ih => simp [expLexOrd, lt_irrefl, ih]

private lemma mulTerm_map_wf {qt : Term} {g : Poly} (hwg : WellFormed g) (hqt : qt.coeff ≠ 0)
    (hlen : ∀ s ∈ g, qt.exp.length = s.exp.length) :
    WellFormed (g.map fun s => { coeff := qt.coeff * s.coeff, exp := expMmul qt.exp s.exp }) := by
  revert hwg hlen
  induction g with
  | nil => intros; simp [WellFormed]
  | cons h t ih =>
    intro hwg hlen
    simp only [List.map_cons]
    have hh_len : qt.exp.length = h.exp.length := hlen h (by simp)
    refine ⟨mul_ne_zero hqt hwg.head_ne_zero, ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_map] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      have hu_len : qt.exp.length = u.exp.length := hlen u (List.mem_cons.mpr (Or.inr hu))
      exact (expMmul_length_eq hu_len).trans (expMmul_length_eq hh_len).symm
    · intro s hs
      simp only [List.mem_map] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      intro heq
      have hu_len : qt.exp.length = u.exp.length := hlen u (List.mem_cons.mpr (Or.inr hu))
      have hcmp : expCmp (expMmul qt.exp u.exp) (expMmul qt.exp h.exp) = .lt := by
        rw [expCmp_expMmul_left hu_len (hu_len.symm.trans hh_len)]
        exact hwg.head_exp_max u hu
      have heq' : expMmul qt.exp u.exp = expMmul qt.exp h.exp := heq
      rw [heq', expCmp_self (expMmul qt.exp h.exp)] at hcmp
      exact absurd hcmp (by decide)
    · intro s hs
      simp only [List.mem_map] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      have hu_len : qt.exp.length = u.exp.length := hlen u (List.mem_cons.mpr (Or.inr hu))
      rw [expCmp_expMmul_left hu_len (hu_len.symm.trans hh_len)]
      exact hwg.head_exp_max u hu
    · apply ih hwg.tail
      intro s hs
      exact hlen s (List.mem_cons.mpr (Or.inr hs))

/-- The leading term of `mulTerm qt g` when `g` is WF with head `lg` and `qt.coeff ≠ 0`. -/
private lemma mulTerm_head {qt : Term} {g : Poly} {lg : Term}
    (hg : g.head? = some lg) (hqt : qt.coeff ≠ 0) (hwg : WellFormed g)
    (hlen : qt.exp.length = lg.exp.length) :
    (mulTerm qt g).head? = some { coeff := qt.coeff * lg.coeff, exp := expMmul qt.exp lg.exp } := by
  obtain ⟨g_tail, rfl⟩ : ∃ t, g = lg :: t := by
    cases g with | nil => simp at hg | cons h t => exact ⟨t, by simp at hg; subst hg; rfl⟩
  -- Compute that mulTerm qt g = normalize (g.map ...)
  have h_mt : mulTerm qt (lg :: g_tail) =
      normalize ((lg :: g_tail).map fun s =>
        { coeff := qt.coeff * s.coeff, exp := expMmul qt.exp s.exp }) := by
    simp only [mulTerm, ne_eq, beq_iff_eq, hqt, not_false_eq_true, ↓reduceIte]
  rw [h_mt, normalize_wf_id (mulTerm_map_wf hwg hqt (fun s hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hlen
    · exact hlen.trans (hwg.head_exp_length s hs).symm))]
  simp [List.map_cons]

/-- Cancelling the common leading term: psub (lf::f') (lf::g') = psub f' g'. -/
private lemma psub_head_head_cancel {lf : Term} {f_rest g_rest : Poly}
    (hwf : WellFormed (lf :: f_rest)) :
    psub (lf :: f_rest) (lf :: g_rest) = psub f_rest g_rest := by
  simp only [psub, padd, pneg, List.map, List.cons_append, normalize]
  -- foldl mergeTerm [] (lf :: f_rest ++ neg_lf :: pneg_rest)
  -- = foldl mergeTerm [lf] (f_rest ++ neg_lf :: pneg_rest)
  rw [show List.foldl mergeTerm [] (lf :: (f_rest ++ ({ lf with coeff := -lf.coeff } ::
      g_rest.map (fun t => { t with coeff := -t.coeff })))) =
      List.foldl mergeTerm f_rest.reverse
        (g_rest.map (fun t => { t with coeff := -t.coeff })) from by
    rw [List.foldl_cons]
    have hmt_lf : mergeTerm [] lf = [lf] := by simp [mergeTerm]
    rw [hmt_lf, List.foldl_append, List.foldl_cons]
    -- foldl mergeTerm [lf] f_rest = f_rest.reverse ++ [lf]
    rw [foldl_mergeTerm_fresh (acc := [lf]) (l := f_rest)
      (fun s hs a ha => by simp only [List.mem_singleton] at ha; subst ha;
                           exact hwf.head_exp_nodup s hs)
      hwf.tail.pairwise_exp_ne]
    -- mergeTerm (f_rest.reverse ++ [lf]) neg_lf = f_rest.reverse
    rw [mergeTerm_cancel f_rest.reverse
      (fun s hs => by rw [List.mem_reverse] at hs; exact hwf.head_exp_nodup s hs)]]
  -- foldl insertSorted [] (foldl mergeTerm f_rest.reverse (pneg_rest))
  -- = foldl insertSorted [] (foldl mergeTerm [] (f_rest ++ pneg_rest))
  congr 1
  rw [← foldl_mergeTerm_wf_rev hwf.tail, ← List.foldl_append]

/-- Every term in `psub f (mulTerm qt g)` has exponent strictly smaller than `LT(f)` in
    grlex and the same length — the key polynomial fact underlying termination. -/
private lemma psub_mulTerm_lt {f g : Poly} {lf lg : Term}
    (hf : f.head? = some lf) (hg : g.head? = some lg)
    (hdiv : expDivides lg.exp lf.exp = true)
    (hwf : WellFormed f) (hwg : WellFormed g) :
    ∀ t ∈ psub f (mulTerm { coeff := lf.coeff / lg.coeff, exp := expMdiv lf.exp lg.exp } g),
      expCmp t.exp lf.exp = .lt ∧ t.exp.length = lf.exp.length := by
  set qt : Term := { coeff := lf.coeff / lg.coeff, exp := expMdiv lf.exp lg.exp }
  have hlf_mem : lf ∈ f := by
    cases f with
    | nil => simp at hf
    | cons hd t =>
      simp only [List.head?, Option.some.injEq] at hf
      exact List.mem_cons.mpr (Or.inl hf.symm)
  have hlg_mem : lg ∈ g := by
    cases g with
    | nil => simp at hg
    | cons hd t =>
      simp only [List.head?, Option.some.injEq] at hg
      exact List.mem_cons.mpr (Or.inl hg.symm)
  have hqt_ne : qt.coeff ≠ 0 :=
    div_ne_zero (hwf.all_coeff_ne_zero lf hlf_mem) (hwg.all_coeff_ne_zero lg hlg_mem)
  have hqt_len : qt.exp.length = lg.exp.length := by
    have hlen_eq : lf.exp.length = lg.exp.length := by
      simp only [expDivides, Bool.and_eq_true, beq_iff_eq] at hdiv; exact hdiv.1.symm
    simp only [qt, expMdiv, List.length_zipWith]; omega
  have hcancel_exp : expMmul qt.exp lg.exp = lf.exp := expMdiv_cancel hdiv
  -- The head of mulTerm qt g is exactly lf
  have hmt_head : (mulTerm qt g).head? = some lf := by
    have h := mulTerm_head hg hqt_ne hwg hqt_len
    rw [show qt.coeff * lg.coeff = lf.coeff from
          div_mul_cancel₀ _ (hwg.all_coeff_ne_zero lg hlg_mem),
        hcancel_exp] at h
    exact h
  -- Decompose f = lf :: f_tail and mulTerm qt g = lf :: mgt_tail
  obtain ⟨f_tail, rfl⟩ : ∃ t, f = lf :: t := by
    cases f with | nil => simp at hf | cons h t =>
      exact ⟨t, by simp at hf; subst hf; rfl⟩
  obtain ⟨mgt_tail, hmgt⟩ : ∃ t, mulTerm qt g = lf :: t := by
    cases h : mulTerm qt g with
    | nil => simp [h] at hmt_head
    | cons hd t =>
      refine ⟨t, ?_⟩
      simp only [h, List.head?, Option.some.injEq] at hmt_head
      subst hmt_head; rfl
  -- WF of (lf :: mgt_tail)
  have hwmt : WellFormed (lf :: mgt_tail) := hmgt ▸ mulTerm_wf hwg hqt_ne
  -- Cancel heads: psub (lf :: f_tail) (lf :: mgt_tail) = psub f_tail mgt_tail
  rw [hmgt, psub_head_head_cancel hwf]
  -- Bound all elements of psub f_tail mgt_tail
  intro t ht
  simp only [psub, padd] at ht
  obtain ⟨s, hs, heq_st⟩ := normalize_exp_mem ht
  simp only [List.mem_append, pneg, List.mem_map] at hs
  rcases hs with hs | ⟨u, hu, rfl⟩
  · -- s ∈ f_tail
    constructor
    · rw [← heq_st]; exact hwf.head_exp_max s hs
    · rw [← heq_st]
      exact hwf.exp_length_eq s (List.mem_cons.mpr (Or.inr hs))
              lf (List.mem_cons.mpr (Or.inl rfl))
  · -- u ∈ mgt_tail (pneg doesn't change exp; heq_st : u.exp = t.exp definitionally)
    have hexp : u.exp = t.exp := heq_st
    constructor
    · rw [← hexp]; exact hwmt.head_exp_max u hu
    · rw [← hexp]
      exact hwmt.exp_length_eq u (List.mem_cons.mpr (Or.inr hu))
               lf (List.mem_cons.mpr (Or.inl rfl))

/-- **Key lemma (division branch)**: a successful `tryDivStep` strictly lowers
    `polyGrlexPair`.
    After cancellation of `LT(f)`, every remaining term is smaller in grlex. -/
private lemma tryDivStep_grlexPair_lt {f g : Poly} {qt : Term} {f' : Poly}
    (h : tryDivStep f g = some (qt, f'))
    (hwf : WellFormed f) (hwg : WellFormed g) :
    Prod.Lex (· < ·) (· < ·) (polyGrlexPair f') (polyGrlexPair f) := by
  -- Unfold the Option-monad do-block step by step
  unfold tryDivStep leadingTerm? at h
  cases hf : f.head? with
  | none => simp [hf] at h
  | some lf =>
    cases hg : g.head? with
    | none => simp [hf, hg] at h
    | some lg =>
      by_cases hdiv : expDivides lg.exp lf.exp = true
      · -- Guard succeeds: simp reduces the do-block to the return value
        simp [hf, hg, hdiv] at h
        obtain ⟨hqt, hf'⟩ := h
        subst hqt hf'
        -- polyGrlexPair f = (expTotalDeg lf.exp + 1, expLexCode lf.exp)
        simp only [polyGrlexPair, leadingTerm?, hf]
        set q : Term := { coeff := lf.coeff / lg.coeff, exp := expMdiv lf.exp lg.exp }
        have hterms := psub_mulTerm_lt hf hg hdiv hwf hwg
        -- Case on whether the result polynomial is empty
        cases h_head : (psub f (mulTerm q g)).head? with
        | none =>
          simp only [polyGrlexPair, h_head]
          exact Prod.Lex.left 0 (expLexCode lf.exp) (Nat.succ_pos _)
        | some lf' =>
          simp only [polyGrlexPair, h_head]
          -- Extract membership of lf' in the result
          have hmem : lf' ∈ psub f (mulTerm q g) := by
            cases h_list : psub f (mulTerm q g) with
            | nil => simp [h_list] at h_head
            | cons hd tl =>
              simp only [h_list, List.head?] at h_head
              exact h_list ▸ List.mem_cons.mpr (Or.inl (Option.some.inj h_head).symm)
          -- Apply the key polynomial bound
          obtain ⟨hcmp, hlen⟩ := hterms lf' hmem
          -- hcmp : expCmp lf'.exp lf.exp = .lt
          simp only [expCmp, expTotalDeg] at hcmp
          -- split_ifs auto-closes the contradictory case (Ordering.gt = Ordering.lt),
          -- leaving exactly 2 goals: degree-drops and same-degree.
          split_ifs at hcmp with h1 h2
          · -- Total degree of lf'.exp drops: first component strictly decreases
            exact Prod.Lex.left (expLexCode lf'.exp) (expLexCode lf.exp)
              (by simp only [expTotalDeg]; omega)
          · -- Same total degree: use expLexCode_strictMono for second component
            have hsum : expTotalDeg lf'.exp = expTotalDeg lf.exp := by
              simp only [expTotalDeg]; omega
            rw [hsum]
            exact Prod.Lex.right (expTotalDeg lf.exp + 1) (expLexCode_strictMono hlen hsum hcmp)
      · -- Guard fails: none = some (...) is a contradiction
        simp only [Bool.not_eq_true] at hdiv
        simp [hf, hg, hdiv] at h

private lemma tryDivStep_result_wf {p g : Poly} {qt : Term} {p' : Poly}
    (h : tryDivStep p g = some (qt, p')) (hwp : WellFormed p) (hwg : WellFormed g) :
    WellFormed p' := by
  unfold tryDivStep leadingTerm? at h
  cases hf : p.head? with
  | none => simp [hf] at h
  | some lf =>
    cases hg : g.head? with
    | none => simp [hf, hg] at h
    | some lg =>
      by_cases hdiv : expDivides lg.exp lf.exp = true
      · simp [hf, hg, hdiv] at h
        obtain ⟨h1, rfl⟩ := h
        subst h1
        -- qt.coeff ≠ 0
        have hlf_mem : lf ∈ p := by
          cases p with
          | nil => simp at hf
          | cons a t =>
            have ha : a = lf := by simpa using hf
            subst ha; exact List.mem_cons.mpr (Or.inl rfl)
        have hlg_mem : lg ∈ g := by
          cases g with
          | nil => simp at hg
          | cons a t =>
            have ha : a = lg := by simpa using hg
            subst ha; exact List.mem_cons.mpr (Or.inl rfl)
        have hqt : ({ coeff := lf.coeff / lg.coeff, exp := expMdiv lf.exp lg.exp } : Term).coeff ≠ 0 :=
          div_ne_zero (hwp.all_coeff_ne_zero lf hlf_mem) (hwg.all_coeff_ne_zero lg hlg_mem)
        have hmt_wf := mulTerm_wf hwg hqt
        have hlg_len : lg.exp.length = lf.exp.length := by
          simp only [expDivides, Bool.and_eq_true, beq_iff_eq] at hdiv; omega
        have hqt_len : (expMdiv lf.exp lg.exp).length = lf.exp.length := expMdiv_length hdiv
        apply psub_wf_of_wf hwp hmt_wf
        intro a ha b hb
        have hb_len : b.exp.length = lf.exp.length := by
          simp only [mulTerm, beq_iff_eq, hqt, ↓reduceIte] at hb
          obtain ⟨s, hs, heq⟩ := normalize_exp_mem hb
          simp only [List.mem_map] at hs
          obtain ⟨u, hu, rfl⟩ := hs
          simp only [heq.symm, expMmul, List.length_zipWith]
          have hg_len : u.exp.length = lg.exp.length := hwg.exp_length_eq u hu lg hlg_mem
          omega
        exact (hwp.exp_length_eq a ha lf hlf_mem).trans hb_len.symm
      · simp only [Bool.not_eq_true] at hdiv
        simp [hf, hg, hdiv] at h

/-- **Key lemma (remainder branch)**: removing `lt = LT(p)` from `p` strictly
    lowers `polyGrlexPair`.
    Proof sketch: `p` is sorted in strictly decreasing grlex order, so every term
    after the head has a strictly smaller exponent; hence `LT(psub p [lt])` is either
    absent (the polynomial becomes zero, lowering the first component to 0) or has
    `expCmp LT(psub p [lt]).exp lt.exp = .lt` — same total degree gives a smaller
    lex code, smaller total degree gives a smaller first component. -/
private lemma psub_head_grlexPair_lt {p : Poly} {lt : Term}
    (h : p.head? = some lt) (hw : WellFormed p) :
    Prod.Lex (· < ·) (· < ·) (polyGrlexPair (psub p [lt])) (polyGrlexPair p) := by
  rw [psub_head_cancel h hw]
  obtain ⟨rest, rfl⟩ : ∃ rest, p = lt :: rest := by
    cases p with
    | nil => simp at h
    | cons hd tl => exact ⟨tl, by simp at h; subst h; rfl⟩
  simp only [List.tail, polyGrlexPair, leadingTerm?, List.head?]
  cases hrest : rest with
  | nil =>
    simp only [List.head?]
    exact Prod.Lex.left _ _ (Nat.succ_pos _)
  | cons lt' rest' =>
    simp only [List.head?]
    have hlt' : expCmp lt'.exp lt.exp = .lt := by
      apply hw.head_exp_max; rw [hrest]; exact List.mem_cons.mpr (Or.inl rfl)
    have hlen' : lt'.exp.length = lt.exp.length := by
      apply hw.head_exp_length; rw [hrest]; exact List.mem_cons.mpr (Or.inl rfl)
    simp only [expCmp, expTotalDeg] at hlt'
    by_cases h1 : lt'.exp.sum < lt.exp.sum
    · simp only [h1, if_true] at hlt'
      exact Prod.Lex.left _ _ (by simp only [expTotalDeg]; omega)
    · by_cases h2 : lt.exp.sum < lt'.exp.sum
      · simp only [show ¬ lt'.exp.sum < lt.exp.sum from h1, h2, if_false, if_true] at hlt'
        exact absurd hlt' (by decide)
      · simp only [show ¬ lt'.exp.sum < lt.exp.sum from h1,
                   show ¬ lt.exp.sum < lt'.exp.sum from h2, if_false] at hlt'
        have hsum' : expTotalDeg lt'.exp = expTotalDeg lt.exp := by
          simp only [expTotalDeg]; omega
        rw [hsum']
        exact Prod.Lex.right _ (expLexCode_strictMono hlen' hsum' hlt')

/-- **Helper lemma**: if the `foldl` scan returns `some (i, qt, p')` then
    `tryDivStep p gs[i]! = some (qt, p')`.
    Proof: induction on `List.range gs.size`; the fold short-circuits on first `some`,
    so the result can only come from index `i` with `tryDivStep p gs[i]! = some (qt, p')`. -/
private lemma foldl_divStep_spec {gs : Array Poly} {p : Poly}
    {i : ℕ} {qt : Term} {p' : Poly}
    (h : (List.range gs.size).foldl
           (fun acc j => if acc.isSome then acc
                         else (tryDivStep p gs[j]!).map fun (q, r) => (j, q, r))
           (none : Option (ℕ × Term × Poly)) = some (i, qt, p')) :
    tryDivStep p gs[i]! = some (qt, p') := by
  -- Generalise to induct on the list
  suffices ∀ (l : List ℕ),
      l.foldl (fun acc j => if acc.isSome then acc
                            else (tryDivStep p gs[j]!).map fun (q, r) => (j, q, r))
              (none : Option (ℕ × Term × Poly)) = some (i, qt, p') →
      tryDivStep p gs[i]! = some (qt, p') from this _ h
  intro l
  induction l with
  | nil => simp
  | cons j rest ih =>
    intro hfold
    simp only [List.foldl_cons, Option.isSome_none] at hfold
    cases htry : tryDivStep p gs[j]! with
    | none =>
      simp [htry] at hfold
      exact ih hfold
    | some pair =>
      obtain ⟨qt', p''⟩ := pair
      simp [htry] at hfold
      -- Once the accumulator is Some, the fold no longer changes it.
      -- Induct on a fresh ∀-bound list to avoid generalising over the outer ih.
      have hstable : ∀ (l : List ℕ), l.foldl
          (fun acc k => if acc.isSome then acc
                        else (tryDivStep p gs[k]!).map fun (q, r) => (k, q, r))
          (some (j, qt', p'') : Option (ℕ × Term × Poly)) = some (j, qt', p'') := by
        intro l
        induction l with
        | nil => rfl
        | cons hd tl ih2 =>
          rw [List.foldl_cons]
          simp only [Option.isSome_some, ite_true]
          exact ih2
      rw [hstable rest] at hfold
      simp only [Option.some.injEq, Prod.mk.injEq] at hfold
      obtain ⟨rfl, rfl, rfl⟩ := hfold
      exact htry

private lemma foldl_divStep_idx_lt {gs : Array Poly} {p : Poly}
    {i : ℕ} {qt : Term} {p' : Poly}
    (h : (List.range gs.size).foldl
           (fun acc j => if acc.isSome then acc
                         else (tryDivStep p gs[j]!).map fun (q, r) => (j, q, r))
           (none : Option (ℕ × Term × Poly)) = some (i, qt, p')) :
    i < gs.size := by
  have stable : ∀ (l : List ℕ) (val : ℕ × Term × Poly),
      l.foldl (fun acc j => if acc.isSome then acc
                            else (tryDivStep p gs[j]!).map fun (q, r) => (j, q, r))
              (some val) = some val := by
    intro l val; induction l with
    | nil => rfl
    | cons j rest ih =>
      rw [List.foldl_cons]; simp only [Option.isSome_some, ↓reduceIte, ih]
  have key : ∀ (l : List ℕ),
      l.foldl (fun acc j => if acc.isSome then acc
                            else (tryDivStep p gs[j]!).map fun (q, r) => (j, q, r))
              none = some (i, qt, p') → i ∈ l := by
    intro l hfold; induction l with
    | nil => simp at hfold
    | cons j rest ih =>
      rw [List.foldl_cons] at hfold
      simp only [Option.isSome_none, if_false] at hfold
      cases htry : tryDivStep p gs[j]! with
      | none =>
        simp only [htry, Option.map_none] at hfold
        exact List.mem_cons.mpr (Or.inr (ih hfold))
      | some pair =>
        obtain ⟨qt', p''⟩ := pair
        simp only [htry, Option.map_some] at hfold
        have heq : some (j, qt', p'') = some (i, qt, p') :=
          (stable rest (j, qt', p'')).symm.trans hfold
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact List.mem_cons.mpr (Or.inl rfl)
  exact List.mem_range.mp (key (List.range gs.size) h)

/-- Core loop: maintains `f = ∑ᵢ qs[i] · gs[i] + r + p`.
    Termination: `polyGrlexPair p` strictly decreases at every recursive call. -/
private def divAux
    (gs : Array Poly) (qs : Array Poly) (r p : Poly)
    (hwp : WellFormed p) (hwgs : ∀ i < gs.size, WellFormed (gs[i]!)) :
    Array Poly × Poly :=
  if p.isEmpty then (qs, r)
  else
    -- Find the first divisor whose leading term divides LT(p)
    let step := (List.range gs.size).foldl (fun acc i =>
      if acc.isSome then acc
      else (tryDivStep p gs[i]!).map fun (qt, p') => (i, qt, p')
    ) (none : Option (ℕ × Term × Poly))
    match h : step with
    | some (i, qt, p') =>
      divAux gs (qs.set! i (padd qs[i]! [qt])) r p'
        (tryDivStep_result_wf (foldl_divStep_spec h) hwp (hwgs i (foldl_divStep_idx_lt h))) hwgs
    | none =>
      -- LT(p) unreducible: move it to the remainder
      match h2 : p.head? with
      | some lt => divAux gs qs (padd r [lt]) (psub p [lt]) (psub_head_wf h2 hwp) hwgs
      | none    => (qs, r)
termination_by polyGrlexPair p
decreasing_by
  · exact tryDivStep_grlexPair_lt (foldl_divStep_spec h) hwp
      (hwgs i (foldl_divStep_idx_lt h))
  · exact psub_head_grlexPair_lt h2 hwp

/-- **Multivariate division algorithm**: divide `f` by the ordered array of divisors `gs`.
    Returns `(quotients, remainder)` satisfying `f = ∑ᵢ quotients[i] * gs[i] + remainder`.
    The remainder has no term divisible by `LT(gs[i])` for any `i`. -/
def divide (f : Poly) (gs : Array Poly)
    (hwf : WellFormed f)
    (hwgs : ∀ i < gs.size, WellFormed (gs[i]!)) : Array Poly × Poly :=
  divAux gs (gs.map fun _ => []) [] f hwf hwgs

/-! ### Pretty printing -/

private def varName (i : ℕ) : String :=
  (["x", "y", "z", "w"] : List String).getD i s!"x{i + 1}"

def expToStr (e : Exp) : String :=
  let parts := (e.mapIdx fun i n =>
    if n == 0 then ""
    else if n == 1 then varName i
    else s!"{varName i}^{n}").filter (· ≠ "")
  if parts.isEmpty then "1" else String.join parts

def termToStr (t : Term) : String :=
  let mon := expToStr t.exp
  if mon == "1" then s!"{t.coeff}"
  else if t.coeff == 1 then mon
  else if t.coeff == -1 then s!"-{mon}"
  else s!"{t.coeff}·{mon}"

def polyToStr : Poly → String
  | [] => "0"
  | first :: rest =>
    rest.foldl (fun s t =>
      if t.coeff < 0 then s ++ " - " ++ termToStr { t with coeff := -t.coeff }
      else s ++ " + " ++ termToStr t
    ) (termToStr first)

/-! ### Examples -/

private lemma wfGs1 {g : Poly} (hw : WellFormed g) :
    ∀ i < (#[g] : Array Poly).size, WellFormed (#[g] : Array Poly)[i]! := by
  intro i hi
  have hsize : (#[g] : Array Poly).size = 1 := rfl
  have hi0 : i = 0 := by omega
  subst hi0; exact hw

private lemma wfGs2 {g1 g2 : Poly} (hw1 : WellFormed g1) (hw2 : WellFormed g2) :
    ∀ i < (#[g1, g2] : Array Poly).size, WellFormed (#[g1, g2] : Array Poly)[i]! := by
  intro i hi
  have hsize : (#[g1, g2] : Array Poly).size = 2 := rfl
  have hi2 : i < 2 := by omega
  interval_cases i
  · exact hw1
  · exact hw2

-- ════════════════════════════════════════════════════════════════
-- Example 1 (univariate): x⁵ - 1  ÷  (x² - 1)
-- Expected: quotient = x³ + x,  remainder = x - 1
-- ════════════════════════════════════════════════════════════════

def ex1_f : Poly := normalize [⟨1, [5]⟩, ⟨-1, [0]⟩]
def ex1_g : Poly := normalize [⟨1, [2]⟩, ⟨-1, [0]⟩]

#eval!
  let (qs, r) := divide ex1_f #[ex1_g] (normalize_wf _ (by native_decide) (by native_decide)) (wfGs1 (normalize_wf _ (by native_decide) (by native_decide)))
  s!"({polyToStr ex1_f}) ÷ ({polyToStr ex1_g})\n" ++
  s!"  quotient  = {polyToStr qs[0]!}\n" ++
  s!"  remainder = {polyToStr r}"

#eval!
  let (qs, r) := divide ex1_f #[ex1_g] (normalize_wf _ (by native_decide) (by native_decide)) (wfGs1 (normalize_wf _ (by native_decide) (by native_decide)))
  let check := padd (pmul qs[0]! ex1_g) r
  s!"Verification: q·g + r = {polyToStr check}  (expect: {polyToStr ex1_f})"

-- ════════════════════════════════════════════════════════════════
-- Example 2 (bivariate, CLS §2.3 Example 1):
-- f  = x²y + xy² + y²
-- g₁ = xy - 1,  g₂ = y² - 1
-- Expected: q₁ = x + y,  q₂ = 1,  r = x + y + 1
-- ════════════════════════════════════════════════════════════════

def ex2_f  : Poly := normalize [⟨1, [2,1]⟩, ⟨1, [1,2]⟩, ⟨1, [0,2]⟩]
def ex2_g1 : Poly := normalize [⟨1, [1,1]⟩, ⟨-1, [0,0]⟩]
def ex2_g2 : Poly := normalize [⟨1, [0,2]⟩, ⟨-1, [0,0]⟩]

#eval!
  let (qs, r) := divide ex2_f #[ex2_g1, ex2_g2]
    (normalize_wf _ (by native_decide) (by native_decide)) (wfGs2 (normalize_wf _ (by native_decide) (by native_decide)) (normalize_wf _ (by native_decide) (by native_decide)))
  s!"f  = {polyToStr ex2_f}\n" ++
  s!"g₁ = {polyToStr ex2_g1},  g₂ = {polyToStr ex2_g2}\n" ++
  s!"q₁ = {polyToStr qs[0]!},  q₂ = {polyToStr qs[1]!}\n" ++
  s!"r  = {polyToStr r}"

#eval!
  let (qs, r) := divide ex2_f #[ex2_g1, ex2_g2]
    (normalize_wf _ (by native_decide) (by native_decide)) (wfGs2 (normalize_wf _ (by native_decide) (by native_decide)) (normalize_wf _ (by native_decide) (by native_decide)))
  let check := padd (padd (pmul qs[0]! ex2_g1) (pmul qs[1]! ex2_g2)) r
  s!"Verification: q₁g₁ + q₂g₂ + r = {polyToStr check}  (expect: {polyToStr ex2_f})"

-- ════════════════════════════════════════════════════════════════
-- Example 3 (order matters): same f, divisors swapped.
-- Remainder changes because the algorithm is order-dependent.
-- ════════════════════════════════════════════════════════════════

#eval!
  let (qs, r) := divide ex2_f #[ex2_g2, ex2_g1]
    (normalize_wf _ (by native_decide) (by native_decide)) (wfGs2 (normalize_wf _ (by native_decide) (by native_decide)) (normalize_wf _ (by native_decide) (by native_decide)))
  s!"Reversed order — g₂ first, g₁ second:\n" ++
  s!"q₂ = {polyToStr qs[0]!},  q₁ = {polyToStr qs[1]!}\n" ++
  s!"r  = {polyToStr r}"

end ExecPolyDiv
