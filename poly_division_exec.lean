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

/-- Core loop: maintains `f = ∑ᵢ qs[i] · gs[i] + r + p`. -/
private partial def divAux
    (gs : Array Poly) (qs : Array Poly) (r p : Poly) : Array Poly × Poly :=
  if p.isEmpty then (qs, r)
  else
    -- Find the first divisor whose leading term divides LT(p)
    let step := (List.range gs.size).foldl (fun acc i =>
      if acc.isSome then acc
      else (tryDivStep p gs[i]!).map fun (qt, p') => (i, qt, p')
    ) (none : Option (ℕ × Term × Poly))
    match step with
    | some (i, qt, p') =>
      divAux gs (qs.set! i (padd qs[i]! [qt])) r p'
    | none =>
      -- LT(p) unreducible: move it to the remainder
      match p.head? with
      | some lt => divAux gs qs (padd r [lt]) (psub p [lt])
      | none    => (qs, r)

/-- **Multivariate division algorithm**: divide `f` by the ordered array of divisors `gs`.
    Returns `(quotients, remainder)` satisfying `f = ∑ᵢ quotients[i] * gs[i] + remainder`.
    The remainder has no term divisible by `LT(gs[i])` for any `i`. -/
def divide (f : Poly) (gs : Array Poly) : Array Poly × Poly :=
  divAux gs (gs.map fun _ => []) [] f

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

-- ════════════════════════════════════════════════════════════════
-- Example 1 (univariate): x⁵ - 1  ÷  (x² - 1)
-- Expected: quotient = x³ + x,  remainder = x - 1
-- ════════════════════════════════════════════════════════════════

def ex1_f : Poly := normalize [⟨1, [5]⟩, ⟨-1, [0]⟩]
def ex1_g : Poly := normalize [⟨1, [2]⟩, ⟨-1, [0]⟩]

#eval
  let (qs, r) := divide ex1_f #[ex1_g]
  s!"({polyToStr ex1_f}) ÷ ({polyToStr ex1_g})\n" ++
  s!"  quotient  = {polyToStr qs[0]!}\n" ++
  s!"  remainder = {polyToStr r}"

#eval
  let (qs, r) := divide ex1_f #[ex1_g]
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

#eval
  let (qs, r) := divide ex2_f #[ex2_g1, ex2_g2]
  s!"f  = {polyToStr ex2_f}\n" ++
  s!"g₁ = {polyToStr ex2_g1},  g₂ = {polyToStr ex2_g2}\n" ++
  s!"q₁ = {polyToStr qs[0]!},  q₂ = {polyToStr qs[1]!}\n" ++
  s!"r  = {polyToStr r}"

#eval
  let (qs, r) := divide ex2_f #[ex2_g1, ex2_g2]
  let check := padd (padd (pmul qs[0]! ex2_g1) (pmul qs[1]! ex2_g2)) r
  s!"Verification: q₁g₁ + q₂g₂ + r = {polyToStr check}  (expect: {polyToStr ex2_f})"

-- ════════════════════════════════════════════════════════════════
-- Example 3 (order matters): same f, divisors swapped.
-- Remainder changes because the algorithm is order-dependent.
-- ════════════════════════════════════════════════════════════════

#eval
  let (qs, r) := divide ex2_f #[ex2_g2, ex2_g1]
  s!"Reversed order — g₂ first, g₁ second:\n" ++
  s!"q₂ = {polyToStr qs[0]!},  q₁ = {polyToStr qs[1]!}\n" ++
  s!"r  = {polyToStr r}"

end ExecPolyDiv
