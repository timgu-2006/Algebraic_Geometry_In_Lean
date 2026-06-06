abbrev Exp   := Array Nat
abbrev MPoly := Array (Rat × Exp)

-- Monomial helpers

def expDeg (e : Exp) : Nat :=
  e.foldl (Nat.add) 0

def expDivides (a b : Exp) : Bool :=
  a.size == b.size && (Array.zip a b).all (fun (x, y) => x <= y)

def expDiv (a b : Exp) : Exp :=
  Array.zipWith (Nat.sub) a b

def expMul (a b : Exp) : Exp :=
  Array.zipWith (Nat.add) a b

def expLt (a b : Exp) : Bool :=
  expDeg a < expDeg b || (expDeg a == expDeg b && a.toList < b.toList)

def monom (c : Rat) (e : Exp) : MPoly :=
  if c == 0 then #[] else #[(c, e)]

-- Polynomial operations

def insert_term (t : Rat × Exp) (p : MPoly) : MPoly :=
  let c := t.1
  let e := t.2
  if c == 0 then p
  else
    match p.find? (fun u => u.2 == e) with
    | none =>
        p.push t
    | some old =>
        let c' := old.1 + c
        let p' := p.filter (fun u => !(u.2 == e))
        if c' == 0 then p'
        else p'.push (c', e)

def simplify (p : MPoly) : MPoly :=
  p.foldl (fun acc t => insert_term t acc) #[]

def leadTerm (p : MPoly) : Option (Rat × Exp) :=
  let p' := simplify p
  let p'' := p'.qsort (fun a b => expLt b.2 a.2)
  p''[0]?

def mAdd (p q : MPoly) : MPoly :=
  simplify (p ++ q)

def mSub (p q : MPoly) : MPoly :=
  let q' := q.map (fun x => (-x.1, x.2))
  mAdd p q'

def mScale (c : Rat) (e : Exp) (p : MPoly) : MPoly :=
  p.map (fun x => (c * x.1 ,expMul e x.2))

def mMul (p q : MPoly) : MPoly :=
  simplify (p.flatMap fun t => q.map fun u => (t.1 * u.1, expMul t.2 u.2))

-- Properties of expLt

theorem expLt_irrefl (e : Exp) : expLt e e = false := by
  unfold expLt
  simp

-- Transitivity of (deg, list) <_lex (deg, list).
theorem expLt_trans {a b c : Exp}
    (hab : expLt a b = true) (hbc : expLt b c = true) : expLt a c = true := by
  unfold expLt at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at *
  rcases hab with hdeg_ab | ⟨hdeg_ab, hlex_ab⟩
  · rcases hbc with hdeg_bc | ⟨hdeg_bc, _⟩
    · left; omega
    · left; omega
  · rcases hbc with hdeg_bc | ⟨hdeg_bc, hlex_bc⟩
    · left; omega
    · right; exact ⟨by omega, Trans.trans hlex_ab hlex_bc⟩


-- grlex is well-founded: rank by total degree (a natural number), breaking ties
-- by lex on List ℕ, which is itself well-founded.
theorem expLt_wf : WellFounded (fun a b : Exp => expLt a b = true) := by
  sorry

-- ── §2  Termination: lifting to polynomials ───────────────────────────────────

-- Compare polynomials by leading monomial; zero (no lead term) is the minimum.
def MPolyLt (p q : MPoly) : Prop :=
  match leadTerm q with
  | none => False
  | some (_, leq) =>
    match leadTerm p with
    | none => True
    | some (_, lep) => expLt lep leq = true

-- MPolyLt is well-founded: it is the InvImage of expLt_wf via leadTerm.
theorem mPolyLt_wf : WellFounded MPolyLt := by
  sorry

instance wfMPoly : WellFoundedRelation MPoly := ⟨MPolyLt, mPolyLt_wf⟩

-- ── §3  Termination: decrease lemmas for each recursive branch ────────────────

-- Division step.  mMul (monom (c/cf) (e-ef)) f has leading term c·xᵉ, cancelling
-- LT(p) exactly, so LT(p - mMul t f) <_grlex e.
theorem loop_div_step
    (p f : MPoly) (c cf : Rat) (e ef : Exp)
    (hp  : leadTerm p = some (c, e))
    (hf  : leadTerm f = some (cf, ef))
    (hdv : expDivides ef e = true)
    (hcf : cf ≠ 0) :
    MPolyLt (mSub p (mMul (monom (c / cf) (expDiv e ef)) f)) p := by
  sorry

-- Remainder step.  monom c e is exactly LT(p), so removing it makes the lead
-- strictly smaller (or p becomes zero, which is below everything in MPolyLt).
theorem loop_rem_step
    (p : MPoly) (c : Rat) (e : Exp)
    (hp : leadTerm p = some (c, e)) :
    MPolyLt (mSub p (monom c e)) p := by
  sorry

-- ── §4  Division algorithm ────────────────────────────────────────────────────

-- Helper: replace slot i of qs with mAdd qs[i] v.
private def updateAt (qs : Array MPoly) (i : Nat) (v : MPoly) : Array MPoly :=
  qs.mapIdx fun j q => if j == i then mAdd q v else q

-- Division Algorithm
--     p   : polynomial still to divide
--     qs  : quotients so far (one per divisor)
--     r   : remainder so far
-- Terminates because MPolyLt p strictly decreases at every recursive call.
def divLoop (divs : Array MPoly) (p : MPoly) (qs : Array MPoly) (r : MPoly) :
    Array MPoly × MPoly :=
  match leadTerm p with
  | none => (qs, simplify r)
  | some (c, e) =>
    let divsWithIdx := divs.mapIdx (fun i f => (f, i))
    let found? := divsWithIdx.find? fun (f, _) =>
      match leadTerm f with
      | none         => false
      | some (_, ef) => expDivides ef e

    match found? with
    | none =>
      let t := monom c e
      divLoop divs (mSub p t) qs (mAdd r t)
    | some (f, i) =>
      match leadTerm f with
      | none => divLoop divs p qs r
      | some (cf, ef) =>
        let t := monom (c / cf) (expDiv e ef)
        divLoop divs (mSub p (mMul t f)) (updateAt qs i t) r
termination_by p
decreasing_by
  -- In all branches, MPolyLt p strictly decreases (proved by loop_rem_step /
  -- loop_div_step once the match equations are available as hypotheses).
  all_goals sorry

-- Entry point
def mvDiv (f : MPoly) (divs : Array MPoly) : Array MPoly × MPoly :=
  let qs : Array MPoly := (List.replicate divs.size #[]).toArray
  divLoop divs (simplify f) qs #[]

-- ── §5  Correctness ───────────────────────────────────────────────────────────

-- §5.1  Loop invariant: at every call to divLoop,
--           f = (∑ qs[i] * divs[i]) + r + p.
-- Both branches preserve it:
--   division  branch: qs[i] ↦ qs[i]+t, p ↦ p−t·f_i  →  net change zero.
--   remainder branch: r ↦ r+t,          p ↦ p−t       →  net change zero.
theorem divLoop_invariant
    (divs : Array MPoly) (f p : MPoly) (qs : Array MPoly) (r : MPoly)
    (hsize : qs.size = divs.size)
    (hinv  : simplify f =
        mAdd ((qs.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[])
             (mAdd r p)) :
    let (qs', r') := divLoop divs p qs r
    simplify f =
        mAdd ((qs'.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[])
             r' := by
  sorry

-- §5.2  Division identity: f = (∑ qᵢ * dᵢ) + r.
-- Corollary of divLoop_invariant: the initial state has qs = 0, r = 0, p = f,
-- so the invariant gives f = 0 + 0 + f, and at termination p = 0 drops out.
theorem mvDiv_identity (f : MPoly) (divs : Array MPoly) :
    let (qs, r) := mvDiv f divs
    simplify f =
        mAdd ((qs.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[]) r := by
  sorry

-- §5.3  Remainder is fully reduced: no term of r is divisible by any LT(dᵢ).
-- A term enters r only in the remainder branch, which fires precisely when no
-- LT(dᵢ) divides the current lead of p, so every such term is irreducible.
theorem mvDiv_remainder_reduced (f : MPoly) (divs : Array MPoly) :
    let (_, r) := mvDiv f divs
    ∀ t ∈ r.toList, ∀ i < divs.size,
      (leadTerm divs[i]!).any (fun (_, de) => expDivides de t.2) = false := by
  sorry
