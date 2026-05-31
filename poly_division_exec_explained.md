# poly_division_exec.lean — What It Proves and Why Each Piece Exists

## The Big Picture

This file is a self-contained *runnable* implementation of the multivariate polynomial division algorithm, working over the rationals ℚ. Where `poly_division.lean` is purely abstract (no computation, just proofs), this file gives you concrete data structures, a concrete algorithm, and a verified proof that the algorithm terminates and is correct.

The end result is a function `divAlgorithm` that you can actually call on concrete polynomials and get a quotient and remainder back, with Lean guaranteeing it is correct.

---

## Part 1 — Data Structures

### Exponent vectors (`Exp`, `expTotalDeg`, `expLexOrd`, `expCmp`, `expBlt`, `expDivides`, `expMdiv`, `expMmul`)

**What they are.** A monomial like `x²y³z` is represented by its list of exponents `[2, 3, 1]`. An `Exp` is just `List ℕ`.

- `expTotalDeg`: total degree = sum of all exponents.
- `expLexOrd`: lex comparison on lists.
- `expCmp`: *graded lex* comparison — compare total degrees first, break ties with lex. This is the monomial order used throughout.
- `expBlt`: boolean version of `expCmp = .lt`, used as a decidable comparison.
- `expDivides a b`: does monomial `a` divide monomial `b`? Equivalent to `a[i] ≤ b[i]` for all `i`.
- `expMdiv b a`: monomial quotient `b/a` — pointwise subtraction (only valid when `a` divides `b`).
- `expMmul a b`: monomial product `a·b` — pointwise addition.

**Why they are needed.** Every operation on polynomials — adding, multiplying, dividing — reduces to operations on exponent vectors. These are the atoms.

### Terms and polynomials (`Term`, `Poly`, `normalize`, arithmetic)

**What they are.** A `Term` is a nonzero rational coefficient paired with an exponent vector. A `Poly` is a list of terms kept in *strictly decreasing graded-lex order* with no zero coefficients and no duplicate exponent vectors — this is the canonical form.

- `mergeTerm`: adds a new term into an accumulator, combining like exponents and dropping zeros.
- `insertSorted`: inserts a term into an already-sorted list, maintaining the graded-lex order.
- `normalize`: takes any list of terms and produces the canonical form: fold with `mergeTerm`, then sort with `insertSorted`.
- `padd`, `pneg`, `psub`, `pmul`, `mulTerm`: standard polynomial arithmetic, all normalise their output.
- `leadingTerm?`: returns the head of the list (the largest term in graded-lex order, if the polynomial is nonzero).

**Why they are needed.** The algorithm operates on canonical-form polynomials. If polynomials are not kept in canonical form, the termination argument breaks (you could not reliably compare "which polynomial is larger") and correctness is undefined.

---

## Part 2 — The Division Step

### `tryDivStep`

**What it does.** Given `f` and a divisor `g`, attempts one reduction step:
1. Look at `LT(f)` (leading term of `f`) and `LT(g)`.
2. If `LM(g)` divides `LM(f)`, compute the quotient term `qt = LT(f) / LT(g)`.
3. Return `(qt, f - qt·g)`.

If `LM(g)` does not divide `LM(f)`, return `none`.

**Why it is needed.** This is the atomic operation of the division algorithm. One call to `tryDivStep` eliminates exactly one monomial from the leading term of `f`.

---

## Part 3 — Termination Infrastructure

This is the most technically involved part of the file. It exists to convince Lean's termination checker that `divAux` (the recursive core of the algorithm) actually terminates.

### The termination measure (`polyGrlexPair`)

**The idea.** The division algorithm terminates because at each step the leading term of the current polynomial strictly decreases in graded-lex order. To make this formal, we need a *natural number* measure that is strictly decreasing — Lean's termination checker requires this.

`polyGrlexPair p` maps a polynomial to a pair `(total degree of LT(p) + 1, lex code of LT(p))` ordered lexicographically. Since both components are natural numbers and the pair order on ℕ × ℕ is well-founded, this works.

### The lex code (`expLexCode`, `lexCodeFrom`)

**What it is.** `expLexCode e` encodes an exponent vector as a single natural number by treating the list as a numeral in base `(total_degree + 1)`. For example, `[2, 1]` with total degree 3 is `2 × 4 + 1 = 9` in base 4.

**Why it works.** Within a fixed total degree, graded-lex reduces to lex. The base-`(d+1)` encoding is strictly monotone for lex order on same-length, same-sum lists, because the most significant digit dominates. This is the content of `expLexCode_strictMono`.

**Why same-length matters.** On variable-length lists, graded-lex is *not* a well-order: you can have an infinite strictly decreasing chain `[4,1] >_grlex [4,0,1] >_grlex [4,0,0,1] > …` by padding with zeros. The file notes this explicitly and observes that all exponent vectors produced by the algorithm have the same length (since `expMmul` and `expMdiv` use `zipWith`, which preserves length). So the same-length restriction is always satisfied in practice.

### The helper lemmas for the lex code

- `expLexCode_eq_from`: `expLexCode` is the same as `lexCodeFrom` starting from 0.
- `lexCodeFrom_nil`, `lexCodeFrom_cons`: unfold `lexCodeFrom` one step.
- `lexCodeFrom_split`: the key algebraic identity — `lexCodeFrom B init l = init × B^n + lexCodeFrom B 0 l` where `n = length l`. This lets you separate the accumulator from the "pure" code.
- `lexCodeFrom_lt_pow`: the code of a length-`n` list with all digits `< B` is less than `B^n`. Used to bound the "tail contribution" when the leading digit already determines the order.
- `nat_mem_le_sum`: every element of a list is at most the sum. Used to check that exponent entries are bounded by the total degree.
- `lexCodeFrom_strictMono`: if `expLexOrd a b = .lt` and `a`, `b` have the same length and all digits bounded by `B`, then `lexCodeFrom B init a < lexCodeFrom B init b`. This is proved by induction on the lists, case-splitting on whether the leading digit of `a` is less than, equal to, or greater than that of `b`.
- `expLexCode_strictMono`: specialises `lexCodeFrom_strictMono` to `expLexCode` for same-length, same-sum lists.

### The ordering lemmas

- `expLexOrd_lt_trans`, `expCmp_lt_trans`, `expBlt_trans`: transitivity. Needed because the well-formedness invariant uses `expCmp`, and the termination argument needs transitivity to chain inequalities.
- `expLexOrd_eq_imp_eq`: if `expLexOrd a b = .eq` then `a = b`. Needed to show the ordering is consistent with equality.
- `expLexOrd_gt_iff_lt_swap`, `expCmp_gt_iff_lt_swap`: `a > b` iff `b < a`. Needed for `WellFormed` proofs where you need to flip comparison directions.

---

## Part 4 — Well-Formedness

### `WellFormed`

**What it is.** A polynomial `p` is `WellFormed` if it is in canonical form: nonzero coefficients, all exponents the same length, all exponents distinct, terms in strictly decreasing graded-lex order.

**Why it is needed.** The termination argument relies on being able to compare polynomials by their leading term. This only makes sense if the canonical form is maintained throughout. `WellFormed` is the invariant that guarantees this.

### The `WellFormed` accessor lemmas

These just extract individual components of the `WellFormed` record:
- `WellFormed.tail`: the tail of a well-formed list is well-formed.
- `WellFormed.head_ne_zero`: the leading coefficient is nonzero.
- `WellFormed.head_exp_length`: all remaining terms have the same exponent length as the head.
- `WellFormed.head_exp_nodup`: no other term has the same exponent as the head.
- `WellFormed.head_exp_max`: all remaining terms have smaller leading exponent.
- `WellFormed.all_coeff_ne_zero`: all coefficients are nonzero (derived from the head + induction).
- `WellFormed.pairwise_exp_ne`: all exponents are distinct (derived from the ordering).
- `WellFormed.exp_length_eq`: all exponents in the list have the same length.

**Why they are needed.** Proof automation can access `WellFormed` only through its definition. These lemmas give names to each condition so downstream proofs can call them cleanly instead of unpacking nested conjunctions manually.

### `insertSorted` and `foldl mergeTerm` lemmas

- `mem_insertSorted`: membership in `insertSorted t p` is membership in `{t} ∪ p`. Needed to reason about what is in a polynomial after normalisation.
- `insertSorted_of_all_lt`: if every element of `p` is smaller than `t`, then `insertSorted t p = t :: p`. This is the "fast path" for inserting the new maximum element.
- `insertSorted_wf`: `insertSorted` preserves `WellFormed` when the inserted term has a fresh exponent and the right length. This is the main structural lemma for maintaining the invariant during arithmetic.

The `foldl mergeTerm` lemmas (further in the file) prove that folding `mergeTerm` over a list collects all coefficients with the same exponent, drops zeros, and maintains membership. Together with `insertSorted_wf` they let you prove `WellFormed (normalize p)`.

---

## Part 5 — The Full Algorithm

### `divAux` (recursive core)

**What it does.** Given a list of divisors, a current polynomial `p`, a quotient accumulator, and a remainder accumulator:
1. For each divisor `gᵢ`, try `tryDivStep p gᵢ`.
2. If a step succeeds (some `gᵢ` divides `LT(p)`), add the quotient term to the `i`-th quotient accumulator and recurse on the reduced `p`.
3. If no step succeeds, move `LT(p)` to the remainder and recurse on `p - LT(p)`.
4. If `p = 0`, return the accumulators.

**Termination.** The measure `polyGrlexPair p` strictly decreases at every recursive call: either a term is eliminated from the leading position (step 2 or step 3), which strictly decreases the leading term in graded-lex order.

### Correctness theorem

The main theorem asserts that `divAux` produces a decomposition `f = ∑ qᵢ·gᵢ + r` where `r` has no term whose exponent is divisible by any `LM(gᵢ)`, and every `qᵢ·gᵢ` has degree at most `deg(f)`. This matches exactly the abstract statement in `poly_division.lean`.

---

## Summary of the Logical Flow

```
Exponent vector operations (expCmp, expDivides, expMdiv, expMmul)
           ↓
Polynomial representation and arithmetic (Term, Poly, normalize, padd, pmul, …)
           ↓
One division step (tryDivStep)
           ↓
Termination measure:
  lexCode monotonicity lemmas
  → expLexCode_strictMono
  → polyGrlexPair strictly decreases
           ↓
Well-formedness invariant (WellFormed)
  accessor lemmas + insertSorted_wf + normalize lemmas
           ↓
divAux terminates and maintains WellFormed
           ↓
Correctness: output satisfies the division algorithm specification
```

The termination and well-formedness parts are the bulk of the file. The actual algorithm (`tryDivStep`, `divAux`) is only a few lines — the rest is the proof that it works.
