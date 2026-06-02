# poly_division_exec.lean — Complete Lemma Reference

This file is a self-contained, verified executable implementation of the multivariate polynomial
division algorithm over ℚ. Every definition and lemma is listed below in the order they appear,
grouped by logical role.

---

## Part 1 — Exponent Vectors

An exponent vector `e : Exp = List ℕ` represents a monomial: index `i` holds the exponent of `xᵢ`.

### Definitions

**`expTotalDeg (e : Exp) : ℕ`**
Total degree of a monomial: the sum of all exponents.

**`expLexOrd : Exp → Exp → Ordering`**
Lexicographic order on exponent vectors, compared left-to-right digit by digit.
Shorter lists are smaller ([] < any non-empty list).

**`expCmp (a b : Exp) : Ordering`**
Graded-lex (grlex) order: compare total degrees first; break ties with `expLexOrd`.
This is the monomial order used throughout.

**`expBlt (a b : Exp) : Bool`**
Boolean version of `expCmp a b = .lt`. Used as a decidable comparison in sorting.

**`expDivides (a b : Exp) : Bool`**
True iff monomial `a` divides monomial `b`, i.e., `a[i] ≤ b[i]` for every `i`.
Requires `a.length = b.length`.

**`expMdiv (b a : Exp) : Exp`**
Monomial quotient `b / a`: pointwise subtraction `b[i] - a[i]`.
Only valid (gives correct result) when `expDivides a b`.

**`expMmul (a b : Exp) : Exp`**
Monomial product `a * b`: pointwise addition `a[i] + b[i]`.

---

## Part 2 — Polynomial Representation and Arithmetic

### Definitions

**`Term`**
A single monomial term: a nonzero rational coefficient `coeff : ℚ` paired with an exponent
vector `exp : Exp`.

**`Poly = List Term`**
A multivariate polynomial: a list of terms kept in **strictly decreasing grlex order**, with no
zero-coefficient terms and no repeated exponent vectors. This is the canonical form.

**`mergeTerm (acc : Poly) (t : Term) : Poly`** *(private)*
Inserts term `t` into accumulator `acc`. If a term with the same exponent already exists,
combines the coefficients (dropping the result if it becomes zero). Used by `normalize`.

**`insertSorted (t : Term) : Poly → Poly`** *(private)*
Inserts term `t` into a grlex-sorted list, maintaining the strictly-decreasing order.
Scan from the front; insert before the first term smaller than `t`.

**`normalize (p : Poly) : Poly`**
Reduces any list of terms to canonical form: fold with `mergeTerm` to combine like
exponents and drop zeros, then fold with `insertSorted` to sort in decreasing grlex order.

**`padd (p q : Poly) : Poly`**
Polynomial addition: concatenate then normalize.

**`pneg (p : Poly) : Poly`**
Polynomial negation: negate every coefficient (no normalization needed).

**`psub (p q : Poly) : Poly`**
Polynomial subtraction: `padd p (pneg q)`.

**`mulTerm (t : Term) (p : Poly) : Poly`**
Multiply every term of `p` by the monomial term `t`. Returns `[]` if `t.coeff = 0`.
Otherwise multiplies coefficients and adds exponents, then normalizes.

**`pmul (p q : Poly) : Poly`**
Polynomial multiplication: distribute `mulTerm` and normalize.

**`leadingTerm? (p : Poly) : Option Term`**
The leading term of a normalized polynomial: just `p.head?` (the first element, which is
largest in grlex order).

---

## Part 3 — Division Algorithm (one step)

**`tryDivStep (f g : Poly) : Option (Term × Poly)`**
Attempts one reduction step of `f` by divisor `g`:
1. Extract `LT(f)` and `LT(g)`.
2. Check `expDivides LM(g) LM(f)`.
3. If yes, compute quotient term `qt = LT(f) / LT(g)` and return `(qt, f - qt·g)`.
4. If no, return `none`.

A successful call eliminates the leading term of `f`.

---

## Part 4 — Termination Infrastructure

The recursive core `divAux` must terminate. Lean requires a well-founded decreasing measure.
The measure used is `polyGrlexPair p : ℕ × ℕ`, which strictly decreases at every recursive call.

### Definitions

**`expLexCode (e : Exp) : ℕ`** *(private)*
Encodes an exponent vector as a single natural number by treating it as a numeral in base
`(expTotalDeg e + 1)`. Specifically: `e.foldl (fun acc x => acc * (total_deg + 1) + x) 0`.

This is strictly monotone with respect to `expLexOrd` on same-length, same-sum lists:
within a fixed total degree, grlex reduces to lex, and the most-significant digit dominates.

**`polyGrlexPair (p : Poly) : ℕ × ℕ`** *(private)*
Termination measure for a polynomial:
- `(0, 0)` if `p` is empty (zero polynomial).
- `(expTotalDeg LT(p) + 1, expLexCode LT(p))` otherwise.

Ordered lexicographically. Well-founded because both components are `ℕ`.

**`lexCodeFrom (B init : ℕ) (l : List ℕ) : ℕ`** *(private)*
Evaluates `l` as a base-`B` numeral starting from accumulator `init`:
`l.foldl (fun acc x => acc * B + x) init`.
Auxiliary to `expLexCode`; the lemmas below are stepping-stones to `expLexCode_strictMono`.

### Lemmas for `expLexCode`

**`expLexCode_eq_from`** *(private)*
`expLexCode e = lexCodeFrom (expTotalDeg e + 1) 0 e`.
Unfolds the definition in terms of `lexCodeFrom` to enable the inductive lemmas below.

**`lexCodeFrom_nil`** *(private)*
`lexCodeFrom B init [] = init`.
Base case: the code of the empty list is just the accumulator.

**`lexCodeFrom_cons`** *(private)*
`lexCodeFrom B init (h :: t) = lexCodeFrom B (init * B + h) t`.
Unrolls one step of the fold.

**`lexCodeFrom_split`** *(private)*
`lexCodeFrom B init l = init * B^(l.length) + lexCodeFrom B 0 l`.
Splits the accumulator `init` out of the fold. Key algebraic identity enabling the
strictly-monotone proof: the accumulator contributes a fixed multiple of `B^n`, so
comparing two codes with the same `init` reduces to comparing the pure codes.

**`lexCodeFrom_lt_pow`** *(private)*
If every digit `x ∈ l` satisfies `x < B`, then `lexCodeFrom B 0 l < B^(l.length)`.
Bounds the pure code by the base raised to the list length.
Used to show the tail contribution is smaller than the leading-digit contribution
when the leading digits differ.

**`nat_mem_le_sum`** *(private)*
If `x ∈ l` then `x ≤ l.sum`.
Used to verify that each exponent in a vector is at most the total degree,
so the digit-bound hypothesis for `lexCodeFrom_lt_pow` is satisfied.

**`lexCodeFrom_strictMono`** *(private)*
If `a` and `b` have the same length, all digits of `a` and `b` are `< B`, and
`expLexOrd a b = .lt`, then `lexCodeFrom B init a < lexCodeFrom B init b`.
Proof by induction on the lists:
- If leading digits differ (`a[0] < b[0]`): use `lexCodeFrom_split` + `lexCodeFrom_lt_pow`
  to bound the tail and show the leading digit dominates.
- If leading digits equal: recurse on tails.
- If `a[0] > b[0]`: `expLexOrd` would be `.gt`, contradicting the hypothesis.

**`expLexCode_strictMono`** *(private)*
If `a` and `b` have the same length, same total degree, and `expLexOrd a b = .lt`,
then `expLexCode a < expLexCode b`.
Specialises `lexCodeFrom_strictMono` to the grlex setting using `nat_mem_le_sum`
to supply the digit bound.

---

## Part 5 — Ordering Transitivity and Symmetry Lemmas

These are technical lemmas needed by the well-formedness proofs and the termination argument.

**`expLexOrd_lt_trans`** *(private)*
`expLexOrd a b = .lt → expLexOrd b c = .lt → expLexOrd a c = .lt`.
Transitivity of the lex order. Proved by induction with case analysis on each leading digit.

**`expCmp_lt_trans`** *(private)*
`expCmp a b = .lt → expCmp b c = .lt → expCmp a c = .lt`.
Transitivity of grlex. Delegates to `expLexOrd_lt_trans` when total degrees are equal.

**`expBlt_trans`** *(private)*
`expBlt a b = true → expBlt b c = true → expBlt a c = true`.
Boolean version of grlex transitivity; thin wrapper over `expCmp_lt_trans`.

**`expLexOrd_eq_imp_eq`** *(private)*
`expLexOrd a b = .eq → a = b`.
The lex order is a total order: `.eq` implies equality.
Used to deduce `a = b` when the comparison returns `.eq`.

**`expLexOrd_gt_iff_lt_swap`** *(private)*
`expLexOrd a b = .gt ↔ expLexOrd b a = .lt`.
The order is antisymmetric: `a > b` iff `b < a`.

**`expCmp_gt_iff_lt_swap`** *(private)*
`expCmp a b = .gt ↔ expCmp b a = .lt`.
Same for grlex; delegates to `expLexOrd_gt_iff_lt_swap` when degrees are equal.

---

## Part 6 — Well-Formedness Invariant

### Definition

**`WellFormed : Poly → Prop`** *(private)*
A polynomial is well-formed if it is in canonical form:
- `[]`: trivially well-formed.
- `h :: rest`: well-formed iff
  1. `h.coeff ≠ 0`
  2. All exponents in `rest` have the same length as `h.exp`
  3. No exponent in `rest` equals `h.exp` (no duplicates)
  4. Every exponent in `rest` is grlex-strictly less than `h.exp`
  5. `rest` is recursively well-formed

### Accessor Lemmas

**`WellFormed.tail`** *(private)*
The tail of a well-formed polynomial is well-formed.

**`WellFormed.head_ne_zero`** *(private)*
The leading coefficient of a well-formed polynomial is nonzero.

**`WellFormed.head_exp_length`** *(private)*
Every term in the tail has the same exponent length as the head.

**`WellFormed.head_exp_nodup`** *(private)*
No term in the tail has the same exponent as the head.

**`WellFormed.head_exp_max`** *(private)*
Every term in the tail is grlex-strictly smaller than the head: `expCmp s.exp h.exp = .lt`.

**`WellFormed.all_coeff_ne_zero`** *(private)*
Every term in a well-formed polynomial has a nonzero coefficient.
Proved by induction using `head_ne_zero` and `tail`.

**`WellFormed.pairwise_exp_ne`** *(private)*
All exponents in a well-formed polynomial are pairwise distinct.
Follows from `head_exp_nodup` by induction.

**`WellFormed.exp_length_eq`** *(private)*
All pairs of terms in a well-formed polynomial have the same exponent length.
Follows from `head_exp_length` by induction.

---

## Part 7 — `insertSorted` and `foldl mergeTerm` Lemmas

These establish correctness and the well-formedness invariant for the building blocks of `normalize`.

**`mem_insertSorted`** *(private)*
`s ∈ insertSorted t p ↔ s = t ∨ s ∈ p`.
Membership in the result of `insertSorted` is membership in the union `{t} ∪ p`.

**`insertSorted_of_all_lt`** *(private)*
If every element of `p` is grlex-smaller than `t`, then `insertSorted t p = t :: p`.
The fast path: when `t` is the new maximum, prepend without scanning.

**`insertSorted_wf`** *(private)*
`insertSorted t p` is well-formed when:
- `t.coeff ≠ 0`
- `p` is well-formed
- `t`'s exponent does not appear in `p`
- `t`'s exponent has the same length as all exponents in `p`

This is the main structural lemma: well-formedness is preserved by insertion.
The proof case-splits on whether `t` is greater or smaller than the current head;
in the "smaller" case, it recurses using `insertSorted_wf` for the tail, then
reassembles the well-formedness conditions at the head.

**`foldl_insertSorted_reverse_wf`** *(private)*
`p.reverse.foldl (fun acc t => insertSorted t acc) [] = p` when `p` is well-formed.
Inserting the terms of a well-formed polynomial in reverse order recovers the original.
Used in `normalize_wf_id`.

**`findIdx?_go_eq_none_aux`** *(private)*
If every element of `l` fails predicate `p`, then `findIdx?.go p l i = none`.
Auxiliary lemma for reasoning about `mergeTerm` when no match exists.

**`findIdx?_eq_none_aux`** *(private)*
If every element of `l` fails predicate `p`, then `l.findIdx? p = none`.
Wrapper over `findIdx?_go_eq_none_aux`.

**`foldl_mergeTerm_fresh`** *(private)*
When all elements of `l` have exponents disjoint from `acc` and pairwise distinct,
`l.foldl mergeTerm acc = l.reverse ++ acc`.
The elements are all "fresh" so no cancellation or merging occurs; the fold just
prepends each term to the accumulator.

**`foldl_mergeTerm_wf_rev`** *(private)*
`p.foldl mergeTerm [] = p.reverse` when `p` is well-formed.
Specialises `foldl_mergeTerm_fresh`: the well-formed terms are pairwise distinct
and the accumulator starts empty, so the fold reverses the list.

**`findIdx?_go_none_all_false`** *(private)*
If `findIdx?.go p l n = none`, then every element of `l` fails predicate `p`.
Converse of `findIdx?_go_eq_none_aux`. Used to extract information from `mergeTerm`'s
`findIdx?` returning `none`.

**`findIdx?_none_all_false`** *(private)*
Wrapper: `l.findIdx? p = none → ∀ x ∈ l, p x = false`.

**`map_exp_set_coeff`** *(private)*
Changing only the coefficient at position `i` does not change the exponent map:
`(acc.set i { acc[i]! with coeff := c }).map (·.exp) = acc.map (·.exp)`.
Used wherever `mergeTerm` sets a coefficient and we need the exponents to be unchanged.

**`forall_mem_set`** *(private)*
If `∀ x ∈ l, p x` and `p a`, then `∀ x ∈ l.set i a, p x`.
Generic helper: a universally-quantified property is preserved by `List.set`
when the replacement also satisfies it.

**`pairwise_ne_set_coeff`** *(private)*
Pairwise exp-distinctness is preserved by a coefficient-only `set`.
Follows from `map_exp_set_coeff`: the exponent map is unchanged, so the pairwise
distinctness of exponents is unchanged.

**`mergeTerm_pairwise_ne`** *(private)*
`mergeTerm acc t` preserves pairwise exp-distinctness of `acc`.
Three cases: erase (sublist preserves pairwise), set-coeff (`pairwise_ne_set_coeff`),
or prepend (the new term's exponent is not in `acc` by `findIdx?_none_all_false`).

**`foldl_mergeTerm_pairwise_ne`** *(private)*
`l.foldl mergeTerm acc` preserves pairwise exp-distinctness.
Induction: apply `mergeTerm_pairwise_ne` at each step.

**`mergeTerm_coeff_ne`** *(private)*
`mergeTerm acc t` preserves the property "all coefficients nonzero" of `acc`,
provided `t.coeff ≠ 0`.

**`foldl_mergeTerm_coeff_ne`** *(private)*
`l.foldl mergeTerm acc` preserves nonzero coefficients (all of `l` and `acc` nonzero).

**`mergeTerm_exp_len`** *(private)*
`mergeTerm acc t` preserves the property "all exponents have length `n`",
provided `t.exp.length = n`.

**`foldl_mergeTerm_exp_len`** *(private)*
`l.foldl mergeTerm acc` preserves uniform exponent length.

**`foldl_insertSorted_wf_aux`** *(private)*
Inserting elements of `q` one by one into a well-formed `acc` yields a well-formed result,
provided the elements of `q` have: nonzero coefficients, exponents fresh w.r.t. `acc`,
uniform length, and pairwise distinct exponents.
The main inductive lemma backing `normalize_wf`.

**`normalize_wf_id`** *(private)*
`normalize p = p` when `p` is already well-formed.
Uses `foldl_mergeTerm_wf_rev` (fold reverses the well-formed list) and
`foldl_insertSorted_reverse_wf` (re-inserting in reverse order recovers the original).

**`normalize_wf`** *(private)*
`normalize p` is well-formed whenever all terms in `p` have nonzero coefficients and
uniform exponent length.

**`normalize_idempotent`** *(private)*
`normalize (normalize p) = normalize p` when all terms of `p` have nonzero coefficients
and uniform length. Follows immediately: `normalize p` is already well-formed, so
`normalize_wf_id` applies.

---

## Part 8 — Arithmetic Well-Formedness Lemmas

**`psub_wf_of_wf`** *(private)*
`psub p q` is well-formed when `p` and `q` are well-formed and all their exponents have
the same length. Follows from `normalize_wf`: `p ++ pneg q` has nonzero coefficients
(since negation preserves nonzero) and uniform length (by hypothesis).

**`findIdx?_eq_none_of_mem_false`** *(private)*
Alias for `findIdx?_eq_none_aux`. Provides a named lemma with a self-documenting name
for the `psub_head_cancel` proof.

**`findIdx?_go_append_last`** *(private)*
If `p x = true` and every element of `l` fails `p`, then
`findIdx?.go p (l ++ [x]) i = some (i + l.length)`.
Used to locate the cancelling term in `mergeTerm_cancel`.

**`findIdx?_append_last`** *(private)*
If `p x = true` and every element of `l` fails `p`, then
`(l ++ [x]).findIdx? p = some l.length`.

**`eraseIdx_append_last`** *(private)*
`(l ++ [x]).eraseIdx l.length = l`.
Erasing the last element of `l ++ [x]` yields `l`.

**`getElem!_append_last`** *(private)*
`(l ++ [x])[l.length]! = x`.
The element at the index just past the end of `l` is `x`.

**`mergeTerm_cancel`** *(private)*
If `t` is the last element of `l ++ [t]` and no earlier element of `l` has exponent `t.exp`,
then `mergeTerm (l ++ [t]) { t with coeff := -t.coeff } = l`.
The negation of `t` cancels `t`, and the result is exactly `l`.
Used in `psub_head_cancel` to show the leading terms cancel.

**`psub_head_cancel`** *(private)*
When `p.head? = some lt` and `p` is well-formed:
`psub p [lt] = p.tail`.
Subtracting the leading term from `p` gives exactly the tail.
Proof: unfold `normalize`, show `foldl mergeTerm` cancels the two copies of `lt`,
leaving `rest.reverse`, then `foldl insertSorted` sorts this back to `rest`.

**`psub_head_wf`** *(private)*
`psub p [lt]` is well-formed when `lt = LT(p)` and `p` is well-formed.
Immediate from `psub_head_cancel`: the result is `p.tail`, which is well-formed by
`WellFormed.tail`.

---

## Part 9 — Sub-lemmas for the Key Polynomial Bound

These lemmas compute how exponents and orderings behave under `expMmul` and `expMdiv`,
needed to prove that a division step strictly decreases the leading term.

**`expMdiv_length`** *(private)*
`(expMdiv b a).length = b.length` when `expDivides a b`.
The quotient exponent has the same length as the dividend.

**`expMmul_length_eq`** *(private)*
`(expMmul a b).length = a.length` when `a.length = b.length`.
The product exponent has the same length as the factors.

**`mulTerm_wf`** *(private)*
`mulTerm qt g` is well-formed when `g` is well-formed and `qt.coeff ≠ 0`.
Follows from `normalize_wf`: the unmapped list has nonzero coefficients (`mul_ne_zero`)
and uniform exponent length (`expMmul_length_eq`).

**`mergeTerm_exp_mem`** *(private)*
Every exponent in `mergeTerm acc t` either came from some element of `acc` or equals `t.exp`.

**`foldl_mergeTerm_exp_mem`** *(private)*
Every exponent in `l.foldl mergeTerm acc` came from some element of `acc` or some element of `l`.

**`foldl_insertSorted_exp_mem_aux`** *(private)*
Every exponent in `q.foldl (insertSorted ·) acc` came from `acc` or `q`.

**`normalize_exp_mem`** *(private)*
Every exponent in `normalize l` came from some element of `l`.
Key corollary: `normalize` cannot invent new exponents.

**`expTotalDeg_expMmul`** *(private)*
`expTotalDeg (expMmul a b) = expTotalDeg a + expTotalDeg b` when `a.length = b.length`.
The total degree of a product is the sum of total degrees.

**`expLexOrd_expMmul_left`** *(private)*
`expLexOrd (expMmul c a) (expMmul c b) = expLexOrd a b` when lengths match.
Left-multiplying by a common monomial `c` preserves lex order.
Proof by induction: `(c + a)[i]` vs `(c + b)[i]` differs exactly where `a[i]` vs `b[i]` differ.

**`expCmp_expMmul_left`** *(private)*
`expCmp (expMmul c a) (expMmul c b) = expCmp a b` when lengths match.
Left-multiplying by `c` preserves grlex order.
Uses `expTotalDeg_expMmul` and `expLexOrd_expMmul_left`.

**`expMdiv_cancel`** *(private)*
`expMmul (expMdiv b a) a = b` when `expDivides a b`.
The fundamental identity: `(b/a) * a = b` for monomials.
Follows by pointwise arithmetic: `(b[i] - a[i]) + a[i] = b[i]`.

**`expCmp_self`** *(private)*
`expCmp a a = .eq`.
Every exponent vector compares equal to itself.

**`mulTerm_map_wf`** *(private)*
The list `g.map (fun s => { coeff := qt.coeff * s.coeff, exp := expMmul qt.exp s.exp })`
is well-formed when `g` is well-formed, `qt.coeff ≠ 0`, and all exponents in `g` have
the same length as `qt.exp`.
Uses `expCmp_expMmul_left` to show the order is preserved by left-multiplication.

**`mulTerm_head`** *(private)*
When `g.head? = some lg`, `qt.coeff ≠ 0`, and `g` is well-formed:
`(mulTerm qt g).head? = some { coeff := qt.coeff * lg.coeff, exp := expMmul qt.exp lg.exp }`.
The leading term of the product is the product of the leading terms.
Proof: `mulTerm qt g = normalize (g.map ...)` and the mapped list is already well-formed
(`mulTerm_map_wf`), so `normalize_wf_id` gives back the same list and the head is the
mapped head of `g`.

**`psub_head_head_cancel`** *(private)*
`psub (lf :: f_rest) (lf :: g_rest) = psub f_rest g_rest`.
When both polynomials share the same leading term `lf`, it cancels:
`(lf + f_rest) - (lf + g_rest) = f_rest - g_rest`.

---

## Part 10 — The Key Polynomial Bound

**`psub_mulTerm_lt`** *(private)*
**The central polynomial fact underlying termination.**

If:
- `f.head? = some lf` (leading term of `f` is `lf`)
- `g.head? = some lg` (leading term of `g` is `lg`)
- `expDivides lg.exp lf.exp` (LM(g) divides LM(f))
- `f` and `g` are well-formed

Then every term `t` in `psub f (mulTerm qt g)` (where `qt = lf / lg`) satisfies:
1. `expCmp t.exp lf.exp = .lt` — exponent of `t` is strictly less than `lf.exp` in grlex
2. `t.exp.length = lf.exp.length` — same exponent length

**Proof sketch:**
- Compute `qt = lf / lg` and show `mulTerm qt g` has leading term exactly `lf`
  (using `mulTerm_head` + `expMdiv_cancel`).
- Cancel the common leading terms using `psub_head_head_cancel`, reducing to
  `psub f_tail mgt_tail`.
- Every term of `f_tail` has exponent smaller than `lf` (by `WellFormed.head_exp_max`).
- Every term of `mgt_tail` has exponent smaller than `lf` (since `mulTerm qt g` is WF
  with head `lf`).
- Use `normalize_exp_mem` to handle that `psub` is a normalize; the exponents can only
  come from the inputs.

---

## Part 11 — Termination Proof Lemmas

**`tryDivStep_grlexPair_lt`** *(private)*
**Key lemma (division branch):** if `tryDivStep f g = some (qt, f')` and `f`, `g` are well-formed,
then `Prod.Lex (· < ·) (· < ·) (polyGrlexPair f') (polyGrlexPair f)`.

The grlex pair of the result is strictly less than that of `f`.

Proof:
- If `f' = []` (empty result), then `polyGrlexPair f' = (0,0)` and the first component drops.
- Otherwise, every term of `f'` satisfies `expCmp t.exp lf.exp = .lt` by `psub_mulTerm_lt`.
  So the new leading term `lf'` satisfies `expCmp lf'.exp lf.exp = .lt`.
  - If `expTotalDeg lf'.exp < expTotalDeg lf.exp`: first component drops → `Prod.Lex.left`.
  - If equal total degrees: use `expLexCode_strictMono` to show the second component drops
    → `Prod.Lex.right`.

**`tryDivStep_result_wf`** *(private)*
If `tryDivStep p g = some (qt, p')` and `p`, `g` are well-formed, then `p'` is well-formed.
Uses `psub_wf_of_wf` and `mulTerm_wf`, with `expMdiv_length` to verify the length condition.

**`psub_head_grlexPair_lt`** *(private)*
**Key lemma (remainder branch):** if `p.head? = some lt` and `p` is well-formed, then
`Prod.Lex (· < ·) (· < ·) (polyGrlexPair (psub p [lt])) (polyGrlexPair p)`.

Proof:
- `psub p [lt] = p.tail` by `psub_head_cancel`.
- If `p.tail = []`: first component drops to 0.
- Otherwise, the new head `lt'` satisfies `expCmp lt'.exp lt.exp = .lt` by `WellFormed.head_exp_max`.
  Same case split on total degree vs. lex code as above.

**`foldl_divStep_spec`** *(private)*
If the fold over `List.range gs.size` (searching for the first successful `tryDivStep`)
returns `some (i, qt, p')`, then `tryDivStep p gs[i]! = some (qt, p')`.

Proves that the fold correctly reports: the returned `i` is indeed the index where the
first successful step occurred, and `(qt, p')` is exactly what `tryDivStep` returned there.

**`foldl_divStep_idx_lt`** *(private)*
Under the same hypothesis, `i < gs.size`.
The returned index is within bounds; follows because `i` must have been in `List.range gs.size`.

---

## Part 12 — The Main Algorithm

**`divAux (gs : Array Poly) (qs : Array Poly) (r p : Poly) (hwp : WellFormed p) (hwgs : ...) : Array Poly × Poly`** *(private)*

The recursive core. Maintains the invariant `f = ∑ᵢ qs[i] · gs[i] + r + p` where `f` is
the original dividend.

At each call:
- If `p = []`: done, return `(qs, r)`.
- **Division branch**: scan divisors for the first `i` with `tryDivStep p gs[i]! = some (qt, p')`.
  - Add `qt` to `qs[i]` and recurse on the reduced polynomial `p'`.
  - Termination: `tryDivStep_grlexPair_lt` ensures `polyGrlexPair p'` < `polyGrlexPair p`.
- **Remainder branch**: no divisor reduces `LT(p)`. Move `LT(p)` to the remainder:
  - Set `r' := padd r [lt]` and `p' := psub p [lt]`.
  - Recurse on `p'`.
  - Termination: `psub_head_grlexPair_lt` ensures `polyGrlexPair p'` < `polyGrlexPair p`.

Termination annotation: `termination_by polyGrlexPair p`.

---

## Summary of the Dependency Graph

```
expLexOrd, expCmp, expBlt, expDivides, expMdiv, expMmul
            ↓
  WellFormed (definition + accessors)
  mergeTerm, insertSorted, normalize
            ↓
  mergeTerm / insertSorted lemmas
  (pairwise_ne, coeff_ne, exp_len, membership, idempotency)
            ↓
  normalize_wf, normalize_wf_id
            ↓
  psub_wf_of_wf, mulTerm_wf, psub_head_cancel
            ↓
  mulTerm_head, psub_head_head_cancel
            ↓
  psub_mulTerm_lt   ←  expTotalDeg_expMmul, expCmp_expMmul_left, expMdiv_cancel
            ↓
  expLexCode, lexCodeFrom lemmas → expLexCode_strictMono
            ↓
  tryDivStep_grlexPair_lt   psub_head_grlexPair_lt
            ↓
  foldl_divStep_spec, foldl_divStep_idx_lt, tryDivStep_result_wf
            ↓
  divAux  (terminates and is correct)
```
