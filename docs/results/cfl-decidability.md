---
title: "Decidability"
description: "A formal Lean 4 proof that membership (via the CYK algorithm) and emptiness are computable for context-free languages."
parent: "Context-free"
nav_order: 4
---

# Membership and emptiness are decidable for context-free languages

## Statement

For context-free languages, two basic problems are **computable**:

- **Membership** — does a given word belong to the language? Decided by the CYK
  algorithm.
- **Emptiness** — does the grammar generate any word at all?

(Universality and equivalence of context-free languages are, by contrast,
undecidable.)

Both are stated as the **uniform computability predicate** for the context-free
class `CF`: a single algorithm, uniform in the encoded grammar, that decides the problem
across the whole class. `ComputableMembership CF` / `ComputableEmptiness CF` each bundle
three obligations about the encoding `contextFreeLanguageOf`:

1. **Adequacy** — `Characterizes CF contextFreeLanguageOf`: the encoding's range is
   *exactly* `CF` (every code denotes a context-free language, and every context-free
   language is denoted by some code).
2. **Effectivity** — `MembershipSemiDecidable contextFreeLanguageOf`: the relation
   `w ∈ contextFreeLanguageOf c` is recursively enumerable jointly in `(c, w)`, so the
   encoding cannot smuggle the answer into the code.
3. The relevant decision is computable.

Without (1)–(2) a positive or negative result could be made vacuous by an adversarial
encoding; together they make the statement a genuine fact about the *class*.

## In Lean

- Membership: `contextFree_computableMembership` — `ComputableMembership CF contextFreeLanguageOf`.
- Emptiness: `contextFree_computableEmptiness` — `ComputableEmptiness CF contextFreeLanguageOf`.

Adequacy is `contextFreeLanguageOf_characterizes`; the membership and emptiness deciders are a bitvector CYK table and a least-fixpoint computation of the productive nonterminals, respectively.

## Proof idea

Membership: convert the grammar to Chomsky normal form (`mathlib_cfg_of_cfg g |>.toCNF`)
and run **CYK** — a dynamic-programming table (`cykBuildTable`) over all substrings
recording which nonterminals derive each substring, with the final check
(`cykMemCheck`) asking whether the start symbol derives the whole word. Nonterminals
are first injected into `ℕ` and nonterminal *sets* are encoded as bitvectors
(`Nat.testBit`), so every table operation is shown `Primrec`; `cf_membership_computable`
packages the result as a `ComputablePred`.

Emptiness: compute the productive nonterminals by iterating the monotone
`productiveStep` operator `g.rules.card` times from `productiveInit`
(`productiveNTs`) — enough iterations to reach the fixpoint — and report nonempty iff
the start symbol is productive. `encoded_cf_emptiness_decidable` is the `Decidable`
instance and `encoded_cf_emptiness_computable` the `ComputablePred`, both uniform in
the encoded grammar.

Adequacy (`contextFreeLanguageOf_characterizes`): *soundness* is immediate — an
`EncodedCFG` decodes to a `CF_grammar` (`toCFGrammar`), so its language is context-free.
*Completeness* takes any context-free language, extracts a grammar with finitely many
nonterminals (`exists_fintype_nt`), reindexes those nonterminals to `Fin (n+1)`, and
reads the grammar off as an `EncodedCFG`. The key lemma is that reindexing the
nonterminals along an equivalence preserves the language (`cf_language_eq_of_rename`):
a derivation pushes forward along the equivalence and pulls back along its inverse via
the lifting machinery (`lift_deri` / `sink_deri`), and since a generated word is
terminal-only the renaming is invisible on the language. Effectivity
(`MembershipSemiDecidable`) is the CYK decider weakened to `REPred` via
`ComputablePred.to_re`.

## Keywords / also known as

context-free membership decidable, CYK algorithm Lean, CFG emptiness decidable,
deciding context-free membership, Cocke–Younger–Kasami, context-free word problem,
type-2 decidability.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
