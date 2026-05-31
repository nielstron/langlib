---
title: "Langlib — formal-language theory and the Chomsky hierarchy, formalized in Lean 4"
description: "Langlib is a Lean 4 + Mathlib library of machine-checked results about regular, context-free, context-sensitive, recursive and recursively enumerable languages, automata, closure properties and decidability."
---

# Langlib: formal-language theory in Lean 4

**Langlib** is a [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/) library of fully machine-checked results about grammars, automata, and language classes across the **Chomsky hierarchy** — regular, deterministic context-free, context-free, indexed, context-sensitive, recursive (decidable) and recursively enumerable languages. It formalizes the standard hierarchy theorems (PDA = CFG, TM = RE), closure properties (including the hard result that **deterministic context-free languages are closed under complement**), and decidability/computability results (including **every context-sensitive language is recursive** and **Post's theorem**). Source and build instructions are on [GitHub](https://github.com/nielstron/langlib).

This page is a catalog of the library's results.

## Main results

- [Deterministic context-free languages are closed under complement](results/dcfl-closed-under-complement.html)
- [DPDA totalization: every DPDA has an equivalent always-halting deciding DPDA](results/dpda-totalization.html)
- [Every context-sensitive language is recursive (CS ⊆ Recursive)](results/context-sensitive-is-recursive.html)
- [Membership in context-sensitive languages is computable](results/context-sensitive-membership-computable.html)
- [Post's theorem (RE ∩ co-RE = recursive)](results/posts-theorem.html)
- [Tape vs. state acceptance for recursive languages](results/tape-vs-state-acceptance-recursive.html)
- [PDA = CFG: pushdown automata recognize exactly the context-free languages](results/pda-equals-cfg.html)
- [TM = RE: Turing machines recognize exactly the recursively enumerable languages](results/tm-equals-re.html)
- [Linear bounded automata and context-sensitive grammars](results/lba-context-sensitive.html) (Myhill construction — partial)
- [The pumping lemma for context-free languages](results/context-free-pumping-lemma.html)
- [Recursive ⊊ RE: recursive is a strict subset of recursively enumerable](results/recursive-strict-subset-re.html)

## Grammar ⇔ automaton equivalences

- [Regular grammars = DFA languages](results/regular-equals-dfa.html) — and left-regular ⇔ right-regular grammars.
- [PDA = CFG](results/pda-equals-cfg.html) — pushdown automata recognize exactly the context-free languages; final-state vs. empty-stack acceptance agree.
- [Linear bounded automata → context-sensitive grammars](results/lba-context-sensitive.html) — the Myhill grammar construction (full LBA ⇔ CSG equivalence not yet formalized); plus NLBA languages ⊆ Turing-machine languages.
- [TM = RE](results/tm-equals-re.html) — Turing machines recognize exactly the recursively enumerable (unrestricted-grammar) languages.
- [Langlib's `is_CF` = Mathlib's `IsContextFree`](results/context-free-equals-mathlib.html) — plus a verified Chomsky normal form.

## Hierarchy: strict inclusions

- [The Chomsky hierarchy is strict](results/chomsky-hierarchy-strict-inclusions.html): Regular ⊊ DCFL ⊊ CFL ⊊ Indexed, Regular ⊊ Linear ⊊ CFL, CF ⊆ CS, Recursive ⊊ RE.
- [{aⁿbⁿcⁿ} is indexed and context-sensitive but not context-free](results/anbncn-not-context-free.html) — the classic separating example.

## Regular languages

- [Regular grammars = DFA languages](results/regular-equals-dfa.html).
- [Right-regular and left-regular grammars](results/regular-grammars.html) — both generate exactly the regular languages.
- [Regular language membership is computable](results/regular-membership-computable.html).
- Top and Bottom are regular: [`Classes/Regular/Examples/TopBot.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Examples/TopBot.lean).
- Closure: union, intersection, complement, concatenation, Kleene star, homomorphism, substitution, inverse homomorphism, reverse, quotient — all **Yes** (see the [closure table](#closure-properties)).

## Deterministic context-free languages (DCFL)

- [DCFL is closed under complement](results/dcfl-closed-under-complement.html) — the marquee result.
- [DPDA totalization](results/dpda-totalization.html) — the always-halting deciding-DPDA construction that powers it.
- DCFL ⊊ CFL: [`DeterministicContextFree/Inclusion/ContextFree.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Inclusion/ContextFree.lean).
- DCFL is **not** closed under union: [`DCF_notClosedUnderUnion`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Union.lean) (and likewise intersection, concatenation, star, homomorphism, substitution, reverse, quotient).
- DCFL **is** closed under intersection with a regular language: [`Closure/IntersectionRegular.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/IntersectionRegular.lean), and union with a regular language: [`Closure/UnionRegular.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/UnionRegular.lean).

## Context-free languages (CFL)

- [PDA = CFG](results/pda-equals-cfg.html).
- [Pumping lemma](results/context-free-pumping-lemma.html) and [Ogden's lemma](results/ogdens-lemma.html).
- [Chomsky normal form & Mathlib compatibility](results/context-free-equals-mathlib.html).
- [Closed under substitution](results/cf-closed-under-substitution.html) — with union, concatenation, homomorphism and Kleene star derived as corollaries.
- [Not closed under intersection](results/cfl-not-closed-under-intersection.html) — via the pumping lemma; non-closure under complement follows as a corollary.
- [Membership (CYK) and emptiness are decidable](results/cfl-decidability.html).
- Closure: union, concatenation, star, homomorphism, substitution, inverse homomorphism, reverse, intersection-with-regular, quotient-with-regular — **Yes**; complement, intersection, quotient — **No**. Also terminal bijections, permutations, prefix and suffix (see the [closure table](#closure-properties)).

## Linear languages

- [Linear grammars and the linear languages](results/linear-grammars.html) — regular ⊊ linear ⊆ context-free; `{aⁿbⁿ}` is linear.
- Regular ⊊ Linear ⊊ CFL: see [strict inclusions](results/chomsky-hierarchy-strict-inclusions.html).

## Indexed languages

- `{aⁿbⁿcⁿ}` is indexed: [`Classes/Indexed/Examples/AnBnCn.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Indexed/Examples/AnBnCn.lean) (see [the separating-example page](results/anbncn-not-context-free.html)).
- CFL ⊊ Indexed: [`ContextFree/Inclusion/StrictIndexed.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean).
- Closure: union, concatenation, homomorphism, inverse homomorphism, reverse — **Yes** (see the [closure table](#closure-properties)).

## Context-sensitive languages (CSL)

- [Every context-sensitive language is recursive (CS ⊆ Recursive)](results/context-sensitive-is-recursive.html).
- [Membership in context-sensitive languages is computable](results/context-sensitive-membership-computable.html).
- [Non-contracting and non-erasing context-sensitive grammars](results/noncontracting-equals-context-sensitive.html) — Langlib defines CS as non-contracting; the equivalence with the non-erasing form is only partially formalized.
- [Linear bounded automata and context-sensitive grammars](results/lba-context-sensitive.html) (Myhill construction — partial).
- CF ⊆ CS: [`ContextFree/Inclusion/ContextSensitive.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/ContextSensitive.lean).
- Closure: ε-free homomorphism — [`Closure/EpsFreeHomomorphism.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Closure/EpsFreeHomomorphism.lean); reverse — [`Closure/Reverse.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Closure/Reverse.lean); terminal bijections — [`Closure/Bijection.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Closure/Bijection.lean).

## Recursive (decidable) languages

- [Post's theorem (RE ∩ co-RE = recursive)](results/posts-theorem.html).
- [Recursive languages are closed under complement](results/recursive-closed-under-complement.html).
- [Tape vs. state acceptance for recursive languages](results/tape-vs-state-acceptance-recursive.html).
- [Recursive ⊊ RE](results/recursive-strict-subset-re.html).
- Closure: reverse — [`Closure/Reverse.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Closure/Reverse.lean).

## Recursively enumerable languages (RE)

- [TM = RE](results/tm-equals-re.html).
- `{aⁿbⁿcⁿ}` is RE: [`Classes/RecursivelyEnumerable/Examples/AnBnCn.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Examples/AnBnCn.lean).
- Closure: union, intersection, complement (**No**), concatenation, star, homomorphism, substitution, inverse homomorphism, reverse, quotient — see the [closure table](#closure-properties). Membership, emptiness, universality and equivalence are all **undecidable**: [`RecursivelyEnumerable/Decidability/`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Decidability).

## Closure properties

A machine-checked closure table across all seven classes is in the project
[README](https://github.com/nielstron/langlib#closure). Abstract closure predicates
(`ClosedUnderUnion`, `ClosedUnderHomomorphism`, …) are defined in
[`Utilities/ClosurePredicates.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Utilities/ClosurePredicates.lean).
Highlights:

- [DCFL closed under complement](results/dcfl-closed-under-complement.html) (but not union/intersection).
- [CFL not closed under intersection](results/cfl-not-closed-under-intersection.html) (nor complement; but closed under union, star, concatenation, …).
- [Recursive closed under complement](results/recursive-closed-under-complement.html); RE **not** closed under complement.

## Decidability and computability

Results proved with the strong `ComputablePred` (genuine computability), not merely
`Decidable`:

- [Regular membership is computable](results/regular-membership-computable.html).
- [Context-free membership (CYK) and emptiness are decidable](results/cfl-decidability.html).
- [Context-sensitive membership is computable](results/context-sensitive-membership-computable.html) (and [every CSL is recursive](results/context-sensitive-is-recursive.html)).
- [Post's theorem](results/posts-theorem.html) underpins the recursive/RE decidability results.

---

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
