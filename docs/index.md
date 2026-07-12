---
title: "Home"
description: "Langlib is a Lean 4 + Mathlib library of machine-checked results about regular, context-free, context-sensitive, recursive and recursively enumerable languages, automata, closure properties and decidability."
seo_title: "Langlib — formal-language theory and the Chomsky hierarchy, formalized in Lean 4"
nav_order: 1
---

# Langlib: formal-language theory in Lean 4

**Langlib** is a [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/) library of fully machine-checked results about grammars, automata, and language classes across the **Chomsky hierarchy** — regular, deterministic context-free, context-free, indexed, context-sensitive, recursive (decidable) and recursively enumerable languages. It formalizes the standard hierarchy theorems (PDA = CFG, CSG = LBA, TM = RE), closure properties (including the hard result that **deterministic context-free languages are closed under complement**), and decidability/computability results (including **every context-sensitive language is recursive** and **Post's theorem**). Source and build instructions are on [GitHub](https://github.com/nielstron/langlib).

This page is a catalog of the library's results.

## Main results

- [Deterministic context-free languages are closed under complement](results/dcfl-closed-under-complement.html)
- [DPDA totalization: every DPDA has an equivalent always-halting deciding DPDA](results/dpda-totalization.html)
- [Every indexed language is context-sensitive](results/indexed-subset-context-sensitive.html)
- [Every context-sensitive language is recursive — and strictly so (CS ⊊ Recursive)](results/context-sensitive-strict-subset-recursive.html)
- [Membership in context-sensitive languages is computable](results/context-sensitive-membership-computable.html)
- [Post's theorem (RE ∩ co-RE = recursive)](results/posts-theorem.html)
- [Tape vs. state acceptance for recursive languages](results/tape-vs-state-acceptance-recursive.html)
- [PDA = CFG: pushdown automata recognize exactly the context-free languages](results/pda-equals-cfg.html)
- [TM = RE: Turing machines recognize exactly the recursively enumerable languages](results/tm-equals-re.html)
- [CSL = LBA: context-sensitive languages are exactly the linear-bounded-automaton languages](results/lba-context-sensitive.html)
- [The pumping lemma for context-free languages](results/context-free-pumping-lemma.html)
- [Recursive ⊊ RE: recursive is a strict subset of recursively enumerable](results/recursive-strict-subset-re.html)

## Grammar ⇔ automaton equivalences

- [Regular grammars = DFA languages](results/regular-equals-dfa.html) — and left-regular ⇔ right-regular grammars.
- [PDA = CFG](results/pda-equals-cfg.html) — pushdown automata recognize exactly the context-free languages; final-state vs. empty-stack acceptance agree.
- [CSL = LBA](results/lba-context-sensitive.html) — context-sensitive grammars and linear bounded automata recognize exactly the same languages (the Myhill–Kuroda theorem); plus NLBA languages ⊆ Turing-machine languages.
- [TM = RE](results/tm-equals-re.html) — Turing machines recognize exactly the recursively enumerable (unrestricted-grammar) languages.
- [Langlib's `is_CF` = Mathlib's `IsContextFree`](results/context-free-equals-mathlib.html) — plus a verified Chomsky normal form.

## Hierarchy: strict inclusions

- [The Chomsky hierarchy is strict](results/chomsky-hierarchy-strict-inclusions.html): Regular ⊊ DCFL ⊊ CFL ⊊ Indexed, Regular ⊊ Linear ⊊ CFL, CF ⊆ CS ⊊ Recursive ⊊ RE.
- [CS ⊊ Recursive: context-sensitive languages are a strict subset of the recursive languages](results/context-sensitive-strict-subset-recursive.html) — by diagonalization (no closure shortcut exists).
- [{aⁿbⁿcⁿ} is indexed and context-sensitive but not context-free](results/anbncn-not-context-free.html) — the classic separating example.

## Regular languages

- [Regular grammars = DFA languages](results/regular-equals-dfa.html).
- [Right-regular and left-regular grammars](results/regular-grammars.html) — both generate exactly the regular languages.
- [Regular language membership is computable](results/regular-membership-computable.html).
- Top and Bottom are regular: `isRegular_top` and `isRegular_bot`.
- Closure: union, intersection, complement, concatenation, Kleene star, homomorphism, substitution, inverse homomorphism, reverse, quotient — all **Yes** (see the [closure table](#closure-properties)).

## Deterministic context-free languages (DCFL)

- [DCFL is closed under complement](results/dcfl-closed-under-complement.html) — the marquee result.
- [DPDA totalization](results/dpda-totalization.html) — the always-halting deciding-DPDA construction that powers it.
- DCFL ⊊ CFL: `DCF_subclass_CF`.
- [Closure properties (full picture)](results/dcfl-closure-properties.html) — closed under complement (and ∩/∪ with a regular language), but **not** under union, intersection, concatenation, star, homomorphism, substitution, or quotient.

## Context-free languages (CFL)

- [PDA = CFG](results/pda-equals-cfg.html).
- [Pumping lemma](results/context-free-pumping-lemma.html) and [Ogden's lemma](results/ogdens-lemma.html).
- [Chomsky normal form & Mathlib compatibility](results/context-free-equals-mathlib.html).
- [Closed under substitution](results/cf-closed-under-substitution.html) — with union, concatenation, homomorphism and Kleene star derived as corollaries.
- [Not closed under intersection](results/cfl-not-closed-under-intersection.html) — via the pumping lemma; non-closure under complement follows as a corollary.
- [Not closed under right quotient](results/cfl-not-closed-under-right-quotient.html) — a concrete powers-of-two construction (but closed under right quotient *with a regular language*).
- [Membership (CYK) and emptiness are decidable](results/cfl-decidability.html).
- Closure: union, concatenation, star, homomorphism, substitution, inverse homomorphism, reverse, intersection-with-regular, quotient-with-regular — **Yes**; complement, intersection, quotient — **No**. Also terminal bijections, permutations, prefix and suffix (see the [closure table](#closure-properties)).

## Linear languages

- [Linear grammars and the linear languages](results/linear-grammars.html) — regular ⊊ linear ⊆ context-free; `{aⁿbⁿ}` is linear.
- Regular ⊊ Linear ⊊ CFL: see [strict inclusions](results/chomsky-hierarchy-strict-inclusions.html).

## Indexed languages

- `{aⁿbⁿcⁿ}` is indexed: `is_Indexed_lang_eq_eq` (see [the separating-example page](results/anbncn-not-context-free.html)).
- CFL ⊊ Indexed: `CF_strict_subclass_Indexed`.
- [Every indexed language is context-sensitive](results/indexed-subset-context-sensitive.html), via Aho's finite compression and a certified linear-space row checker.
- Closure: union, concatenation, homomorphism, inverse homomorphism, reverse — **Yes** (see the [closure table](#closure-properties)).

## Context-sensitive languages (CSL)

- [Every context-sensitive language is recursive, strictly (CS ⊊ Recursive)](results/context-sensitive-strict-subset-recursive.html) — recursive via bounded derivations, and strictly so by diagonalization.
- [Membership in context-sensitive languages is computable](results/context-sensitive-membership-computable.html).
- [Non-contracting and non-erasing context-sensitive grammars](results/noncontracting-equals-context-sensitive.html) — Langlib defines CS as non-contracting; the equivalence with the non-erasing form is only partially formalized.
- [CSL = LBA: context-sensitive grammars and linear bounded automata recognize the same languages](results/lba-context-sensitive.html) (the Myhill–Kuroda theorem).
- [Indexed ⊆ context-sensitive](results/indexed-subset-context-sensitive.html) — the finite normal-form Aho simulation and its `21|w|` scheduler bound.
- CF ⊆ CS: `CF_subclass_CS`.
- Closure: ε-free homomorphism — `CS_closedUnderEpsFreeHomomorphism`; reverse — `CS_closedUnderReverse`; terminal bijections — `CS_bijemap_iff_CS`.

## Recursive (decidable) languages

- [Post's theorem (RE ∩ co-RE = recursive)](results/posts-theorem.html).
- [Recursive languages are closed under complement](results/recursive-closed-under-complement.html).
- [Tape vs. state acceptance for recursive languages](results/tape-vs-state-acceptance-recursive.html).
- [Recursive ⊊ RE](results/recursive-strict-subset-re.html).
- Closure: reverse — `Recursive_closedUnderReverse`.

## Recursively enumerable languages (RE)

- [TM = RE](results/tm-equals-re.html).
- [Compiling search procedures to Turing machines](results/search-procedures-to-turing-machines.html) — the reusable semi-decision → TM bridge behind TM = RE and the RE closures.
- [Closure properties (grammar & TM constructions)](results/re-closure-properties.html) — closed under union, intersection, concatenation, star, homomorphism, inverse homomorphism, reverse, quotient and substitution; **not** complement.
- `{aⁿbⁿcⁿ}` is RE: `lang_eq_eq_is_RE`.
- Membership, emptiness, universality and equivalence are all **undecidable**: `RE_membership_undecidable`, `RE_emptiness_undecidable`, `RE_universality_undecidable`, `RE_equivalence_undecidable`.

## Closure properties

A machine-checked closure table across all seven classes is in the project
[README](https://github.com/nielstron/langlib#closure). Abstract closure predicates
(`ClosedUnderUnion`, `ClosedUnderHomomorphism`, …) are defined as standalone
predicates. Highlights:

- [DCFL closure profile](results/dcfl-closure-properties.html) — closed under complement, but not union/intersection/concatenation/star/homomorphism.
- [CFL closed under substitution](results/cf-closed-under-substitution.html) (and its corollaries); **not** closed under [intersection](results/cfl-not-closed-under-intersection.html) or [right quotient](results/cfl-not-closed-under-right-quotient.html) (nor complement).
- [Recursive closed under complement](results/recursive-closed-under-complement.html); [RE closed under all standard operations except complement](results/re-closure-properties.html).

## Decidability and computability

Membership, emptiness, universality and equivalence are stated as **uniform**
class-level predicates (`ComputableMembership`, `ComputableEmptiness`, …): each bundles
that the encoding is **adequate** (`Characterizes C` — its range is exactly the class),
**effective** (`MembershipSemiDecidable`), and that the relevant decision is computable.
This makes both the positive and negative results genuine statements about the class,
not artefacts of the encoding.

- [Regular membership is computable](results/regular-membership-computable.html).
- [Context-free membership (CYK) and emptiness are decidable](results/cfl-decidability.html).
- [Context-sensitive membership is computable](results/context-sensitive-membership-computable.html) (and [every CSL is recursive — strictly](results/context-sensitive-strict-subset-recursive.html)).
- [Post's theorem](results/posts-theorem.html) underpins the recursive/RE decidability results.

---

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
