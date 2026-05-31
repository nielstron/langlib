---
title: "Closure properties of recursively enumerable languages"
description: "Formal Lean 4 proofs that recursively enumerable languages are closed under union, intersection, concatenation, star, homomorphism, inverse homomorphism, reverse, quotient and substitution — but not complement — split by grammar-based vs Turing-machine constructions."
parent: "Recursively enumerable"
nav_order: 3
---

# Closure properties of recursively enumerable languages

## Statement

The recursively enumerable (RE, Chomsky type-0) languages are closed under essentially
**every** standard operation — union, intersection, concatenation, Kleene star,
homomorphism, inverse homomorphism, reverse, right quotient, substitution — with the
single famous exception of **complement**.

In Langlib `is_RE` is defined natively via **unrestricted grammars**
(`∃ g : grammar T, grammar_language g = L`). Accordingly the proofs fall into two
styles, and this page groups them that way:

- **Grammar constructions** — directly build a new type-0 grammar from the given one(s).
- **Turing-machine constructions** — exhibit a *semi-decider* (a dovetailed search that
  accepts exactly the members), compile it to a Turing machine via the
  [search-to-machine bridge](search-procedures-to-turing-machines.html), and bridge
  back to a grammar via [TM = RE](tm-equals-re.html).

## Closed under — grammar constructions

Proved by transforming the unrestricted grammar(s) directly:

- [`RE_of_RE_u_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Union.lean) — **union**: a fresh start symbol nondeterministically picks one of the two grammars (nonterminals tagged to avoid clashes).
- [`RE_of_RE_c_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Concatenation.lean) — **concatenation**: an initial rule emits the left grammar's start symbol followed by the right's; the tagged halves then derive independently.
- [`RE_of_star_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Star.lean) — **Kleene star**: fresh start/separator/scanner nonterminals splice together arbitrarily many copies, scanning terminals left to right.
- [`RE_of_reverse_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Reverse.lean) — **reverse**: reverse each rule's left context, right context, and output string.
- [`RE_closedUnderEpsFreeHomomorphism`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Homomorphism.lean) — **ε-free homomorphism**: a two-phase grammar lifts each terminal to a placeholder nonterminal, then expands each placeholder to its homomorphic image (soundness needs the homomorphism to be ε-free).

## Closed under — Turing-machine constructions

Proved by semi-deciding membership with a dovetailed search and compiling it to a
machine (the `re…Test` searches below), then converting back to a grammar:

- [`RE_of_RE_i_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Intersection.lean) — **intersection**: search for a *pair* of derivation witnesses (one per grammar) for the same word (also `RE_closedUnderIntersectionWithRegular`).
- [`RE_closedUnderHomomorphism`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Homomorphism.lean) — **(general) homomorphism**: search for a source word whose homomorphic image is the input and which the source grammar derives.
- [`RE_of_inverseHomomorphism_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/InverseHomomorphism.lean) — **inverse homomorphism**: compute `h(input)` and test membership in the original grammar.
- [`RE_of_RE_rightQuotient_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Quotient.lean) — **right quotient**: search for a suffix in the second language making `input · suffix` derivable (also `RE_closedUnderRightQuotientWithRegular`).
- [`RE_of_subst_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Substitution.lean) — **substitution**: assembled from the operations above (a per-symbol block under star, intersected with an inverse-homomorphic projection, then erased by a homomorphism), so it ultimately rests on the TM-based intersection and inverse homomorphism.

**Why a machine and not a grammar?** Each of these imposes a *condition relating
derivations* — a conjunction of two derivations, or an existential over preimages —
that an unrestricted grammar cannot enforce directly, but a Turing machine can
semi-decide by dovetailed search.

## Not closed under complement

[`RE_notClosedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Closure/Complement.lean) — the one operation that fails. The halting problem is encoded as a unary RE language; if its complement were also RE, then by [Post's theorem](posts-theorem.html) (RE ∩ co-RE = recursive) the halting problem would be recursive — contradicting its undecidability (Mathlib's `ComputablePred.halting_problem_not_re`). Equivalently, closure under complement would collapse RE to the recursive languages, contradicting [Recursive ⊊ RE](recursive-strict-subset-re.html).

## Keywords / also known as

recursively enumerable closure properties, RE closed under union intersection
concatenation star, type-0 language closure, RE not closed under complement,
semi-decidable language closure, unrestricted grammar constructions, Turing machine
closure constructions, Lean formalization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
