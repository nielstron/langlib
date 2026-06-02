---
title: "Post's theorem (RE ∩ co-RE = recursive)"
description: "A formal Lean 4 proof of Post's theorem: a language is recursive (decidable) iff both it and its complement are recursively enumerable."
parent: "Recursive"
nav_order: 1
---

# Post's theorem: RE ∩ co-RE = recursive

## Statement

A language `L` is **recursive** (decidable) if and only if both `L` and its
complement `Lᶜ` are **recursively enumerable** (semi-decidable). Equivalently,
`RE ∩ co-RE = Recursive`. Langlib formalizes the substantive direction: if `L` and
`Lᶜ` are both RE, then `L` is recursive.

## In Lean

In `Classes/Recursive/Basics/Post.lean`:

- [`is_Recursive_of_isRE_of_isRE_compl`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Basics/Post.lean) — recursive form: `is_RE L → is_RE Lᶜ → is_Recursive L`.
- [`computablePred_of_isRE_of_isRE_compl`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Basics/Post.lean) — computability form: yields an explicit `ComputablePred` decider.
- [`REPred_mem_of_is_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Basics/Post.lean) — bridges the language-level RE predicate to a computability-theoretic `RePred`.

## Proof idea

The argument reduces to Mathlib's computability-theoretic version of Post's theorem,
`ComputablePred.computable_iff_re_compl_re'`: a predicate is computable iff both it and
its negation are `RePred` (recursively enumerable).

1. **Membership is an `RePred` for any RE language** (`REPred_mem_of_is_RE`). Given a
   grammar `g` generating `L`, `grammar_equivalent_finiteNT` replaces it by an
   equivalent grammar `g'` with finitely many nonterminals (made `Primcodable`).
   Membership of `w` is then the semi-decidable search `∃ seq, grammarTest g' seq w =
   true` over candidate derivation sequences. This is exposed as a domain of `Nat.rfind`
   — decoding each natural to a sequence via `Encodable.decode` and testing it with the
   computable `grammarTest g'` (`grammarTest_computable₂`) — so it is `Partrec`; its
   domain is the `RePred`. Soundness/completeness of the search
   (`grammarTest_sound` / `grammarTest_complete`) identify this domain with `w ∈ L`.

2. **From RE ∩ co-RE to computable membership** (`computablePred_of_isRE_of_isRE_compl`).
   Apply step 1 to `L` and to `Lᶜ` (rewriting `RePred` of the complement through
   `Set.mem_compl_iff`), then feed both `RePred` facts to
   `ComputablePred.computable_iff_re_compl_re'` to get a `ComputablePred`.

3. **From computable membership to recursive** (`is_Recursive_of_isRE_of_isRE_compl`).
   `ComputablePred.computable_iff` extracts a total computable decider `f`, which
   `is_Recursive_of_computable_decide` compiles into an always-halting `Turing.TM0`
   decider, i.e. `is_Recursive L`.

## Keywords / also known as

Post's theorem, RE intersect co-RE equals recursive, decidable iff semidecidable
and co-semidecidable, recursive equals RE and co-RE, complementation theorem for
recursively enumerable sets, Emil Post theorem computability.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
