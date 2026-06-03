---
title: "Membership computable"
description: "A formal Lean 4 proof that membership in a regular language (DFA acceptance) is a computable predicate."
parent: "Regular"
nav_order: 3
---

# Regular language membership is computable

## Statement

Membership in a regular language is **computable**: there is an algorithm that runs a
DFA on a word and always halts with the correct accept/reject verdict.

This is packaged as the uniform class-level predicate `ComputableMembership RG` (and
emptiness as `ComputableEmptiness RG`), uniform in the encoded right-regular grammar.

## In Lean

- `regular_computableMembership` — `ComputableMembership RG regularLanguageOf`, the uniform class-level statement.
- `regular_computableEmptiness` — `ComputableEmptiness RG regularLanguageOf`.
- `dfa_membership_computablePred` — the underlying `ComputablePred (· ∈ M.accepts)` for a DFA `M`.

## Proof idea

`dfa_membership_computablePred` rewrites `w ∈ M.accepts` as `M.eval w ∈ M.accept`
and exhibits the decision function as a composition of two computable maps. First,
`M.eval = List.foldl M.step M.start` is primitive recursive by `Primrec.list_foldl`:
the step `M.step` is a function out of the finite domain `σ × α`, hence primitive
recursive via `Primrec.dom_finite`. Second, the accept-state test
`s ↦ decide (s ∈ M.accept)` is primitive recursive, again by `Primrec.dom_finite`
over the finite `σ`. Composing the two gives `ComputablePred (· ∈ M.accepts)`.
`regular_membership_computablePred` then unfolds `L.IsRegular` to a concrete DFA `M`,
equips its state type with a `Primcodable` instance via `Fin (Fintype.card σ)`, and
applies the DFA result.

## Keywords / also known as

regular language membership decidable, DFA acceptance computable, deciding regular
membership, ComputablePred regular language, finite automaton word problem.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
