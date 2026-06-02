---
title: "Grammar forms"
description: "How Langlib defines context-sensitive languages (via non-contracting grammars) and the partially-formalized relationship to the classical non-erasing context-preserving form."
parent: "Context-sensitive"
nav_order: 2
---

# Non-contracting and non-erasing context-sensitive grammars

There are two classical ways to define the context-sensitive (Chomsky type-1)
grammars, and they are *provably* the same class only via a real construction
(Kuroda normal form). This page records exactly which definition Langlib uses and how
much of the bridge to the other one is formalized.

## The two definitions

- **Non-contracting (monotone):** no rule shortens the sentential form — every rule
  `α → β` has `|β| ≥ |α|`. A single rule may rewrite a whole block, e.g. `A B → C D`.
- **Non-erasing / context-preserving:** every rule has the restricted shape
  `α A β → α γ β` with `γ ≠ ε` — only one nonterminal is rewritten, and only in a
  fixed left/right context.

**Langlib's context-sensitive languages are defined via the *non-contracting* form.**
`is_CS` quantifies over `grammar_context_sensitive` grammars, whose core condition is
`grule_noncontracting` (`|output| ≥ |input|`), together with an optional distinguished
`S → ε` rule guarded by `initial_not_on_rhs` (`S` may not appear on any right-hand
side when `S → ε` is present).

## In Lean

The definition:

- [`is_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Definition.lean) via [`grammar_context_sensitive`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Definition.lean) and [`grule_noncontracting`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Definition.lean) — the **non-contracting** definition.
- The non-erasing form is a separate notion: [`csrule`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Grammars/ContextSensitive/Definition.lean) / [`CS_grammar`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Grammars/ContextSensitive/Definition.lean) (with `output_nonempty`), surfaced as [`is_CS_via_csg`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Definition.lean).

## What is proven (and what isn't)

- ✅ **Non-erasing ⇒ non-contracting:** [`CS_is_noncontracting`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Grammars/NonContracting/Equivalence/ContextSensitive.lean) — every `CS_grammar` induces a non-contracting grammar with the same language.
- ✅ **Non-contracting ⇒ `is_CS`:** [`is_CS_of_is_noncontracting`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Definition.lean) — but this is essentially **by definition**, since `is_CS` already *means* non-contracting (the proof is a one-liner).
- ◑ **Non-contracting ⇒ non-erasing (the hard direction):** the "lock" construction builds a non-erasing `CS_grammar` from a non-contracting grammar, and **one** language inclusion is proven unconditionally ([`grammar_language_subset_csg_of_noncontracting`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Grammars/NonContracting/Equivalence/ContextSensitive.lean)).
- ⬜ **The reverse inclusion is not yet established:** the full correctness of the construction (and hence a genuine non-erasing ⇔ non-contracting equivalence) is currently **conditional on an unproven property**, [`NC_locked_dirty_interval_macro_property`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Grammars/NonContracting/Equivalence/ContextSensitive.lean), which appears only as a hypothesis and is never discharged.

So Langlib **uses** the non-contracting definition, fully proves that non-erasing
grammars are a special case of it, and has built — but not yet completely verified —
the harder converse construction.

## Proof idea (the lock construction)

The remaining work is to simulate an arbitrary block-rewriting non-contracting rule
`X₁…Xₘ → Y₁…Yₙ` by single-symbol, context-preserving (non-erasing) steps. Fresh
**"lock"** nonterminals fire the rule one position at a time: a marker sweeps across
the `m` positions, replacing each `Xᵢ` while carrying the surrounding context along,
and only unlocks once the whole block has become `Y₁…Yₙ`. Each individual step is
genuinely context-sensitive. The missing piece is the bookkeeping lemma
(`NC_locked_dirty_interval_macro_property`) needed to show the locked grammar derives
*exactly* the same terminal words, not a superset.

## Keywords / also known as

context-sensitive grammar definition, non-contracting vs non-erasing grammars,
monotone grammars, Kuroda normal form, type-1 grammar normal form, length-increasing
grammars, Lean formalization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
