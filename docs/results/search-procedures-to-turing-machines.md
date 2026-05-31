---
title: "Compiling search procedures to Turing machines (semi-decision → RE)"
description: "A reusable Lean 4 bridge that turns any computable search procedure into a Turing machine and hence a recursively enumerable language — the infrastructure behind TM = RE and the RE closure proofs."
---

# Compiling search procedures to Turing machines

## Why this exists

A language is **recursively enumerable** exactly when membership can be
*semi-decided*: enumerate candidate witnesses, test each, and halt as soon as one
works. Proving RE-ness one machine at a time is painful, so Langlib builds the bridge
**once**, as a small DSL: give it a *computable test* and it returns an actual Turing
machine recognizing the language. This is the engine behind both
[TM = RE](tm-equals-re.html) and the [RE closure properties](re-closure-properties.html)
(union, intersection, homomorphism, quotient, substitution, …) — each of those just
assembles a new computable test and feeds it to the bridge.

## The abstraction: `SearchProc`

A [`SearchProc`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/DSL/SearchProcedure.lean) captures the universal semi-decision pattern:

> *enumerate candidates from a countable domain; test each one; halt when a witness is found.*

The basic constructor [`searchNat`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/DSL/SearchProcedure.lean) builds one from a test `test : ℕ → List T → Bool`, and [`searchNat_language`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/DSL/SearchProcedure.lean) pins down what it accepts:

> `(searchNat test).language = { w | ∃ n, test n w = true }`.

## The bridge

Three steps take a *computable* test all the way to a Turing machine (every step is
`sorry`-free):

1. [`search_is_partrec`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/DSL/SearchProcToTM0.lean) — the µ-search over a computable `test` is **partial recursive**: it produces a Mathlib `ToPartrec.Code` `c` with `(∃ a, test a w) ↔ (c.eval [encode w]).Dom`.
2. [`code_implies_isTM_direct`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/DSL/CodeToTMDirect.lean) — that `Code` is compiled **directly to a `TM0` machine** realizing it (the bulk of the DSL: laying the partrec evaluator out as tape operations, via the block-realizability files).
3. [`is_TM_of_searchable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/DSL/SearchProcToTM0.lean) — the packaged result: from a computable `test` and `L = { w | ∃ a, test a w }`, it produces a `TM0.Machine M` and encoding with `w ∈ L ↔ (TM0.eval M (enc w)).Dom` (i.e. [`is_TM L`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/Definition.lean)).

Finally [`tm_recognizable_implies_re`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/Equivalence/TMToGrammar.lean) / [`is_TM_iff_is_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/Equivalence/TMEqualsRE.lean) convert the machine back into an unrestricted grammar, so `is_TM L → is_RE L`.

## The canonical instance: grammar membership *is* a search

The reason RE languages (defined via grammars) plug straight into this bridge is that
**membership in a grammar's language is itself a search** over derivation sequences:

- [`grammarTest`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/Equivalence/GrammarToTM/MembershipTest.lean) `g seq w` — checks whether a candidate derivation `seq` actually derives `w` in `g`.
- [`grammarTest_computable₂`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/Equivalence/GrammarToTM/MembershipComputability.lean) — that check is computable; [`grammarTest_complete`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Turing/Equivalence/GrammarToTM/MembershipTest.lean) — every member has a witnessing `seq`.

So `w ∈ grammar_language g ↔ ∃ seq, grammarTest g seq w`, a computable search — which is the `is_RE → is_TM` half of TM = RE. The [RE closure proofs](re-closure-properties.html) reuse exactly this: e.g. intersection builds the test `reIntersectionTest = grammarTest g₁ ∧ grammarTest g₂` over a *pair* of derivation witnesses, proves it computable, and hands it to `search_is_partrec` / `code_implies_isTM_direct`.

## Construction idea

The hard engineering is step 2 — realizing an arbitrary partial-recursive `Code` as a
concrete one-tape `TM0` machine. The DSL does this compositionally: each `Code`
constructor (composition, primitive recursion, the `rfind` µ-search) is realized as a
reusable "block" that operates on an encoded tape region (`SearchProcToTM0`,
`CodeToTMDirect`, and the `*BlockRealizability` files), and the blocks compose into a
machine whose halting domain matches the search's success set.

## Keywords / also known as

semi-decision procedure to Turing machine, search to TM compiler, recursively
enumerable via search, partial recursive Code to TM0, dovetailing witness search,
grammar membership semi-decidable, RE closure infrastructure, Lean formalization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
