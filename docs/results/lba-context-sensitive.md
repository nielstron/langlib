---
title: "Linear bounded automata and context-sensitive grammars"
description: "Lean 4 formalizations relating linear bounded automata to context-sensitive grammars: the Myhill grammar construction and NLBA ⊆ Turing-machine languages."
parent: "Context-sensitive"
nav_order: 2
---

# Linear bounded automata and context-sensitive grammars

## Statement

The automaton model for the **context-sensitive** (type-1) languages is the
**linear bounded automaton** (LBA): a Turing machine restricted to the portion of
tape occupied by its input. The classical theorem is that LBAs and context-sensitive
grammars characterize the same class (the **Myhill–Landweber–Kuroda** result).

Langlib formalizes part of this bridge — see precisely what is and isn't proven
below; the full equivalence is **not yet complete**.

## What is proven (and what isn't)

- ✅ **The Myhill grammar is constructed** from an LBA, as a `CS_grammar` — the
  **non-erasing** (context-preserving) form of context-sensitive grammar — with its
  non-empty-output obligation discharged by `myhillAllRules_output_nonempty`.
- ✅ **NLBA languages ⊆ Turing-machine languages** (the LBA → TM inclusion).
- ⬜ **No language-level correspondence is proven, in either direction.** The file
  contains no theorem relating the Myhill grammar's language to the LBA's language —
  not even one inclusion — so neither LBA → CSG nor CSG → LBA is established. The only
  exported result about the construction is that its rules are well-formed
  (non-erasing).
- ⬜ **The converse direction (CSG → LBA)** — every context-sensitive language is
  accepted by some LBA — is not formalized at all.

So this is currently a grammar *construction* plus a separate *inclusion*, **not** a
proven `LBA ⇔ CSG` equivalence.

A further subtlety: the Myhill grammar is a `CS_grammar` (the non-erasing form), which
is itself only [partially bridged](noncontracting-equals-context-sensitive.html) to
Langlib's canonical context-sensitive class `is_CS` (defined via non-contracting
grammars). So even completing the Myhill correctness proof would not immediately yield
membership in `is_CS` without that bridge.

## In Lean

The LBA → CSG (Myhill) construction is in
`Automata/LinearBounded/Equivalence/LBAToCSG.lean`:

- [`myhillGrammar`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG.lean) — the (non-erasing) `CS_grammar` built from an LBA.
- [`myhillAllRules`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG.lean) and [`myhillAllRules_output_nonempty`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG.lean) — its rule set and the proof that every rule has non-empty output (the only exported theorem in the file).

On the inclusion side, every NLBA-recognizable language is Turing-recognizable —
`Automata/LinearBounded/Inclusion/TuringMachine.lean` shows
**NLBA languages ⊆ Turing-machine languages** via BFS determinization (see
[`LanguageN`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Inclusion/TuringMachine.lean)).
This combines with [CS ⊆ recursive](context-sensitive-is-recursive.html) to place the
context-sensitive languages inside the recursively enumerable ones.

## Proof idea

The Myhill grammar encodes LBA configurations as bracketed sentential forms of
bounded length and runs the LBA's transitions *in reverse*: starting from an
accepting configuration, it rewrites back to the input word. Because the LBA never
leaves the input region, all intermediate sentential forms have bounded length and
the rules never erase — so the result is structurally a (non-erasing)
context-sensitive grammar. Proving this construction **sound and complete** with
respect to the LBA's language — i.e. that it generates exactly that language — is the
remaining work. The NLBA ⊆ TM direction simulates the (nondeterministic) LBA by a
Turing machine that tracks the whole reachable configuration set, expanding it one
step at a time.

## Keywords / also known as

linear bounded automata context-sensitive grammars, LBA and CSG, Myhill
construction, type-1 languages automaton, NLBA, deterministic linear bounded
automaton, context-sensitive languages LBA characterization, LBA subset Turing
machine.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
