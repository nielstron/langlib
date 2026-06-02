---
title: "CSL = LBA: context-sensitive languages are exactly the linear-bounded-automaton languages"
description: "A formal Lean 4 proof of the Myhill–Landweber–Kuroda theorem: context-sensitive grammars and linear bounded automata characterize the same class of languages."
parent: "Context-sensitive"
nav_order: 2
---

# Context-sensitive languages are exactly the LBA languages (CSL = LBA)

## Statement

The automaton model for the **context-sensitive** (type-1) languages is the
**linear bounded automaton** (LBA): a nondeterministic Turing machine restricted to the
portion of tape occupied by its input. The classical **Myhill–Landweber–Kuroda** theorem
says that LBAs and context-sensitive grammars characterize the same class of languages.

Langlib formalizes this as a full class equality

$$\mathrm{CS} = \mathrm{LBA},$$

machine-checked and free of `sorry`.

## In Lean

In `Automata/LinearBounded/Equivalence/ContextSensitive.lean`:

- [`CS_eq_LBA`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — the class equality `(CS : Set (Language T)) = LBA`.
- [`CS_subset_LBA`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — Kuroda's direction: every context-sensitive language is recognized by an LBA.
- [`LBA_subset_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — Myhill's direction: every LBA language is context-sensitive.
- [`myhill_language_eq`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — the core LBA → CS bisimulation: the Myhill grammar generates exactly the LBA's (non-empty) language.

The two construction halves live in their own directories, each split into a machine/grammar
construction plus completeness and soundness arguments, mirroring the `TM = RE` and `PDA = CFG`
developments:

- **LBA → CS (Myhill)** — [`Equivalence/LBAToCSG.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG.lean) (the grammar `myhillGrammar`), with [`LBAToCSG/Completeness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG/Completeness.lean) and [`LBAToCSG/Soundness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG/Soundness.lean).
- **CS → LBA (Kuroda)** — [`Equivalence/CSGToLBA.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA.lean) (the simulator `kMachine`, capstone `noncontracting_finite_to_LBA`), with [`CSGToLBA/Construction.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA/Construction.lean), [`CSGToLBA/Completeness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA/Completeness.lean) (`kMachine_complete`) and [`CSGToLBA/Soundness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA/Soundness.lean) (`kMachine_sound`).

## The LBA model and the empty word

Langlib's LBA stays close to its Turing-machine / recursive definitions: the tape alphabet is
`Option (T ⊕ Γ)` (the same sum shape as the recursive/TM model) for a finite working alphabet
`Γ`, the input is written canonically via `some ∘ Sum.inl`, and the tape has **exactly `|w|`
cells** — the working space comes entirely from `Γ` (which is provably the same class as a
`k·|w|`-cell model, but keeps a clean one-cell-per-symbol correspondence).

Because a bounded tape has no cell to run on for the empty input, the recognizer pairs the
machine with an explicit `acceptEmpty : Bool`. This is exactly the role of the optional `S → ε`
rule in the definition of a context-sensitive grammar: it decides membership of `ε` and is
otherwise irrelevant to the genuinely space-bounded computation on non-empty inputs. It is what
makes the two classes *equal* rather than merely "equal up to `ε`".

## Proof idea

**CS → LBA (Kuroda).** Given a context-sensitive language, restrict to a non-contracting grammar
`g₀` with finitely many nonterminals (`exists_noncontracting_offEmpty_of_CS`), whose language is
the original one minus `ε`. The simulator `kMachine g₀` works on a tape of `|w|` cells whose
work track decodes to a sentential form. It nondeterministically **runs the grammar backwards**:
from the input word it repeatedly rewrites an occurrence of a rule's output back to the rule's
input pattern (`patList`), and accepts once the track has been reduced to the single start
symbol `[S]`. Non-contraction guarantees every sentential form of a derivation of `w` fits in
`|w|` cells, so the bounded tape suffices. *Completeness* replays a forward derivation
`[S] ⇒* w` in reverse (`kMachine_complete`); *soundness* maintains a forward invariant — at
every reachable configuration the decoded form still derives to `w`, so an accepting run that
verifies `[S]` exhibits a genuine derivation (`kMachine_sound`).

**LBA → CS (Myhill).** The Myhill grammar encodes LBA configurations as bracketed
sentential forms of bounded length and runs the LBA's transitions in reverse. Because the LBA
never leaves the input region, intermediate forms stay bounded and the rules never erase, so the
construction is structurally context-sensitive; `myhill_language_eq` proves it generates exactly
the automaton's non-empty language.

The empty-word bookkeeping (via `acceptEmpty` and the optional `S → ε` rule) and the reduction
between the non-contracting core and Langlib's canonical class `is_CS` glue the two halves into
the class equality `CS_eq_LBA`.

## Related

Every LBA language is also Turing-recognizable —
[`Automata/LinearBounded/Inclusion/TuringMachine.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Inclusion/TuringMachine.lean)
shows **NLBA languages ⊆ Turing-machine languages** via BFS determinization. Combined with
[CS ⊆ recursive](context-sensitive-is-recursive.html) this places the context-sensitive
languages inside the recursive (hence recursively enumerable) ones. The non-contracting form of
context-sensitive grammar used in the Kuroda direction is bridged to Langlib's canonical class in
[non-contracting = context-sensitive](noncontracting-equals-context-sensitive.html).

## Keywords / also known as

context-sensitive languages equal linear bounded automata, CSL = LBA, LBA ⇔ CSG,
Myhill–Landweber–Kuroda theorem, Kuroda construction, Myhill grammar construction, type-1
languages automaton characterization, NLBA, nondeterministic linear bounded automaton.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
