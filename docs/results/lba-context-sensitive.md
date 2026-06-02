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

The headline equality is [`CS_eq_LBA`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/EndmarkerToFlag.lean) — `(CS : Set (Language T)) = LBA` — for the canonical **endmarker** LBA (`is_LBA`/`LBA`, defined in `Automata/LinearBounded/Definition.lean`).

Its two halves are proved against an internal marker-free *flag* model `LBA_flag`
(`Automata/LinearBounded/FlagModel.lean`), which is then shown equal to the endmarker model. In
`Automata/LinearBounded/Equivalence/ContextSensitive.lean`:

- [`CS_eq_LBA_flag`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — `(CS : Set (Language T)) = LBA_flag`.
- [`CS_subset_LBA_flag`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — Kuroda's direction: every context-sensitive language is recognized by an LBA.
- [`LBA_flag_subset_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — Myhill's direction: every LBA language is context-sensitive.
- [`myhill_language_eq`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — the core LBA → CS bisimulation: the Myhill grammar generates exactly the LBA's (non-empty) language.

The equivalence of the two models is [`LBA_eq_LBA_flag`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/EndmarkerToFlag.lean) (`LBA = LBA_flag`), from the two simulations in `Equivalence/EndmarkerTape.lean` (flag ⊆ endmarker) and `Equivalence/EndmarkerToFlag.lean` (endmarker ⊆ flag).

The two construction halves live in their own directories, each split into a machine/grammar
construction plus completeness and soundness arguments, mirroring the `TM = RE` and `PDA = CFG`
developments:

- **LBA → CS (Myhill)** — [`Equivalence/LBAToCSG.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG.lean) (the grammar `myhillGrammar`), with [`LBAToCSG/Completeness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG/Completeness.lean) and [`LBAToCSG/Soundness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/LBAToCSG/Soundness.lean).
- **CS → LBA (Kuroda)** — [`Equivalence/CSGToLBA.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA.lean) (the simulator `kMachine`, capstone `noncontracting_finite_to_LBA`), with [`CSGToLBA/Construction.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA/Construction.lean), [`CSGToLBA/Completeness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA/Completeness.lean) (`kMachine_complete`) and [`CSGToLBA/Soundness.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/CSGToLBA/Soundness.lean) (`kMachine_sound`).

## The LBA model and the empty word

The canonical model is the **endmarker** LBA. The input `w` is written bracketed between a left
endmarker `⊢` and a right endmarker `⊣`, so the tape is `⊢ w ⊣` with `|w| + 2` cells, over the
alphabet `EndAlpha T Γ = Option (T ⊕ Γ) ⊕ Bool` (interior = blank / input / work over a finite
work alphabet `Γ`; the two `Bool` symbols are the endmarkers). The head is confined to the
bracketed region by the usual boundary clamping, and the working space comes entirely from `Γ`.

Crucially the empty word gets the genuine two-cell tape `⊢⊣`, on which the machine runs like any
other input: it accepts `ε` exactly when its transitions accept with the two markers adjacent. So
the machine itself decides `ε` — no external flag is needed, and `CS = LBA` holds on the nose
(rather than merely "up to `ε`").

Internally the two halves of the theorem are first proved against a marker-free **flag** model
(exactly `|w|` cells over `Option (T ⊕ Γ)`, with a Boolean `acceptEmpty` deciding `ε` in the role
of a grammar's optional `S → ε` rule), then transferred to the endmarker model via the
`LBA = LBA_flag` equivalence. The flag model is an internal convenience and never appears in the
final statement.

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

The empty-word bookkeeping (the optional `S → ε` rule, mirrored internally by the flag model's
`acceptEmpty`) and the reduction between the non-contracting core and Langlib's canonical class
`is_CS` glue the two halves into `CS_eq_LBA_flag`; transferring along `LBA = LBA_flag` gives the
headline endmarker-model equality `CS_eq_LBA`.

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
