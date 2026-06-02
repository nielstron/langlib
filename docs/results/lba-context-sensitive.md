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

- [`CS_eq_LBA`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — the headline class equality `(CS : Set (Language T)) = LBA` for the canonical **endmarker** LBA (`is_LBA`/`LBA`, `Automata/LinearBounded/Definition.lean`).
- [`CS_subset_LBA`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) / [`LBA_subset_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — the Kuroda and Myhill directions.
- [`is_LBA_pos_iff`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — `is_LBA_pos L ↔ is_CS L ∧ [] ∉ L`: the genuinely space-bounded core. The marker-free `|w|`-cell model `is_LBA_pos` (`Automata/LinearBounded/Positive.lean`) recognizes exactly the **ε-free** context-sensitive languages.
- [`myhill_language_eq`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) — the core LBA → CS bisimulation: the Myhill grammar generates exactly the bounded-tape machine's (non-empty) language.

The endmarker's two simulations live in `Equivalence/EndmarkerTape.lean` (`simMachine`/`language_simMachine_eq` — run a bounded-tape machine on `⊢ w ⊣`) and `Equivalence/EndmarkerToFlag.lean` (`flagMachine`/`language_flagMachine_eq` — fold the markers away onto `|w|` cells).

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

The genuinely space-bounded content is isolated in the marker-free `|w|`-cell model `is_LBA_pos`
(`Automata/LinearBounded/Positive.lean`): a tape of exactly `|w|` cells over `Option (T ⊕ Γ)`,
which (having no cell to run on for `ε`) recognizes precisely the **ε-free** context-sensitive
languages — `is_LBA_pos L ↔ is_CS L ∧ [] ∉ L`. The endmarker model is this plus the `ε` case, run
natively on `⊢⊣`; that single extra cell is exactly what upgrades "ε-free CSL" to all of `CS`. So
there is no empty-word *flag* anywhere — the only place `ε` is decided is the machine's behaviour on
the two-cell tape `⊢⊣`.

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

The reduction between the non-contracting core and Langlib's canonical class `is_CS` gives the
ε-free characterization `is_LBA_pos_iff`; running the bounded-tape machine on `⊢ w ⊣` and deciding
`ε` on `⊢⊣` (the two `language_*_eq` simulations) then upgrades it to the headline `CS_eq_LBA`.

## Related

Every LBA language is also Turing-recognizable —
[`Automata/LinearBounded/Inclusion/TuringMachine.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Inclusion/TuringMachine.lean)
shows **NLBA languages ⊆ Turing-machine languages** via BFS determinization. Combined with
[CS ⊆ recursive](context-sensitive-strict-subset-recursive.html) this places the context-sensitive
languages inside the recursive (hence recursively enumerable) ones. The non-contracting form of
context-sensitive grammar used in the Kuroda direction is bridged to Langlib's canonical class in
[non-contracting = context-sensitive](noncontracting-equals-context-sensitive.html).

## Keywords / also known as

context-sensitive languages equal linear bounded automata, CSL = LBA, LBA ⇔ CSG,
Myhill–Landweber–Kuroda theorem, Kuroda construction, Myhill grammar construction, type-1
languages automaton characterization, NLBA, nondeterministic linear bounded automaton.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
