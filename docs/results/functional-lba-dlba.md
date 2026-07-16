---
title: "Functional LBA determinization"
description: "The formal single-valued LBA-to-DLBA conversion, and the precise boundary of the open first LBA problem."
parent: "Context-sensitive"
nav_order: 6
---

# Functional LBAs are deterministic; the general LBA problem remains open

## The open problem

Langlib's `LBA` is the class recognized by nondeterministic linear bounded
automata, while `DLBA` is its deterministic counterpart.  The easy inclusion

$$\mathrm{DLBA}\subseteq\mathrm{LBA}$$

is formalized, but the reverse inclusion is the classical **first LBA
problem**:

$$\mathrm{LBA}\stackrel{?}{=}\mathrm{DLBA}.$$

In standard complexity terminology this is
`NSPACE(O(n)) =? DSPACE(O(n))`.  It remains open; neither an equality proof nor
a separating language is currently known.  Exponential padding shows that
`L = NL` would imply equality at linear space, so a strict LBA/DLBA separation
would in particular prove `L ≠ NL`.

That complexity-theoretic comparison uses the standard model equivalences.
Langlib's current `is_DLBA` presentation permits a deterministic machine to
loop on rejected inputs and handles `ε` with a separate bit. Finite-configuration
cycle detection and packed tracks remove those conventions in linear space,
but that DLBA totalization/model-equivalence bridge is not yet formalized here.

## The verified deterministic boundary

The file
[`Automata/LinearBounded/Functional.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/Functional.lean)
proves the complete machine-level converse when the LBA's local transition
relation is already single-valued:

- `LBA.Machine.Functional` says that every state/symbol pair has at most one
  outgoing move.
- `LBA.Machine.toDLBA` follows that unique move and halts as soon as an
  accepting LBA state is reached.
- `LBA.Machine.accepts_toDLBA_iff` proves, for every bounded starting
  configuration, that the resulting DLBA accepts exactly when the functional
  LBA accepts.
- `LBA.Machine.languageRecognized_toDLBA_eq` lifts this to equality of the
  languages recognized with the same input embedding and empty-word decision.
- `LBA.Machine.languageEnd_toDLBA_eq` gives the corresponding equality on
  canonical bracketed endmarker inputs, including `ε`.
- `is_DLBA_iff_exists_functional_lba` characterizes Langlib's `is_DLBA`
  exactly as finite functional marker-free LBA presentations with an
  empty-word bit.
- `DLBA.toLBA'_functional` proves that Langlib's existing DLBA-to-LBA
  embedding is functional.

The acceptance conventions differ slightly: an LBA accepts when it can reach
an accepting state, whereas a DLBA accepts by halting in one.  The conversion
therefore truncates the unique run at its first accepting state.  The proof
shows that this convention is not the obstacle—the unresolved step is
eliminating genuine branching while retaining a linear tape bound.

## Why the standard constructions stop short

For an input of length `n`, an LBA has exponentially many configurations, each
describable in `O(n)` space.  Acceptance is directed reachability in this
implicit configuration graph.

- A nondeterministic machine stores one current configuration and guesses the
  next edge, using linear space.
- Savitch's recursive deterministic reachability algorithm stores `O(n)`
  recursion levels containing `O(n)`-size configurations, giving quadratic
  rather than linear space.
- Immerman–Szelepcsényi inductive counting proves closure under complement in
  nondeterministic linear space.  Its witnesses are still guessed
  nondeterministically, so it constructs another NLBA, not a DLBA.

The usual separation attempt also fails at the linear bound.  A universal
machine simulating an input-encoded target needs an overhead depending on the
target's number of states and tape symbols.  Those quantities are unbounded
over all encoded DLBAs, so the overhead is not one fixed constant times the
input length.  This is precisely the defect in published diagonalization
claims purporting to resolve the problem.

Langlib makes the underlying same-length capacity issue explicit in
[`Automata/LinearBounded/ConfigurationEncoding.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/LinearBounded/ConfigurationEncoding.lean):
if a source tape alphabet is strictly larger than a fixed target tape
alphabet, no fixed target state type can injectively encode every source tape
using the same number of cells at every length
(`DLBA.no_uniform_same_length_boundedTape_encoding`).  This is a static
information-capacity obstruction, not a language-class separation; it does not
rule out semantic simulations or simulations using a constant-factor larger
tape.

## References

- S.-Y. Kuroda, [*Classes of Languages and Linear-Bounded
  Automata*](https://doi.org/10.1016/S0019-9958(64)90120-2), 1964.
- Walter J. Savitch, [*Relationships between nondeterministic and deterministic
  tape complexities*](https://doi.org/10.1016/S0022-0000(70)80006-X), 1970.
- Jerome Feldman and James Owings, [*A class of universal linear bounded
  automata*](https://doi.org/10.1016/0020-0255(73)90036-4), 1973.
- Juris Hartmanis and Harry B. Hunt III,
  [*The LBA Problem and its Importance in the Theory of
  Computing*](https://hdl.handle.net/1813/6015), 1973.
- Neil Immerman, [*Nondeterministic Space is Closed under
  Complementation*](https://doi.org/10.1137/0217058), 1988.
- Thomas Preu,
  [*Refuting Tianrong Lin's “Resolution of The Linear-Bounded Automata
  Question”*](https://arxiv.org/abs/2110.12421), 2022.
