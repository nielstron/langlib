<p align="center">
  <img src="docs/logo.svg" alt="Langlib logo" width="160">
  <h1>Langlib</h1>
</p>

[![CI](https://github.com/nielstron/langlib/actions/workflows/build.yml/badge.svg)](https://github.com/nielstron/langlib/actions/workflows/build.yml)

`Langlib` is a Lean 4 library of formalized results from formal language theory, defining and relating various grammars, language classes, and automata across the Chomsky hierarchy and beyond.

📖 **Documentation:** [overview](https://nielstron.github.io/langlib/) · [API reference](https://nielstron.github.io/langlib/api/)


## Proof overview
The goal of this library is to encapsulate some core results of the (extended) Chomsky hierarchy: inclusions, closures and decidability.
The following gives a rough overview over the contents in highly condensed form.

The tables contain standard results. `🔗` indicates that the linked file
contains a corresponding definition or theorem stated explicitly for the displayed
language or presentation classes.
More detailed results and developed tooling (e.g., Pumping lemmas, Totalizations) can be found in the [documentation](https://nielstron.github.io/langlib/).

### Hierarchy And Equivalences

Each class of the (extended) hierarchy is characterized as a grammar or automaton
(or both, and variants thereof). We show (strict) inclusions of the classes and
equivalences between different characterizations.

In an inclusion row, a link is attached only when the cited file states a theorem
explicitly for the language or presentation classes displayed in that column. The
proof may use established equivalences. Parenthesized `⊆` links record a proved
weaker inclusion when the displayed strict result is not yet formalized for those
classes.

| Class Name | Grammar | Relation | Automaton |
| --- | --- | --- | --- |
| Regular | Regular (Left-regular [🔗](src/Langlib/Grammars/LeftRegular/Definition.lean) ⇔[🔗](src/Langlib/Grammars/LeftRegular/Equivalence/RightRegular.lean) Right-regular [🔗](src/Langlib/Grammars/RightRegular/Definition.lean)) | ⇔ [🔗](src/Langlib/Automata/FiniteState/Equivalence/Regular.lean)| Finite Automata [🔗](src/Langlib/Automata/FiniteState/Definition.lean) (NFA ⇔ [🔗](src/Langlib/Automata/FiniteState/Equivalence/Determinization.lean) DFA) |
| | ⊊ [🔗](src/Langlib/Classes/Regular/Inclusion/StrictLR.lean) |  | ⊊ [🔗](src/Langlib/Automata/FiniteState/Inclusion/StrictDeterministicPushdown.lean) |
| Deterministic context-free | LR(k), `k > 0` [🔗](src/Langlib/Grammars/LR/Definition.lean) | ⇔ [🔗](src/Langlib/Grammars/LR/Equivalence.lean) | Deterministic Pushdown Automata [🔗](src/Langlib/Automata/DeterministicPushdown/Definition.lean) |
| | ⊊ [🔗](src/Langlib/Grammars/LR/Inclusion/StrictContextFree.lean) |  | ⊊ [🔗](src/Langlib/Automata/DeterministicPushdown/Inclusion/StrictPushdown.lean) |
| Context-free | Context-free [🔗](src/Langlib/Grammars/ContextFree/Definition.lean) | ⇔ [🔗](src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) | Pushdown Automata [🔗](src/Langlib/Automata/Pushdown/Definition.lean) (Final State ⇔ [🔗](src/Langlib/Automata/Pushdown/Basics/FinalStateEmptyStack.lean) Empty Stack) |
| | ⊊ [🔗](src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean) (⊊ CS [🔗](src/Langlib/Classes/ContextFree/Inclusion/StrictContextSensitive.lean))|  | ⊊ |
| Indexed | Indexed [🔗](src/Langlib/Grammars/Indexed/Definition.lean) | ⇔ | Nested Stack Automata |
| | ⊊ [🔗](src/Langlib/Classes/Indexed/Inclusion/StrictContextSensitive.lean) |  | ⊊ |
| Context-sensitive | Context-sensitive [🔗](src/Langlib/Grammars/ContextSensitive/Definition.lean) (Non-erasing ⇔ [🔗](src/Langlib/Grammars/NonContracting/Equivalence/ContextSensitiveGeneral.lean) Non-contracting [🔗](src/Langlib/Grammars/NonContracting/Definition.lean)) | ⇔ [🔗](src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) | Linear Bounded Automaton [🔗](src/Langlib/Automata/LinearBounded/Definition.lean) (DLBA [🔗](src/Langlib/Automata/DeterministicLinearBounded/Definition.lean) ⇔? NLBA (⊆ [🔗](src/Langlib/Automata/DeterministicLinearBounded/Inclusion/LinearBounded.lean))) |
|  |  |  | ⊊ [🔗](src/Langlib/Automata/LinearBounded/Inclusion/Recursive.lean) |
| Recursive |  ⊊ [🔗](src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) (⊆ [🔗](src/Langlib/Classes/ContextSensitive/Inclusion/Recursive.lean)) | | Turing-machines with halting deciders [🔗](src/Langlib/Classes/Recursive/Definition.lean) |
|  |  |  | ⊊ [🔗](src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean)  |
| Recursively Enumerable | Unrestricted [🔗](src/Langlib/Grammars/Unrestricted/Definition.lean) | ⇔ [🔗](src/Langlib/Automata/Turing/Equivalence/RecursivelyEnumerable.lean) | Turing-machines [🔗](src/Langlib/Automata/Turing/Definition.lean) |

The `DLBA ⇔? NLBA` entry is the **first LBA problem**, which remains open:
in complexity terminology it asks whether deterministic and nondeterministic
linear space have the same power.  Langlib proves the easy `DLBA ⊆ NLBA`
direction above and the machine-level converse for an NLBA whose transition
relation is already single-valued
[🔗](src/Langlib/Automata/LinearBounded/Functional.lean).  The
Immerman–Szelepcsényi complement construction does not settle this question:
it constructs another nondeterministic linear-space machine rather than a
deterministic one.  A separate positive boundary is now checked directly.  If one constant
bounds every tape boundary of one selected accepting run for each accepted
word, the finite crossing-profile construction recognizes the same language
with an NFA, hence a DFA and a DLBA
[🔗](src/Langlib/Automata/LinearBounded/BoundedCrossingLanguage.lean).  Other
accepting and rejecting runs remain unrestricted, the accepting head may be
anywhere, and the proof includes one-cell tapes, clamped endpoint moves, and
arbitrary finite alphabet/state cardinalities.  The converse is exact: the
explicit DFA scanner crosses every physical boundary exactly once, so every
positive fixed at-most-crossing cap, and also the class with an existential
uniform cap, gives exactly the DFA/NFA/regular languages
[🔗](src/Langlib/Automata/LinearBounded/BoundedCrossingRegularCharacterization.lean).
Cap zero is the sole exception: a run cannot leave the left marker, and its
slice class is exactly `{∅, Set.univ}`
[🔗](src/Langlib/Automata/LinearBounded/BoundedCrossingZero.lean).
The sharp lattice is stated directly for all named classes
[🔗](src/Langlib/Automata/LinearBounded/BoundedCrossingCapHierarchy.lean):
cap zero is contained in every positive cap, DFA, NFA, regular, uniform-crossing,
and fixed-head-turn class, and each inclusion is strict exactly when the terminal
type is nonempty.  Thus one terminal symbol is necessary and sufficient; over an
empty terminal type all these classes contain only the two possible languages and
coincide.
More generally, after stationary and outward-clamped moves are erased, every
boundary is crossed at most `head turns + 1` times.  Hence, for every fixed
`r`, LBAs having one selected accepting run with at most `r` physical head
reversals recognize exactly the regular languages
[🔗](src/Langlib/Automata/LinearBounded/HeadTurnCrossing.lean).
Every individual finite run has some word-dependent cap; the crossing theorem
needs one cap uniform over the whole language, so it does not apply to an
arbitrary LBA.  Likewise, the fixed-turn theorem says nothing about a turn
bound that grows with the input length.

Sweeping, without a uniform bound on the number of sweeps, is an exact normal
form.  On the nondeterministic side, the promise covers every finite trace from
every canonical input in the relevant model (nonempty in the marker-free
model), including nonaccepting branches and arbitrary finite prefixes: after
stationary and outward-clamped moves are ignored, a genuine
change of head direction may occur only when its source head is at a physical
endpoint
[🔗](src/Langlib/Automata/LinearBounded/Sweeping.lean).  The marker-free and
canonical-endmarker class equalities are respectively
`SweepingLBA_pos = LBA_pos`
[🔗](src/Langlib/Automata/LinearBounded/SweepingCharacterization.lean) and
`SweepingLBA = LBA`
[🔗](src/Langlib/Automata/LinearBounded/SweepingEndmarkerCharacterization.lean).
The latter treats `epsilon` on its actual two-cell `⊢⊣` tape rather than
through a separately chosen acceptance bit.  The theorem statements impose no
`Nonempty` typeclass or cardinality lower bound on the terminal, work, or state
types.  The certified-row construction remains nondeterministic and can make
unboundedly many endpoint turns; it proves neither `LBA = DLBA` nor a
determinization theorem.

There is also a separate direct deterministic normal form.
`SweepingDLBA = DLBA`
[🔗](src/Langlib/Automata/LinearBounded/DeterministicSweeping/Characterization.lean)
is proved by a same-width compiler which stores the simulated source head and
state in the finite tape alphabet and executes each deterministic source step
during endpoint-to-endpoint passes.  The construction handles the one-cell
tape and both clamped source moves uniformly, preserves the named DLBA class's
explicit `epsilon` bit, and satisfies the same all-finite-prefix sweeping
predicate after viewing the deterministic machine as an LBA.  This compiler
starts from an already deterministic machine, so it does not supply the open
inclusion `LBA ⊆ DLBA`.
The actual-endmarker form `SweepingEndDLBA = DLBA`
[🔗](src/Langlib/Automata/LinearBounded/DeterministicSweeping/EndmarkerCharacterization.lean)
removes that external bit: its deterministic machine decides every word on
the genuine tape `⊢w⊣`, including the two-cell tape `⊢⊣` for `epsilon`.

For a finite ambient terminal type with a chosen primitive-codable presentation,
the effective interface now also covers internal signatures encoded at runtime.
The bounded-crossing raw code stores numeric work/state cardinalities, an
initial state, a crossing cap, accepting states, and a finite local transition
table; the query word is a separate input.  One primitive-recursive evaluator
decides the pair `(code, word)`, and the range of these varying-internal-signature,
varying-cap codes is exactly the DFA/NFA/regular class
[🔗](src/Langlib/Automata/LinearBounded/BoundedCrossingVaryingEncodedMembership.lean).
For ordinary LBAs, a separate five-field code omits the crossing cap as well as
the word.  Its evaluator computes the finite configuration bound from the code
and query word and enumerates bounded schedules; semantic loop erasure proves
that this search decides ordinary membership.  The resulting presentation
characterizes exactly `LBA`
[🔗](src/Langlib/Automata/LinearBounded/EncodedMembership.lean).  This is an
external exhaustive bounded-schedule search, justified by finiteness of the
configuration graph, with no promised linear-space bound; it does not turn an
encoded NLBA into a DLBA and has no bearing on the open equality.

The open reverse inclusion is equivalent to deterministic
reachability for finite fixed-width row systems even when their local edge
verifier is deterministic, the row graph is acyclic, and every row has both
indegree and outdegree at most two
[🔗](src/Langlib/Automata/LinearBounded/CertifiedRowSystem/StrictDegreeCharacterization.lean).
At the machine level, every LBA also has an equivalent presentation whose
configuration graph has both directed degrees at most two
[🔗](src/Langlib/Automata/LinearBounded/BoundedDegree.lean).  A guarded
same-width clock compiler strengthens this to a globally acyclic
presentation, and the degree serializers preserve that property.  A further
same-width four-phase compiler gives two partial-bijection layers whose
monochromatic paths have length at most two; alternatively, a two-phase split
gives three directed matching layers.  Both globally acyclic, degree-two
normal forms still recognize exactly `LBA`
[🔗](src/Langlib/Automata/LinearBounded/MachineShortLayers/LanguageEquivalence.lean)
[🔗](src/Langlib/Automata/LinearBounded/MachineThreeMatchings/NormalForm.lean).
These are nondeterministic normal forms, not DLBA constructions.  They should
not be confused with the more restrictive exact-two-matching presentation
promise below: the first form permits monochromatic paths of two edges, while
the second uses three colors.
Labeled first-final runs also give the checked sandwich
`DLBA ⊆ ULBA ⊆ LBA` and factor the open equality into disambiguating LBAs
and then determinizing the unambiguous class
[🔗](src/Langlib/Automata/LinearBounded/Unambiguous.lean).
At the explicit finite-graph level, arbitrary reachability has a
single-designated-target, globally acyclic, degree-two presentation with two
supplied linear `2`-diforests
[🔗](src/Langlib/Automata/LinearBounded/ShortLayerSubdivisionReachability.lean).
A separate vertex split gives three supplied matching layers, also in a DAG,
while two matching layers have no reachable branch away from the initial
vertex
[🔗](src/Langlib/Automata/LinearBounded/ThreeMatchingReachability.lean).
That one-branch obstruction is the combinatorial core of the checked
machine-level consequence: every LBA presentation
whose complete fixed-width step relation is exactly the union of two directed
matchings recognizes a `DLBA` language, with no acyclicity premise
[🔗](src/Langlib/Automata/LinearBounded/MachineTwoMatchings/Determinize.lean).
The compiler pins the initial choice, clocks each functional branch, and tries
the finite branches sequentially while restoring the canonical input.  Its
explicit empty-word bit is obtained by bounded simulation of the resulting
finite deterministic machine, rather than by consulting language membership.
Thus two exact matching layers are determinizable, whereas the three-matching
normal form above already presents every LBA language.  This does not resolve
`LBA = DLBA`, because no reduction from the universal three-layer form to two
layers is proved.
The converse deterministic compiler is now checked directly.  It refines a
fixed-slot Euler traversal into a marked, clamping-safe raw LBA: immutable
boundary information detects blocked moves before departure, every unavoidable
double-predecessor landing is terminal, and an explicit microphase flips on
every edge.  Exact macro simulation and reflection hold between boundary-coded
canonical configurations, and canonical initialization proves that invariant
for every word, including the genuine two-cell empty input.  Independently,
raw indegree two and the terminal-double-merge theorem quantify over all raw
configurations and all widths, including malformed tapes and width zero.
Consequently `DLBA ⊆ TwoMatchingLBA`, and together with the compiler above,

> `TwoMatchingLBA = DLBA`.

The class equality and the exact remaining frontier are stated directly in
[🔗](src/Langlib/Automata/LinearBounded/GraphWalking/MarkedEulerProbe/ClassEquivalence.lean):
`LBA = DLBA` holds iff the universal acyclic degree-two three-matching class is
contained in (equivalently, equal to) `TwoMatchingLBA`.  Thus the marked Euler
construction completes the deterministic side but does not choose a branch of
an arbitrary nondeterministic LBA.

The older globally cofunctional route remains a useful model warning.  Under
clamped movement, global raw cofunctionality forces every enabled move to stay,
and the globally cofunctional endmarker-LBA class is exactly
`{∅, Set.univ}`
[🔗](src/Langlib/Automata/LinearBounded/Cofunctional/Triviality.lean).
In particular the repository's still stronger, unusually raw
`ReversibleLBA` class has the same collapse
[🔗](src/Langlib/Automata/LinearBounded/MachineTwoMatchings/ReversibleTriviality.lean).
The successful marked compiler targets two matchings directly instead of
claiming global cofunctionality.
The complementary fixed-slot reduction remains as a fully explicit numbered
construction whose own vertex gadgets are necessarily cyclic
[🔗](src/Langlib/Automata/LinearBounded/LinearTwoDiforestReachability.lean).
The checked two-layer reachability recurrence and ordered-fork construction
also show why selecting a canonical successful color would already solve the
underlying reachability instance; total permutation layers form a reversible
positive frontier, but even one one-way partial-bijection edge cannot be
totalized while reflecting directed reachability.
The [first-LBA boundary note](docs/results/first-lba-problem-boundaries.md)
records the exact equivalences, restricted positive cases, failed proof
routes, and current literature status.

The strict hierarchy results are uniform over every finite alphabet meeting the
displayed result's sharp or currently proved size bound: Regular ⊊ LR(k)/DPDA
requires at least two symbols; LR(k)/DPDA ⊊ CF, CF ⊊ Indexed, and CF ⊊ CS
are proved for at least three; Indexed ⊊ CS requires at least two; and the
strict inclusions CS/LBA ⊊ Recursive, CS ⊊ RE, and Recursive ⊊ RE require
a nonempty alphabet.
The underlying inclusion Indexed ⊆ CS
[🔗](src/Langlib/Classes/Indexed/Inclusion/ContextSensitive.lean) holds over every
terminal type.

**Additional results**

- Context Free Languages ⇔ [🔗](src/Langlib/Grammars/ContextFree/MathlibCFG.lean) Mathlib's `IsContextFree`.
- Regular ⊊ [🔗](src/Langlib/Classes/Regular/Inclusion/StrictLinear.lean) Linear ⊊ [🔗](src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean) Context-free.
- Regular ⊆ [🔗](src/Langlib/Classes/Regular/Inclusion/Recursive.lean) Recursive.
- Context-free ⊆ [🔗](src/Langlib/Classes/ContextFree/Inclusion/Recursive.lean) Recursive.

### Closure

We define abstract closure predicates (`ClosedUnderUnion`, `ClosedUnderHomomorphism`, etc.) for uniform proofs in [🔗](src/Langlib/Utilities/ClosurePredicates.lean).

| Operation | Regular | DCFL | CFL | IND | CSL | Recursive | RE |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Union | Yes [🔗](src/Langlib/Classes/Regular/Closure/Union.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Union.lean) |
| Intersection | Yes [🔗](src/Langlib/Classes/Regular/Closure/Intersection.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Intersection.lean) | No [🔗](src/Langlib/Classes/ContextFree/Closure/Intersection.lean) | No [🔗](src/Langlib/Classes/Indexed/Closure/Intersection.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Intersection.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Intersection.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Intersection.lean) |
| Complement | Yes [🔗](src/Langlib/Classes/Regular/Closure/Complement.lean) | Yes [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) | No [🔗](src/Langlib/Classes/ContextFree/Closure/Complement.lean) | No [🔗](src/Langlib/Classes/Indexed/Closure/Complement.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Complement.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Complement.lean) | No [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Complement.lean) |
| Concatenation | Yes [🔗](src/Langlib/Classes/Regular/Closure/Concatenation.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Concatenation.lean) |
| Kleene star | Yes [🔗](src/Langlib/Classes/Regular/Closure/Star.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Star.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Star.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Star.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Star.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Star.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Star.lean) |
| (String) homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/Homomorphism.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Homomorphism.lean) | No [🔗](src/Langlib/Classes/ContextSensitive/Closure/Homomorphism.lean) | No [🔗](src/Langlib/Classes/Recursive/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Homomorphism.lean) |
| `ε`-free (string) homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/Homomorphism.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/EpsFreeHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/EpsFreeHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Homomorphism.lean) |
| Substitution | Yes [🔗](src/Langlib/Classes/Regular/Closure/Substitution.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Substitution.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Substitution.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Substitution.lean) | No [🔗](src/Langlib/Classes/ContextSensitive/Closure/Substitution.lean) | No [🔗](src/Langlib/Classes/Recursive/Closure/Substitution.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Substitution.lean) |
| Inverse homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/InverseHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/InverseHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/InverseHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/InverseHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/InverseHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/InverseHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/InverseHomomorphism.lean) |
| Reverse | Yes [🔗](src/Langlib/Classes/Regular/Closure/Reverse.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Reverse.lean) |
| Intersection with a regular language | Yes [🔗](src/Langlib/Classes/Regular/Closure/Intersection.lean) | Yes [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/IntersectionRegular.lean)| Yes [🔗](src/Langlib/Classes/ContextFree/Closure/IntersectionRegular.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/IntersectionRegular.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/IntersectionRegular.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/IntersectionRegular.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Intersection.lean) |
| Right quotient | Yes [🔗](src/Langlib/Classes/Regular/Closure/Quotient.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Quotient.lean) | No [🔗](src/Langlib/Classes/ContextFree/Closure/Quotient.lean) | No [🔗](src/Langlib/Classes/Indexed/Closure/Quotient.lean) | No [🔗](src/Langlib/Classes/ContextSensitive/Closure/Quotient.lean) | No [🔗](src/Langlib/Classes/Recursive/Closure/Quotient.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Quotient.lean) |
| Right quotient with a regular language | Yes [🔗](src/Langlib/Classes/Regular/Closure/Quotient.lean) | Yes [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/QuotientRegular.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Quotient.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/QuotientRegular.lean) | No [🔗](src/Langlib/Classes/ContextSensitive/Closure/QuotientRegular.lean) | No [🔗](src/Langlib/Classes/Recursive/Closure/QuotientRegular.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Quotient.lean) |

For a negative closure entry, `No` means that closure fails over some finite
alphabet; it does not claim failure over every alphabet.  The linked files expose
embedding/cardinality variants (for example, `_of_embedding` and `_of_card`) giving
the proved sufficient alphabet-size bounds.  Positive entries are stated uniformly
over the finite alphabet assumptions required by their definitions.


Additional DCFL results:

- [Union with a regular language](src/Langlib/Classes/DeterministicContextFree/Closure/UnionRegular.lean)

Additional CFL results:

- [Terminal bijections](src/Langlib/Classes/ContextFree/Closure/Bijection.lean)
- [Terminal permutations](src/Langlib/Classes/ContextFree/Closure/Permutation.lean)
- [Prefix](src/Langlib/Classes/ContextFree/Closure/Prefix.lean)
- [Suffix](src/Langlib/Classes/ContextFree/Closure/Suffix.lean)

Additional CSL results:

- [Terminal bijections](src/Langlib/Classes/ContextSensitive/Closure/Bijection.lean)

### Decidability

Membership is the uniform word problem for a concrete presentation: the input is a
valid encoded automaton, grammar, or program together with a word.
`ComputableMembership`
[🔗](src/Langlib/Utilities/ComputabilityPredicates.lean) takes an optional
validity promise, requires valid codes to present exactly the stated language
class, and requires one partial-recursive evaluator to halt and answer correctly
on every valid code-and-word pair.  It separately requires raw encoded membership
to be uniformly recursively enumerable; this prevents the semantic decoding map
itself from hiding a non-r.e. membership oracle.

The remaining columns use the corresponding uniform emptiness, universality, and
equivalence problems for the concrete presentation named by each linked theorem.
In particular, the deterministic context-free membership and emptiness proofs use
encoded grammars, while its universality and equivalence proofs use promised-total
encoded DPDAs.

| Language | Membership | Emptiness | Universality | Equivalence |
| --- | --- | --- | --- | --- |
| Regular | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Membership.lean) | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Emptiness.lean) | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Universality.lean) | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Equivalence.lean) |
| Deterministic context-free | ✓ [🔗](src/Langlib/Classes/DeterministicContextFree/Decidability/Membership.lean) | ✓ [🔗](src/Langlib/Classes/DeterministicContextFree/Decidability/Emptiness.lean) | ✓ [🔗](src/Langlib/Classes/DeterministicContextFree/Decidability/Universality.lean) | ✓ [🔗](src/Langlib/Classes/DeterministicContextFree/Decidability/Equivalence.lean) |
| Context-free | ✓ [🔗](src/Langlib/Classes/ContextFree/Decidability/Membership.lean) | ✓ [🔗](src/Langlib/Classes/ContextFree/Decidability/Emptiness.lean) | ✗ [🔗](src/Langlib/Classes/ContextFree/Decidability/Universality.lean) | ✗ [🔗](src/Langlib/Classes/ContextFree/Decidability/Equivalence.lean) |
| Context-sensitive | ✓ [🔗](src/Langlib/Classes/ContextSensitive/Decidability/Characterization.lean) | ✗ [🔗](src/Langlib/Classes/ContextSensitive/Decidability/Emptiness.lean) | ✗ [🔗](src/Langlib/Classes/ContextSensitive/Decidability/Universality.lean) | ✗ [🔗](src/Langlib/Classes/ContextSensitive/Decidability/Equivalence.lean) |
| Recursive | ✓ [🔗](src/Langlib/Classes/Recursive/Decidability/Membership.lean) | ✗ [🔗](src/Langlib/Classes/Recursive/Decidability/Emptiness.lean) | ✗ [🔗](src/Langlib/Classes/Recursive/Decidability/Universality.lean) | ✗ [🔗](src/Langlib/Classes/Recursive/Decidability/Equivalence.lean) |
| Recursively enumerable | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Membership.lean) | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Emptiness.lean) | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Universality.lean) | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Equivalence.lean) |

For Recursive membership, the input program is promised to be an always-halting
decider.  The linked theorem supplies one universal evaluator taking the raw program
code and word jointly, proves that it halts and is correct under that promise, and
shows that valid codes present exactly the recursive languages over every finite
computably encoded alphabet.  Emptiness, universality, and equivalence are
undecidable for this presentation over every nonempty computably encoded alphabet;
nonemptiness is optimal because an empty alphabet has only the empty word.  The
separate diagonal result
[🔗](src/Langlib/Classes/Recursive/Decidability/UniformMembership.lean) says that
these semantically valid programs cannot instead be replaced by an adequate
`Primcodable` type on which membership is total for every raw code; that is a
different, stronger requirement.

## How To Use The Library

For most uses, import the hub:

```lean
import Langlib
```

If you only need one part of the development, import the corresponding module directly, for example:

```lean
import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.Definition
import Langlib.Automata.Pushdown.Equivalence.ContextFree
import Langlib.Classes.Regular.Decidability.Membership
import Langlib.Classes.Recursive.Decidability.Membership
```

The files in [test/LanglibTest](test/LanglibTest) provide small worked examples:

- [test/LanglibTest/DemoContextFree.lean](test/LanglibTest/DemoContextFree.lean)
- [test/LanglibTest/DemoContextSensitive.lean](test/LanglibTest/DemoContextSensitive.lean)
- [test/LanglibTest/DemoUnrestricted.lean](test/LanglibTest/DemoUnrestricted.lean)

To build the library and examples, run:

```sh
lake build
```

## Installation Instructions

To install Lean 4, follow the [Lean community manual](https://leanprover-community.github.io/get_started.html).

To download and build this project, run:

```sh
git clone https://github.com/nielstron/langlib
cd langlib
lake build
```

## Acknowledgements

This repository started as a Lean 4 port of
[madvorak/grammars](https://github.com/madvorak/grammars).
It further includes a port of the Pumping Lemma proof from [AlexLoitzl/pumping_cfg](https://github.com/AlexLoitzl/pumping_cfg/) and the equivalence proof between CFGs and PDAs from [shetzl/autth](https://github.com/shetzl/autth/tree/PDA).

> A part of this repository was created with the help of [Aristotle](https://aristotle.harmonic.fun). It's an amazing tool for ambitious proofs. Special thanks to the developers to provide this tool to the community!
