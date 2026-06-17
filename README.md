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

The tables contain standard results, `🔗` indicates that this repository contains a corresponding proof file (possibly to a weaker variant of the result, e.g. ⊊  vs. ⊆  and ⇔ vs. ⇒)
More detailed results and developed tooling (e.g., Pumping lemmas, Totalizations) can be found in the [documentation](https://nielstron.github.io/langlib/).

### Hierarchy And Equivalences

Each class of the (extended) hierarchy is charaterized as grammar or automaton (or both, and variants thereof). We show (strict) inclusions of the classes and equivalences between different characterizations.

| Grammar side | Relation | Automaton side |
| --- | --- | --- |
| Regular languages (Left-regular ⇔[🔗](src/Langlib/Grammars/LeftRegular/Equivalence/RightRegular.lean) Right-regular) | ⇔ [🔗](src/Langlib/Automata/FiniteState/Equivalence/Regular.lean)| DFA languages (Mathlib) |
| ⊊ [🔗](src/Langlib/Classes/Regular/Inclusion/StrictLR.lean) |  | ⊊ [🔗](src/Langlib/Classes/Regular/Inclusion/StrictDeterministicContextFree.lean) |
| LR(k) grammar languages [🔗](src/Langlib/Grammars/LR/Definition.lean) | ⇔ | DPDA final-state languages [🔗](src/Langlib/Classes/DeterministicContextFree/Definition.lean) |
| ⊊ (⊆ [🔗](src/Langlib/Grammars/LR/Inclusion/ContextFree.lean)) |  | ⊊ [🔗](src/Langlib/Automata/DeterministicPushdown/Inclusion/StrictPushdown.lean) |
| Context-free languages | ⇔ [🔗](src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) | PDA languages (Final State ⇔ Empty Stack [🔗](src/Langlib/Automata/Pushdown/Basics/FinalStateEmptyStack.lean)) |
| ⊊ [🔗](src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean) (⊊ CS [🔗](src/Langlib/Classes/ContextFree/Inclusion/StrictContextSensitive.lean))|  | ⊊ |
| Indexed languages | ⇔ | Nested Stack Automata |
| ⊊ |  | ⊊ |
| Context-sensitive languages (Non-erasing ⇔ Non-contracting (⇒ [🔗](src/Langlib/Grammars/NonContracting/Equivalence/ContextSensitive.lean))) | ⇔ [🔗](src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean) | LBA languages (DLBA ⊆ [🔗](src/Langlib/Automata/DeterministicLinearBounded/Inclusion/LinearBounded.lean) LBA, LBA ⊆? DLBA) |
| ⊊ [🔗](src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) |  | ⊊ [🔗](src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) (⊆ RE [🔗](src/Langlib/Automata/LinearBounded/Inclusion/TuringMachine.lean)) |
| Recursive languages | ≝ [🔗](src/Langlib/Classes/Recursive/Definition.lean) | Turing-machine languages (Mathlib), with halting deciders |
| ⊊ [🔗](src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) |  | ⊊ [🔗](src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean)  |
| Recursively enumerable languages | ⇔ [🔗](src/Langlib/Automata/Turing/Equivalence/TMEqualsRE.lean) | Turing-machine languages (Mathlib) |

**Additional results**

- Context Free Languages ⇔ [🔗](src/Langlib/Grammars/ContextFree/MathlibCFG.lean) Mathlib's `IsContextFree`.
- Regular ⊊ [🔗](src/Langlib/Classes/Regular/Inclusion/StrictLinear.lean) Linear ⊊ [🔗](src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean) Context-free.
- Regular ⊆ [🔗](src/Langlib/Classes/Regular/Inclusion/Recursive.lean) Recursive.
- Context-free ⊆ [🔗](src/Langlib/Classes/ContextFree/Inclusion/Recursive.lean) Recursive.

### Closure

We define abstract closure predicates (`ClosedUnderUnion`, `ClosedUnderHomomorphism`, etc.) for uniform proofs in [🔗](src/Langlib/Utilities/ClosurePredicates.lean).

| Operation | Regular | DCFL | CFL | IND | CSL | Recursive | RE |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Union | Yes [🔗](src/Langlib/Classes/Regular/Closure/Union.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Union.lean) | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Union.lean) |
| Intersection | Yes [🔗](src/Langlib/Classes/Regular/Closure/Intersection.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Intersection.lean) | No [🔗](src/Langlib/Classes/ContextFree/Closure/Intersection.lean) | No | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Intersection.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Intersection.lean) |
| Complement | Yes [🔗](src/Langlib/Classes/Regular/Closure/Complement.lean) | Yes [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) | No [🔗](src/Langlib/Classes/ContextFree/Closure/Complement.lean) | No | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Complement.lean) | No [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Complement.lean) |
| Concatenation | Yes [🔗](src/Langlib/Classes/Regular/Closure/Concatenation.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Concatenation.lean) | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Concatenation.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Concatenation.lean) |
| Kleene star | Yes [🔗](src/Langlib/Classes/Regular/Closure/Star.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Star.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Star.lean) | Yes | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Star.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Star.lean) |
| (String) homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/Homomorphism.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Homomorphism.lean) | No | No [🔗](src/Langlib/Classes/Recursive/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Homomorphism.lean) |
| `ε`-free (string) homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/Homomorphism.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Homomorphism.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/EpsFreeHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/EpsFreeHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Homomorphism.lean) |
| Substitution | Yes [🔗](src/Langlib/Classes/Regular/Closure/Substitution.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Substitution.lean) | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Substitution.lean) | Yes | No | No | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Substitution.lean) |
| Inverse homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/InverseHomomorphism.lean) | Yes | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/InverseHomomorphism.lean) | Yes | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/InverseHomomorphism.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/InverseHomomorphism.lean) |
| Reverse | Yes [🔗](src/Langlib/Classes/Regular/Closure/Reverse.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Reverse.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Reverse.lean) |
| Intersection with a regular language | Yes [🔗](src/Langlib/Classes/Regular/Closure/Intersection.lean) | Yes [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/IntersectionRegular.lean)| Yes [🔗](src/Langlib/Classes/ContextFree/Closure/IntersectionRegular.lean) | Yes | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/IntersectionRegular.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Intersection.lean) |
| Right quotient | Yes [🔗](src/Langlib/Classes/Regular/Closure/Quotient.lean) | No [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/Quotient.lean) | No [🔗](src/Langlib/Classes/ContextFree/Closure/Quotient.lean) | No | No | No | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Quotient.lean) |
| Right quotient with a regular language | Yes [🔗](src/Langlib/Classes/Regular/Closure/Quotient.lean) | Yes | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Quotient.lean) | Yes | Yes | No [🔗](src/Langlib/Classes/Recursive/Closure/QuotientRegular.lean) | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Quotient.lean) |


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

Each column refers to the corresponding uniform computability predicate
(`ComputableMembership`, `ComputableEmptiness`, `ComputableUniversality`,
`ComputableEquivalence`) defined in
[🔗](src/Langlib/Utilities/ComputabilityPredicates.lean).

| Language | Membership | Emptiness | Universality | Equivalence |
| --- | --- | --- | --- | --- |
| Regular | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Membership.lean) | ✓ | ✓ | ✓ |
| Deterministic context-free | ✓ | ✓ | ✓ | ✓ |
| Context-free | ✓ [🔗](src/Langlib/Classes/ContextFree/Decidability/Membership.lean) | ✓ [🔗](src/Langlib/Classes/ContextFree/Decidability/Emptiness.lean) | ✗ | ✗ |
| Context-sensitive | ✓ [🔗](src/Langlib/Classes/ContextSensitive/Decidability/Characterization.lean) | ✗ | ✗ | ✗ |
| Recursive | ✓ [🔗](src/Langlib/Classes/Recursive/Decidability/Membership.lean) | ✗ | ✗ | ✗ |
| Recursively enumerable | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Membership.lean) | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Emptiness.lean) | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Universality.lean) | ✗ [🔗](src/Langlib/Classes/RecursivelyEnumerable/Decidability/Equivalence.lean) |

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
