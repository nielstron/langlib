# Langlib 
[![CI](https://github.com/nielstron/langlib/actions/workflows/build.yml/badge.svg)](https://github.com/nielstron/langlib/actions/workflows/build.yml)

`Langlib` is a Lean 4 library of formalized results about grammars, language classes, and automata across the Chomsky hierarchy.

### Regular Languages

- [Right-regular grammars](src/Langlib/Grammars/RightRegular/Definition.lean)
- [Left-regular grammars](src/Langlib/Grammars/LeftRegular/Definition.lean)
- [Top and Bottom are Regular](src/Langlib/Classes/Regular/Examples/TopBot.lean)

### Linear and DCF Languages

- [Linear Languages](src/Langlib/Classes/Linear/Definition.lean)
- [Deterministic Context-Free Languages](src/Langlib/Classes/DeterministicContextFree/Definition.lean)
- [`{aⁿbⁿ}` is Linear](src/Langlib/Classes/ContextFree/Examples/AnBn.lean)

### Context-Free Languages

- [Definition](src/Langlib/Classes/ContextFree/Definition.lean)
- [Context-free grammars](src/Langlib/Grammars/ContextFree/Definition.lean)
- [Pumping lemma](src/Langlib/Classes/ContextFree/Basics/Pumping.lean)
- [Ogdens Lemma](src/Langlib/Classes/ContextFree/Basics/Ogden.lean)
- [Chomsky normal form](src/Langlib/Classes/ContextFree/NormalForms/ChomskyNormalForm.lean)

### Indexed Languages

- [Indexed grammars](src/Langlib/Grammars/Indexed/Definition.lean)
- [`{aⁿbⁿcⁿ}` is Indexed](src/Langlib/Classes/Indexed/Examples/AnBnCn.lean)

### Context-Sensitive Languages

- [Context-sensitive grammars](src/Langlib/Grammars/ContextSensitive/Definition.lean)
- [Noncontracting grammars](src/Langlib/Grammars/NonContracting/Definition.lean)

### Recursive Languages

- [Recursive Languages](src/Langlib/Classes/Recursive/Definition.lean)

### Recursively Enumerable Languages

- [Unrestricted grammars](src/Langlib/Grammars/Unrestricted/Definition.lean)
- [Kuroda normal form](src/Langlib/Classes/RecursivelyEnumerable/NormalForms/Kuroda.lean)
- [`{aⁿbⁿcⁿ}` is RE](src/Langlib/Classes/RecursivelyEnumerable/Examples/AnBnCn.lean)

### Automata

- [Pushdown automata](src/Langlib/Automata/Pushdown/Definition.lean)
- [Deterministic pushdown automata](src/Langlib/Automata/DeterministicPushdown/Definition.lean)
- [Linear bounded automata](src/Langlib/Automata/LinearBounded/Definition.lean)
- [Deterministic linear bounded automata](src/Langlib/Automata/DeterministicLinearBounded/Definition.lean)

### Examples

- [Context-free example grammar](test/LanglibTest/DemoContextFree.lean)
- [Context-sensitive example grammars](test/LanglibTest/DemoContextSensitive.lean)
- [Unrestricted example grammar](test/LanglibTest/DemoUnrestricted.lean)

## Proof overview

`🔗` indicates that this repository contains a corresponding proof file.

### Hierarchy And Equivalences

| Grammar side | Relation | Automaton side |
| --- | --- | --- |
| Regular languages (Left-regular ⇔[🔗](src/Langlib/Grammars/LeftRegular/Equivalence/LGEquivRG.lean) Right-regular) | ⇔ [🔗](src/Langlib/Automata/FiniteState/Equivalence/RegularDFAEquiv.lean)| DFA languages (Mathlib) |
| ⊊ [🔗](src/Langlib/Classes/Regular/Basics/StrictInclusion.lean) |  | ⊊ [🔗](src/Langlib/Classes/Regular/Basics/Inclusion.lean) |
| Deterministic context-free languages | ≝ [🔗](src/Langlib/Classes/DeterministicContextFree/Definition.lean) | DPDA final-state languages |
| ⊊ (⊆ [🔗](src/Langlib/Classes/DeterministicContextFree/Basics/Inclusion.lean)) |  | ⊊ (⊆ [🔗](src/Langlib/Automata/DeterministicPushdown/Basics/Inclusion.lean)) |
| Context-free languages | ⇔ [🔗](src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) | PDA languages (Final State ⇔ Empty Stack (⇒ [🔗](src/Langlib/Automata/Pushdown/Basics/FinalStateEmptyStackEquiv.lean))) |
| ⊊ [🔗](src/Langlib/Classes/ContextFree/Basics/StrictInclusionIndexed.lean) (⊆ CS [🔗](src/Langlib/Classes/ContextFree/Basics/InclusionCS.lean))|  | ⊊ |
| Indexed languages | ⇔ | Nested Stack Automata |
| ⊊ |  | ⊊ |
| Context-sensitive languages (Non-erasing ⇔ Non-contracting (⇒ [🔗](src/Langlib/Grammars/NonContracting/Equivalence/ContextSensitive.lean))) | ⇔ | LBA languages (LBA ⇔? DLBA) |
| ⊊ (⊆ RE [🔗](src/Langlib/Classes/ContextSensitive/Basics/Inclusion.lean)) |  | ⊊ (⊆ RE [🔗](src/Langlib/Automata/LinearBounded/Basics/Inclusion.lean)) |
| Recursive languages | ≝ [🔗](src/Langlib/Classes/Recursive/Definition.lean) | Turing-machine languages (Mathlib), with halting deciders |
| ⊊ (⊆ [🔗](src/Langlib/Classes/Recursive/Basics/Inclusion.lean)) |  | ⊊ (⊆ [🔗](src/Langlib/Classes/Recursive/Basics/Inclusion.lean)) |
| Recursively enumerable languages | ⇔ (⇐ [🔗](src/Langlib/Automata/Turing/Equivalence/TMToGrammar.lean)) | Turing-machine languages (Mathlib) |

**Additional results**

- Context Free Languages ⇔ [🔗](src/Langlib/Classes/ContextFree/Basics/Inclusion.lean) Mathlib's `IsContextFree`.
- Regular ⊊ [🔗](src/Langlib/Classes/Regular/Basics/StrictInclusionLinear.lean) Linear ⊊ (⊆ [🔗](src/Langlib/Classes/Linear/Basics/Inclusion.lean)) Context-free.



### Closure


| Operation | Regular | DCFL | CFL | IND | CSL | Recursive | RE |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Union | Yes [🔗](src/Langlib/Classes/Regular/Closure/Union.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/Indexed/Closure/Union.lean) | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Union.lean) | Yes | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Union.lean) |
| Intersection | Yes [🔗](src/Langlib/Classes/Regular/Closure/Intersection.lean) | No | No [🔗](src/Langlib/Classes/ContextFree/Closure/Intersection.lean) | No | Yes | Yes | Yes |
| Complement | Yes [🔗](src/Langlib/Classes/Regular/Closure/Complement.lean) | Yes [(🔗)](src/Langlib/Automata/DeterministicPushdown/ClosureProperties/Complement.lean) | No [🔗](src/Langlib/Classes/ContextFree/Closure/Complement.lean) | No | Yes | Yes [🔗](src/Langlib/Classes/Recursive/Closure/Complement.lean) | No |
| Concatenation | Yes [🔗](src/Langlib/Classes/Regular/Closure/Concatenation.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Concatenation.lean) | Yes | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Concatenation.lean) | Yes | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Concatenation.lean) |
| Kleene star | Yes [🔗](src/Langlib/Classes/Regular/Closure/Star.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Star.lean) | Yes | Yes | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Star.lean) | Yes |
| (String) homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/Homomorphism.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) | Yes | No | No | Yes |
| `ε`-free (string) homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/Homomorphism.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) | Yes | Yes | Yes | Yes |
| Substitution | Yes [🔗](src/Langlib/Classes/Regular/Closure/Union.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Substitution.lean) | Yes | Yes | No | Yes |
| Inverse homomorphism | Yes [🔗](src/Langlib/Classes/Regular/Closure/InverseHomomorphism.lean) | Yes | Yes [🔗](src/Langlib/Classes/Regular/Closure/InverseHomomorphism.lean) | Yes | Yes | Yes | Yes |
| Reverse | Yes [🔗](src/Langlib/Classes/Regular/Closure/Reverse.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Reverse.lean) | Yes | Yes [🔗](src/Langlib/Classes/ContextSensitive/Closure/Reverse.lean) | Yes | Yes [🔗](src/Langlib/Classes/RecursivelyEnumerable/Closure/Reverse.lean) |
| Intersection with a regular language | Yes [🔗](src/Langlib/Classes/Regular/Closure/Intersection.lean) | Yes [🔗](src/Langlib/Classes/DeterministicContextFree/Closure/IntersectionRegular.lean)| Yes [🔗](src/Langlib/Classes/ContextFree/Closure/IntersectionRegular.lean) | Yes | Yes | Yes | Yes |
| Right quotient | Yes [🔗](src/Langlib/Classes/Regular/Closure/Quotient.lean) | No | No | No | No | No | Yes |
| Right quotient with a regular language | Yes [🔗](src/Langlib/Classes/Regular/Closure/Quotient.lean) | No | Yes [🔗](src/Langlib/Classes/ContextFree/Closure/Quotient.lean) | Yes | Yes | Yes | Yes |

Additional context-free closure results formalized here:

- [Terminal bijections](src/Langlib/Classes/ContextFree/Closure/Bijection.lean)
- [Terminal permutations](src/Langlib/Classes/ContextFree/Closure/Permutation.lean)
- [Prefix](src/Langlib/Classes/ContextFree/Closure/Prefix.lean)
- [Suffix](src/Langlib/Classes/ContextFree/Closure/Suffix.lean)

### Decidability

> TODO: Some results are shown against Mathlibs `Decidable` which is too weak. The proof are yet to be rewritten for `ComputablePred`.

| Language | Membership | Emptiness | Universality | Equivalence |
| --- | --- | --- | --- | --- |
| Regular | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Membership.lean) | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Emptiness.lean) | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Universality.lean) | ✓ [🔗](src/Langlib/Classes/Regular/Decidability/Equivalence.lean) |
| Deterministic context-free | ✓ | ✓ | ✓ | ✓ |
| Context-free | ✓ [🔗](src/Langlib/Classes/ContextFree/Decidability/Membership.lean) | ✓ [🔗](src/Langlib/Classes/ContextFree/Decidability/Emptiness.lean) | ✗ | ✗ |
| Context-sensitive | ✓ [🔗](src/Langlib/Classes/ContextSensitive/Decidability/Membership.lean) | ✗ | ✗ | ✗ |
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

> A large part of this repository was created with the help of [Aristotle](https://aristotle.harmonic.fun). It's an amazing tool for ambitious proofs. Special thanks to the developers to provide this tool to the community!
