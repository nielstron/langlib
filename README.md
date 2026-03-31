# Lean 4 Formal Grammar Library
[![CI](https://github.com/nielstron/grammars4/actions/workflows/build.yml/badge.svg)](https://github.com/nielstron/grammars4/actions/workflows/build.yml)

This repository contains formalized results about grammars, languages, and automata across the Chomsky hierarchy.

The main library entry point is [src/Grammars.lean](src/Grammars.lean).


### Regular Languages

- Definition inherited from Mathlib

### Context-Free Grammars

- [Definition](src/Grammars/Classes/ContextFree/Basics/Definition.lean)
- [Pumping lemma](src/Grammars/Classes/ContextFree/Basics/Pumping.lean)
- [Ogdens Lemma](src/Grammars/Classes/ContextFree/Basics/Ogden.lean)
- [Chomsky normal form](src/Grammars/Classes/ContextFree/NormalForms/ChomskyNormalForm.lean)

### Deterministic Context-Free Languages

- [Definition](src/Grammars/Classes/DetContextFree/Basics/DCFL.lean)

### Context-Sensitive Grammars

- [Definition](src/Grammars/Classes/ContextSensitive/Basics/Definition.lean)
- [Noncontracting grammars](src/Grammars/Classes/ContextSensitive/Basics/NonContracting.lean)

### Unrestricted Grammars

- [Definition](src/Grammars/Classes/Unrestricted/Basics/Definition.lean)
- [Kuroda normal form](src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean)

### Automata

- [Pushdown automata](src/Grammars/Automata/Pushdown/Basics/PDA.lean)
- [Deterministic pushdown automata](src/Grammars/Automata/DetPushdown/Basics/DPDA.lean)
- [Linear bounded automata](src/Grammars/Automata/LinearBounded/Basics/LBA.lean)
- Turing Machines inherited from Mathlib

### Examples

- [Context-free example grammar](test/Grammars/Test/DemoContextFree.lean)
- [Context-sensitive example grammars](test/Grammars/Test/DemoContextSensitive.lean)
- [Unrestricted example grammar](test/Grammars/Test/DemoUnrestricted.lean)

## Proof overview

`🔗` indicates that this repository contains a corresponding proof file.

### Hierarchy And Equivalences

| Grammar side | Relation | Automaton side |
| --- | --- | --- |
| Regular languages | ≡ | DFA languages (Mathlib) |
| ⊆ |  |  |
| Deterministic context-free languages | ≡ [🔗](src/Grammars/Classes/DetContextFree/Basics/DCFL.lean) | DPDA final-state languages |
| ⊆ [🔗](src/Grammars/Classes/DetContextFree/Basics/Inclusion.lean) |  | ⊆ [🔗](src/Grammars/Automata/DetPushdown/Basics/Inclusion.lean) |
| Context-free languages | ⇔ [🔗](src/Grammars/Classes/ContextFree/Basics/PDAEquivalence.lean) | PDA languages (Final State ⇔ Empty Stack [🔗](src/Grammars/Automata/Pushdown/Basics/FinalStateEmptyStackEquiv.lean)) |
| ⊆ [🔗](src/Grammars/Classes/ContextFree/Basics/Inclusion.lean) without `ε`-productions |  |  |
| Context-sensitive languages (Non-erasing ⇔ Non-contracting) | ⇔ | LBA languages |
| ⊆ [🔗](src/Grammars/Classes/ContextSensitive/Basics/Inclusion.lean) |  | ⊆ [🔗](src/Grammars/Automata/LinearBounded/Basics/Inclusion.lean) |
| Recursively enumerable languages | ⇔ | Turing-machine languages (Mathlib) |

The repository also proves that the project's notion of context-free language is
⇔ [🔗](src/Grammars/Classes/ContextFree/Basics/Inclusion.lean) Mathlib's `IsContextFree`.



### Closure


| Language | Union | Intersection | Complement | Concatenation | Kleene star | Reversal | Left quotient | Right quotient |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Regular | ✓ [🔗](src/Grammars/Classes/Regular/ClosureProperties/Union.lean) | ✓ [🔗](src/Grammars/Classes/Regular/ClosureProperties/Intersection.lean) | ✓ [🔗](src/Grammars/Classes/Regular/ClosureProperties/Complement.lean) | ✓ | ✓ | ✓ [🔗](src/Grammars/Classes/Regular/ClosureProperties/Reverse.lean) | ✓ | ✓ [🔗](src/Grammars/Classes/Regular/ClosureProperties/Quotient.lean) |
| Deterministic context-free | ✗ | REG, i.g. ✗ | ✓ [🔗](src/Grammars/Automata/DetPushdown/ClosureProperties/Complement.lean) | ✗ | ✗ | ✗ | ✗ | REG |
| Context-free | ✓ [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean) | REG [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/IntersectionRegular.lean), i.g. ✗ [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/Intersection.lean)  | ✗ [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/Complement.lean) | ✓ [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean) | ✓ [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/Star.lean) | ✓ [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean) | REG | REG [🔗](src/Grammars/Classes/ContextFree/ClosureProperties/Quotient.lean) |
| Context-sensitive | ✓ | ✓ | ✓ | ✓ [🔗](src/Grammars/Classes/ContextSensitive/ClosureProperties/Concatenation.lean) | ✓ | ✓ [🔗](src/Grammars/Classes/ContextSensitive/ClosureProperties/Reverse.lean) | ✗ | ✗ |
| Recursively enumerable | ✓ [🔗](src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean) | ✓ | ✗ | ✓ [🔗](src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean) | ✓ | ✓ [🔗](src/Grammars/Classes/Unrestricted/ClosureProperties/Reverse.lean) | ✓ | ✓ |

Additional context-free closure results formalized here:

- [Substitution](src/Grammars/Classes/ContextFree/ClosureProperties/Substitution.lean)
- [Terminal bijections](src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean)
- [Terminal permutations](src/Grammars/Classes/ContextFree/ClosureProperties/Permutation.lean)
- [Prefix](src/Grammars/Classes/ContextFree/ClosureProperties/Prefix.lean)
- [Suffix](src/Grammars/Classes/ContextFree/ClosureProperties/Suffix.lean)

### Decidability

| Language | Membership | Emptiness | Universality | Equivalence |
| --- | --- | --- | --- | --- |
| Regular | ✓ [🔗](src/Grammars/Classes/Regular/Decidability/Membership.lean) | ✓ [🔗](src/Grammars/Classes/Regular/Decidability/Emptiness.lean) | ✓ [🔗](src/Grammars/Classes/Regular/Decidability/Universality.lean) | ✓ |
| Deterministic context-free | ✓ | ✓ | ✓ | ✓ |
| Context-free | ✓ [🔗](src/Grammars/Classes/ContextFree/Decidability/Membership.lean) | ✓ [🔗](src/Grammars/Classes/ContextFree/Decidability/Emptiness.lean) | ✗ | ✗ |
| Context-sensitive | ✓ [🔗](src/Grammars/Classes/ContextSensitive/Decidability/Membership.lean) | ✗ | ✗ | ✗ |
| Recursively enumerable | ✗ | ✗ | ✗ | ✗ |

## How To Use The Library

For most uses, import the hub:

```lean
import Grammars
```

If you only need one part of the development, import the corresponding module directly, for example:

```lean
import Grammars.Classes.ContextFree.Basics.Definition
import Grammars.Classes.ContextFree.Basics.PDAEquivalence
import Grammars.Classes.Regular.Decidability.Membership
```

The files in [test/Grammars/Test](test/Grammars/Test) provide small worked examples:

- [test/Grammars/Test/DemoContextFree.lean](test/Grammars/Test/DemoContextFree.lean)
- [test/Grammars/Test/DemoContextSensitive.lean](test/Grammars/Test/DemoContextSensitive.lean)
- [test/Grammars/Test/DemoUnrestricted.lean](test/Grammars/Test/DemoUnrestricted.lean)

To build the library and examples, run:

```sh
lake build
```

## Installation Instructions

To install Lean 4, follow the [Lean community manual](https://leanprover-community.github.io/get_started.html).

To download this project, run:

```sh
git clone https://github.com/nielstron/grammars4
cd grammars4
```

To check the library and tests, run:

```sh
lake build
```

## Acknowledgements

This repository started as a Lean 4 port of
[madvorak/grammars](https://github.com/madvorak/grammars).
It further includes a port of the Pumping Lemma proof from [AlexLoitzl/pumping_cfg](https://github.com/AlexLoitzl/pumping_cfg/) and the equivalence proof between CFGs and PDAs from [shetzl/autth](https://github.com/shetzl/autth/tree/PDA).

Some of the context-free grammar work is also being upstreamed to Mathlib / CSlib.
Open PRs by the same author can be found
[here](https://github.com/leanprover-community/mathlib4/pulls?q=sort%3Aupdated-desc+is%3Apr+is%3Aopen+author%3Anielstron+ContextFreeGrammar).

> A large part of this repository was created with the help of [Aristotle](https://aristotle.harmonic.fun). It's an amazing tool for ambitious proofs. Special thanks to the developers to provide this tool to the community!
