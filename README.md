# Lean4 Formal Grammar Library
[![CI](https://github.com/nielstron/grammars4/actions/workflows/build.yml/badge.svg)](https://github.com/nielstron/grammars4/actions/workflows/build.yml)

## Instructions

To install Lean 4, follow the [Lean community manual](https://leanprover-community.github.io/get_started.html).

To download this project, run:

```sh
git clone https://github.com/nielstron/grammars4
```

To check the library and tests, run:

```sh
lake build
```

## Overview

This repository contains a variety of results about various classes of languages in the Chomsky hierarchy.

### Regular languages

#### Basics

- [Non-regular language (`anbn`)](src/Grammars/Classes/Regular/Basics/NonRegular.lean)

#### Closure results

- [Union](src/Grammars/Classes/Regular/ClosureProperties/Union.lean)
- [Intersection](src/Grammars/Classes/Regular/ClosureProperties/Intersection.lean)
- [Complement](src/Grammars/Classes/Regular/ClosureProperties/Complement.lean)
- [Reversal](src/Grammars/Classes/Regular/ClosureProperties/Reverse.lean)
- [Prefix and suffix](src/Grammars/Classes/Regular/ClosureProperties/PrefixSuffix.lean)

#### Decidability results

- [Membership](src/Grammars/Classes/Regular/Decidability/Membership.lean)
- [Emptiness](src/Grammars/Classes/Regular/Decidability/Emptiness.lean)
- [Universality](src/Grammars/Classes/Regular/Decidability/Universality.lean)

### Context-free grammars

#### Basics

- [Definition](src/Grammars/Classes/ContextFree/Basics/Definition.lean)
- [Pumping lemma](src/Grammars/Classes/ContextFree/Basics/Pumping.lean)
- [Equivalence to PDAs](src/Grammars/Classes/ContextFree/Basics/PDAEquivalence.lean)

#### Examples

- [Demo grammar and language equality](test/Grammars/Test/DemoContextFree.lean)

#### Normal forms

- [Chomsky normal form grammars](src/Grammars/Classes/ContextFree/NormalForms/ChomskyNormalForm.lean)

#### Decidability results

- [Membership](src/Grammars/Classes/ContextFree/Decidability/Membership.lean)
- [Emptiness](src/Grammars/Classes/ContextFree/Decidability/Emptiness.lean)

#### Closure results

- [Substitution](src/Grammars/Classes/ContextFree/ClosureProperties/Substitution.lean)
- [Union](src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean)
- [Concatenation](src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean)
- [Kleene star](src/Grammars/Classes/ContextFree/ClosureProperties/Star.lean)
- [Reversal](src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean)
- [Terminal bijections](src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean)
- [Terminal permutations](src/Grammars/Classes/ContextFree/ClosureProperties/Permutation.lean)
- [Intersection with Regular Languages](src/Grammars/Classes/ContextFree/ClosureProperties/IntersectionRegular.lean)

#### Non-closure results

- [Intersection](src/Grammars/Classes/ContextFree/ClosureProperties/Intersection.lean)
- [Complement](src/Grammars/Classes/ContextFree/ClosureProperties/Complement.lean)

### Context-sensitive grammars

#### Basics

- [Definition](src/Grammars/Classes/ContextSensitive/Basics/Definition.lean)

#### Examples

- [Demo grammar](test/Grammars/Test/DemoContextSensitive.lean)

#### Closure results

- [Concatenation](src/Grammars/Classes/ContextSensitive/ClosureProperties/Concatenation.lean)

### Unrestricted grammars / recursively enumerable languages

#### Basics

- [Definition](src/Grammars/Classes/Unrestricted/Basics/Definition.lean)

#### Examples

- [Demo grammar](test/Grammars/Test/DemoUnrestricted.lean)

#### Closure results

- [Union](src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean)
- [Reversal](src/Grammars/Classes/Unrestricted/ClosureProperties/Reverse.lean)
- [Concatenation](src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean)
- [Kleene star](src/Grammars/Classes/Unrestricted/ClosureProperties/Star.lean)

#### Normal forms

- [Kuroda normal form](src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean)

## Checked statement summary

[`test/Grammars/Test/Results.lean`](test/Grammars/Test/Results.lean) currently checks the presence of these major named statements:

- Regular-language operations `prefixLang`, `suffixLang`, and their regularity theorems
- Regular closure under reversal, union, intersection, and complement
- Regular decidability of membership, emptiness, and universality
- A regular pumping theorem interface
- Context-free Chomsky normal form grammars and translation to CNF
- Context-free decidability of membership and emptiness
- Context-free closure under union, reversal, and concatenation
- Context-free non-closure under intersection and complement
- Unrestricted / recursively enumerable closure under union, reversal, concatenation, and star

The unrestricted concatenation and star developments, the context-sensitive concatenation module,
and the Kuroda normal form existence statement are present in the repository, but some of these
files still depend on unfinished placeholders or an axiom-backed statement.

## Acknowledgements

This repository started as a Lean 4 port of 
[madvorak/grammars](https://github.com/madvorak/grammars).
It further includes a port of the Pumping Lemma proof from [AlexLoitzl/pumping_cfg](https://github.com/AlexLoitzl/pumping_cfg/) and the equivalence proof between CFGs and PDAs from [shetzl/autth](https://github.com/shetzl/autth/tree/PDA).

Some of the context-free grammar work is also being upstreamed to Mathlib / CSlib.
Open PRs by the same author can be found
[here](https://github.com/leanprover-community/mathlib4/pulls?q=sort%3Aupdated-desc+is%3Apr+is%3Aopen+author%3Anielstron+ContextFreeGrammar).

> A large part of this repository was created with the help of [Aristotle](https://aristotle.harmonic.fun). It's an amazing tool for ambitious proofs. Special thanks to the developers to provide this tool to the community!