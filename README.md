# Grammars formally in Lean

## Instructions

In order to install Lean 4, follow the [manual](https://leanprover-community.github.io/get_started.html).

In order to download this project, run `git clone https://github.com/nielstron/grammars4` in your Unix-like command line.

In order to check that the proofs are correct, run `lake build` from the root directory of this project.

## Overview

> This project is WIP translation of https://github.com/madvorak/grammars, not everything has been ported to Lean 4 yet. Check the status of the build for details: [![CI](https://github.com/nielstron/grammars4/actions/workflows/build.yml/badge.svg)](https://github.com/nielstron/grammars4/actions/workflows/build.yml)

> The Context Free part of the proofs, in particular regarding closure under mapping, union and concatenation are being merged into Mathlib / CSlib. You find the corresponding PRs [here](https://github.com/leanprover-community/mathlib4/pulls?q=sort%3Aupdated-desc+is%3Apr+is%3Aopen+author%3Anielstron+ContextFreeGrammar)

Below you find what has been completed so far.

### Context-free grammars

[Definition](src/Grammars/Classes/ContextFree/Basics/Definition.lean)

[Example](test/Grammars/Test/DemoContextFree.lean)

[Closure under union](src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean)

[Closure under reversal](src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean)

[Closure under concatenation](src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean)

[Non-closure under intersection](src/Grammars/Classes/ContextFree/ClosureProperties/Intersection.lean) (\*)

[Non-closure under complement](src/Grammars/Classes/ContextFree/ClosureProperties/Complement.lean) (\*)

\* missing proof: [Context-free pumping lemma](src/Grammars/Classes/ContextFree/Basics/Pumping.lean), which is independently proven by [Alex Loitzl](https://github.com/AlexLoitzl/pumping_cfg)

### Context-sensitive grammars

[Example](test/Grammars/Test/DemoContextSensitive.lean)

### Unrestricted grammars

(a.k.a. general grammars, a.k.a. type-0 grammars, a.k.a. recursively-enumerable grammars, a.k.a. phrase-structure grammars, a.k.a. grammars)

[Definition](src/Grammars/Classes/Unrestricted/Basics/Definition.lean)

[Example](test/Grammars/Test/DemoUnrestricted.lean)

[Closure under union](src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean)

[Closure under reversal](src/Grammars/Classes/Unrestricted/ClosureProperties/Reverse.lean)

[Closure under concatenation](src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean)

[Closure under Kleene star](src/Grammars/Classes/Unrestricted/ClosureProperties/Star.lean)
