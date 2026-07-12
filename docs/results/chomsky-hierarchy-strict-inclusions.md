---
title: "Chomsky hierarchy"
description: "Lean 4 proofs of the formalized Chomsky-hierarchy inclusions: Regular ⊊ DCFL ⊊ CFL ⊊ Indexed ⊊ CS ⊊ Recursive ⊊ RE."
nav_order: 2
---

# The Chomsky hierarchy is strict

## Statement

Langlib formalizes the following strict inclusions and the currently available bridges
between the grammar classes:

- **Regular ⊊ Deterministic context-free ⊊ Context-free**
- **Context-free ⊊ Indexed ⊊ Context-sensitive ⊊ Recursive ⊊ Recursively enumerable**
- **Regular ⊊ Linear ⊊ CFL**

The displayed chains are class-level shorthand. The per-alphabet strictness theorems carry
the hypotheses listed below. In particular, `Indexed ⊊ CS` is proved for finite alphabets
with at least two symbols, whereas `Indexed ⊆ CS` holds over every terminal type.

## In Lean

- Regular ⊊ DCFL: [`RG_strict_subclass_DCF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Inclusion/StrictDeterministicContextFree.lean).
- Regular ⊊ Linear: `RG_strict_subclass_Linear`; Linear ⊊ CF: [`Linear_strict_subclass_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean), separated by `{0ⁿ1ⁿ2ᵐ3ᵐ}` via the [linear pumping lemma](linear-pumping-lemma.html).
- DCFL ⊊ CFL: `is_CF_of_is_DCF` / `DCF_subclass_CF` (strictness via `DPDA_strict_subclass_PDA`).
- CFL ⊊ Indexed: [`CF_strict_subclass_Indexed`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean) and [`CF_subclass_Indexed_and_exists_strict`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean).
- Indexed ⊊ CS: [`Indexed_strict_subclass_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Indexed/Inclusion/StrictContextSensitive.lean), for a finite alphabet `T` satisfying `2 ≤ Fintype.card T`. Its inclusion half is the arbitrary-alphabet theorem `Indexed_subclass_CS`; see the [Aho simulation development](indexed-subset-context-sensitive.html).
- CF ⊆ CS: `CF_subclass_CS`.
- CS ⊊ Recursive: [`CS_strict_subclass_Recursive`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) — by diagonalization; see the [dedicated page](context-sensitive-strict-subset-recursive.html).
- Recursive ⊊ RE: see the [dedicated page](recursive-strict-subset-re.html).

## Proof idea

Each strict inclusion combines an *inclusion* (every grammar/automaton of the lower
class is one of the upper class) with strictness witnessed in one of two ways — a
*separating language* in the upper class but provably not the lower, or a *closure
mismatch* where the two classes differ on a closure operation.

- **Regular ⊊ DCFL** (`RG_strict_subclass_DCF`) and **Regular ⊊ Linear**
  (`RG_strict_subclass_Linear`): the separating language is `{aⁿbⁿ}` (`anbn`), which
  is deterministic context-free (`anbn_is_DCF`) and linear but not regular
  (`anbn_not_isRegular`, via the regular pumping lemma); transported to a nontrivial
  alphabet by an injective letter map.
- **DCFL ⊊ CFL** (`DCF_strict_subclass_CF`): a *closure mismatch*, not a witness
  language. Over `Fin 3` the DCF languages are closed under complement
  (`DCF_closedUnderComplement`) but the CF languages are not
  (`CF_notClosedUnderComplement`); `strict_subset_of_subset_different_property` turns
  this differing closure property into proper containment.
  `DPDA_strict_subclass_PDA` transfers this to the automaton classes.
- **Linear ⊊ CFL** (`Linear_strict_subclass_CF`): the separating language is
  `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4` (`L4`), context-free (`L4_is_CF`, a concatenation of two
  `{aⁿbⁿ}` blocks) but not linear (`L4_not_is_Linear`, via the
  [linear pumping lemma](linear-pumping-lemma.html)).
- **CFL ⊊ Indexed** (`CF_strict_subclass_Indexed`): the separating language is
  `{aⁿbⁿcⁿ}`, indexed (an indexed grammar with a stack-bottom marker forcing each
  nonterminal to consume exactly as many flags as were pushed) but not context-free.
- **Indexed ⊊ CS** combines two independent arguments. The inclusion
  (`Indexed_subclass_CS`) is Aho's finite compression, scheduled in linear logical space
  and compiled through an exact finite row checker. Strictness starts from the unary
  halting language. `is_RE_exists_CS_homomorphicImage` constructs a context-sensitive
  language over `Option Unit` whose padding-erasing homomorphic image is that halting
  language. If the padded language were indexed, closure of indexed languages under
  arbitrary homomorphism would make the halting language indexed, hence context-sensitive
  and recursive, contradicting `haltingUnaryLanguage_not_Recursive`. This binary witness
  is transported along an alphabet embedding to every finite `T` with
  `2 ≤ Fintype.card T`; see the [dedicated page](indexed-subset-context-sensitive.html).
- **CS ⊊ Recursive** (`CS_strict_subclass_Recursive`): by diagonalization over an
  effective enumeration of context-sensitive grammars; see the
  [dedicated page](context-sensitive-strict-subset-recursive.html).
- **Recursive ⊊ RE**: a closure mismatch — recursive languages are closed under
  complement, RE languages are not; see the [dedicated page](recursive-strict-subset-re.html).

## Keywords / also known as

Chomsky hierarchy strict, regular proper subset context-free, DCFL proper subset
CFL, context-free proper subset indexed, indexed proper subset context-sensitive, recursive proper subset recursively
enumerable, language class separations, proper containment Chomsky hierarchy.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
