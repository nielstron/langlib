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

The displayed chains are class-level shorthand. Every headline strictness theorem ranges
over an arbitrary finite alphabet with the stated lower bound on its number of elements. In particular,
`Indexed ⊊ CS` is proved for alphabets with at least 2 elements, whereas `Indexed ⊆ CS`
holds over every terminal type.

## In Lean

- Regular ⊊ DCFL: [`RG_strict_subclass_DCF_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Inclusion/StrictDeterministicContextFree.lean), for every finite alphabet with at least 2 elements.
- Regular ⊊ Linear: `RG_strict_subclass_Linear_of_card`, for every finite alphabet with at least 2 elements; Linear ⊊ CF: [`Linear_strict_subclass_CF_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean), for every finite alphabet with at least 4 elements, separated by `{0ⁿ1ⁿ2ᵐ3ᵐ}` via the [linear pumping lemma](linear-pumping-lemma.html).
- DCFL ⊊ CFL: [`DCF_strict_subclass_CF_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Inclusion/StrictContextFree.lean), for every finite alphabet with at least 3 elements.
- CFL ⊊ Indexed: [`CF_strict_subclass_Indexed`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean), for every finite alphabet with at least 3 elements; its inclusion half is `CF_subclass_Indexed`.
- Indexed ⊊ CS: [`Indexed_strict_subclass_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Indexed/Inclusion/StrictContextSensitive.lean), for every finite alphabet with at least 2 elements. Its inclusion half is the arbitrary-alphabet theorem `Indexed_subclass_CS`; see the [Aho simulation development](indexed-subset-context-sensitive.html).
- CF ⊆ CS: `CF_subclass_CS`.
- CS ⊊ Recursive: [`CS_strict_subclass_Recursive_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean), for every finite alphabet with at least 1 element, by diagonalization; see the [dedicated page](context-sensitive-strict-subset-recursive.html).
- Recursive ⊊ RE: `Recursive_strict_subclass_RE_of_card`, for every finite alphabet with at least 1 element; see the [dedicated page](recursive-strict-subset-re.html).

## Proof idea

Each strict inclusion combines an *inclusion* (every grammar/automaton of the lower
class is one of the upper class) with strictness witnessed in one of two ways — a
*separating language* in the upper class but provably not the lower, or a *closure
mismatch* where the two classes differ on a closure operation.

- **Regular ⊊ DCFL** (`RG_strict_subclass_DCF_of_card`) and **Regular ⊊ Linear**
  (`RG_strict_subclass_Linear_of_card`): the separating language is `{aⁿbⁿ}` (`anbn`), which
  is deterministic context-free (`anbn_is_DCF`) and linear but not regular
  (`anbn_not_isRegular`, via the regular pumping lemma); transported to a nontrivial
  alphabet with at least 2 elements by an injective letter map.
- **DCFL ⊊ CFL** (`DCF_strict_subclass_CF_of_card`): a *closure mismatch*, not a witness
  language. Over a 3-element alphabet, the DCF languages are closed under complement
  (`DCF_closedUnderComplement`) but the CF languages are not
  (`CF_notClosedUnderComplement`); `strict_subset_of_subset_different_property` turns
  this differing closure property into proper containment, then injective relabelling
  transports it to every alphabet with at least 3 elements.
  `DPDA_strict_subclass_PDA_of_card` gives the corresponding automaton-class statement.
- **Linear ⊊ CFL** (`Linear_strict_subclass_CF_of_card`): the separating language is
  `{0ⁿ1ⁿ2ᵐ3ᵐ}` over a 4-element alphabet (`anbncmdm`), context-free (`anbncmdm_is_CF`, a
  concatenation of two `{aⁿbⁿ}` blocks) but not linear (`anbncmdm_not_is_Linear`, via the
  [linear pumping lemma](linear-pumping-lemma.html)); injective relabelling transports it to
  every alphabet with at least 4 elements.
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
  is transported along an alphabet embedding to every finite alphabet with at least
  2 elements; see the [dedicated page](indexed-subset-context-sensitive.html).
- **CS ⊊ Recursive** (`CS_strict_subclass_Recursive_of_card`): by diagonalization over an
  effective enumeration of context-sensitive grammars; see the
  [dedicated page](context-sensitive-strict-subset-recursive.html).
- **Recursive ⊊ RE**: a closure mismatch — recursive languages are closed under
  complement, RE languages are not; see the [dedicated page](recursive-strict-subset-re.html).

## Keywords / also known as

Chomsky hierarchy strict, regular proper subset context-free, DCFL proper subset
CFL, context-free proper subset indexed, indexed proper subset context-sensitive, recursive proper subset recursively
enumerable, language class separations, proper containment Chomsky hierarchy.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
