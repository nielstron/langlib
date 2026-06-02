---
title: "CS ⊊ Recursive: context-sensitive languages are recursive, and strictly so"
description: "Formal Lean 4 proofs that every context-sensitive language is recursive (CS ⊆ Recursive), and that the inclusion is strict (CS ⊊ Recursive), by diagonalization."
parent: "Context-sensitive"
nav_order: 3
---

# Context-sensitive languages and recursiveness (CS ⊆ Recursive, strictly)

## Statement

Every **context-sensitive language** (CSL) is **recursive** (decidable): there is an algorithm
that, given a word, always halts and correctly answers whether the word is in the language. As a
class inclusion, `CS ⊆ Recursive`.

Moreover the inclusion is **strict**: there is a recursive language that is **not**
context-sensitive, so `CS ⊊ Recursive`.

Nonemptiness of the alphabet is necessary for strictness — over an empty alphabet there are only
two languages and both classes coincide.

## Why CS ⊆ Recursive (the easy inclusion)

A context-sensitive grammar is **non-contracting**: every rule has a right-hand side at least as
long as its left-hand side, so a derivation can never shrink. Therefore a word of length `n` can
only be derived through sentential forms of length `≤ n`, drawn from a finite alphabet — finitely
many in all, bounding both how long and how many derivation sequences need to be examined.

So membership is decided by a terminating **bounded derivation-sequence search**, which is in fact
primitive recursive in the word, giving a genuine
[computable membership predicate](context-sensitive-membership-computable.html); a computable
decider is recursive. This is exactly what makes the diagonal language below *recursive*.

## In Lean

The inclusion `CS ⊆ Recursive`, in `Classes/ContextSensitive/Inclusion/Recursive.lean`:

- [`is_Recursive_of_is_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/Recursive.lean) — pointwise: `is_CS L → is_Recursive L`.
- [`CS_subset_Recursive_class`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/Recursive.lean) — class-level: `(CS : Set (Language T)) ⊆ Recursive`.
- Both are immediate from the computable membership decider [`computablePred_mem_of_is_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Decidability/Membership.lean) (`Classes/ContextSensitive/Decidability/Membership.lean`), which is the constructive heart of the inclusion — see [membership is computable](context-sensitive-membership-computable.html).

The strictness `CS ⊊ Recursive`, in `Classes/ContextSensitive/Inclusion/StrictRecursive.lean`:

- [`CS_strict_subclass_Recursive`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) — the headline `(CS : Set (Language T)) ⊂ Recursive`, for a nonempty finite alphabet `T`.
- [`diagonal_strict`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) — the abstract diagonalization core.
- [`exists_cs_enumeration`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) — the effective enumeration of context-sensitive languages with a uniformly computable membership oracle.
- [`memOracle_computable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/StrictRecursive.lean) — the membership oracle's joint computability, built on the uniform decider [`memCode`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Decidability/Membership.lean) (`memCode_sound` / `memCode_complete` / `code_of_CS`, in `Classes/ContextSensitive/Decidability/Membership.lean`).

The proof uses only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

## Why a closure argument does not work

For [Recursive ⊊ RE](recursive-strict-subset-re.html) there is a shortcut: recursive
languages are closed under complement while RE languages are not, so the two classes
cannot coincide. **No such shortcut exists here.** By Immerman–Szelepcsényi the
context-sensitive languages (`= NSPACE(n)`) are closed under complement, exactly like the
recursive languages; in fact the two classes agree on *every* standard closure operation —
union, intersection, complement, concatenation, Kleene star, reverse, ε-free homomorphism,
inverse homomorphism, ε-free substitution — and both fail the erasing operations. So no
closure property separates them, and strictness must be witnessed by a genuine
**diagonalization**.

## Proof idea

The argument is the classical diagonal construction, made effective.

**1. An effective enumeration of context-sensitive languages.** A context-sensitive
grammar is coded as data with its nonterminals fixed to `ℕ` (`Code T = List (grule T ℕ) × ℕ`),
which is `Primcodable`. A word `u` is decoded to a grammar by its length (`List.length` is onto
`ℕ` for a nonempty alphabet, so every coded grammar is hit). The language `enumLang u` is the
set of words accepted by a **bounded search over derivation sequences**: replay candidate
sequences of rule applications from the start symbol and check whether one yields exactly the
target word, searching all sequences up to a length/position bound that is large enough for
non-contracting grammars.

**2. The oracle is uniformly computable.** The key technical step (`memOracle_computable`) is
that membership in `enumLang u` is computable **jointly** in the grammar code `u` and the input
word — not merely for each fixed grammar. This rests on `primrec_applyRuleSeq_uniform`, a
re-derivation of the project's
[membership search](context-sensitive-membership-computable.html) that is primitive recursive
in the rule list treated as runtime data.

**3. The bounded search is correct.** It is sound (`memCode_sound`: a found sequence is a real
derivation) and complete within the bound (`memCode_complete`). Completeness is the heart of the
argument: take a **shortest** witnessing derivation sequence; if any intermediate sentential
form repeated, splicing out the loop would give a shorter witness, so the forms are
duplicate-free. For a non-contracting grammar every such form has length at most `|v|` over the
finitely many symbols occurring in the grammar, so a counting bound (`nodup_forms_card_bound`)
caps the number of distinct forms — hence the sequence length — within the search bound. The
optional erasing rule `S → ε` is handled separately: the start symbol occurs only in the initial
form, so that rule can fire at most once and never enlarges the workspace.

**4. Coverage.** Every context-sensitive language is `enumLang u` for some `u`
(`code_of_CS`): relabel the finitely many nonterminals of a context-sensitive grammar to `ℕ`
(preserving the language and context-sensitivity), then surjectivity of the word-to-code map
finds an index.

**5. Diagonalize.** With the enumeration `e` (covering all context-sensitive languages) and the
total computable oracle `mem`, define the diagonal language
`D = { v | mem v v = false }`. Then `D` is recursive — its characteristic function is
computable — but it is **not** context-sensitive: if `D = e u`, then `u ∈ D` iff `u ∉ e u = D`,
a contradiction. So `D` witnesses `CS ⊊ Recursive`.

## Keywords / also known as

context-sensitive languages are recursive, CS ⊆ Recursive, every context-sensitive language is
decidable, CSL decidability, type-1 languages are decidable, LBA languages are decidable;
context-sensitive strictly contained in recursive, CSL proper subset of decidable languages,
CS ⊊ Recursive, diagonalization over context-sensitive grammars, recursive but not
context-sensitive language, NSPACE(n) ⊊ recursive, effective enumeration of context-sensitive
grammars.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
