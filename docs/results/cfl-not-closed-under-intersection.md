---
title: "Context-free languages are not closed under intersection"
description: "A formal Lean 4 proof that context-free languages are not closed under intersection (via the pumping lemma), with non-closure under complement as a corollary."
parent: "Context-free"
nav_order: 6
---

# Context-free languages are not closed under intersection

## Statement

The class of **context-free languages** (CFL) is **not** closed under intersection:
there are two context-free languages whose intersection is not context-free. The
witness used in the source is

> `{aⁿbⁿcⁿ}` = `{aⁿbⁿcᵐ}` ∩ `{aⁿbᵐcᵐ}`,

where each factor (`lang_eq_any` and `lang_any_eq`) is context-free — only one pair
of adjacent blocks is constrained to have equal length, which a single stack can
check — but the intersection `lang_eq_eq = {aⁿbⁿcⁿ}` is **not** context-free, ruled
out by the [pumping lemma for context-free languages](context-free-pumping-lemma.html).

Non-closure under **complement** then follows as a corollary: context-free languages
*are* closed under union, so if they were also closed under complement, De Morgan's
law would force closure under intersection — a contradiction.

## In Lean

Non-closure under intersection, in `Classes/ContextFree/Closure/Intersection.lean`:

- [`CF_notClosedUnderIntersection`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Intersection.lean) — the class is not closed under intersection.
- [`CF_notClosedUnderIntersection_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Intersection.lean) — over any alphabet with enough symbols.
- [`notCF_lang_eq_eq`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Intersection.lean) — the intersection witness language is not context-free (the pumping-lemma step).

Non-closure under complement (the corollary), in `Classes/ContextFree/Closure/Complement.lean`:

- [`CF_notClosedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Complement.lean) / [`CF_notClosedUnderComplement_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Complement.lean).

## Proof idea

**The two factors are context-free.** Each is a concatenation of context-free
pieces (CFL is closed under concatenation, `CF_of_CF_c_CF`): `lang_eq_any = {aⁿbⁿ} ·
{cᵐ}` via `CF_lang_eq_any`, and `lang_any_eq = {aⁿ} · {bᵐcᵐ}` via `CF_lang_any_eq`
(the `{bᵐcᵐ}` factor obtained from `{aⁿbⁿ}` by a letter permutation).

**The intersection is `{aⁿbⁿcⁿ}`.** `intersection_of_lang_eq_eq` and
`lang_eq_eq_of_intersection` prove `lang_eq_any ⊓ lang_any_eq = lang_eq_eq`; the
harder inclusion uses `nthLe`-based block comparisons (`doubled_le_singled` /
`doubled_ge_singled`) to force the two block-count witnesses to agree.

**`{aⁿbⁿcⁿ}` is not context-free** (`notCF_lang_eq_eq`). Apply `CF_pumping` to
`aⁿ⁺¹bⁿ⁺¹cⁿ⁺¹` to get a decomposition `u v x y z` with `|vy| > 0` and `|vxy| ≤ n`.
The length bound forces `vy` to omit at least one of the three letters
(`not_all_letters`). The contradiction is packaged in `false_of_uvvxyyz`: pumping to
`u v² x y² z` keeps the count of the omitted letter at `n+1`, but `vy` contains at
least one of the other two letters (its first letter, by `elimin_abc`), so that
letter's count rises above `n+1`, breaking the equal-count condition of `lang_eq_eq`.
The three symmetric cases (whichever letter is omitted) reuse the same lemma. This
gives non-closure under intersection directly (`nnyCF_of_CF_i_CF`,
`CF_notClosedUnderIntersection`), and `CF_notClosedUnderIntersection_of_card`
transfers it to any alphabet with at least three symbols via an injection from
`Fin 3`.

For complement: CFLs are closed under union and `A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ`, so closure
under complement would imply the just-refuted closure under intersection.

## Keywords / also known as

context-free not closed under intersection, CFL intersection not context-free,
anbncn not context-free, context-free not closed under complement, pumping lemma
context-free, De Morgan context-free closure, type-2 languages closure properties.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
