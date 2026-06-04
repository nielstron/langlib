---
title: "PDA = CFG"
description: "A formal Lean 4 proof that pushdown automata and context-free grammars recognize exactly the same class of languages."
parent: Equivalences
nav_order: 1
grandparent: Context-free
---

# Pushdown automata recognize exactly the context-free languages (PDA = CFG)

## Statement

A language is **context-free** if and only if it is recognized by a **pushdown
automaton** (PDA). The grammar model (context-free grammars) and the automaton
model (PDAs) define one and the same language class.

## In Lean

- [`is_PDA_iff_isContextFree`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) — pointwise: `is_PDA L ↔ L.IsContextFree`.
- [`CF_eq_PDA_Class`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) — class equality `(CF : Set (Language T)) = PDA.Class`.
- [`is_PDA_of_isContextFree`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) and [`is_CF_of_is_PDA`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) — the two inclusions.

PDA acceptance by final state and by empty stack define the same class — see
[Acceptance modes](pda-acceptance-modes.html).

## Proof idea

Both directions use **acceptance by empty stack**, which is then bridged to
final-state acceptance.

**CFG → PDA** (`CFG_to_PDA.M`). Given a grammar `G`, build a PDA
with a single state `Q.loop`, stack alphabet `Symbol T G.NT`, and start symbol
`nonterminal G.initial`. Its transitions implement a leftmost-derivation simulation:
an ε-move replaces a nonterminal `N` on top of the stack by `α` for each rule
`⟨N, α⟩ ∈ G.rules` (`M_consumes_nonterminal`), and an input-move pops a terminal off
the stack when it matches the next input symbol (`M_consumes_terminal`). The two
inclusions `M_reaches_off_G_derives` and `G_derives_of_M_reaches` (the latter by
induction on the number of PDA steps) give `pda_of_cfg : G.language = (M G).acceptsByEmptyStack`.

**PDA → CFG** (`PDA_to_CFG.G`). From a PDA `M`, build a grammar
whose nonterminals (`N`) are the triples `N.single q Z p` and the bounded lists
`N.list q α p`, plus a start symbol `N.start`. A triple `q Z p` derives exactly the
input strings along which `M` goes from state `q` to state `p` while net-popping the
single stack symbol `Z`. The rule families (`compute_rule`/`compute_rule'`,
`split_rule`, `epsilon_rule`, `start_rule`) are shown finite via the bound
`max_push M` on stack pushes. Correctness is `cfg_of_pda : (G M).language = M.acceptsByEmptyStack`,
proved through `derives_of_reachesIn` and `reachesIn_of_derivesLeftmostIn` (both by
strong induction on step count).

Both constructions use empty-stack acceptance; that it agrees with final-state acceptance
is the separate [Acceptance modes](pda-acceptance-modes.html) result.

## Keywords / also known as

PDA equals CFG, pushdown automata equal context-free grammars, context-free
languages are PDA-recognizable, CFG to PDA construction, PDA to CFG construction,
acceptance by final state equals acceptance by empty stack, Chomsky type-2
automaton characterization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
