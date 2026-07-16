---
title: Deterministic context-free
nav_order: 6
has_children: true
---

# Deterministic context-free languages

The **deterministic context-free** (DCF) languages — the languages of LR parsers, the
proper subclass of the context-free languages closed under complement.

- **Automata.** *Deterministic pushdown automata* (DPDA): a pushdown automaton with at
  most one applicable move in every configuration. The normal form used here is the
  always-halting *total* DPDA (`DPDA.IsTotal`), with language-level presentation
  `is_DCF_total`.
- **Grammars.** *LR(k) grammars*: a rightmost handle is uniquely determined by the
  already-read prefix and `k` terminals of lookahead. For every fixed `k > 0`,
  [LR(k) languages are exactly DPDA languages](results/lr-equals-dpda.html); the
  existential finite-lookahead class `LR` therefore equals `DPDA.Class` and `DCF`.
