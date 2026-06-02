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
  always-halting deciding DPDA `is_DCF_decider`.
