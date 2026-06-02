---
title: Context-free
nav_order: 5
has_children: true
---

# Context-free languages

The **context-free** (type-2) languages — the languages of nested, recursive structure.

- **Grammars.** *Context-free grammars* (`is_CF`): every rule has the form `A → α`, a
  single nonterminal on the left and an arbitrary string `α` of terminals and nonterminals
  on the right.
- **Automata.** *Pushdown automata* (`is_PDA`) — finite automata with a stack, under
  final-state or empty-stack acceptance (the two agree).
