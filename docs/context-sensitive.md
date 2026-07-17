---
title: Context-sensitive
nav_order: 7
has_children: true
---

# Context-sensitive languages

The **context-sensitive** (type-1) languages — the languages recognizable in
nondeterministic linear space. Their membership problems are decidable, but
whether every context-sensitive language is recognizable in deterministic
linear space is the open first LBA problem.

- **Grammars.** *Non-contracting grammars* (`is_CS`): every rule `α → β` satisfies
  `|α| ≤ |β|`, equivalently the context-sensitive form `γ A δ → γ β δ` with `β ≠ ε`.
- **Automata.** *Linear bounded automata* (`LBA`) — nondeterministic Turing machines
  confined to the tape cells occupied by the input (`NSPACE(n)`).

Key developments include [CSL = LBA](results/lba-context-sensitive.html), computable
membership, the [functional LBA-to-DLBA
conversion](results/functional-lba-dlba.html), the [exact formal and restricted
boundaries of the first LBA problem](results/first-lba-problem-boundaries.html),
and the strict inclusion into recursive languages.
