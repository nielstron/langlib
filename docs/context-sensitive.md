---
title: Context-sensitive
nav_order: 7
has_children: true
---

# Context-sensitive languages

The **context-sensitive** (type-1) languages — the languages decidable in linear space.

- **Grammars.** *Non-contracting grammars* (`is_CS`): every rule `α → β` satisfies
  `|α| ≤ |β|`, equivalently the context-sensitive form `γ A δ → γ β δ` with `β ≠ ε`.
- **Automata.** *Linear bounded automata* (`LBA`) — nondeterministic Turing machines
  confined to the tape cells occupied by the input (`NSPACE(n)`).

Key developments include [CSL = LBA](results/lba-context-sensitive.html),
[indexed languages are context-sensitive](results/indexed-subset-context-sensitive.html),
computable membership, and the strict inclusion into recursive languages.
