---
title: Linear
nav_order: 4
has_children: true
---

# Linear languages

The **linear** languages — strictly between the regular and the context-free languages
(`{aⁿbⁿ}` is the prototypical linear, non-regular example).

- **Grammars.** *Linear grammars* (`grammar_linear`): every rule has the form `A → u B v`
  or `A → w`, where `A`, `B` are nonterminals and `u`, `v`, `w` are terminal strings — at
  most one nonterminal on the right, in any position.
