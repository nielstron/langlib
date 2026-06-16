module

public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Langlib.Examples.AnBnCn
public import Langlib.Classes.ContextSensitive.Examples.AnBnCn
public import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
@[expose]
public section

/-! # `{aⁿbⁿcⁿ}` as an RE Language

The language `{aⁿbⁿcⁿ}` is recursively enumerable because it is context-sensitive
(`lang_eq_eq_is_CS`, with the generating grammar and its derivation in
`Langlib.Classes.ContextSensitive.Examples.AnBnCn`) and every context-sensitive language is
recursively enumerable (`is_RE_of_CS`).

## Main declarations

- `lang_eq_eq_is_RE`
-/

/-- The language `{aⁿbⁿcⁿ}` is recursively enumerable, since it is context-sensitive. -/
public theorem lang_eq_eq_is_RE : is_RE lang_eq_eq :=
  is_RE_of_CS lang_eq_eq_is_CS

end
