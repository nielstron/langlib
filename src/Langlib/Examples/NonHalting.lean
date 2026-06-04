module

public import Langlib.Examples.Halting
@[expose]
public section

/-! # The unary non-halting language

The complement of `haltingUnaryLanguage`: the language of (codes of) all Turing machines
that do *not* halt on input `0`.  It is the canonical example of a language that is not
recursively enumerable; that proof lives in
`Langlib.Classes.RecursivelyEnumerable.Examples.NonHalting`.
-/

/-- Unary non-halting language: the complement of `haltingUnaryLanguage`, i.e. the language
of all Turing machines that do not halt on input `0`. -/
@[expose]
public def nonHaltingUnaryLanguage : Language Unit :=
  haltingUnaryLanguageᶜ

end
