module

public import Mathlib.Computability.Language
public import Mathlib.Computability.PartrecCode
@[expose]
public section

/-! # The unary halting language

The language used in the Turing-machine decidability development.  A word over the
singleton alphabet `Unit` carries no information beyond its length, so we read the length
`n` of a word as the code number of a partial-recursive program
`Nat.Partrec.Code.ofNatCode n` and ask whether that program halts on input `0`.

This is the language of (codes of) all halting Turing machines.  It is recursively
enumerable but not recursive; the recursive-enumerability proof lives in
`Langlib.Classes.RecursivelyEnumerable.Examples.Halting`.
-/

/-- Unary halting language: a word is accepted when its length decodes to a code that
halts on input `0`.  This is the language of all halting Turing machines. -/
@[expose]
public def haltingUnaryLanguage : Language Unit :=
  fun w => ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom

end
