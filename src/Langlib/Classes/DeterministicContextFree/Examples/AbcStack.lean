module

public import Langlib.Classes.DeterministicContextFree.Definition
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
@[expose]
public section

/-! # Shared stack alphabet for the `a b c` DPDA examples

`ABCStack` is the pushdown stack alphabet shared by the deterministic pushdown automata
recognising `{aⁿbⁿcᵐ}` (`Langlib.Classes.DeterministicContextFree.Examples.AnBnCm`) and
`{aⁿbᵐcᵐ}` (`Langlib.Classes.DeterministicContextFree.Examples.AnBmCm`). It lives in its
own leaf module so that neither example needs to publicly depend on the other.
-/

namespace DCFLIntersection

public inductive ABCStack where
  | bottom
  | mark
  deriving DecidableEq, Fintype

end DCFLIntersection

end
