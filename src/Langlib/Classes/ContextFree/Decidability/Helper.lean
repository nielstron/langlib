import Langlib.Utilities.ComputabilityPredicates
import Langlib.Classes.ContextFree.Basics.EncodedCFG

/-- The language represented by an encoded context-free grammar. -/
def contextFreeLanguageOf (G : EncodedCFG T) : Language T :=
  CF_language G.toCFGrammar

/-- The uniform membership predicate for encoded context-free grammars.

The input is a pair `(G, w)`, with both the encoded grammar and the word freshly
provided to the predicate. -/
def contextFreeMembershipPredicate (p : EncodedCFG T × List T) : Prop :=
  p.2 ∈ contextFreeLanguageOf p.1

/-- Uniform computability of membership for encoded context-free grammars. -/
abbrev ContextFreeComputableMembership (T : Type) [Primcodable T] : Prop :=
  ComputableMembership (contextFreeLanguageOf : EncodedCFG T → Language T)
