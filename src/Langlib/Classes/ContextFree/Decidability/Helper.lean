import Langlib.Utilities.ComputabilityPredicates
import Langlib.Classes.ContextFree.Basics.EncodedCFG

/-- The language represented by an encoded context-free grammar. -/
def contextFreeLanguageOf (G : EncodedCFG T) : Language T :=
  CF_language G.toCFGrammar
