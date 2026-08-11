module

public import Langlib.Classes.ContextFree.Inclusion.Indexed
public import Langlib.Classes.ContextFree.Examples.AbnAbStarPowPredN

@[expose]
public section

/-!
# The language `{a b^n (a b*)^(n-1) | n >= 1}` is indexed

The shared example is context-free, hence indexed.
-/

/-- The language `{a b^n (a b*)^(n-1) | n >= 1}` is indexed. -/
public theorem abnAbStarPowPredN_is_Indexed : is_Indexed abnAbStarPowPredN :=
  is_Indexed_of_is_CF abnAbStarPowPredN_is_CF

