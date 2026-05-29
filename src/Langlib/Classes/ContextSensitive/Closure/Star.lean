module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.ContextSensitive.Closure.Quotient

/-!
# Context-Sensitive Non-Closure Under Kleene Star

With the current non-contracting `is_CS` definition, no context-sensitive language contains the
empty word.  Since `L∗` always contains the empty word, any nonempty alphabet gives a small
counterexample.
-/

variable {T : Type}

/-- Context-sensitive languages are not closed under Kleene star for the current `is_CS`. -/
public theorem CS_notClosedUnderKleeneStar [Nonempty T] :
    ¬ ClosedUnderKleeneStar (α := T) is_CS := by
  intro hclosed
  let a : T := Classical.ofNonempty
  exact not_CS_of_nil_mem (L := KStar.kstar ({[a]} : Language T))
    (Language.nil_mem_kstar ({[a]} : Language T))
    (hclosed ({[a]} : Language T) (CS_singleton_letter a))
