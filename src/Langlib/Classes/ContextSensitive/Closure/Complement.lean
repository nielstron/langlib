module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.ContextSensitive.Closure.Quotient
import Langlib.Grammars.ContextSensitive.Toolbox
import Langlib.Grammars.ContextSensitive.UnrestrictedCharacterization

/-!
# Context-Sensitive Non-Closure Under Complement

Under the current non-contracting `is_CS` definition, context-sensitive languages never contain
the empty word.  The empty language is context-sensitive, but its complement contains the empty
word, so the class is not closed under complement.
-/

variable {T : Type}

private def emptyCSGrammar (T : Type) : CS_grammar T where
  nt := Unit
  initial := ()
  rules := []
  output_nonempty := by
    intro _ h
    cases h

private theorem emptyCSGrammar_language :
    CS_language (emptyCSGrammar T) = (0 : Language T) := by
  ext w
  constructor
  · intro hw
    unfold CS_language at hw
    cases CS_tran_or_id_of_deri hw with
    | inl hid =>
        cases w <;> simp [emptyCSGrammar] at hid
    | inr hstep =>
        obtain ⟨_, ht, _⟩ := hstep
        obtain ⟨r, _, _, hr, _, _⟩ := ht
        cases hr
  · intro hw
    cases hw

/-- The empty language is context-sensitive. -/
public theorem CS_empty : is_CS (0 : Language T) :=
  is_CS_via_csg_implies_is_CS ⟨emptyCSGrammar T, emptyCSGrammar_language⟩

/-- Context-sensitive languages are not closed under complement for the current `is_CS`. -/
public theorem CS_notClosedUnderComplement :
    ¬ ClosedUnderComplement (α := T) is_CS := by
  intro hclosed
  have hcomp := hclosed (0 : Language T) CS_empty
  exact not_CS_of_nil_mem (L := (0 : Language T)ᶜ) (Language.notMem_zero []) hcomp
