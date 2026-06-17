module

public import Langlib.Classes.ContextFree.Decidability.Membership
public import Langlib.Classes.Recursive.Inclusion.ByTapeFromComputable

@[expose]
public section

/-! # Context-Free Languages Included in Recursive Languages

This file proves that every context-free language over a finite, encodable alphabet
is recursive.  The proof chooses an encoded CFG for the language, specializes the
uniform encoded-CFG membership decider to that code, and then applies the generic
construction of a recursive language from a total computable Boolean decider.

## Main results

- `is_Recursive_of_is_CF` — every context-free language is recursive.
- `CF_subset_Recursive` — class-level inclusion `CF ⊆ Recursive`.
-/

variable {T : Type}

/-- Every context-free language over a finite alphabet is recursive. -/
public theorem is_Recursive_of_is_CF [Fintype T] [DecidableEq T] [Primcodable T]
    {L : Language T} (hL : is_CF L) : is_Recursive L := by
  obtain ⟨c, hc⟩ :=
    (ContextFree.EncodedCFG.contextFreeLanguageOf_characterizes (T := T) L).mp hL
  obtain ⟨f, hf, hspec⟩ :=
    ComputablePred.computable_iff.mp (contextFree_membership_computablePred (T := T))
  refine is_Recursive_of_computable_decide L (fun w => f (c, w))
    (hf.comp ((Computable.const c).pair Computable.id)) ?_
  intro w
  rw [← hc]
  simpa using (iff_of_eq (congrFun hspec (c, w)))

/-- The context-free languages are included in the recursive languages. -/
public theorem CF_subset_Recursive [Fintype T] [DecidableEq T] [Primcodable T] :
    (CF : Set (Language T)) ⊆ (Recursive : Set (Language T)) :=
  fun _ hL => is_Recursive_of_is_CF hL
