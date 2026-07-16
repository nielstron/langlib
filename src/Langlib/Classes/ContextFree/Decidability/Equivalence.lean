module

public import Langlib.Classes.ContextFree.Decidability.Universality
public import Langlib.Classes.Regular.Inclusion.ContextFree
public import Langlib.Automata.FiniteState.Equivalence.Regular

@[expose]
public section

/-!
# Undecidability of equivalence for encoded context-free grammars

The reduction itself is presentation-independent: an equivalence procedure can
compare its input with one fixed code for the universal language.  This file
first records that implication for the repository's concrete `EncodedCFG`
presentation.  Context-free equivalence is then ruled out by the encoded
universality reduction over every sufficiently large finite alphabet.
-/

namespace ContextFreeEquivalence

variable {T : Type}

private def universalDFA : DFA T Unit where
  start := ()
  step _ _ := ()
  accept := Set.univ

private theorem universalDFA_accepts :
    (universalDFA (T := T)).accepts = (Set.univ : Language T) := by
  apply Set.eq_univ_of_forall
  intro w
  change (universalDFA (T := T)).eval w ∈ Set.univ
  exact Set.mem_univ _

/-- The universal language is context-free over every terminal type. -/
theorem universalLanguage_is_CF [Fintype T] :
    is_CF (Set.univ : Language T) := by
  apply is_CF_of_is_RG
  apply is_RG_of_isRegular
  exact ⟨Unit, inferInstance, universalDFA,
    universalDFA_accepts⟩

/-- For concrete encoded CFGs, a uniform equivalence procedure would give a
uniform universality procedure for exactly the same raw presentation. -/
theorem computableEquivalence_implies_computableUniversality
    [Fintype T] [Primcodable T] :
    ComputableEquivalence (CF : Set (Language T))
        (contextFreeLanguageOf : EncodedCFG T → Language T) →
      ComputableUniversality (CF : Set (Language T))
        (contextFreeLanguageOf : EncodedCFG T → Language T) := by
  intro h
  exact h.computableUniversality_of_univ_mem universalLanguage_is_CF

/-- **Equivalence of encoded context-free grammars is not computable over any
sufficiently large finite terminal alphabet.**  The alphabet bound is exactly
the fixed bound supplied by the native universality reduction. -/
theorem contextFree_computableEquivalence_undecidable :
    ∃ n : Nat, ∀ (T : Type) (_ : Fintype T),
      n ≤ Fintype.card T →
      letI : DecidableEq T := Classical.decEq T
      letI : Primcodable T :=
        Primcodable.ofEquiv (Fin (Fintype.card T))
          (Fintype.truncEquivFin T).out
      ¬ ComputableEquivalence (CF : Set (Language T))
        (contextFreeLanguageOf : EncodedCFG T → Language T) := by
  obtain ⟨n, huniversality⟩ :=
    ContextFreeUniversality.contextFree_computableUniversality_undecidable
  refine ⟨n, ?_⟩
  intro T hT hcard
  letI : Fintype T := hT
  letI : DecidableEq T := Classical.decEq T
  letI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T))
      (Fintype.truncEquivFin T).out
  intro hequivalence
  exact huniversality T hT hcard
    (computableEquivalence_implies_computableUniversality hequivalence)

end ContextFreeEquivalence
