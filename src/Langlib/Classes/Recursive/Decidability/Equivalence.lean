module

public import Langlib.Classes.Recursive.Decidability.Emptiness

@[expose]
public section

/-!
# Undecidability of equivalence for recursive languages

Recursive languages are presented by raw partial-recursive program codes under
the semantic promise `RecursiveDeciderCode.Valid` that the program halts on every
encoded word.  Although membership is uniformly decidable under this promise,
equivalence is not: there is no single partial-recursive Boolean procedure which
terminates on every pair of valid codes and decides whether their languages agree.

The reduction compiles one valid decider for the empty language.  Comparing an
arbitrary valid code with that fixed code would decide emptiness, contradicting
`emptiness_undecidable`.
-/

namespace RecursiveDeciderCode

open Nat.Partrec

variable {T : Type} [Primcodable T]

/-- No promise algorithm can decide whether two valid always-halting decider codes
denote the same language. -/
public theorem equivalence_undecidable [Nonempty T] :
    ¬ ComputablePredOnPromise
      (fun p : Code × Code ↦ Valid (T := T) p.1 ∧ Valid (T := T) p.2)
      (fun p ↦ language (T := T) p.1 = language (T := T) p.2) := by
  intro hEquivalent
  apply emptiness_undecidable (T := T)
  let emptyTest : Unit → List T → Bool := fun _ _ ↦ false
  have hemptyTest : Computable₂ emptyTest := (Computable.const false).to₂
  let emptyCode : Code := compileBool emptyTest hemptyTest ()
  have hemptyValid : Valid (T := T) emptyCode :=
    compileBool_valid emptyTest hemptyTest ()
  have hemptyLanguage : language (T := T) emptyCode = (∅ : Set (List T)) := by
    rw [language_compileBool emptyTest hemptyTest]
    simp [emptyTest]
  obtain ⟨evalEquivalent, hevalPartrec, hevalSpec⟩ := hEquivalent
  let evalEmpty : Code →. Bool := fun c ↦ evalEquivalent (c, emptyCode)
  refine ⟨evalEmpty, ?_, ?_⟩
  · exact hevalPartrec.comp
      (Computable.pair Computable.id (Computable.const emptyCode))
  · intro c hc
    have hrun := hevalSpec (c, emptyCode) ⟨hc, hemptyValid⟩
    refine ⟨hrun.1, ?_⟩
    simpa only [evalEmpty, hemptyLanguage] using hrun.2

/-- **Equivalence is not uniformly decidable for recursive languages.**

For every nonempty computably encoded alphabet, no partial-recursive Boolean
evaluator can halt on all pairs of valid recursive-decider codes and decide
equality of their denoted languages. -/
public theorem recursive_computableEquivalence_undecidable [Nonempty T] :
    ¬ ComputableEquivalence Recursive (language (T := T))
      (valid := Valid (T := T)) := by
  intro h
  exact equivalence_undecidable (T := T) h.2.2

end RecursiveDeciderCode
