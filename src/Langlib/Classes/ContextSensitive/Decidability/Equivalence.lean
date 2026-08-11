module

public import Langlib.Classes.ContextSensitive.Decidability.Emptiness

@[expose]
public section

/-!
# Undecidability of equivalence for context-sensitive grammar codes

The fixed code with no grammar rules denotes the empty language.  Consequently,
a uniform equivalence procedure for concrete context-sensitive codes would decide
emptiness by comparing its input with that fixed code.
-/

namespace ContextSensitiveEquivalence

variable {T : Type} [DecidableEq T] [Primcodable T]

private def emptyRawCode : Code T := ([], 0)

private theorem emptyRawCode_context_sensitive :
    grammar_context_sensitive (ofCode (emptyRawCode (T := T))) := by
  constructor
  · intro r hr
    simp [emptyRawCode, ofCode] at hr
  · rintro ⟨r, hr, _⟩
    simp [emptyRawCode, ofCode] at hr

/-- A fixed concrete context-sensitive code for the empty language. -/
private def emptyCSCode : ContextSensitive.CSCode T :=
  ⟨emptyRawCode, emptyRawCode_context_sensitive⟩

private theorem emptyRawCode_language :
    grammar_language (ofCode (emptyRawCode (T := T))) =
      (∅ : Set (List T)) := by
  ext w
  constructor
  · intro hw
    change grammar_derives (ofCode (emptyRawCode (T := T)))
      [symbol.nonterminal 0] (w.map symbol.terminal) at hw
    rcases grammar_tran_or_id_of_deri hw with heq | ⟨sf, hfirst, _⟩
    · cases w <;> simp at heq
    · obtain ⟨r, hr, _, _, _, _⟩ := hfirst
      simp [emptyRawCode, ofCode] at hr
  · exact fun hw => hw.elim

private theorem emptyCSCode_language :
    ContextSensitive.contextSensitiveLanguageOf' (emptyCSCode (T := T)) =
      (∅ : Set (List T)) := by
  change contextSensitiveLanguageOf (emptyRawCode (T := T)) = _
  rw [ContextSensitive.csLang_eq emptyRawCode_context_sensitive]
  exact emptyRawCode_language

/-- Equivalence is not uniformly decidable for concrete context-sensitive
grammar codes over any nonempty computably encoded alphabet. -/
public theorem contextSensitive_computableEquivalence_undecidable
    [Nonempty T] :
    ¬ ComputableEquivalence (CS : Set (Language T))
      (ContextSensitive.contextSensitiveLanguageOf' :
        ContextSensitive.CSCode T → Language T) := by
  intro hEquivalent
  apply ContextSensitiveEmptiness.contextSensitive_computableEmptiness_undecidable
    (T := T)
  refine ⟨hEquivalent.1, hEquivalent.2.1, ?_⟩
  obtain ⟨evalEquivalent, hevalPartrec, hevalSpec⟩ := hEquivalent.2.2
  let evalEmpty : ContextSensitive.CSCode T →. Bool :=
    fun sc => evalEquivalent (sc, emptyCSCode)
  refine ⟨evalEmpty, ?_, ?_⟩
  · exact hevalPartrec.comp
      (Computable.pair Computable.id (Computable.const emptyCSCode))
  · intro sc _
    have hrun := hevalSpec (sc, emptyCSCode) ⟨trivial, trivial⟩
    refine ⟨hrun.1, ?_⟩
    simpa only [evalEmpty, emptyCSCode_language] using hrun.2

end ContextSensitiveEquivalence

end
