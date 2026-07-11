module

public import Langlib.Grammars.Indexed.NormalForm.AhoLanguageCorrectness
public import Langlib.Grammars.Indexed.NormalForm.AhoRowSystemSoundness
public import Langlib.Grammars.Indexed.NormalForm.AhoRunnerTop

@[expose]
public section

/-!
# The finite normal-form indexed-to-LBA core

This module joins the grammar semantics of Aho's machine to its executable certified-row
implementation.  The only hypothesis below is the parse scheduler's uniform linear bound.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- A uniform twenty-one-slots-per-terminal scheduler turns the language of a finite normal-form
indexed grammar into an input-sized LBA language. -/
public theorem is_LBA_pos_language_of_bounded_complete
    {g : IndexedGrammar T} [Fintype T] [DecidableEq T]
    [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm)
    (hcomplete : ∀ {input : List T}, NFParse g g.initial [] input →
      BoundedReaches g input (21 * input.length)
        (initialConfig g) (finalConfig g input.length)) :
    is_LBA_pos g.Language := by
  rw [language_eq_paddedReachLanguage_of_bounded_complete hNF hcomplete]
  exact is_LBA_pos_paddedReachLanguage g

/-- It suffices to construct the ordinary and copy-on-write overlay runner modes for every
root parse.  The canonical root owner pool then supplies the required bounded execution. -/
public theorem is_LBA_pos_language_of_completeScheduleRuns
    {g : IndexedGrammar T} [Fintype T] [DecidableEq T]
    [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm)
    (hruns : ∀ {input : List T} (parse : NFParse g g.initial [] input),
      CompleteScheduleRuns parse) :
    is_LBA_pos g.Language := by
  apply is_LBA_pos_language_of_bounded_complete hNF
  intro input parse
  exact complete_bounded_of_completeScheduleRuns parse (hruns parse)

/-- Every finite normal-form indexed grammar is recognized by a positive-input LBA. -/
public theorem is_LBA_pos_language
    {g : IndexedGrammar T} [Fintype T] [DecidableEq T]
    [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) : is_LBA_pos g.Language := by
  apply is_LBA_pos_language_of_bounded_complete hNF
  intro input parse
  exact complete_bounded parse

end Aho
end IndexedGrammar
