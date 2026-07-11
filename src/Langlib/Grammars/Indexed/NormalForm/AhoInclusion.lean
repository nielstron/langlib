module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Language
public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowSystem
public import Langlib.Grammars.Indexed.NormalForm.AhoRunnerTop

@[expose]
public section

/-!
# The finite normal-form indexed-to-LBA core

This module joins the grammar semantics of Aho's machine to its executable certified-row
implementation. The only hypothesis below is the parse scheduler's uniform linear bound.
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

/-- Every finite normal-form indexed grammar is recognized by a positive-input LBA. The proof
combines the uniform `complete_bounded` schedule with certified-row exactness and compilation. -/
public theorem is_LBA_pos_language
    {g : IndexedGrammar T} [Fintype T] [DecidableEq T]
    [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) : is_LBA_pos g.Language := by
  apply is_LBA_pos_language_of_bounded_complete hNF
  intro input parse
  exact complete_bounded parse

end Aho
end IndexedGrammar
