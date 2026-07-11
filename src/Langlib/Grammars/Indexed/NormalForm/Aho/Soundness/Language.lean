module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.PaddedReach
public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Acceptance
public import Langlib.Grammars.Indexed.NormalForm.AhoCertificate

@[expose]
public section

/-!
# Language equivalence for Aho's bounded simulation

This module isolates the final grammar/machine language argument.  Soundness is unconditional;
the completeness hypothesis is precisely the uniform twenty-one-slots-per-terminal theorem supplied
by the parse-directed scheduler.
-/

open Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Once every concrete normal-form parse has a twenty-one-linear bounded run, semantic padded-row
reachability recognizes exactly the language of the grammar. -/
public theorem language_eq_paddedReachLanguage_of_bounded_complete
    {g : IndexedGrammar T} [Fintype g.nt] [DecidableEq g.nt]
    (hNF : g.IsNormalForm)
    (hcomplete : ∀ {input : List T}, NFParse g g.initial [] input →
      BoundedReaches g input (21 * input.length)
        (initialConfig g) (finalConfig g input.length)) :
    g.Language = paddedReachLanguage g := by
  ext input
  constructor
  · intro hgen
    have hne : input ≠ [] := by
      intro hnil
      subst input
      exact g.not_generates_nil_of_noEpsilon
        (g.noEpsilon_of_isNormalForm hNF) hgen
    rcases (NFParse.nonempty_initial_iff_generates hNF).2 hgen with ⟨parse⟩
    have hrun := hcomplete parse
    apply mem_paddedReachLanguage_of_boundedReaches hne
    simpa [workWidth, Nat.mul_comm] using hrun
  · intro hmem
    have hbounded := boundedReaches_of_mem_paddedReachLanguage hmem
    have hreach : ReflTransGen (CompositeStep g input)
        (initialConfig g) (finalConfig g input.length) :=
      hbounded.2.mono fun _ _ hstep => hstep.1
    exact ControlDenotation.ahoMachine_sound hreach

end Aho
end IndexedGrammar
