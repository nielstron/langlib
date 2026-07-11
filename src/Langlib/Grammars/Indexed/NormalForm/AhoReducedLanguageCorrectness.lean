module

public import Langlib.Grammars.Indexed.NormalForm.AhoLanguageCorrectness
public import Langlib.Grammars.Indexed.NormalForm.AhoReducedParse
public import Langlib.Grammars.Indexed.NormalForm.AhoRowSystemSoundness

@[expose]
public section

/-!
# Language correctness from reduced parses

Language completeness is existential in the parse certificate.  Consequently the bounded Aho
run only has to be constructed for constructor-count-minimal root parses, not for every parse
tree containing arbitrary unary detours.
-/

open Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- A bounded run for every reduced root parse suffices for language correctness. -/
public theorem language_eq_paddedReachLanguage_of_nodeMinimal_complete
    {g : IndexedGrammar T} [Fintype g.nt] [DecidableEq g.nt]
    (hNF : g.IsNormalForm)
    (hcomplete : ∀ {input : List T} (parse : NFParse g g.initial [] input),
      parse.IsNodeMinimal →
      BoundedReaches g input (21 * input.length)
        (initialConfig g) (finalConfig g input.length)) :
    g.Language = paddedReachLanguage g := by
  apply language_eq_paddedReachLanguage_of_bounded_complete hNF
  intro input parse
  obtain ⟨reduced, hreduced⟩ := parse.exists_nodeMinimal
  exact hcomplete reduced hreduced

/-- Still weaker, it is enough to produce one reduced parse and bounded run for each generated
word.  This formulation is useful when the scheduler constructs its own canonical certificate. -/
public theorem language_eq_paddedReachLanguage_of_exists_nodeMinimal_complete
    {g : IndexedGrammar T} [Fintype g.nt] [DecidableEq g.nt]
    (hNF : g.IsNormalForm)
    (hcomplete : ∀ {input : List T}, input ∈ g.Language →
      ∃ parse : NFParse g g.initial [] input,
        parse.IsNodeMinimal ∧
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
    obtain ⟨_parse, _hminimal, hrun⟩ := hcomplete hgen
    apply mem_paddedReachLanguage_of_boundedReaches hne
    simpa [workWidth, Nat.mul_comm] using hrun
  · intro hmem
    have hbounded := boundedReaches_of_mem_paddedReachLanguage hmem
    have hreach : ReflTransGen (CompositeStep g input)
        (initialConfig g) (finalConfig g input.length) :=
      hbounded.2.mono fun _ _ hstep => hstep.1
    exact ControlDenotation.ahoMachine_sound hreach

/-- The finite normal-form Aho-to-LBA reduction only needs bounded completeness for reduced root
parses. -/
public theorem is_LBA_pos_language_of_nodeMinimal_bounded_complete
    {g : IndexedGrammar T} [Fintype T] [DecidableEq T]
    [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm)
    (hcomplete : ∀ {input : List T} (parse : NFParse g g.initial [] input),
      parse.IsNodeMinimal →
      BoundedReaches g input (21 * input.length)
        (initialConfig g) (finalConfig g input.length)) :
    is_LBA_pos g.Language := by
  rw [language_eq_paddedReachLanguage_of_nodeMinimal_complete hNF hcomplete]
  exact is_LBA_pos_paddedReachLanguage g

/-- Existential reduced-parse completeness is likewise enough for the LBA inclusion. -/
public theorem is_LBA_pos_language_of_exists_nodeMinimal_complete
    {g : IndexedGrammar T} [Fintype T] [DecidableEq T]
    [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm)
    (hcomplete : ∀ {input : List T}, input ∈ g.Language →
      ∃ parse : NFParse g g.initial [] input,
        parse.IsNodeMinimal ∧
        BoundedReaches g input (21 * input.length)
          (initialConfig g) (finalConfig g input.length)) :
    is_LBA_pos g.Language := by
  rw [language_eq_paddedReachLanguage_of_exists_nodeMinimal_complete hNF hcomplete]
  exact is_LBA_pos_paddedReachLanguage g

end Aho
end IndexedGrammar
