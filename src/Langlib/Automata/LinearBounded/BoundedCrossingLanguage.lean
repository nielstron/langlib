module

public import Langlib.Automata.FiniteState.FixedContext
public import Langlib.Automata.FiniteState.Inclusion.DeterministicLinearBounded
public import Langlib.Automata.LinearBounded.BoundedCrossing
public import Langlib.Automata.LinearBounded.BoundedCrossingCertificate
public import Langlib.Automata.LinearBounded.BoundedCrossingCertificateExactSoundness
public import Langlib.Automata.LinearBounded.BoundedCrossingCertificateSoundness
public import Langlib.Automata.LinearBounded.BoundedCrossingTraceCertificate
public import Langlib.Automata.LinearBounded.EndmarkerWord

@[expose]
public section

/-!
# Terminal-word automaton for bounded crossing profiles

The local profile automaton reads every physical tape cell, including the two endmarkers.  This
module pulls it back to the original terminal alphabet by supplying those two fixed cells and
embedding each terminal as its canonical input-tape symbol.
-/

namespace LBA.BoundedCrossing

universe u v w

variable {Terminal : Type u} {Work : Type v} {State : Type w}

/-- The bounded-profile NFA presented over ordinary terminal words rather than full endmarker
tape words. -/
def terminalProfileNFA
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    NFA Terminal (ScanState (LBA.EndAlpha Terminal Work) State bound) :=
  NFA.fixedContextMap (profileNFA M bound)
    [LBA.leftMark] [LBA.rightMark] LBA.inputCell

/-- The words having at least one accepting canonical run whose every physical boundary is
crossed at most `bound` times. -/
def LanguageWithBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    Language Terminal :=
  fun word ↦ AcceptsWithBound M (LBA.initCfgEnd M word) bound

/-- The fixed-bound language slices are monotone in their crossing cap. -/
theorem languageWithBound_mono
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    {smaller larger : Nat} (hbound : smaller ≤ larger) :
    ∀ word, word ∈ LanguageWithBound M smaller →
      word ∈ LanguageWithBound M larger := by
  intro word haccept
  exact haccept.mono hbound

/-- Every accepted word has some finite crossing cap, so an LBA language is the increasing
countable union of its fixed-bound slices.  This statement supplies no single uniform cap. -/
theorem languageEnd_eq_iUnion_languageWithBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) :
    LBA.LanguageEnd M = ⋃ bound : Nat, LanguageWithBound M bound := by
  ext word
  change LBA.Accepts M (LBA.initCfgEnd M word) ↔
    word ∈ ⋃ bound : Nat, LanguageWithBound M bound
  rw [accepts_iff_exists_acceptsWithBound]
  constructor
  · rintro ⟨bound, haccept⟩
    exact Set.mem_iUnion.mpr ⟨bound, haccept⟩
  · intro haccept
    rcases Set.mem_iUnion.mp haccept with ⟨bound, hbound⟩
    exact ⟨bound, hbound⟩

/-- A fixed slice equals the whole source language exactly when its cap works uniformly for one
selected accepting run of every accepted word. -/
theorem languageWithBound_eq_languageEnd_iff_hasUniformAcceptingBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    LanguageWithBound M bound = LBA.LanguageEnd M ↔
      HasUniformAcceptingBound M bound := by
  constructor
  · intro heq word haccept
    have hslice : word ∈ LanguageWithBound M bound := by
      rw [heq]
      exact haccept
    exact hslice
  · intro hbound
    ext word
    constructor
    · exact accepts_of_acceptsWithBound
    · exact hbound word

/-- `terminalProfileNFA` feeds the profile checker exactly the canonical bracketed tape word. -/
theorem mem_terminalProfileNFA_iff_mem_endWord
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (word : List Terminal) :
    word ∈ (terminalProfileNFA M bound).accepts ↔
      LBA.endWord (Work := Work) word ∈ (profileNFA M bound).accepts := by
  rw [show (terminalProfileNFA M bound).accepts =
      {word | [LBA.leftMark] ++ word.map LBA.inputCell ++ [LBA.rightMark] ∈
        (profileNFA M bound).accepts} from
    NFA.fixedContextMap_correct (profileNFA M bound)
      [LBA.leftMark] [LBA.rightMark] LBA.inputCell]
  rfl

/-- A bounded-crossing accepting witness on the canonical endmarker tape is accepted by the
terminal-word profile automaton. -/
theorem mem_terminalProfileNFA_of_acceptsWithBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (word : List Terminal)
    (haccept : AcceptsWithBound M (LBA.initCfgEnd M word) bound) :
    word ∈ (terminalProfileNFA M bound).accepts := by
  rw [mem_terminalProfileNFA_iff_mem_endWord, ← LBA.ofFn_loadEnd_contents]
  apply mem_profileNFA_of_acceptsWithBound haccept
  · rfl
  · rfl

/-- Spatial profile acceptance synchronizes to a genuine run from the function-valued initial
configuration. -/
theorem accepts_initialCfgFn_of_mem_profileNFA
    (M : LBA.Machine Gamma State) (bound n : Nat)
    (input : Fin (n + 1) → Gamma)
    (hmem : List.ofFn input ∈ (profileNFA M bound).accepts) :
    LBA.Accepts M (Soundness.initialCfgFn M input) := by
  rcases (mem_profileNFA_iff_nonempty_cellCertificate M bound n input).1 hmem with
    ⟨certificate⟩
  exact Soundness.accepts_initialCfgFn_of_cellCertificate M bound n input certificate

@[simp] theorem initialCfgFn_loadEnd_contents
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (word : List Terminal) :
    Soundness.initialCfgFn M (LBA.loadEnd (Γ := Work) word).contents =
      LBA.initCfgEnd M word := by
  rfl

/-- Every word accepted by the terminal profile automaton has a genuine source-machine
accepting run. -/
theorem accepts_of_mem_terminalProfileNFA
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (word : List Terminal)
    (hmem : word ∈ (terminalProfileNFA M bound).accepts) :
    LBA.Accepts M (LBA.initCfgEnd M word) := by
  have hcells :
      List.ofFn (LBA.loadEnd (Γ := Work) word).contents ∈
        (profileNFA M bound).accepts := by
    rw [LBA.ofFn_loadEnd_contents]
    exact (mem_terminalProfileNFA_iff_mem_endWord M bound word).1 hmem
  simpa using accepts_initialCfgFn_of_mem_profileNFA M bound _ _ hcells

/-- Exact terminal-word correctness: the finite profile automaton accepts precisely the words
having an accepting run with the advertised crossing cap. -/
theorem mem_terminalProfileNFA_iff_acceptsWithBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (word : List Terminal) :
    word ∈ (terminalProfileNFA M bound).accepts ↔
      AcceptsWithBound M (LBA.initCfgEnd M word) bound := by
  rw [mem_terminalProfileNFA_iff_mem_endWord, ← LBA.ofFn_loadEnd_contents,
    Soundness.mem_profileNFA_iff_acceptsWithBound_initialCfgFn,
    initialCfgFn_loadEnd_contents]

/-- Every fixed-cap slice of an LBA language is recognized exactly by its bounded-profile
automaton. -/
theorem terminalProfileNFA_accepts_eq_languageWithBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    (terminalProfileNFA M bound).accepts = LanguageWithBound M bound := by
  ext word
  exact mem_terminalProfileNFA_iff_acceptsWithBound M bound word

/-- Under one uniform selected-accepting crossing cap, the terminal profile automaton recognizes
the whole source language exactly. -/
theorem terminalProfileNFA_accepts_eq_languageEnd_of_hasUniformAcceptingBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (hbound : HasUniformAcceptingBound M bound) :
    (terminalProfileNFA M bound).accepts = LBA.LanguageEnd M := by
  ext word
  constructor
  · exact accepts_of_mem_terminalProfileNFA M bound word
  · intro haccept
    exact mem_terminalProfileNFA_of_acceptsWithBound M bound word (hbound word haccept)

/-- Once semantic correctness of the profile checker has been established for a language, its
finite-state presentation immediately packages that language as NFA-recognizable. -/
theorem is_NFA_of_terminalProfileNFA_accepts_eq
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    {language : Language Terminal}
    (hcorrect : (terminalProfileNFA M bound).accepts = language) :
    is_NFA language := by
  classical
  exact ⟨ScanState (LBA.EndAlpha Terminal Work) State bound, inferInstance,
    terminalProfileNFA M bound, hcorrect⟩

/-- The analogous DFA packaging follows by finite-state subset construction. -/
theorem is_DFA_of_terminalProfileNFA_accepts_eq
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    {language : Language Terminal}
    (hcorrect : (terminalProfileNFA M bound).accepts = language) :
    is_DFA language :=
  is_NFA_iff_is_DFA.mp
    (is_NFA_of_terminalProfileNFA_accepts_eq M bound hcorrect)

/-- Every fixed crossing-cap slice of a finite LBA is NFA-recognizable. -/
theorem is_NFA_languageWithBound
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    is_NFA (LanguageWithBound M bound) :=
  is_NFA_of_terminalProfileNFA_accepts_eq M bound
    (terminalProfileNFA_accepts_eq_languageWithBound M bound)

/-- Every fixed crossing-cap slice of a finite LBA is DFA-recognizable. -/
theorem is_DFA_languageWithBound
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    is_DFA (LanguageWithBound M bound) :=
  is_NFA_iff_is_DFA.mp (is_NFA_languageWithBound M bound)

/-- Every fixed crossing-cap slice of a finite LBA has a deterministic-LBA presentation. -/
theorem is_DLBA_languageWithBound
    {Terminal Work State : Type}
    [Fintype Terminal] [DecidableEq Terminal]
    [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    is_DLBA (LanguageWithBound M bound) :=
  is_DLBA_of_is_NFA (is_NFA_languageWithBound M bound)

/-- A finite LBA presentation with one uniform selected-accepting crossing cap recognizes a
finite-state language. -/
theorem is_NFA_languageEnd_of_hasUniformAcceptingBound
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (hbound : HasUniformAcceptingBound M bound) :
    is_NFA (LBA.LanguageEnd M) :=
  is_NFA_of_terminalProfileNFA_accepts_eq M bound
    (terminalProfileNFA_accepts_eq_languageEnd_of_hasUniformAcceptingBound
      M bound hbound)

/-- Deterministic finite-state form of the bounded-crossing regularity theorem. -/
theorem is_DFA_languageEnd_of_hasUniformAcceptingBound
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (hbound : HasUniformAcceptingBound M bound) :
    is_DFA (LBA.LanguageEnd M) :=
  is_NFA_iff_is_DFA.mp
    (is_NFA_languageEnd_of_hasUniformAcceptingBound M bound hbound)

/-- In particular, a uniformly bounded-crossing LBA language has a concrete deterministic-LBA
presentation. -/
theorem is_DLBA_languageEnd_of_hasUniformAcceptingBound
    {Terminal Work State : Type}
    [Fintype Terminal] [DecidableEq Terminal]
    [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat)
    (hbound : HasUniformAcceptingBound M bound) :
    is_DLBA (LBA.LanguageEnd M) :=
  is_DLBA_of_is_NFA
    (is_NFA_languageEnd_of_hasUniformAcceptingBound M bound hbound)

end LBA.BoundedCrossing

end
