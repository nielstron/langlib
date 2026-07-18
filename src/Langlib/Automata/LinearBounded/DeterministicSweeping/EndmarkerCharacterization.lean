module

public import Langlib.Automata.LinearBounded.DeterministicSweeping.Simulation
public import Langlib.Automata.LinearBounded.DeterministicSweeping.Sweeping
public import Langlib.Automata.LinearBounded.SweepingEndmarkerCharacterization
public import Langlib.Automata.LinearBounded.Unambiguous

import Mathlib.Tactic

@[expose]
public section

/-!
# Sweeping deterministic LBAs on actual endmarker tapes

This file derives the canonical-endmarker form of the deterministic sweeping normal form.
Unlike the marker-free `SweepingDLBA` presentation, an endmarker machine runs on the genuine
two-cell tape `⊢⊣` for the empty word.  Thus acceptance of `ε` is performed by the machine
itself, not by an external Boolean.

The construction never determinizes a nondeterministic machine.  It starts with a DLBA, passes
through only functional presentations of that same deterministic computation, applies the
deterministic sweeping compiler, and renames finite tape alphabets.  Consequently this theorem
is a normal form for `DLBA`; it has no bearing on the open equality `LBA = DLBA`.
-/

namespace DLBA

universe u v w u'

/-! ## Deterministic canonical-endmarker semantics -/

/-- Initial deterministic configuration on the actual bracketed tape `⊢ w ⊣`.

For `w = []` this is the genuine two-cell tape `⊢⊣`; no separate empty-word flag is
present. -/
@[expose]
public noncomputable def initCfgEnd
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (LBA.EndAlpha T Work) State) (word : List T) :
    Cfg (LBA.EndAlpha T Work) State (word.length + 1) :=
  ⟨M.initial, LBA.loadEnd word⟩

/-- Language accepted by a deterministic machine on canonical actual-endmarker inputs. -/
@[expose]
public noncomputable def LanguageEnd
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (LBA.EndAlpha T Work) State) : _root_.Language T :=
  fun word => Accepts M (initCfgEnd M word)

@[simp]
public theorem liftCfg_initCfgEnd
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq (LBA.EndAlpha T Work)]
    (M : Machine (LBA.EndAlpha T Work) State) (word : List T) :
    liftCfg (initCfgEnd M word) = LBA.initCfgEnd (toLBA' M) word :=
  rfl

/-- The direct deterministic endmarker semantics agrees exactly with the standard
deterministic-to-LBA view. -/
public theorem languageEnd_toLBA'_eq
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq (LBA.EndAlpha T Work)]
    (M : Machine (LBA.EndAlpha T Work) State) :
    LBA.LanguageEnd (toLBA' M) = LanguageEnd M := by
  funext word
  apply propext
  change LBA.Accepts (toLBA' M) (liftCfg (initCfgEnd M word)) ↔
    Accepts M (initCfgEnd M word)
  exact ⟨lba_accepts_implies_dlba_accepts' M _,
    dlba_accepts_implies_lba_accepts' M _⟩

/-- Embedded nonempty-word semantics also agrees exactly with the standard
deterministic-to-LBA view. -/
public theorem languageViaEmbed_toLBA'_eq
    {Input : Type u} {Gamma : Type v} {State : Type w}
    [DecidableEq Gamma]
    (M : Machine Gamma State) (embed : Input → Gamma) :
    LBA.LanguageViaEmbed (toLBA' M) embed = LanguageViaEmbed M embed := by
  funext word
  apply propext
  constructor
  · rintro ⟨hne, haccept⟩
    refine ⟨hne, lba_accepts_implies_dlba_accepts' M _ ?_⟩
    simpa only [liftCfg] using haccept
  · rintro ⟨hne, haccept⟩
    refine ⟨hne, ?_⟩
    simpa only [liftCfg] using dlba_accepts_implies_lba_accepts' M _ haccept

namespace Machine

/-! ## Deterministic alphabet transport -/

/-- Rename every read and written symbol of a deterministic machine along an equivalence. -/
@[expose]
public def alphabetEquivTransport
    {Gamma : Type u} {Gamma' : Type u'} {State : Type w}
    (M : Machine Gamma State) (alphabetEquiv : Gamma ≃ Gamma') :
    Machine Gamma' State where
  transition state observed :=
    (M.transition state (alphabetEquiv.symm observed)).map fun move =>
      (move.1, alphabetEquiv move.2.1, move.2.2)
  accept := M.accept
  initial := M.initial

@[simp]
public theorem alphabetEquivTransport_accept
    {Gamma : Type u} {Gamma' : Type u'} {State : Type w}
    (M : Machine Gamma State) (alphabetEquiv : Gamma ≃ Gamma') (state : State) :
    (M.alphabetEquivTransport alphabetEquiv).accept state = M.accept state :=
  rfl

@[simp]
public theorem alphabetEquivTransport_initial
    {Gamma : Type u} {Gamma' : Type u'} {State : Type w}
    (M : Machine Gamma State) (alphabetEquiv : Gamma ≃ Gamma') :
    (M.alphabetEquivTransport alphabetEquiv).initial = M.initial :=
  rfl

@[simp]
public theorem alphabetEquivTransport_transition
    {Gamma : Type u} {Gamma' : Type u'} {State : Type w}
    (M : Machine Gamma State) (alphabetEquiv : Gamma ≃ Gamma')
    (state : State) (observed : Gamma') :
    (M.alphabetEquivTransport alphabetEquiv).transition state observed =
      (M.transition state (alphabetEquiv.symm observed)).map fun move =>
        (move.1, alphabetEquiv move.2.1, move.2.2) :=
  rfl

/-- Deterministic alphabet transport commutes exactly with the standard functional LBA view.
The accepting bridge added by `toLBA'` is stationary and writes back the observed symbol, so it
is transported just like an ordinary deterministic transition. -/
public theorem toLBA'_alphabetEquivTransport
    {Gamma : Type u} {Gamma' : Type u'} {State : Type w}
    [DecidableEq Gamma] [DecidableEq Gamma']
    (M : Machine Gamma State) (alphabetEquiv : Gamma ≃ Gamma') :
    toLBA' (M.alphabetEquivTransport alphabetEquiv) =
      (toLBA' M).equivTransport alphabetEquiv (Equiv.refl (Option State)) := by
  cases M with
  | mk transition accept initial =>
    unfold toLBA' alphabetEquivTransport LBA.Machine.equivTransport
    congr 1
    funext state observed
    cases state with
    | none => rfl
    | some state =>
        cases htransition : transition state (alphabetEquiv.symm observed) with
        | none =>
            by_cases haccept : accept state = true
            · simp only [htransition, haccept, if_pos, Option.map_none]
              ext move
              rcases move with ⟨target, written, direction⟩
              simp [htransition, haccept]
            · have hacceptFalse : accept state = false :=
                Bool.eq_false_of_not_eq_true haccept
              simp [htransition, hacceptFalse]
        | some move =>
            rcases move with ⟨next, written, direction⟩
            simp only [htransition, Option.map_some]
            ext move
            rcases move with ⟨target, renamed, moved⟩
            simp [htransition]
            intro _ _
            constructor
            · intro hrenamed
              rw [hrenamed, alphabetEquiv.symm_apply_apply]
            · intro hpulled
              calc
                renamed = alphabetEquiv (alphabetEquiv.symm renamed) :=
                  (alphabetEquiv.apply_symm_apply renamed).symm
                _ = alphabetEquiv written := congrArg alphabetEquiv hpulled

/-! ## Strong sweeping promise on actual endmarker inputs -/

/-- Every finite trace of the deterministic machine's standard LBA view, from every actual
canonical tape `⊢ w ⊣`, is sweeping.  In particular this quantifies over the two-cell tape
for `ε`, rejecting computations, and arbitrary finite prefixes. -/
public def SweepingEnd
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq (LBA.EndAlpha T Work)]
    (M : Machine (LBA.EndAlpha T Work) State) : Prop :=
  (toLBA' M).SweepingEnd

end Machine

namespace DeterministicSweeping

/-! ## From the named flag presentation to an actual endmarker machine -/

/-- Deterministic actual-endmarker simulator for the named marker-free DLBA presentation.

The intermediate LBA is functional because it is built from `toLBA' M`; `toDLBA` merely
repackages that unique transition relation with the deterministic halt-and-test convention. -/
@[expose]
public noncomputable def endmarkerSource
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq (Option (T ⊕ Work))]
    (M : Machine (Option (T ⊕ Work)) State) (acceptEmpty : Bool) :
    Machine (LBA.EndAlpha T Work) (LBA.SimState (Option State)) :=
  (LBA.simMachine (toLBA' M) acceptEmpty).toDLBA

/-- The intermediate endmarker simulator has a single-valued transition relation. -/
public theorem endmarkerSource_intermediate_functional
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq (Option (T ⊕ Work))]
    (M : Machine (Option (T ⊕ Work)) State) (acceptEmpty : Bool) :
    (LBA.simMachine (toLBA' M) acceptEmpty).Functional :=
  LBA.Machine.simMachine_functional (toLBA' M) (toLBA'_functional M) acceptEmpty

/-- The actual-endmarker source recognizes exactly the original flag presentation, including
the flag's value on `ε`, now decided by the machine while running on `⊢⊣`. -/
public theorem endmarkerSource_languageEnd_eq
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq (Option (T ⊕ Work))]
    (M : Machine (Option (T ⊕ Work)) State) (acceptEmpty : Bool) :
    LanguageEnd (endmarkerSource M acceptEmpty) =
      LanguageRecognized M (fun terminal => some (Sum.inl terminal)) acceptEmpty := by
  let intermediate := LBA.simMachine (toLBA' M) acceptEmpty
  calc
    LanguageEnd (endmarkerSource M acceptEmpty) =
        LBA.LanguageEnd intermediate := by
      change
        (fun word => Accepts intermediate.toDLBA
          ⟨intermediate.toDLBA.initial, LBA.loadEnd word⟩) =
          LBA.LanguageEnd intermediate
      simpa only [LBA.Machine.toDLBA_initial] using
        intermediate.languageEnd_toDLBA_eq
          (endmarkerSource_intermediate_functional M acceptEmpty)
    _ = LBA.LanguageRecognized (toLBA' M)
          (fun terminal => some (Sum.inl terminal)) acceptEmpty :=
      by simpa only [intermediate] using
        LBA.language_simMachine_eq (toLBA' M) acceptEmpty
    _ = LanguageRecognized M
          (fun terminal => some (Sum.inl terminal)) acceptEmpty := by
      funext word
      apply propext
      simp only [LBA.LanguageRecognized, LanguageRecognized]
      rw [languageViaEmbed_toLBA'_eq]

/-- Pull an actual-endmarker deterministic source back to the bracket-token alphabet. -/
@[expose]
public def bracketSource
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (LBA.EndAlpha T Work) State) :
    Machine (LBA.BracketAlpha T Work) State :=
  M.alphabetEquivTransport (LBA.bracketAlphabetEquiv T Work).symm

/-- On every well-formed bracket-token word, the pulled-back deterministic source accepts
exactly when the actual-endmarker source accepts `⊢ w ⊣`. -/
public theorem bracketSource_languageViaEmbed_bracketWord_iff
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq T] [DecidableEq Work]
    (M : Machine (LBA.EndAlpha T Work) State) (word : List T) :
    LanguageViaEmbed (bracketSource M) (LBA.bracketEmbed (Work := Work))
        (LBA.bracketWord word) ↔
      LanguageEnd M word := by
  rw [← congrFun (languageViaEmbed_toLBA'_eq (bracketSource M)
    (LBA.bracketEmbed (Work := Work))) (LBA.bracketWord word)]
  change
    LBA.LanguageViaEmbed
        (toLBA' (M.alphabetEquivTransport
          (LBA.bracketAlphabetEquiv T Work).symm))
        (LBA.bracketEmbed (Work := Work)) (LBA.bracketWord word) ↔ _
  rw [Machine.toLBA'_alphabetEquivTransport]
  exact (LBA.languageViaEmbed_equivTransport_bracketWord_iff (toLBA' M) word).trans
    (Iff.of_eq (congrFun (languageEnd_toLBA'_eq M) word))

/-! ## Returning a bracket-token deterministic machine to actual endmarkers -/

/-- Rename a deterministic bracket-token machine into a machine over the actual canonical
endmarker alphabet. -/
@[expose]
public def bracketToEnd
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (LBA.BracketAlpha T Work) State) :
    Machine (LBA.EndAlpha T Work) State :=
  M.alphabetEquivTransport (LBA.bracketAlphabetEquiv T Work)

/-- Strong marker-free sweeping transports to strong actual-endmarker sweeping, including all
prefixes on the two-cell tape for `ε`. -/
public theorem bracketToEnd_sweepingEnd
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq T] [DecidableEq Work]
    (M : Machine (LBA.BracketAlpha T Work) State)
    (hsweeping : M.SweepingViaEmbed (LBA.bracketEmbed (Work := Work))) :
    (bracketToEnd M).SweepingEnd := by
  unfold Machine.SweepingEnd bracketToEnd
  rw [Machine.toLBA'_alphabetEquivTransport]
  exact LBA.Machine.sweepingEnd_equivTransport_of_sweepingViaEmbed
    (toLBA' M) hsweeping

/-- Returning from bracket tokens to actual endmarkers preserves the language on every
well-formed canonical word exactly. -/
public theorem bracketToEnd_languageEnd_iff
    {T : Type u} {Work : Type v} {State : Type w}
    [DecidableEq T] [DecidableEq Work]
    (M : Machine (LBA.BracketAlpha T Work) State) (word : List T) :
    LanguageEnd (bracketToEnd M) word ↔
      LanguageViaEmbed M (LBA.bracketEmbed (Work := Work))
        (LBA.bracketWord word) := by
  calc
    LanguageEnd (bracketToEnd M) word ↔
        LBA.LanguageEnd (toLBA' (bracketToEnd M)) word :=
      Iff.of_eq (congrFun (languageEnd_toLBA'_eq (bracketToEnd M)).symm word)
    _ ↔ LBA.LanguageEnd
          ((toLBA' M).equivTransport
            (LBA.bracketAlphabetEquiv T Work) (Equiv.refl (Option State))) word := by
      rw [bracketToEnd, Machine.toLBA'_alphabetEquivTransport]
    _ ↔ LBA.LanguageViaEmbed (toLBA' M)
          (LBA.bracketEmbed (Work := Work)) (LBA.bracketWord word) :=
      LBA.languageEnd_equivTransport_bracket_iff (toLBA' M) word
    _ ↔ LanguageViaEmbed M (LBA.bracketEmbed (Work := Work))
          (LBA.bracketWord word) :=
      Iff.of_eq (congrFun
        (languageViaEmbed_toLBA'_eq M (LBA.bracketEmbed (Work := Work)))
        (LBA.bracketWord word))

end DeterministicSweeping

end DLBA

/-! ## Named actual-endmarker deterministic sweeping class -/

/-- A language has a sweeping deterministic presentation on actual canonical endmarker tapes.
There is no `acceptEmpty` field: the witness machine runs on `⊢⊣` for `ε`. -/
@[expose]
public def is_SweepingEndDLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Work State : Type) (_ : Fintype Work) (_ : Fintype State)
    (_ : DecidableEq Work) (_ : DecidableEq State)
    (M : DLBA.Machine (LBA.EndAlpha T Work) State),
    M.SweepingEnd ∧ DLBA.LanguageEnd M = L

/-- Languages recognized by sweeping deterministic machines on actual endmarker tapes. -/
@[expose]
public def SweepingEndDLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_SweepingEndDLBA

/-- Forgetting the sweeping normal form and converting the functional endmarker presentation
back to the named marker-free DLBA convention preserves the language exactly. -/
public theorem is_SweepingEndDLBA_imp_is_DLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_SweepingEndDLBA L) : is_DLBA L := by
  obtain ⟨Work, State, hWork, hState, hdecWork, hdecState,
    M, _hsweeping, hM⟩ := hL
  letI := hWork
  letI := hState
  letI := hdecWork
  letI := hdecState
  have hdeterministic : is_DLBA (LBA.LanguageEnd (DLBA.toLBA' M)) :=
    is_DLBA_languageEnd_of_functional
      (DLBA.toLBA' M) (DLBA.toLBA'_functional M)
  rw [DLBA.languageEnd_toLBA'_eq M, hM] at hdeterministic
  exact hdeterministic

/-- Actual-endmarker sweeping DLBAs recognize no languages beyond `DLBA`. -/
public theorem SweepingEndDLBA_subset_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingEndDLBA : Set (Language T)) ⊆ DLBA :=
  fun _ hL => is_SweepingEndDLBA_imp_is_DLBA hL

/-- Every named DLBA language has a deterministic sweeping presentation on actual canonical
endmarker tapes.  In particular, the presentation decides `ε` by running on `⊢⊣`; the
source presentation's Boolean is consumed by `endmarkerSource` and is not retained in the
target model. -/
public theorem is_DLBA_imp_is_SweepingEndDLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_DLBA L) : is_SweepingEndDLBA L := by
  obtain ⟨Work, State, hWork, hState, hdecWork, hdecState,
    acceptEmpty, M, hM⟩ := hL
  letI := hWork
  letI := hState
  letI := hdecWork
  letI := hdecState
  letI : DecidableEq (LBA.BracketAlpha T Work) := inferInstance
  letI : DecidableEq (LBA.SimState (Option State)) := inferInstance
  letI : DecidableEq
      (DLBA.DeterministicSweeping.Cell (LBA.BracketAlpha T Work)
        (LBA.SimState (Option State))) := inferInstance
  letI : DecidableEq
      (DLBA.DeterministicSweeping.Alphabet (LBA.BracketToken T)
        (LBA.BracketAlpha T Work) (LBA.SimState (Option State))) := inferInstance
  let EndSource :=
    DLBA.DeterministicSweeping.endmarkerSource M acceptEmpty
  let BracketSource :=
    DLBA.DeterministicSweeping.bracketSource EndSource
  let SweepMachine :=
    DLBA.DeterministicSweeping.machine BracketSource
      (LBA.bracketEmbed (Work := Work))
  let EndMachine :=
    DLBA.DeterministicSweeping.bracketToEnd SweepMachine
  refine ⟨
    DLBA.DeterministicSweeping.Cell (LBA.BracketAlpha T Work)
      (LBA.SimState (Option State)),
    DLBA.DeterministicSweeping.Phase (LBA.SimState (Option State)),
    inferInstance, inferInstance, inferInstance, inferInstance,
    EndMachine, ?_, ?_⟩
  · apply DLBA.DeterministicSweeping.bracketToEnd_sweepingEnd
    change SweepMachine.SweepingViaEmbed
      (DLBA.DeterministicSweeping.inputEmbed
        (Γ := LBA.BracketAlpha T Work)
        (Q := LBA.SimState (Option State)))
    exact DLBA.DeterministicSweeping.machine_sweepingViaEmbed BracketSource
      (LBA.bracketEmbed (Work := Work))
  · funext word
    apply propext
    calc
      DLBA.LanguageEnd EndMachine word ↔
          DLBA.LanguageViaEmbed SweepMachine
            (LBA.bracketEmbed
              (Work := DLBA.DeterministicSweeping.Cell
                (LBA.BracketAlpha T Work) (LBA.SimState (Option State))))
            (LBA.bracketWord word) :=
        DLBA.DeterministicSweeping.bracketToEnd_languageEnd_iff SweepMachine word
      _ ↔ DLBA.LanguageViaEmbed BracketSource
            (LBA.bracketEmbed (Work := Work)) (LBA.bracketWord word) := by
        change
          DLBA.LanguageViaEmbed SweepMachine
              (DLBA.DeterministicSweeping.inputEmbed
                (Γ := LBA.BracketAlpha T Work)
                (Q := LBA.SimState (Option State)))
              (LBA.bracketWord word) ↔ _
        exact Iff.of_eq (congrFun
          (DLBA.DeterministicSweeping.machine_languageViaEmbed BracketSource
            (LBA.bracketEmbed (Work := Work)))
          (LBA.bracketWord word))
      _ ↔ DLBA.LanguageEnd EndSource word :=
        DLBA.DeterministicSweeping.bracketSource_languageViaEmbed_bracketWord_iff
          EndSource word
      _ ↔ DLBA.LanguageRecognized M
            (fun terminal => some (Sum.inl terminal)) acceptEmpty word :=
        Iff.of_eq (congrFun
          (DLBA.DeterministicSweeping.endmarkerSource_languageEnd_eq M acceptEmpty) word)
      _ ↔ L word := Iff.of_eq (congrFun hM word)

/-- Every deterministic-LBA language is recognized by an actual-endmarker sweeping DLBA. -/
public theorem DLBA_subset_SweepingEndDLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (DLBA : Set (Language T)) ⊆ SweepingEndDLBA :=
  fun _ hL => is_DLBA_imp_is_SweepingEndDLBA hL

/-- Sweeping deterministic machines on actual canonical endmarker tapes recognize exactly the
named deterministic-LBA class. -/
public theorem SweepingEndDLBA_eq_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingEndDLBA : Set (Language T)) = DLBA :=
  Set.Subset.antisymm SweepingEndDLBA_subset_DLBA DLBA_subset_SweepingEndDLBA

/-- Pointwise exact actual-endmarker deterministic sweeping characterization. -/
public theorem is_SweepingEndDLBA_iff_is_DLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_SweepingEndDLBA L ↔ is_DLBA L :=
  ⟨is_SweepingEndDLBA_imp_is_DLBA, is_DLBA_imp_is_SweepingEndDLBA⟩

/-- Base-class-first orientation of the actual-endmarker characterization. -/
public theorem is_DLBA_iff_is_SweepingEndDLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_DLBA L ↔ is_SweepingEndDLBA L :=
  (is_SweepingEndDLBA_iff_is_DLBA L).symm

/-- Membership form of the exact actual-endmarker sweeping class equality. -/
public theorem mem_SweepingEndDLBA_iff_mem_DLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    L ∈ (SweepingEndDLBA : Set (Language T)) ↔ L ∈ DLBA :=
  is_SweepingEndDLBA_iff_is_DLBA L

end
