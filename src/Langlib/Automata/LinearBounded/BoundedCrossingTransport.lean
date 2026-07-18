module

public import Langlib.Automata.LinearBounded.AlphabetTransport
public import Langlib.Automata.LinearBounded.BoundedCrossingLanguage
import Mathlib.Tactic

@[expose]
public section

/-!
# Transporting bounded-crossing LBA presentations along finite-type equivalences

Renaming both the tape alphabet and the control states changes no physical computation.  This
file packages the simultaneous renaming on configurations and machines, transports concrete
`StepTrace`s in both directions, and proves that trace length and every literal tape-boundary
crossing count are unchanged.

The final specialization renames an endmarker machine's work alphabet and states.  The induced
endmarker-alphabet equivalence fixes blanks, terminals, and both markers, so it carries every
canonical tape `⊢ w ⊣` to itself.  Consequently `LanguageWithBound` is invariant.  In
particular, arbitrary finite work and state types may be replaced by their canonical `Fin`
enumerations in an adequacy proof without putting those noncanonical equivalences into an
executable code or membership evaluator.

No finiteness, inhabitedness, or cardinality assumption is used by the generic transport.
-/

namespace LBA

universe u v u' v'

variable {Gamma : Type u} {State : Type v}
variable {Gamma' : Type u'} {State' : Type v'}

/-- Simultaneously rename the control state and every tape cell of a configuration. -/
public def machineEquivCfg (alphabetEquiv : Gamma ≃ Gamma')
    (stateEquiv : State ≃ State') {n : Nat} :
    DLBA.Cfg Gamma State n ≃ DLBA.Cfg Gamma' State' n where
  toFun cfg := ⟨stateEquiv cfg.state, alphabetEquivTape alphabetEquiv cfg.tape⟩
  invFun cfg :=
    ⟨stateEquiv.symm cfg.state, alphabetEquivTape alphabetEquiv.symm cfg.tape⟩
  left_inv cfg := by
    cases cfg with
    | mk state tape =>
      simp only
      congr 1
      · exact stateEquiv.symm_apply_apply state
      · exact (alphabetEquivTape alphabetEquiv).left_inv tape
  right_inv cfg := by
    cases cfg with
    | mk state tape =>
      simp only
      congr 1
      · exact stateEquiv.apply_symm_apply state
      · exact (alphabetEquivTape alphabetEquiv).right_inv tape

@[simp] public theorem machineEquivCfg_state
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (cfg : DLBA.Cfg Gamma State n) :
    (machineEquivCfg alphabetEquiv stateEquiv cfg).state =
      stateEquiv cfg.state := rfl

@[simp] public theorem machineEquivCfg_tape
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (cfg : DLBA.Cfg Gamma State n) :
    (machineEquivCfg alphabetEquiv stateEquiv cfg).tape =
      alphabetEquivTape alphabetEquiv cfg.tape := rfl

@[simp] public theorem machineEquivCfg_head
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (cfg : DLBA.Cfg Gamma State n) :
    (machineEquivCfg alphabetEquiv stateEquiv cfg).tape.head =
      cfg.tape.head := rfl

@[simp] public theorem machineEquivCfg_updateMove
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (state : State) (tape : DLBA.BoundedTape Gamma n)
    (written : Gamma) (direction : DLBA.Dir) :
    machineEquivCfg alphabetEquiv stateEquiv
        (⟨state, (tape.write written).moveHead direction⟩ :
          DLBA.Cfg Gamma State n) =
      ⟨stateEquiv state,
        ((alphabetEquivTape alphabetEquiv tape).write
          (alphabetEquiv written)).moveHead direction⟩ := by
  change
    (⟨stateEquiv state,
      alphabetEquivTape alphabetEquiv
        ((tape.write written).moveHead direction)⟩ :
        DLBA.Cfg Gamma' State' n) = _
  rw [alphabetEquivTape_moveHead, alphabetEquivTape_write]

/-- Rename the alphabet and state types of an LBA along equivalences. -/
public def Machine.equivTransport (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State') :
    Machine Gamma' State' where
  transition state observed :=
    {move |
      (stateEquiv.symm move.1, alphabetEquiv.symm move.2.1, move.2.2) ∈
        M.transition (stateEquiv.symm state) (alphabetEquiv.symm observed)}
  accept state := M.accept (stateEquiv.symm state)
  initial := stateEquiv M.initial

@[simp] public theorem Machine.mem_equivTransport_transition_iff
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    (state target : State') (observed written : Gamma')
    (direction : DLBA.Dir) :
    (target, written, direction) ∈
        (M.equivTransport alphabetEquiv stateEquiv).transition state observed ↔
      (stateEquiv.symm target, alphabetEquiv.symm written, direction) ∈
        M.transition (stateEquiv.symm state) (alphabetEquiv.symm observed) :=
  Iff.rfl

@[simp] public theorem Machine.equivTransport_accept
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    (state : State') :
    (M.equivTransport alphabetEquiv stateEquiv).accept state =
      M.accept (stateEquiv.symm state) := rfl

@[simp] public theorem Machine.equivTransport_initial
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State') :
    (M.equivTransport alphabetEquiv stateEquiv).initial =
      stateEquiv M.initial := rfl

/-- One-step computations are invariant under simultaneous alphabet/state renaming. -/
public theorem Machine.step_equivTransport_iff
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (source target : DLBA.Cfg Gamma State n) :
    Step (M.equivTransport alphabetEquiv stateEquiv)
        (machineEquivCfg alphabetEquiv stateEquiv source)
        (machineEquivCfg alphabetEquiv stateEquiv target) ↔
      Step M source target := by
  constructor
  · rintro ⟨nextState, written, direction, henabled, htarget⟩
    refine ⟨stateEquiv.symm nextState, alphabetEquiv.symm written,
      direction, ?_, ?_⟩
    · simpa using henabled
    · apply (machineEquivCfg alphabetEquiv stateEquiv).injective
      rw [htarget]
      simp
  · rintro ⟨nextState, written, direction, henabled, rfl⟩
    refine ⟨stateEquiv nextState, alphabetEquiv written, direction, ?_, ?_⟩
    · simpa using henabled
    · exact machineEquivCfg_updateMove
        alphabetEquiv stateEquiv nextState source.tape written direction

/-- Arbitrary-target form of `step_equivTransport_iff`. -/
public theorem Machine.step_equivTransport_iff_symm
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (source target : DLBA.Cfg Gamma' State' n) :
    Step (M.equivTransport alphabetEquiv stateEquiv) source target ↔
      Step M ((machineEquivCfg alphabetEquiv stateEquiv).symm source)
        ((machineEquivCfg alphabetEquiv stateEquiv).symm target) := by
  simpa using M.step_equivTransport_iff alphabetEquiv stateEquiv
    ((machineEquivCfg alphabetEquiv stateEquiv).symm source)
    ((machineEquivCfg alphabetEquiv stateEquiv).symm target)

namespace StepTrace

/-- Transport every step of a concrete trace along simultaneous alphabet/state renaming. -/
public def equivTransport (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State') :
    {n : Nat} → {source target : DLBA.Cfg Gamma State n} →
      StepTrace M source target →
        StepTrace (M.equivTransport alphabetEquiv stateEquiv)
          (machineEquivCfg alphabetEquiv stateEquiv source)
          (machineEquivCfg alphabetEquiv stateEquiv target)
  | _, _, _, .refl cfg => .refl (machineEquivCfg alphabetEquiv stateEquiv cfg)
  | _, _, _, .head step rest =>
      .head ((M.step_equivTransport_iff alphabetEquiv stateEquiv _ _).2 step)
        (equivTransport M alphabetEquiv stateEquiv rest)

/-- Pull a transported trace back to the original alphabet and state types. -/
public def equivTransportSymm (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State') :
    {n : Nat} → {source target : DLBA.Cfg Gamma' State' n} →
      StepTrace (M.equivTransport alphabetEquiv stateEquiv) source target →
        StepTrace M
          ((machineEquivCfg alphabetEquiv stateEquiv).symm source)
          ((machineEquivCfg alphabetEquiv stateEquiv).symm target)
  | _, _, _, .refl cfg =>
      .refl ((machineEquivCfg alphabetEquiv stateEquiv).symm cfg)
  | _, _, _, .head step rest =>
      .head ((M.step_equivTransport_iff_symm alphabetEquiv stateEquiv _ _).1 step)
        (equivTransportSymm M alphabetEquiv stateEquiv rest)

/-- Configuration renaming preserves whether one step crosses a fixed physical boundary. -/
@[simp] public theorem crossesBoundary_machineEquivCfg_iff
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (boundary : Fin n)
    (source target : DLBA.Cfg Gamma State n) :
    CrossesBoundary boundary
        (machineEquivCfg alphabetEquiv stateEquiv source)
        (machineEquivCfg alphabetEquiv stateEquiv target) ↔
      CrossesBoundary boundary source target := by
  rfl

/-- Pulling configurations back along the renaming also preserves boundary crossings. -/
@[simp] public theorem crossesBoundary_machineEquivCfg_symm_iff
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (boundary : Fin n)
    (source target : DLBA.Cfg Gamma' State' n) :
    CrossesBoundary boundary
        ((machineEquivCfg alphabetEquiv stateEquiv).symm source)
        ((machineEquivCfg alphabetEquiv stateEquiv).symm target) ↔
      CrossesBoundary boundary source target := by
  rfl

/-- Simultaneous alphabet/state renaming preserves the number of steps literally. -/
@[simp] public theorem length_equivTransport
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Gamma State n}
    (trace : StepTrace M source target) :
    (equivTransport M alphabetEquiv stateEquiv trace).length = trace.length := by
  induction trace with
  | refl => simp [equivTransport, length]
  | head step rest ih =>
      simp only [equivTransport, length, ih]

/-- Pulling a transported trace back preserves its number of steps literally. -/
@[simp] public theorem length_equivTransportSymm
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Gamma' State' n}
    (trace : StepTrace (M.equivTransport alphabetEquiv stateEquiv) source target) :
    (equivTransportSymm M alphabetEquiv stateEquiv trace).length = trace.length := by
  induction trace with
  | refl => simp [equivTransportSymm, length]
  | head step rest ih =>
      simp only [equivTransportSymm, length, ih]

/-- Simultaneous alphabet/state renaming preserves every boundary crossing count literally. -/
@[simp] public theorem crossingCount_equivTransport
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Gamma State n}
    (trace : StepTrace M source target) (boundary : Fin n) :
    (equivTransport M alphabetEquiv stateEquiv trace).crossingCount boundary =
      trace.crossingCount boundary := by
  induction trace with
  | refl => simp [equivTransport, crossingCount]
  | head step rest ih =>
      simp only [equivTransport, crossingCount,
        crossesBoundary_machineEquivCfg_iff, ih]

/-- Pulling a transported trace back preserves every boundary crossing count literally. -/
@[simp] public theorem crossingCount_equivTransportSymm
    (M : Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Gamma' State' n}
    (trace : StepTrace (M.equivTransport alphabetEquiv stateEquiv) source target)
    (boundary : Fin n) :
    (equivTransportSymm M alphabetEquiv stateEquiv trace).crossingCount boundary =
      trace.crossingCount boundary := by
  induction trace with
  | refl => simp [equivTransportSymm, crossingCount]
  | head step rest ih =>
      simp only [equivTransportSymm, crossingCount,
        crossesBoundary_machineEquivCfg_symm_iff, ih]

/-- Changing only the dependent source index of a trace by equality changes no crossing count. -/
@[simp] public theorem crossingCount_cast_source
    {M : Machine Gamma State} {n : Nat}
    {source source' target : DLBA.Cfg Gamma State n}
    (hsource : source = source') (trace : StepTrace M source target)
    (boundary : Fin n) :
    (hsource ▸ trace).crossingCount boundary = trace.crossingCount boundary := by
  subst source'
  rfl

end StepTrace

/-! ## Canonical endmarker alphabets -/

universe t x x'

variable {Terminal : Type t} {Work : Type x} {Work' : Type x'}

/-- Rename only the work-symbol summand of a canonical endmarker alphabet.  Terminals, the
blank, and both endmarkers are fixed literally. -/
public def endAlphaEquiv (workEquiv : Work ≃ Work') :
    EndAlpha Terminal Work ≃ EndAlpha Terminal Work' :=
  Equiv.sumCongr
    (Equiv.optionCongr (Equiv.sumCongr (Equiv.refl Terminal) workEquiv))
    (Equiv.refl Bool)

@[simp] public theorem endAlphaEquiv_leftMark (workEquiv : Work ≃ Work') :
    endAlphaEquiv (Terminal := Terminal) workEquiv
        (leftMark : EndAlpha Terminal Work) =
      (leftMark : EndAlpha Terminal Work') := rfl

@[simp] public theorem endAlphaEquiv_rightMark (workEquiv : Work ≃ Work') :
    endAlphaEquiv (Terminal := Terminal) workEquiv
        (rightMark : EndAlpha Terminal Work) =
      (rightMark : EndAlpha Terminal Work') := rfl

@[simp] public theorem endAlphaEquiv_inputCell
    (workEquiv : Work ≃ Work') (terminal : Terminal) :
    endAlphaEquiv workEquiv (inputCell (Work := Work) terminal) =
      inputCell (Work := Work') terminal := rfl

/-- Renaming the work-symbol summand carries a canonical bracketed input tape to the canonical
bracketed tape over the new work alphabet. -/
public theorem alphabetEquivTape_endAlphaEquiv_loadEnd
    (workEquiv : Work ≃ Work') (word : List Terminal) :
    alphabetEquivTape (endAlphaEquiv workEquiv)
        (loadEnd (Γ := Work) word) =
      loadEnd (Γ := Work') word := by
  apply congrArg (fun contents ↦
    (⟨contents, ⟨0, Nat.succ_pos _⟩⟩ :
      DLBA.BoundedTape (EndAlpha Terminal Work') (word.length + 1)))
  funext index
  change endAlphaEquiv workEquiv
      (if index.val = 0 then (leftMark : EndAlpha Terminal Work)
      else if h : index.val - 1 < word.length then
        Sum.inl (some (Sum.inl (word.get ⟨index.val - 1, h⟩)))
      else rightMark) =
    (if index.val = 0 then (leftMark : EndAlpha Terminal Work')
    else if h : index.val - 1 < word.length then
      Sum.inl (some (Sum.inl (word.get ⟨index.val - 1, h⟩)))
    else rightMark)
  split
  · simp_all
  · split
    · simp_all [endAlphaEquiv]
    · simp_all

/-- Simultaneously renaming the work alphabet and states sends the canonical initial
configuration to the canonical initial configuration of the transported machine. -/
public theorem machineEquivCfg_initCfgEnd
    (M : Machine (EndAlpha Terminal Work) State)
    (workEquiv : Work ≃ Work') (stateEquiv : State ≃ State')
    (word : List Terminal) :
    machineEquivCfg (endAlphaEquiv workEquiv) stateEquiv
        (initCfgEnd M word) =
      initCfgEnd (M.equivTransport (endAlphaEquiv workEquiv) stateEquiv) word := by
  change
    (⟨stateEquiv M.initial,
      alphabetEquivTape (endAlphaEquiv workEquiv) (loadEnd (Γ := Work) word)⟩ :
      DLBA.Cfg (EndAlpha Terminal Work') State' (word.length + 1)) =
    ⟨stateEquiv M.initial, loadEnd (Γ := Work') word⟩
  rw [alphabetEquivTape_endAlphaEquiv_loadEnd]

/-- Canonicalize arbitrary finite work and state signatures to `Fin` types.  This definition is
intentionally noncomputable: it belongs in adequacy proofs, never in an executable encoding or
membership evaluator. -/
public noncomputable def Machine.finSignatureTransport
    [Fintype Work] [Fintype State]
    (M : Machine (EndAlpha Terminal Work) State) :
    Machine (EndAlpha Terminal (Fin (Fintype.card Work)))
      (Fin (Fintype.card State)) :=
  M.equivTransport
    (endAlphaEquiv (Fintype.equivFin Work))
    (Fintype.equivFin State)

end LBA

namespace LBA.BoundedCrossing

universe u v u' v'

variable {Gamma : Type u} {State : Type v}
variable {Gamma' : Type u'} {State' : Type v'}

/-- Bounded acceptance is invariant under simultaneous alphabet/state renaming, with every
individual crossing count preserved rather than merely bounded again. -/
public theorem acceptsWithBound_equivTransport_iff
    (M : LBA.Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (source : DLBA.Cfg Gamma State n) (bound : Nat) :
    AcceptsWithBound (M.equivTransport alphabetEquiv stateEquiv)
        (LBA.machineEquivCfg alphabetEquiv stateEquiv source) bound ↔
      AcceptsWithBound M source bound := by
  constructor
  · rintro ⟨target, trace, hfinal, hcross⟩
    let originalTarget :=
      (LBA.machineEquivCfg alphabetEquiv stateEquiv).symm target
    let pulledTrace : LBA.StepTrace M
        ((LBA.machineEquivCfg alphabetEquiv stateEquiv).symm
          (LBA.machineEquivCfg alphabetEquiv stateEquiv source))
        originalTarget :=
      LBA.StepTrace.equivTransportSymm M alphabetEquiv stateEquiv trace
    have hsource :
        (LBA.machineEquivCfg alphabetEquiv stateEquiv).symm
            (LBA.machineEquivCfg alphabetEquiv stateEquiv source) = source :=
      (LBA.machineEquivCfg alphabetEquiv stateEquiv).left_inv source
    let originalTrace : LBA.StepTrace M source originalTarget :=
      hsource ▸ pulledTrace
    refine ⟨originalTarget, originalTrace, ?_, ?_⟩
    · simpa [originalTarget] using hfinal
    · intro boundary
      have hpulled :
          pulledTrace.crossingCount boundary ≤ bound := by
        change
          (LBA.StepTrace.equivTransportSymm M alphabetEquiv stateEquiv trace).crossingCount
              boundary ≤ bound
        simpa using hcross boundary
      simpa [originalTrace] using hpulled
  · rintro ⟨target, trace, hfinal, hcross⟩
    refine ⟨LBA.machineEquivCfg alphabetEquiv stateEquiv target,
      LBA.StepTrace.equivTransport M alphabetEquiv stateEquiv trace, ?_, ?_⟩
    · simpa using hfinal
    · intro boundary
      simpa using hcross boundary

/-- Ordinary acceptance is likewise invariant under simultaneous alphabet/state renaming. -/
public theorem accepts_equivTransport_iff
    (M : LBA.Machine Gamma State)
    (alphabetEquiv : Gamma ≃ Gamma') (stateEquiv : State ≃ State')
    {n : Nat} (source : DLBA.Cfg Gamma State n) :
    LBA.Accepts (M.equivTransport alphabetEquiv stateEquiv)
        (LBA.machineEquivCfg alphabetEquiv stateEquiv source) ↔
      LBA.Accepts M source := by
  rw [accepts_iff_exists_acceptsWithBound,
    accepts_iff_exists_acceptsWithBound]
  constructor
  · rintro ⟨bound, haccept⟩
    exact ⟨bound,
      (acceptsWithBound_equivTransport_iff M alphabetEquiv stateEquiv source bound).mp
        haccept⟩
  · rintro ⟨bound, haccept⟩
    exact ⟨bound,
      (acceptsWithBound_equivTransport_iff M alphabetEquiv stateEquiv source bound).mpr
        haccept⟩

universe t x x'

variable {Terminal : Type t} {Work : Type x} {Work' : Type x'}

/-- Work-alphabet and state renaming preserves the fixed-cap language of a canonical endmarker
machine exactly. -/
public theorem languageWithBound_equivTransport
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (workEquiv : Work ≃ Work') (stateEquiv : State ≃ State')
    (bound : Nat) :
    LanguageWithBound
        (M.equivTransport (LBA.endAlphaEquiv workEquiv) stateEquiv) bound =
      LanguageWithBound M bound := by
  ext word
  change
    AcceptsWithBound
        (M.equivTransport (LBA.endAlphaEquiv workEquiv) stateEquiv)
        (LBA.initCfgEnd
          (M.equivTransport (LBA.endAlphaEquiv workEquiv) stateEquiv) word)
        bound ↔
      AcceptsWithBound M (LBA.initCfgEnd M word) bound
  rw [← LBA.machineEquivCfg_initCfgEnd M workEquiv stateEquiv word]
  exact acceptsWithBound_equivTransport_iff M
    (LBA.endAlphaEquiv workEquiv) stateEquiv (LBA.initCfgEnd M word) bound

/-- Work-alphabet and state renaming also preserves the unrestricted endmarker language
exactly. -/
public theorem languageEnd_equivTransport
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (workEquiv : Work ≃ Work') (stateEquiv : State ≃ State') :
    LBA.LanguageEnd
        (M.equivTransport (LBA.endAlphaEquiv workEquiv) stateEquiv) =
      LBA.LanguageEnd M := by
  ext word
  change
    LBA.Accepts
        (M.equivTransport (LBA.endAlphaEquiv workEquiv) stateEquiv)
        (LBA.initCfgEnd
          (M.equivTransport (LBA.endAlphaEquiv workEquiv) stateEquiv) word) ↔
      LBA.Accepts M (LBA.initCfgEnd M word)
  rw [← LBA.machineEquivCfg_initCfgEnd M workEquiv stateEquiv word]
  exact accepts_equivTransport_iff M
    (LBA.endAlphaEquiv workEquiv) stateEquiv (LBA.initCfgEnd M word)

/-- In particular, replacing arbitrary finite work and state types by their canonical `Fin`
enumerations preserves every fixed-cap language.  No lower bound on either cardinality is an
assumption. -/
public theorem languageWithBound_finSignatureTransport
    [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    LanguageWithBound M.finSignatureTransport bound =
      LanguageWithBound M bound := by
  exact languageWithBound_equivTransport M
    (Fintype.equivFin Work) (Fintype.equivFin State) bound

/-- Canonical finite-signature transport also preserves unrestricted endmarker languages. -/
public theorem languageEnd_finSignatureTransport
    [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) :
    LBA.LanguageEnd M.finSignatureTransport = LBA.LanguageEnd M := by
  exact languageEnd_equivTransport M
    (Fintype.equivFin Work) (Fintype.equivFin State)

end LBA.BoundedCrossing

end
