module

public import Langlib.Automata.LinearBounded.SweepingCharacterization
public import Langlib.Automata.LinearBounded.EndmarkerWord
public import Langlib.Automata.LinearBounded.BoundedCrossingTransport
public import Langlib.Automata.LinearBounded.Equivalence.EndmarkerTape

import Mathlib.Tactic

@[expose]
public section

/-!
# Sweeping canonical endmarker LBAs

Canonical endmarker inputs can be viewed as nonempty marker-free words over the token alphabet
`Bool ⊕ T`: the two Boolean tokens are the left and right brackets, while `T` supplies the
interior input tokens.  Transporting the tape alphabet along the exact resulting equivalence
lets the marker-free sweeping characterization handle the empty input and empty terminal
alphabets without any special machine-level case.
-/

namespace LBA

universe u v w

/-- Tokens occurring in a bracketed canonical endmarker word.  `false` is the left bracket,
`true` the right bracket, and `Sum.inr t` is the terminal `t`. -/
public abbrev BracketToken (T : Type u) := Bool ⊕ T

/-- The marker-free alphabet in which bracket tokens are input symbols and `Work` remains the
work-symbol alphabet. -/
public abbrev BracketAlpha (T : Type u) (Work : Type v) :=
  Option (BracketToken T ⊕ Work)

/-- Canonical marker-free embedding of a bracket token. -/
public def bracketEmbed {T : Type u} {Work : Type v} :
    BracketToken T → BracketAlpha T Work :=
  fun token => some (.inl token)

/-- Exact tape-alphabet equivalence between bracket tokens and canonical endmarkers. -/
public def bracketAlphabetEquiv (T : Type u) (Work : Type v) :
    BracketAlpha T Work ≃ EndAlpha T Work where
  toFun
    | none => .inl none
    | some (.inl (.inl boundary)) => .inr boundary
    | some (.inl (.inr terminal)) => .inl (some (.inl terminal))
    | some (.inr work) => .inl (some (.inr work))
  invFun
    | .inl none => none
    | .inl (some (.inl terminal)) => some (.inl (.inr terminal))
    | .inl (some (.inr work)) => some (.inr work)
    | .inr boundary => some (.inl (.inl boundary))
  left_inv symbol := by cases symbol with
    | none => rfl
    | some symbol => cases symbol with
      | inl token => cases token <;> rfl
      | inr work => rfl
  right_inv symbol := by
    cases symbol with
    | inl interior => cases interior with
      | none => rfl
      | some symbol => cases symbol <;> rfl
    | inr boundary => rfl

@[simp] public theorem bracketAlphabetEquiv_bracketEmbed_left
    {T : Type u} {Work : Type v} (boundary : Bool) :
    bracketAlphabetEquiv T Work
        (bracketEmbed (Work := Work) (Sum.inl boundary : BracketToken T)) =
      (Sum.inr boundary : EndAlpha T Work) := rfl

@[simp] public theorem bracketAlphabetEquiv_bracketEmbed_terminal
    {T : Type u} {Work : Type v} (terminal : T) :
    bracketAlphabetEquiv T Work
        (bracketEmbed (Work := Work) (Sum.inr terminal : BracketToken T)) =
      inputCell (Work := Work) terminal := rfl

/-- The token word corresponding to the canonical tape `⊢ w ⊣`. -/
public def bracketWord {T : Type u} (word : List T) : List (BracketToken T) :=
  (Sum.inl false : BracketToken T) ::
    word.map (fun terminal => Sum.inr terminal) ++
      [Sum.inl true]

@[simp] public theorem bracketWord_nil {T : Type u} :
    bracketWord ([] : List T) =
      [Sum.inl false, Sum.inl true] := rfl

@[simp] public theorem length_bracketWord {T : Type u} (word : List T) :
    (bracketWord word).length = word.length + 2 := by
  simp [bracketWord]

@[simp] public theorem bracketWord_ne_nil {T : Type u} (word : List T) :
    bracketWord word ≠ [] := by
  simp [bracketWord]

/-- The vector form of `bracketWord`, indexed exactly like `loadEnd`. -/
public def bracketInput {T : Type u} (word : List T) :
    Fin (word.length + 2) → BracketToken T :=
  fun index =>
    if index.val = 0 then .inl false
    else if h : index.val - 1 < word.length then
      .inr (word.get ⟨index.val - 1, h⟩)
    else .inl true

/-- Enumerating the vector form recovers the bracket-token word exactly. -/
public theorem ofFn_bracketInput {T : Type u} (word : List T) :
    List.ofFn (bracketInput word) = bracketWord word := by
  apply List.ext_get
  · simp [bracketWord]
  · intro index hleft hright
    simp only [List.length_ofFn] at hleft
    rw [List.get_ofFn]
    simp only [bracketInput, Fin.val_cast]
    by_cases hzero : index = 0
    · subst index
      simp [bracketWord]
    · rw [if_neg hzero]
      by_cases hinput : index - 1 < word.length
      · rw [dif_pos hinput]
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        simp [bracketWord, List.get_eq_getElem] at hinput ⊢
        rw [List.getElem_append_left (by simpa using hinput),
          List.getElem_map]
      · rw [dif_neg hinput]
        have hlast : index = word.length + 1 := by omega
        subst index
        simp [bracketWord]

/-- Mapping the token word through the alphabet equivalence gives the existing canonical
endmarker word exactly. -/
public theorem map_bracketWord_eq_endWord
    {T : Type u} {Work : Type v} (word : List T) :
    (bracketWord word).map
        (fun token => bracketAlphabetEquiv T Work
          (bracketEmbed (Work := Work) token)) =
      endWord (Work := Work) word := by
  simp [bracketWord, endWord]

/-- Exact bracket-word/load equivalence, including the empty word. -/
public theorem ofFn_loadEnd_contents_eq_map_bracketWord
    {T : Type u} {Work : Type v} (word : List T) :
    List.ofFn (loadEnd (Γ := Work) word).contents =
      (bracketWord word).map
        (fun token => bracketAlphabetEquiv T Work
          (bracketEmbed (Work := Work) token)) := by
  rw [ofFn_loadEnd_contents, map_bracketWord_eq_endWord]

/-- Enumerating a canonical nonempty list-loaded tape recovers the list exactly. -/
public theorem ofFn_loadList_contents
    {Alphabet : Type u} (symbols : List Alphabet) (hne : symbols ≠ []) :
    List.ofFn (loadList symbols hne).contents = symbols := by
  apply List.ext_get
  · simp only [List.length_ofFn]
    have hpos := List.length_pos_of_ne_nil hne
    omega
  · intro index hleft hright
    rw [List.get_ofFn]
    rfl

@[simp] public theorem bracketAlphabetEquiv_bracketInput
    {T : Type u} {Work : Type v} (word : List T)
    (index : Fin (word.length + 2)) :
    bracketAlphabetEquiv T Work
        (bracketEmbed (Work := Work) (bracketInput word index)) =
      (loadEnd (Γ := Work) word).contents index := by
  simp only [bracketInput, loadEnd]
  split
  · simp_all
  · split
    · simp_all [inputCell]
    · simp_all

/-- Canonical marker-free configuration on the bracket-token vector. -/
public def canonicalBracketCfg
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (BracketAlpha T Work) State) (word : List T) :
    DLBA.Cfg (BracketAlpha T Work) State (word.length + 1) :=
  ⟨M.initial,
    ⟨fun index => bracketEmbed (Work := Work) (bracketInput word index), 0⟩⟩

/-- Transporting a canonical bracket-vector configuration gives the canonical endmarker
configuration exactly, with no tape-length cast. -/
public theorem machineEquivCfg_canonicalBracketCfg
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (BracketAlpha T Work) State) (word : List T) :
    machineEquivCfg (bracketAlphabetEquiv T Work) (Equiv.refl State)
        (canonicalBracketCfg M word) =
      initCfgEnd
        (M.equivTransport (bracketAlphabetEquiv T Work) (Equiv.refl State)) word := by
  apply cfg_ext
  · rfl
  · funext index
    exact bracketAlphabetEquiv_bracketInput word index
  · rfl

/-- Pulling a canonical endmarker configuration back through the bracket equivalence gives the
canonical bracket-vector configuration exactly. -/
public theorem machineEquivCfg_symm_initCfgEnd
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (EndAlpha T Work) State) (word : List T) :
    machineEquivCfg (bracketAlphabetEquiv T Work).symm (Equiv.refl State)
        (initCfgEnd M word) =
      canonicalBracketCfg
        (M.equivTransport (bracketAlphabetEquiv T Work).symm (Equiv.refl State)) word := by
  apply cfg_ext
  · rfl
  · funext index
    change (bracketAlphabetEquiv T Work).symm
        ((loadEnd (Γ := Work) word).contents index) =
      bracketEmbed (Work := Work) (bracketInput word index)
    rw [← bracketAlphabetEquiv_bracketInput word index]
    exact (bracketAlphabetEquiv T Work).symm_apply_apply _
  · rfl

private theorem finFunction_heq_of_ofFn_eq
    {Alphabet : Type u} {m n : Nat}
    {left : Fin m → Alphabet} {right : Fin n → Alphabet}
    (h : List.ofFn left = List.ofFn right) : HEq left right := by
  have hsigma := (List.ofFn_inj').mp h
  cases hsigma
  rfl

/-- The canonical `loadList` configuration of `bracketWord` is heterogeneously equal to the
dimension-clean bracket-vector configuration.  This isolates the sole arithmetic tape-length
transport: `(word.length + 2) - 1 = word.length + 1`. -/
public theorem initCfgList_bracketWord_heq_canonicalBracketCfg
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (BracketAlpha T Work) State) (word : List T)
    (hne : (bracketWord word).map (bracketEmbed (Work := Work)) ≠ []) :
    HEq
      (initCfgList M
        ((bracketWord word).map (bracketEmbed (Work := Work))) hne)
      (canonicalBracketCfg M word) := by
  let symbols := (bracketWord word).map (bracketEmbed (Work := Work))
  have hdimension : symbols.length - 1 = word.length + 1 := by
    simp [symbols]
  refine cfg_heq hdimension rfl ?_
  refine boundedtape_heq hdimension ?_ rfl
  apply finFunction_heq_of_ofFn_eq
  calc
    List.ofFn
        (loadList symbols hne).contents = symbols :=
      ofFn_loadList_contents symbols hne
    _ = List.ofFn
        (canonicalBracketCfg M word).tape.contents := by
      change (bracketWord word).map (bracketEmbed (Work := Work)) =
        List.ofFn (bracketEmbed (Work := Work) ∘ bracketInput word)
      rw [← List.map_ofFn, ofFn_bracketInput]

/-- On every well-formed bracket-token word, list-level marker-free recognition is exactly
acceptance from the dimension-clean canonical bracket-vector configuration. -/
public theorem languageViaEmbed_bracketWord_iff
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (BracketAlpha T Work) State) (word : List T) :
    LanguageViaEmbed M (bracketEmbed (Work := Work)) (bracketWord word) ↔
      Accepts M (canonicalBracketCfg M word) := by
  change
    (∃ hne : (bracketWord word).map (bracketEmbed (Work := Work)) ≠ [],
      Accepts M
        (initCfgList M
          ((bracketWord word).map (bracketEmbed (Work := Work))) hne)) ↔ _
  constructor
  · rintro ⟨hne, haccept⟩
    exact (accepts_heq M (by simp)
      (initCfgList_bracketWord_heq_canonicalBracketCfg M word hne)).mp haccept
  · intro haccept
    let hne : (bracketWord word).map (bracketEmbed (Work := Work)) ≠ [] := by
      simp [bracketWord]
    refine ⟨hne, ?_⟩
    exact (accepts_heq M (by simp)
      (initCfgList_bracketWord_heq_canonicalBracketCfg M word hne)).mpr haccept

/-! ## Sweeping under alphabet and state equivalence -/

universe u' v'

@[simp] public theorem HeadTurns.physicalDirection_machineEquivCfg
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (source target : DLBA.Cfg Alphabet State n) :
    HeadTurns.physicalDirection
        (machineEquivCfg alphabetEquiv stateEquiv source)
        (machineEquivCfg alphabetEquiv stateEquiv target) =
      HeadTurns.physicalDirection source target := rfl

@[simp] public theorem HeadTurns.physicalDirection_machineEquivCfg_symm
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (source target : DLBA.Cfg Alphabet' State' n) :
    HeadTurns.physicalDirection
        ((machineEquivCfg alphabetEquiv stateEquiv).symm source)
        ((machineEquivCfg alphabetEquiv stateEquiv).symm target) =
      HeadTurns.physicalDirection source target := rfl

@[simp] public theorem Sweeping.atEndpoint_machineEquivCfg_iff
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (cfg : DLBA.Cfg Alphabet State n) :
    Sweeping.AtEndpoint (machineEquivCfg alphabetEquiv stateEquiv cfg) ↔
      Sweeping.AtEndpoint cfg := Iff.rfl

@[simp] public theorem Sweeping.atEndpoint_machineEquivCfg_symm_iff
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (cfg : DLBA.Cfg Alphabet' State' n) :
    Sweeping.AtEndpoint ((machineEquivCfg alphabetEquiv stateEquiv).symm cfg) ↔
      Sweeping.AtEndpoint cfg := Iff.rfl

@[simp] public theorem Sweeping.advanceDirection_machineEquivCfg
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (previous : Option HeadTurns.Direction)
    (source target : DLBA.Cfg Alphabet State n) :
    Sweeping.advanceDirection previous
        (machineEquivCfg alphabetEquiv stateEquiv source)
        (machineEquivCfg alphabetEquiv stateEquiv target) =
      Sweeping.advanceDirection previous source target := by
  simp [Sweeping.advanceDirection]

@[simp] public theorem Sweeping.advanceDirection_machineEquivCfg_symm
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (previous : Option HeadTurns.Direction)
    (source target : DLBA.Cfg Alphabet' State' n) :
    Sweeping.advanceDirection previous
        ((machineEquivCfg alphabetEquiv stateEquiv).symm source)
        ((machineEquivCfg alphabetEquiv stateEquiv).symm target) =
      Sweeping.advanceDirection previous source target := by
  simp [Sweeping.advanceDirection]

@[simp] public theorem Sweeping.turnAllowed_machineEquivCfg_iff
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (previous : Option HeadTurns.Direction)
    (source target : DLBA.Cfg Alphabet State n) :
    Sweeping.TurnAllowed previous
        (machineEquivCfg alphabetEquiv stateEquiv source)
        (machineEquivCfg alphabetEquiv stateEquiv target) ↔
      Sweeping.TurnAllowed previous source target := by
  simp [Sweeping.TurnAllowed, Sweeping.DirectionAllowed]

@[simp] public theorem Sweeping.turnAllowed_machineEquivCfg_symm_iff
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} (previous : Option HeadTurns.Direction)
    (source target : DLBA.Cfg Alphabet' State' n) :
    Sweeping.TurnAllowed previous
        ((machineEquivCfg alphabetEquiv stateEquiv).symm source)
        ((machineEquivCfg alphabetEquiv stateEquiv).symm target) ↔
      Sweeping.TurnAllowed previous source target := by
  simp [Sweeping.TurnAllowed, Sweeping.DirectionAllowed]

namespace StepTrace

/-- Simultaneous alphabet/state renaming preserves the strong sweeping predicate on a concrete
trace. -/
@[simp] public theorem sweepingFrom_equivTransport
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (M : Machine Alphabet State)
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Alphabet State n}
    (trace : StepTrace M source target)
    (previous : Option HeadTurns.Direction) :
    (equivTransport M alphabetEquiv stateEquiv trace).SweepingFrom previous ↔
      trace.SweepingFrom previous := by
  induction trace generalizing previous with
  | refl => simp [equivTransport]
  | @head source next target step rest ih =>
      simp only [equivTransport, sweepingFrom_head,
        Sweeping.turnAllowed_machineEquivCfg_iff,
        Sweeping.advanceDirection_machineEquivCfg, ih]

/-- Pulling a transported trace back through alphabet/state renaming preserves sweeping
exactly. -/
@[simp] public theorem sweepingFrom_equivTransportSymm
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (M : Machine Alphabet State)
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Alphabet' State' n}
    (trace : StepTrace (M.equivTransport alphabetEquiv stateEquiv) source target)
    (previous : Option HeadTurns.Direction) :
    (equivTransportSymm M alphabetEquiv stateEquiv trace).SweepingFrom previous ↔
      trace.SweepingFrom previous := by
  induction trace generalizing previous with
  | refl => simp [equivTransportSymm]
  | @head source next target step rest ih =>
      simp only [equivTransportSymm, sweepingFrom_head,
        Sweeping.turnAllowed_machineEquivCfg_symm_iff,
        Sweeping.advanceDirection_machineEquivCfg_symm, ih]

@[simp] public theorem sweeping_equivTransport
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (M : Machine Alphabet State)
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Alphabet State n}
    (trace : StepTrace M source target) :
    (equivTransport M alphabetEquiv stateEquiv trace).Sweeping ↔
      trace.Sweeping :=
  sweepingFrom_equivTransport M alphabetEquiv stateEquiv trace none

@[simp] public theorem sweeping_equivTransportSymm
    {Alphabet : Type u} {State : Type v}
    {Alphabet' : Type u'} {State' : Type v'}
    (M : Machine Alphabet State)
    (alphabetEquiv : Alphabet ≃ Alphabet') (stateEquiv : State ≃ State')
    {n : Nat} {source target : DLBA.Cfg Alphabet' State' n}
    (trace : StepTrace (M.equivTransport alphabetEquiv stateEquiv) source target) :
    (equivTransportSymm M alphabetEquiv stateEquiv trace).Sweeping ↔
      trace.Sweeping :=
  sweepingFrom_equivTransportSymm M alphabetEquiv stateEquiv trace none

/-- Changing only a trace's propositionally equal source configuration preserves sweeping. -/
@[simp] public theorem sweeping_cast_source
    {Alphabet : Type u} {State : Type v} {n : Nat}
    {M : Machine Alphabet State}
    {source source' target : DLBA.Cfg Alphabet State n}
    (hsource : source = source') (trace : StepTrace M source target) :
    (hsource ▸ trace).Sweeping ↔ trace.Sweeping := by
  subst source'
  rfl

end StepTrace

namespace Machine

/-- Every concrete trace from every canonical endmarker input is sweeping.  This includes the
two-cell input for `ε`, rejecting branches, and traces stopped at arbitrary finite prefixes. -/
public def SweepingEnd
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (EndAlpha T Work) State) : Prop :=
  ∀ (word : List T) {target : DLBA.Cfg (EndAlpha T Work) State (word.length + 1)},
    ∀ trace : StepTrace M (initCfgEnd M word) target,
      trace.Sweeping

/-- Transporting a strong marker-free sweeping promise through the bracket/endmarker alphabet
equivalence gives the strong canonical endmarker promise. -/
public theorem sweepingEnd_equivTransport_of_sweepingViaEmbed
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (BracketAlpha T Work) State)
    (hsweeping : M.SweepingViaEmbed (bracketEmbed (Work := Work))) :
    (M.equivTransport (bracketAlphabetEquiv T Work) (Equiv.refl State)).SweepingEnd := by
  intro word target trace
  let pulledTrace := StepTrace.equivTransportSymm M
    (bracketAlphabetEquiv T Work) (Equiv.refl State) trace
  have hsource :
      (machineEquivCfg (bracketAlphabetEquiv T Work) (Equiv.refl State)).symm
          (initCfgEnd
            (M.equivTransport (bracketAlphabetEquiv T Work) (Equiv.refl State)) word) =
        canonicalBracketCfg M word := by
    rw [← machineEquivCfg_canonicalBracketCfg M word]
    exact (machineEquivCfg (bracketAlphabetEquiv T Work)
      (Equiv.refl State)).left_inv _
  let canonicalTrace : StepTrace M (canonicalBracketCfg M word)
      ((machineEquivCfg (bracketAlphabetEquiv T Work)
        (Equiv.refl State)).symm target) :=
    hsource ▸ pulledTrace
  have hcanonical : canonicalTrace.Sweeping := by
    exact hsweeping (bracketInput word) canonicalTrace
  have hpulled : pulledTrace.Sweeping := by
    simpa [canonicalTrace] using hcanonical
  exact (StepTrace.sweeping_equivTransportSymm M
    (bracketAlphabetEquiv T Work) (Equiv.refl State) trace).mp hpulled

end Machine

/-! ## Exact language transport on well-formed bracket words -/

/-- Turning a marker-free bracket-token machine into an endmarker machine preserves its language
on the canonical bracket words exactly. -/
public theorem languageEnd_equivTransport_bracket_iff
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (BracketAlpha T Work) State) (word : List T) :
    LanguageEnd
        (M.equivTransport (bracketAlphabetEquiv T Work) (Equiv.refl State)) word ↔
      LanguageViaEmbed M (bracketEmbed (Work := Work)) (bracketWord word) := by
  rw [languageViaEmbed_bracketWord_iff]
  change
    Accepts
        (M.equivTransport (bracketAlphabetEquiv T Work) (Equiv.refl State))
        (initCfgEnd
          (M.equivTransport (bracketAlphabetEquiv T Work) (Equiv.refl State)) word) ↔
      Accepts M (canonicalBracketCfg M word)
  rw [← machineEquivCfg_canonicalBracketCfg M word]
  exact BoundedCrossing.accepts_equivTransport_iff M
    (bracketAlphabetEquiv T Work) (Equiv.refl State)
    (canonicalBracketCfg M word)

/-- Pulling an endmarker machine back to bracket tokens preserves its language on every
well-formed bracket word exactly. -/
public theorem languageViaEmbed_equivTransport_bracketWord_iff
    {T : Type u} {Work : Type v} {State : Type w}
    (M : Machine (EndAlpha T Work) State) (word : List T) :
    LanguageViaEmbed
        (M.equivTransport (bracketAlphabetEquiv T Work).symm (Equiv.refl State))
        (bracketEmbed (Work := Work)) (bracketWord word) ↔
      LanguageEnd M word := by
  rw [languageViaEmbed_bracketWord_iff]
  change
    Accepts
        (M.equivTransport (bracketAlphabetEquiv T Work).symm (Equiv.refl State))
        (canonicalBracketCfg
          (M.equivTransport (bracketAlphabetEquiv T Work).symm (Equiv.refl State)) word) ↔
      Accepts M (initCfgEnd M word)
  rw [← machineEquivCfg_symm_initCfgEnd M word]
  exact BoundedCrossing.accepts_equivTransport_iff M
    (bracketAlphabetEquiv T Work).symm (Equiv.refl State)
    (initCfgEnd M word)

end LBA

/-! ## The named canonical endmarker sweeping class -/

/-- A language is recognized by a sweeping canonical endmarker LBA when some finite machine
recognizes it and every concrete trace from every bracketed input is sweeping. -/
@[expose]
public def is_SweepingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Work State : Type) (_ : Fintype Work) (_ : Fintype State)
    (_ : DecidableEq Work) (_ : DecidableEq State)
    (M : LBA.Machine (LBA.EndAlpha T Work) State),
    M.SweepingEnd ∧ LBA.LanguageEnd M = L

/-- Languages recognized by sweeping canonical endmarker LBAs. -/
@[expose]
public def SweepingLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_SweepingLBA

/-- Forgetting the strong all-traces sweeping promise gives an ordinary canonical endmarker
LBA presentation. -/
public theorem is_SweepingLBA_imp_is_LBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_SweepingLBA L) : is_LBA L := by
  obtain ⟨Work, State, hWork, hState, hdecWork, hdecState,
    M, _hsweeping, hM⟩ := hL
  exact ⟨Work, State, hWork, hState, hdecWork, hdecState, M, hM⟩

/-- Sweeping canonical endmarker languages are ordinary LBA languages. -/
public theorem SweepingLBA_subset_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingLBA : Set (Language T)) ⊆ LBA :=
  fun _ hL => is_SweepingLBA_imp_is_LBA hL

/-- Every canonical endmarker LBA language has a presentation whose every canonical trace is
sweeping.

Only well-formed bracket words are queried in the pointwise target-language proof, so the
intermediate marker-free language's values on malformed token words are irrelevant. -/
public theorem is_LBA_imp_is_SweepingLBA
    {T : Type} [hT : Fintype T] [hdecT : DecidableEq T] {L : Language T}
    (hL : is_LBA L) : is_SweepingLBA L := by
  obtain ⟨Work, State, hWork, hState, hdecWork, hdecState, M, hM⟩ := hL
  letI := hWork
  letI := hState
  letI := hdecWork
  letI := hdecState
  let bracketMachine :=
    M.equivTransport (LBA.bracketAlphabetEquiv T Work).symm (Equiv.refl State)
  let bracketLanguage : Language (LBA.BracketToken T) :=
    LBA.LanguageViaEmbed bracketMachine (LBA.bracketEmbed (Work := Work))
  have hbracketLBA : is_LBA_pos bracketLanguage := by
    exact ⟨Work, State, hWork, hState, hdecWork, hdecState,
      bracketMachine, rfl⟩
  have hbracketSweeping : is_SweepingLBA_pos bracketLanguage := by
    change bracketLanguage ∈ (SweepingLBA_pos : Set (Language (LBA.BracketToken T)))
    rw [SweepingLBA_pos_eq_LBA_pos]
    exact hbracketLBA
  obtain ⟨SweepWork, SweepState, hSweepWork, hSweepState,
      hdecSweepWork, hdecSweepState, SweepMachine,
      hSweepPromise, hSweepLanguage⟩ :=
    hbracketSweeping
  letI := hSweepWork
  letI := hSweepState
  letI := hdecSweepWork
  letI := hdecSweepState
  let EndMachine := SweepMachine.equivTransport
    (LBA.bracketAlphabetEquiv T SweepWork) (Equiv.refl SweepState)
  refine ⟨SweepWork, SweepState, hSweepWork, hSweepState,
    hdecSweepWork, hdecSweepState, EndMachine, ?_, ?_⟩
  · exact LBA.Machine.sweepingEnd_equivTransport_of_sweepingViaEmbed
      SweepMachine hSweepPromise
  · funext word
    apply propext
    calc
      LBA.LanguageEnd EndMachine word ↔
          LBA.LanguageViaEmbed SweepMachine
            (LBA.bracketEmbed (Work := SweepWork))
            (LBA.bracketWord word) :=
        LBA.languageEnd_equivTransport_bracket_iff SweepMachine word
      _ ↔ bracketLanguage (LBA.bracketWord word) := by
        exact Iff.of_eq (congrFun hSweepLanguage (LBA.bracketWord word))
      _ ↔ LBA.LanguageEnd M word := by
        exact LBA.languageViaEmbed_equivTransport_bracketWord_iff M word
      _ ↔ L word := by
        rw [hM]

/-- Every ordinary canonical endmarker LBA language is recognized by a sweeping one. -/
public theorem LBA_subset_SweepingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (LBA : Set (Language T)) ⊆ SweepingLBA :=
  fun _ hL => is_LBA_imp_is_SweepingLBA hL

/-- Sweeping canonical endmarker LBAs recognize exactly the ordinary LBA class. -/
public theorem SweepingLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingLBA : Set (Language T)) = LBA :=
  Set.Subset.antisymm SweepingLBA_subset_LBA LBA_subset_SweepingLBA

/-- Pointwise exact canonical endmarker sweeping characterization. -/
public theorem is_SweepingLBA_iff_is_LBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_SweepingLBA L ↔ is_LBA L :=
  ⟨is_SweepingLBA_imp_is_LBA, is_LBA_imp_is_SweepingLBA⟩

/-- Conventional base-class-first orientation of the pointwise characterization. -/
public theorem is_LBA_iff_is_SweepingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_SweepingLBA L :=
  (is_SweepingLBA_iff_is_LBA L).symm

/-- Membership form of the exact equality of the named classes. -/
public theorem mem_SweepingLBA_iff_mem_LBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    L ∈ (SweepingLBA : Set (Language T)) ↔ L ∈ LBA :=
  is_SweepingLBA_iff_is_LBA L

end
