module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDANormalizationComputability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerRootFiniteWindowRecurrence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposingPairReductionComputability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FirstOrderCompleteness
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.MarkerStableUnifiedCompleteness
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.MarkerStableSufficientBasis
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotStairBase

@[expose]
public section

/-!
# Uniform equivalence for encoded deterministic pushdown automata

This file is the effective endpoint of the DPDA-to-first-order reduction.
It first records the general pullback principle needed by any computable
trace-pair compiler, then instantiates it with `pairTraceData` and the canonical
enumeration of the finite source alphabet.

The remaining first-order completeness argument is isolated in the hypothesis
of `dcf_computableEquivalence_of_completeOpenSoundBounds`; no semantic proof is
hidden in the compiler or in the validity promise.
-/

open DCFEquivalence

namespace DCFEncodedDPDA

namespace EncodedDPDA

variable {T : Type} [Fintype T] [Primcodable T]
  [DecidableEq T]

public abbrev EquivalenceInput (T : Type) :=
  EncodedDPDA T × EncodedDPDA T

@[expose] public def EquivalenceInput.Valid
    (input : EquivalenceInput T) : Prop :=
  input.1.Valid ∧ input.2.Valid

@[expose] public def EquivalenceInput.LanguageEquivalent
    (input : EquivalenceInput T) : Prop :=
  language input.1 = language input.2

/-- Pull a promise-computable first-order trace-equivalence predicate back
along any computable compiler which preserves validity and source-language
equivalence on valid DPDA pairs. -/
public theorem languageEquivalence_computablePredOnPromise_of_traceCompiler
    {TraceAction : Type} [Primcodable TraceAction] [DecidableEq TraceAction]
    {traceValid :
      EncodedFirstOrderGrammar.TracePair TraceAction → Prop}
    (compile : EquivalenceInput T →
      EncodedFirstOrderGrammar.TracePair TraceAction)
    (compileComputable : Computable compile)
    (compileValid : ∀ input, input.Valid →
      traceValid (compile input))
    (compileCorrect : ∀ input, input.Valid →
      ((compile input).1.TraceEquivalent
          (compile input).2.1 (compile input).2.2 ↔
        input.LanguageEquivalent))
    (traceEquivalence :
      ComputablePredOnPromise
        traceValid
        (fun input : EncodedFirstOrderGrammar.TracePair TraceAction =>
          input.1.TraceEquivalent input.2.1 input.2.2)) :
    ComputablePredOnPromise
      (fun input : EquivalenceInput T => input.Valid)
      (fun input : EquivalenceInput T =>
        input.LanguageEquivalent) := by
  have hpullback : ComputablePredOnPromise
      (fun input : EquivalenceInput T => input.Valid)
      (fun input : EquivalenceInput T =>
        (compile input).1.TraceEquivalent
          (compile input).2.1 (compile input).2.2) :=
    traceEquivalence.pullbackOnPromise compileComputable compileValid
  apply hpullback.congr
  intro input hvalid
  exact compileCorrect input hvalid

/-- Generic final reduction leaf.  A future compressed/exposing compiler only
has to provide the computable map, preservation of its chosen target promise,
and the semantic equivalence bridge listed here. -/
public theorem dcf_computableEquivalence_of_traceCompiler
    {TraceAction : Type} [Primcodable TraceAction] [DecidableEq TraceAction]
    {traceValid :
      EncodedFirstOrderGrammar.TracePair TraceAction → Prop}
    (compile : EquivalenceInput T →
      EncodedFirstOrderGrammar.TracePair TraceAction)
    (compileComputable : Computable compile)
    (compileValid : ∀ input, input.Valid →
      traceValid (compile input))
    (compileCorrect : ∀ input, input.Valid →
      ((compile input).1.TraceEquivalent
          (compile input).2.1 (compile input).2.2 ↔
        input.LanguageEquivalent))
    (traceEquivalence :
      ComputablePredOnPromise traceValid
        (fun input : EncodedFirstOrderGrammar.TracePair TraceAction =>
          input.1.TraceEquivalent input.2.1 input.2.2)) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) :=
  ⟨language_characterizesOn, language_membershipSemiDecidable,
    languageEquivalence_computablePredOnPromise_of_traceCompiler
      compile compileComputable compileValid compileCorrect
      traceEquivalence⟩

/-- Exact final contract for the compressed DPDA translation: compile valid
source pairs to valid exposing first-order trace pairs, preserve language
equivalence, and discharge the structured ordinary/marker stair theorem on
exposing grammars. -/
public theorem dcf_computableEquivalence_of_exposingTraceCompiler
    {TraceAction : Type} [Primcodable TraceAction] [DecidableEq TraceAction]
    (compile : EquivalenceInput T →
      EncodedFirstOrderGrammar.TracePair TraceAction)
    (compileComputable : Computable compile)
    (compileValid : ∀ input, input.Valid →
      EncodedFirstOrderGrammar.ValidExposingTracePair (compile input))
    (compileCorrect : ∀ input, input.Valid →
      ((compile input).1.TraceEquivalent
          (compile input).2.1 (compile input).2.2 ↔
        input.LanguageEquivalent))
    (hstair : ∀ g : EncodedFirstOrderGrammar TraceAction,
      g.WellFormed → g.ExposingNormalForm →
      ∃ queryWidth criticalWidth,
        g.HasWitnessedRegularActiveStairBase queryWidth ∧
          g.HasUniformMarkerStableWitnessedRegularActiveStairBase
            criticalWidth) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) := by
  apply dcf_computableEquivalence_of_traceCompiler
    compile compileComputable compileValid compileCorrect
  exact
    EncodedFirstOrderGrammar.traceEquivalence_computablePredOnPromise_of_witnessedAndMarkerStableStairBasesOnExposing
      hstair

/-- Final exposing-compiler wrapper with the ordinary stair supplied directly
by the operational structured-pivot bound.  The critical marker-stable stair
remains a separate uniform premise because its marker-elimination invariants
are independent of the semantic/progress repair. -/
public theorem
    dcf_computableEquivalence_of_exposingTraceCompiler_of_structuredPivotBounds
    {TraceAction : Type} [Primcodable TraceAction] [DecidableEq TraceAction]
    (compile : EquivalenceInput T →
      EncodedFirstOrderGrammar.TracePair TraceAction)
    (compileComputable : Computable compile)
    (compileValid : ∀ input, input.Valid →
      EncodedFirstOrderGrammar.ValidExposingTracePair (compile input))
    (compileCorrect : ∀ input, input.Valid →
      ((compile input).1.TraceEquivalent
          (compile input).2.1 (compile input).2.2 ↔
        input.LanguageEquivalent))
    (hquery : ∀ g : EncodedFirstOrderGrammar TraceAction,
      g.WellFormed → ∀ hnormal : g.ExposingNormalForm,
      ∃ bound actionBound,
        0 < bound ∧
          g.exposureBound hnormal ≤ bound ∧
          g.HasUniformStructuredPivotRebaseBound bound actionBound)
    (hcritical : ∀ g : EncodedFirstOrderGrammar TraceAction,
      g.WellFormed → g.ExposingNormalForm →
      ∃ criticalWidth,
        g.HasUniformMarkerStableWitnessedRegularActiveStairBase
          criticalWidth) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) := by
  apply dcf_computableEquivalence_of_exposingTraceCompiler
    compile compileComputable compileValid compileCorrect
  intro g hg hnormal
  obtain ⟨bound, actionBound, hbound, hexposureBound, hm2⟩ :=
    hquery g hg hnormal
  obtain ⟨criticalWidth, hcriticalStair⟩ :=
    hcritical g hg hnormal
  exact ⟨g.fixedTailWidthBound bound, criticalWidth,
    g.hasWitnessedRegularActiveStairBase_of_structuredPivotRebaseBound
      hg hnormal hbound hexposureBound actionBound hm2,
    hcriticalStair⟩

/-- A duplicate-free exhaustive list of a finite alphabet type. -/
public noncomputable def canonicalAlphabet : List T :=
  (Finset.univ : Finset T).toList

/-- The canonical compressed exposing trace pair produced from two encoded
DPDAs using the duplicate-free enumeration of the finite alphabet. -/
@[expose] public noncomputable def equivalenceExposingTracePair
    (input : EquivalenceInput T) :
    EncodedFirstOrderGrammar.TracePair (Option T) :=
  DPDANormalization.pairExposingTraceData input.1 input.2
    (canonicalAlphabet (T := T))

/-- The canonical compressed DPDA-pair compiler is total computable. -/
public theorem equivalenceExposingTracePair_computable :
    Computable (equivalenceExposingTracePair (T := T)) := by
  have hinput : Computable (fun input : EquivalenceInput T =>
      (input.1, input.2, canonicalAlphabet (T := T))) :=
    Computable.pair Computable.fst
      (Computable.pair Computable.snd
        (Computable.const (canonicalAlphabet (T := T))))
  apply ((DPDANormalization.pairExposingTraceData_computable
    (Action := T)).comp hinput).of_eq
  intro input
  simp [equivalenceExposingTracePair]

omit [Primcodable T] in
/-- Valid encoded DPDAs compile to a valid exposing-normal-form first-order
grammar with two ground initial terms. -/
public theorem equivalenceExposingTracePair_valid
    (input : EquivalenceInput T) (hvalid : input.Valid) :
    EncodedFirstOrderGrammar.ValidExposingTracePair
      (equivalenceExposingTracePair input) := by
  simpa [equivalenceExposingTracePair] using
    DPDANormalization.pairExposingTraceData_valid
      input.1 input.2 (canonicalAlphabet (T := T))
      hvalid.1 hvalid.2 (Finset.nodup_toList _)
      (by intro action; simp [canonicalAlphabet])

omit [Primcodable T] in
/-- Correctness of the canonical compressed effective reduction. -/
public theorem equivalenceExposingTracePair_traceEquivalent_iff
    (input : EquivalenceInput T) (hvalid : input.Valid) :
    (equivalenceExposingTracePair input).1.TraceEquivalent
        (equivalenceExposingTracePair input).2.1
        (equivalenceExposingTracePair input).2.2 ↔
      input.LanguageEquivalent := by
  simpa [equivalenceExposingTracePair,
    EquivalenceInput.LanguageEquivalent] using
    DPDANormalization.pairExposingTraceData_traceEquivalent_iff_language_eq
      input.1 input.2 (canonicalAlphabet (T := T))
      hvalid.1 hvalid.2 (Finset.nodup_toList _)
      (by intro action; simp [canonicalAlphabet])

/-- The concrete compressed compiler reduces encoded-DPDA equivalence to the
witnessed ordinary and marker-stable stair theorem on exposing grammars. -/
public theorem
    dcf_computableEquivalence_of_exposingWitnessedAndMarkerStableStairBases
    (hstair : ∀ g : EncodedFirstOrderGrammar (Option T),
      g.WellFormed → g.ExposingNormalForm →
      ∃ queryWidth criticalWidth,
        g.HasWitnessedRegularActiveStairBase queryWidth ∧
          g.HasUniformMarkerStableWitnessedRegularActiveStairBase
            criticalWidth) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) :=
  dcf_computableEquivalence_of_exposingTraceCompiler
    (equivalenceExposingTracePair (T := T))
    (equivalenceExposingTracePair_computable (T := T))
    equivalenceExposingTracePair_valid
    equivalenceExposingTracePair_traceEquivalent_iff hstair

/-- The proof-free first-order trace pair produced from two encoded DPDAs,
using the canonical duplicate-free enumeration of the finite alphabet. -/
@[expose] public noncomputable def equivalenceTracePair
    (input : EquivalenceInput T) :
    EncodedFirstOrderGrammar.TracePair (Option T) :=
  DPDANormalization.pairTraceData input.1 input.2
    (canonicalAlphabet (T := T))

/-- The canonical DPDA-pair-to-trace-pair compiler is total computable. -/
public theorem equivalenceTracePair_computable :
    Computable (equivalenceTracePair (T := T)) := by
  have hinput : Computable (fun input : EquivalenceInput T =>
      (input.1, input.2, canonicalAlphabet (T := T))) :=
    (Computable.pair Computable.fst
      (Computable.pair Computable.snd
        (Computable.const (canonicalAlphabet (T := T)))))
  apply ((DPDANormalization.pairTraceData_computable
    (Action := T)).comp hinput).of_eq
  intro input
  simp [equivalenceTracePair]

omit [Primcodable T] in
/-- Valid encoded DPDAs compile to a valid deterministic first-order grammar
with two ground initial terms. -/
public theorem equivalenceTracePair_valid
    (input : EquivalenceInput T) (hvalid : input.Valid) :
    EncodedFirstOrderGrammar.ValidTracePair
      (equivalenceTracePair input) := by
  simpa [equivalenceTracePair] using
    DPDANormalization.pairTraceData_valid
      input.1 input.2 (canonicalAlphabet (T := T))
      hvalid.1 hvalid.2 (Finset.nodup_toList _)
      (by intro action; simp [canonicalAlphabet])

omit [Primcodable T] in
/-- Correctness of the canonical effective reduction. -/
public theorem equivalenceTracePair_traceEquivalent_iff
    (input : EquivalenceInput T) (hvalid : input.Valid) :
    (equivalenceTracePair input).1.TraceEquivalent
        (equivalenceTracePair input).2.1
        (equivalenceTracePair input).2.2 ↔
      input.LanguageEquivalent := by
  simpa [equivalenceTracePair, EquivalenceInput.LanguageEquivalent] using
    DPDANormalization.pairTraceData_traceEquivalent_iff_language_eq
      input.1 input.2 (canonicalAlphabet (T := T))
      hvalid.1 hvalid.2 (Finset.nodup_toList _)
      (by intro action; simp [canonicalAlphabet])

/-- Any promise-computable trace-equivalence procedure on valid translated
pairs yields a promise-computable language-equivalence procedure for valid
encoded DPDAs. -/
public theorem languageEquivalence_computablePredOnPromise_of_traceEquivalence
    (traceEquivalence :
      ComputablePredOnPromise
        (EncodedFirstOrderGrammar.ValidTracePair
          (Action := Option T))
        (fun input :
          EncodedFirstOrderGrammar.TracePair (Option T) =>
          input.1.TraceEquivalent input.2.1 input.2.2)) :
    ComputablePredOnPromise
      (fun input : EquivalenceInput T => input.Valid)
      (fun input : EquivalenceInput T =>
        input.LanguageEquivalent) :=
  languageEquivalence_computablePredOnPromise_of_traceCompiler
    (equivalenceTracePair (T := T))
    (equivalenceTracePair_computable (T := T))
    equivalenceTracePair_valid equivalenceTracePair_traceEquivalent_iff
    traceEquivalence

/-- The standard encoded-DPDA presentation has computable language
equivalence as soon as valid translated first-order trace pairs have a
promise-computable trace-equivalence procedure. -/
public theorem dcf_computableEquivalence_of_traceEquivalence
    (traceEquivalence :
      ComputablePredOnPromise
        (EncodedFirstOrderGrammar.ValidTracePair
          (Action := Option T))
        (fun input :
          EncodedFirstOrderGrammar.TracePair (Option T) =>
          input.1.TraceEquivalent input.2.1 input.2.2)) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) :=
  ⟨language_characterizesOn, language_membershipSemiDecidable,
    languageEquivalence_computablePredOnPromise_of_traceEquivalence
      traceEquivalence⟩

/-- Final conditional leaf: complete bounded open-sound bases for valid
first-order grammars imply computable equivalence of deterministic
context-free languages in the concrete encoded-DPDA presentation. -/
public theorem dcf_computableEquivalence_of_completeOpenSoundBounds
    (complete : ∀ g :
      EncodedFirstOrderGrammar (Option T),
      g.WellFormed → g.HasCompleteOpenSoundBound) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) := by
  apply dcf_computableEquivalence_of_traceEquivalence
  exact
    DCFEquivalence.EncodedFirstOrderGrammar.traceEquivalence_computablePredOnPromise_of_completeOpenSoundBounds
      complete

/-- Final DPDA-equivalence endpoint for the witnessed regular stair interface
produced by the structured pivot construction and its marker-stable critical
counterpart. -/
public theorem
    dcf_computableEquivalence_of_witnessedAndMarkerStableStairBases
    (hstair : ∀ g :
      EncodedFirstOrderGrammar (Option T),
      g.WellFormed →
      ∃ queryWidth criticalWidth,
        g.HasWitnessedRegularActiveStairBase queryWidth ∧
          g.HasUniformMarkerStableWitnessedRegularActiveStairBase
            criticalWidth) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) := by
  apply dcf_computableEquivalence_of_traceEquivalence
  exact
    DCFEquivalence.EncodedFirstOrderGrammar.traceEquivalence_computablePredOnPromise_of_witnessedAndMarkerStableStairBases
      hstair

/-- Final compiler wiring from the root-syntactic critical-window theorem.

The premise is deliberately the one remaining grammar-level operational
statement: every exposing grammar admits a positive structured-pivot bound
whose marker-free trajectories have uniform root-syntactic finite windows.
The critical recurrence turns this into the sole marker-stable stair needed
by unified completeness, and the canonical compressed compiler then pulls
the resulting trace-equivalence procedure back to encoded DPDAs. -/
public theorem
    dcf_computableEquivalence_of_uniformMarkerStableRootFiniteWindowsOnExposing
    (hrootWindows : ∀ g :
      EncodedFirstOrderGrammar (Option T),
      g.WellFormed → ∀ hnormal : g.ExposingNormalForm,
      ∃ bound,
        g.exposureBound hnormal ≤ bound ∧
          g.HasUniformMarkerStableRootFiniteWindows bound) :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) := by
  apply dcf_computableEquivalence_of_traceCompiler
    (equivalenceExposingTracePair (T := T))
    (equivalenceExposingTracePair_computable (T := T))
    equivalenceExposingTracePair_valid
    equivalenceExposingTracePair_traceEquivalent_iff
  apply
    DCFEquivalence.EncodedFirstOrderGrammar.traceEquivalence_computablePredOnPromise_of_uniformMarkerStableStairBasesOnExposing
  intro g hg hnormal
  obtain ⟨bound, hexposureBound, hrootWindow⟩ :=
    hrootWindows g hg hnormal
  exact ⟨g.criticalDepthPrefixTailBound bound,
    g.hasUniformMarkerStableWitnessedRegularActiveStairBase_of_rootFiniteWindows
      hg hnormal hexposureBound hrootWindow⟩

/-- Language equivalence of encoded deterministic pushdown automata is
uniformly computable on the validity promise. -/
public theorem dcf_computableEquivalence :
    ComputableEquivalence DCF
      (language : EncodedDPDA T → Language T)
      (valid := Valid) := by
  apply
    dcf_computableEquivalence_of_uniformMarkerStableRootFiniteWindowsOnExposing
  intro g _hg hnormal
  let bound := g.exposureBound hnormal
  exact ⟨bound, le_rfl,
    g.hasUniformMarkerStableRootFiniteWindows bound
      (g.exposureBound_pos hnormal)⟩

end EncodedDPDA

end DCFEncodedDPDA
