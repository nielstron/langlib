module

public import Langlib.Classes.DeterministicContextFree.Basics.EncodedDPDA
public import Langlib.Automata.DeterministicPushdown.ClosureProperties.Complement
public import Langlib.Utilities.PromiseComputability
public import Langlib.Utilities.PrimrecHelpers
@[expose]
public section

/-!
# Uniform universality for finite encoded DPDAs

Universality of a promised-total DPDA is emptiness of the machine obtained by
flipping its final states.  Emptiness is decided here directly as pushdown
control-state reachability.  Input labels are erased: every finite path through
the resulting pushdown system spells a word, and every accepting run gives such
a path.

The executable analysis is a finite P-automaton saturation.  Rather than rely on
an unbounded semantic choice, it enumerates all subsets of the finite summary
triple space and intersects those closed under the pushdown rules.  This is a
deliberately simple (though exponential) implementation of the least saturated
relation.
-/

open PDA List

namespace DCFEncodedDPDA.EncodedDPDA

variable {T : Type} [Fintype T] [DecidableEq T]

/-! ## Raw finite saturation -/

/-- A stack-summary transition `(source control, stack symbol, target control)`.
The extra control index `numStates` is the P-automaton sink. -/
public abbrev SummaryTriple := ℕ × ℕ × ℕ

@[expose] public def pStateCount (c : EncodedDPDA T) : ℕ := c.numStates + 1
@[expose] public def sinkIndex (c : EncodedDPDA T) : ℕ := c.numStates

@[expose] public def normalizedFinals (c : EncodedDPDA T) : List ℕ :=
  c.finalIndices.map fun q => q % c.numStates

/-- A control index is a rejecting state of the original machine, hence a final
state of its complement. -/
@[expose] public def isRejectingIndex (c : EncodedDPDA T) (q : ℕ) : Bool :=
  decide (q < c.numStates ∧ q ∉ c.normalizedFinals)

@[expose] public def normalizedEpsilonSource (c : EncodedDPDA T) (r : EpsilonRow) : ℕ :=
  r.1 % c.numStates
@[expose] public def normalizedEpsilonTop (c : EncodedDPDA T) (r : EpsilonRow) : ℕ :=
  r.2.1 % c.numStackSymbols
@[expose] public def normalizedEpsilonTarget (c : EncodedDPDA T) (r : EpsilonRow) : ℕ :=
  r.2.2.1 % c.numStates
@[expose] public def normalizedEpsilonReplacement (c : EncodedDPDA T) (r : EpsilonRow) :
    List ℕ :=
  r.2.2.2.map fun Z => Z % c.numStackSymbols

@[expose] public def normalizedInputSource (c : EncodedDPDA T) (r : InputRow T) : ℕ :=
  r.1 % c.numStates
@[expose] public def normalizedInputTop (c : EncodedDPDA T) (r : InputRow T) : ℕ :=
  r.2.2.1 % c.numStackSymbols
@[expose] public def normalizedInputTarget (c : EncodedDPDA T) (r : InputRow T) : ℕ :=
  r.2.2.2.1 % c.numStates
@[expose] public def normalizedInputReplacement (c : EncodedDPDA T) (r : InputRow T) :
    List ℕ :=
  r.2.2.2.2.map fun Z => Z % c.numStackSymbols

/-- Does an epsilon table row have the same source and stack top as `r`? -/
@[expose] public def sameEpsilonKey (c : EncodedDPDA T) (r s : EpsilonRow) : Bool :=
  decide (c.normalizedEpsilonSource s = c.normalizedEpsilonSource r ∧
    c.normalizedEpsilonTop s = c.normalizedEpsilonTop r)

/-- Does an input table row have the same source, letter, and stack top as `r`? -/
@[expose] public def sameInputKey (c : EncodedDPDA T) (r s : InputRow T) : Bool :=
  decide (c.normalizedInputSource s = c.normalizedInputSource r ∧
    s.2.1 = r.2.1 ∧ c.normalizedInputTop s = c.normalizedInputTop r)

/-- Epsilon rows actually selected by first-match decoding. -/
@[expose] public def effectiveEpsilonRows (c : EncodedDPDA T) : List EpsilonRow :=
  c.epsilonRows.filter fun r =>
    decide (c.epsilonRows.find? (c.sameEpsilonKey r) = some r)

/-- Input rows actually selected by first-match decoding.  Epsilon priority is
included in the filter. -/
@[expose] public def effectiveInputRows (c : EncodedDPDA T) : List (InputRow T) :=
  c.inputRows.filter fun r =>
    decide (c.epsilonRows.find? (fun s => decide
      (c.normalizedEpsilonSource s = c.normalizedInputSource r ∧
        c.normalizedEpsilonTop s = c.normalizedInputTop r)) = none ∧
      c.inputRows.find? (c.sameInputKey r) = some r)

/-- Every possible finite P-automaton summary triple. -/
@[expose] public def allSummaryTriples (c : EncodedDPDA T) : List SummaryTriple :=
  (List.range c.pStateCount).flatMap fun p =>
    (List.range c.numStackSymbols).flatMap fun Z =>
      (List.range c.pStateCount).map fun r => (p, Z, r)

/-- Base summaries: the sink consumes arbitrary stack suffixes, and every rejecting
control state can jump to the sink. -/
@[expose] public def baseSummaryTriples (c : EncodedDPDA T) : List SummaryTriple :=
  c.allSummaryTriples.filter fun t =>
    decide ((t.1 = c.sinkIndex ∧ t.2.2 = c.sinkIndex) ∨
      (c.isRejectingIndex t.1 = true ∧ t.2.2 = c.sinkIndex))

/-- Advance a finite set of P-automaton controls across one stack symbol. -/
@[expose] public def advanceSummaryStates (c : EncodedDPDA T)
    (R : List SummaryTriple) (states : List ℕ) (Z : ℕ) : List ℕ :=
  (List.range c.pStateCount).filter fun middle =>
    states.any fun p => decide ((p, Z % c.numStackSymbols, middle) ∈ R)

/-- Controls reachable after reading a stack word top-to-bottom. -/
@[expose] public def summaryDestinations (c : EncodedDPDA T)
    (R : List SummaryTriple) (states : List ℕ) (gamma : List ℕ) : List ℕ :=
  gamma.foldl (c.advanceSummaryStates R) states

/-- Test for a path through a candidate summary relation, reading a stack word
top-to-bottom. -/
@[expose] public def summaryPath (c : EncodedDPDA T) (R : List SummaryTriple)
    (p : ℕ) (gamma : List ℕ) (r : ℕ) : Bool :=
  decide (r ∈ c.summaryDestinations R [p] gamma)

/-- A finite candidate relation contains the base and is closed under every
effective pushdown transition. -/
@[expose] public def summaryClosed (c : EncodedDPDA T) (R : List SummaryTriple) : Bool :=
  ((c.baseSummaryTriples.all fun t => decide (t ∈ R)) &&
    (c.effectiveEpsilonRows.all fun row =>
    (List.range c.pStateCount).all fun r =>
      decide (c.summaryPath R (c.normalizedEpsilonTarget row)
          (c.normalizedEpsilonReplacement row) r = true →
        (c.normalizedEpsilonSource row,
          c.normalizedEpsilonTop row, r) ∈ R))) &&
  (c.effectiveInputRows.all fun row =>
    (List.range c.pStateCount).all fun r =>
      decide (c.summaryPath R (c.normalizedInputTarget row)
          (c.normalizedInputReplacement row) r = true →
        (c.normalizedInputSource row,
          c.normalizedInputTop row, r) ∈ R))

/-- The least closed summary relation, computed as the intersection of all closed
subsets of the finite triple space. -/
@[expose] public def leastSummaryRelation (c : EncodedDPDA T) : List SummaryTriple :=
  c.allSummaryTriples.filter fun t =>
    c.allSummaryTriples.sublists.all fun R =>
      !c.summaryClosed R || decide (t ∈ R)

/-- Does the erased pushdown system reach a rejecting control state? -/
@[expose] public def hasRejectingReach (c : EncodedDPDA T) : Bool :=
  (List.range c.pStateCount).any fun r =>
    c.summaryPath c.leastSummaryRelation
      (c.initialIndex % c.numStates)
      [c.startIndex % c.numStackSymbols] r &&
      (decide (r = c.sinkIndex) || c.isRejectingIndex r)

/-- Executable universality test for a promised-total encoded DPDA. -/
@[expose] public def checkUniversal (c : EncodedDPDA T) : Bool :=
  !c.hasRejectingReach

/-! ## Logical specification of the finite saturation -/

/-- Propositional path semantics of `summaryPath`. -/
public inductive RawSummaryPath (c : EncodedDPDA T) (R : List SummaryTriple) :
    ℕ → List ℕ → ℕ → Prop
  | nil (p) : RawSummaryPath c R p [] p
  | cons {p middle r Z gamma} :
      middle < c.pStateCount →
      (p, Z % c.numStackSymbols, middle) ∈ R →
      RawSummaryPath c R middle gamma r →
      RawSummaryPath c R p (Z :: gamma) r

namespace RawSummaryPath

public theorem mono {c : EncodedDPDA T} {R S : List SummaryTriple}
    (hsub : ∀ t, t ∈ R → t ∈ S)
    {p gamma r} (h : RawSummaryPath c R p gamma r) :
    RawSummaryPath c S p gamma r := by
  induction h with
  | nil p => exact .nil p
  | cons hmiddle hstep _ ih => exact .cons hmiddle (hsub _ hstep) ih

end RawSummaryPath

/-- Propositional closure condition corresponding to `summaryClosed`. -/
@[expose] public def RawSummaryClosed (c : EncodedDPDA T)
    (R : List SummaryTriple) : Prop :=
  (∀ t ∈ c.baseSummaryTriples, t ∈ R) ∧
  (∀ row ∈ c.effectiveEpsilonRows, ∀ r < c.pStateCount,
    RawSummaryPath c R (c.normalizedEpsilonTarget row)
      (c.normalizedEpsilonReplacement row) r →
    (c.normalizedEpsilonSource row, c.normalizedEpsilonTop row, r) ∈ R) ∧
  (∀ row ∈ c.effectiveInputRows, ∀ r < c.pStateCount,
    RawSummaryPath c R (c.normalizedInputTarget row)
      (c.normalizedInputReplacement row) r →
    (c.normalizedInputSource row, c.normalizedInputTop row, r) ∈ R)

public theorem mem_allSummaryTriples_iff (c : EncodedDPDA T)
    (p Z r : ℕ) :
    (p, Z, r) ∈ c.allSummaryTriples ↔
      p < c.pStateCount ∧ Z < c.numStackSymbols ∧ r < c.pStateCount := by
  simp [allSummaryTriples]

private theorem mem_summaryDestinations_iff (c : EncodedDPDA T)
    (R : List SummaryTriple) (states : List ℕ) (gamma : List ℕ) (r : ℕ) :
    r ∈ c.summaryDestinations R states gamma ↔
      ∃ p ∈ states, RawSummaryPath c R p gamma r := by
  induction gamma generalizing states with
  | nil =>
      simp only [summaryDestinations, List.foldl_nil]
      constructor
      · intro hr
        exact ⟨r, hr, .nil r⟩
      · rintro ⟨p, hp, hpath⟩
        cases hpath
        exact hp
  | cons Z gamma ih =>
      change r ∈ c.summaryDestinations R
          (c.advanceSummaryStates R states Z) gamma ↔ _
      rw [ih]
      constructor
      · rintro ⟨middle, hmiddle, hrest⟩
        have hfiltered := List.mem_filter.mp hmiddle
        have hmiddleLt : middle < c.pStateCount :=
          List.mem_range.mp hfiltered.1
        obtain ⟨p, hp, hstep⟩ := List.any_eq_true.mp hfiltered.2
        exact ⟨p, hp, .cons hmiddleLt (by simpa using hstep) hrest⟩
      · rintro ⟨p, hp, hpath⟩
        cases hpath with
        | cons hmiddle hstep hrest =>
            refine ⟨_, List.mem_filter.mpr ⟨List.mem_range.mpr hmiddle, ?_⟩,
              hrest⟩
            exact List.any_eq_true.mpr ⟨p, hp, by simpa using hstep⟩

public theorem summaryPath_eq_true_iff (c : EncodedDPDA T)
    (R : List SummaryTriple) (p : ℕ) (gamma : List ℕ) (r : ℕ) :
    c.summaryPath R p gamma r = true ↔ RawSummaryPath c R p gamma r := by
  rw [summaryPath, decide_eq_true_eq,
    mem_summaryDestinations_iff]
  constructor
  · rintro ⟨q, hq, hpath⟩
    simp only [List.mem_singleton] at hq
    subst q
    exact hpath
  · intro hpath
    exact ⟨p, by simp, hpath⟩

public theorem summaryClosed_eq_true_iff (c : EncodedDPDA T)
    (R : List SummaryTriple) :
    c.summaryClosed R = true ↔ RawSummaryClosed c R := by
  simp only [summaryClosed, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hbase, hepsilon⟩, hinput⟩
    refine ⟨hbase, ?_, ?_⟩
    · intro row hrow r hr hpath
      have h := hepsilon row hrow r (List.mem_range.mpr hr)
      exact h ((summaryPath_eq_true_iff c R _ _ _).mpr hpath)
    · intro row hrow r hr hpath
      have h := hinput row hrow r (List.mem_range.mpr hr)
      exact h ((summaryPath_eq_true_iff c R _ _ _).mpr hpath)
  · rintro ⟨hbase, hepsilon, hinput⟩
    refine ⟨⟨hbase, ?_⟩, ?_⟩
    · intro row hrow r hr hpath
      exact hepsilon row hrow r (List.mem_range.mp hr)
        ((summaryPath_eq_true_iff c R _ _ _).mp hpath)
    · intro row hrow r hr hpath
      exact hinput row hrow r (List.mem_range.mp hr)
        ((summaryPath_eq_true_iff c R _ _ _).mp hpath)

public theorem mem_leastSummaryRelation_iff (c : EncodedDPDA T)
    (t : SummaryTriple) :
    t ∈ c.leastSummaryRelation ↔
      t ∈ c.allSummaryTriples ∧
      ∀ R : List SummaryTriple, R <+ c.allSummaryTriples →
        RawSummaryClosed c R → t ∈ R := by
  simp only [leastSummaryRelation, List.mem_filter, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true, decide_eq_true_eq,
    List.mem_sublists]
  constructor
  · rintro ⟨hall, hleast⟩
    refine ⟨hall, ?_⟩
    intro R hsub hclosed
    have h := hleast R hsub
    have hc : c.summaryClosed R = true :=
      (summaryClosed_eq_true_iff c R).mpr hclosed
    exact h.resolve_left (by simpa [hc])
  · rintro ⟨hall, hleast⟩
    refine ⟨hall, ?_⟩
    intro R hsub
    by_cases hclosed : RawSummaryClosed c R
    · exact Or.inr (hleast R hsub hclosed)
    · left
      have hc : c.summaryClosed R ≠ true := fun h =>
        hclosed ((summaryClosed_eq_true_iff c R).mp h)
      exact Bool.eq_true_of_not_eq_false (by
        intro hfalse
        cases hs : c.summaryClosed R <;> simp_all)

private theorem epsilonSummary_mem_all (c : EncodedDPDA T)
    (row : EpsilonRow) {r : ℕ} (hr : r < c.pStateCount) :
    (c.normalizedEpsilonSource row, c.normalizedEpsilonTop row, r) ∈
      c.allSummaryTriples := by
  rw [mem_allSummaryTriples_iff]
  refine ⟨?_, ?_, hr⟩
  · exact (Nat.mod_lt _ c.numStates_pos).trans (by simp [pStateCount])
  · exact Nat.mod_lt _ c.numStackSymbols_pos

private theorem inputSummary_mem_all (c : EncodedDPDA T)
    (row : InputRow T) {r : ℕ} (hr : r < c.pStateCount) :
    (c.normalizedInputSource row, c.normalizedInputTop row, r) ∈
      c.allSummaryTriples := by
  rw [mem_allSummaryTriples_iff]
  refine ⟨?_, ?_, hr⟩
  · exact (Nat.mod_lt _ c.numStates_pos).trans (by simp [pStateCount])
  · exact Nat.mod_lt _ c.numStackSymbols_pos

public theorem allSummaryTriples_closed (c : EncodedDPDA T) :
    RawSummaryClosed c c.allSummaryTriples := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (List.mem_filter.mp ht).1
  · intro row _ r hr _
    exact epsilonSummary_mem_all c row hr
  · intro row _ r hr _
    exact inputSummary_mem_all c row hr

/-- The computed intersection is itself closed. -/
public theorem leastSummaryRelation_closed (c : EncodedDPDA T) :
    RawSummaryClosed c c.leastSummaryRelation := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    apply (mem_leastSummaryRelation_iff c t).2
    refine ⟨(List.mem_filter.mp ht).1, ?_⟩
    intro R hsub hclosed
    exact hclosed.1 t ht
  · intro row hrow r hr hpath
    apply (mem_leastSummaryRelation_iff c _).2
    refine ⟨epsilonSummary_mem_all c row hr, ?_⟩
    intro R hsub hclosed
    exact hclosed.2.1 row hrow r hr
      (hpath.mono fun t ht =>
        (mem_leastSummaryRelation_iff c t).1 ht |>.2 R hsub hclosed)
  · intro row hrow r hr hpath
    apply (mem_leastSummaryRelation_iff c _).2
    refine ⟨inputSummary_mem_all c row hr, ?_⟩
    intro R hsub hclosed
    exact hclosed.2.2 row hrow r hr
      (hpath.mono fun t ht =>
        (mem_leastSummaryRelation_iff c t).1 ht |>.2 R hsub hclosed)

/-- The computed relation is contained in every propositionally closed relation,
even when that relation is not already represented as a sublist of the canonical
triple enumeration. -/
public theorem leastSummaryRelation_minimal (c : EncodedDPDA T)
    {R : List SummaryTriple} (hclosed : RawSummaryClosed c R)
    {t : SummaryTriple} (ht : t ∈ c.leastSummaryRelation) : t ∈ R := by
  let canonical := c.allSummaryTriples.filter fun u => decide (u ∈ R)
  have hsub : canonical <+ c.allSummaryTriples := List.filter_sublist
  have hcanonical : RawSummaryClosed c canonical := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      exact List.mem_filter.mpr ⟨(List.mem_filter.mp hu).1, by
        simpa using hclosed.1 u hu⟩
    · intro row hrow r hr hpath
      have hpathR : RawSummaryPath c R (c.normalizedEpsilonTarget row)
          (c.normalizedEpsilonReplacement row) r :=
        hpath.mono fun u hu => by simpa using (List.mem_filter.mp hu).2
      exact List.mem_filter.mpr ⟨epsilonSummary_mem_all c row hr,
        by simpa using hclosed.2.1 row hrow r hr hpathR⟩
    · intro row hrow r hr hpath
      have hpathR : RawSummaryPath c R (c.normalizedInputTarget row)
          (c.normalizedInputReplacement row) r :=
        hpath.mono fun u hu => by simpa using (List.mem_filter.mp hu).2
      exact List.mem_filter.mpr ⟨inputSummary_mem_all c row hr,
        by simpa using hclosed.2.2 row hrow r hr hpathR⟩
  have hmemCanonical :=
    (mem_leastSummaryRelation_iff c t).1 ht |>.2 canonical hsub hcanonical
  simpa using (List.mem_filter.mp hmemCanonical).2

/-! ## Effective rows and decoded transitions -/

@[simp] theorem state_normalized (c : EncodedDPDA T) (q : ℕ) :
    c.state (q % c.numStates) = c.state q := by
  apply Fin.ext
  simp only [state, Fin.val_mk, Nat.mod_mod]

@[simp] theorem stackSymbol_normalized (c : EncodedDPDA T) (Z : ℕ) :
    c.stackSymbol (Z % c.numStackSymbols) = c.stackSymbol Z := by
  apply Fin.ext
  simp only [stackSymbol, Fin.val_mk, Nat.mod_mod]

@[simp] theorem replacement_normalized (c : EncodedDPDA T) (beta : List ℕ) :
    c.replacement (beta.map fun Z => Z % c.numStackSymbols) =
      c.replacement beta := by
  simp only [replacement, List.map_map, Function.comp_def,
    stackSymbol_normalized]

public theorem effectiveEpsilonRow_transition (c : EncodedDPDA T)
    {row : EpsilonRow} (hrow : row ∈ c.effectiveEpsilonRows) :
    c.toDPDA.epsilon_transition
        (c.state (c.normalizedEpsilonSource row))
        (c.stackSymbol (c.normalizedEpsilonTop row)) =
      some (c.state (c.normalizedEpsilonTarget row),
        c.replacement (c.normalizedEpsilonReplacement row)) := by
  obtain ⟨_, hselected⟩ := List.mem_filter.mp hrow
  simp only [decide_eq_true_eq] at hselected
  change c.epsilonLookup _ _ = _
  unfold epsilonLookup
  have hpred : (fun s : EpsilonRow =>
      decide (s.1 % c.numStates = (c.state (c.normalizedEpsilonSource row)).val ∧
        s.2.1 % c.numStackSymbols =
          (c.stackSymbol (c.normalizedEpsilonTop row)).val)) =
      c.sameEpsilonKey row := by
    funext s
    simp only [sameEpsilonKey, normalizedEpsilonSource, normalizedEpsilonTop,
      state, stackSymbol, Fin.val_mk, Nat.mod_mod]
  rw [hpred, hselected]
  simp only [Option.map_some, normalizedEpsilonTarget,
    normalizedEpsilonReplacement, state_normalized, replacement_normalized]

public theorem effectiveInputRow_transition (c : EncodedDPDA T)
    {row : InputRow T} (hrow : row ∈ c.effectiveInputRows) :
    c.toDPDA.transition
        (c.state (c.normalizedInputSource row)) row.2.1
        (c.stackSymbol (c.normalizedInputTop row)) =
      some (c.state (c.normalizedInputTarget row),
        c.replacement (c.normalizedInputReplacement row)) := by
  obtain ⟨_, hselected⟩ := List.mem_filter.mp hrow
  simp only [decide_eq_true_eq] at hselected
  obtain ⟨hepsilon, hinput⟩ := hselected
  change (if (c.epsilonLookup _ _).isSome then none else c.inputLookup _ _ _) = _
  have hεpred : (fun s : EpsilonRow => decide
      (c.normalizedEpsilonSource s = c.normalizedInputSource row ∧
        c.normalizedEpsilonTop s = c.normalizedInputTop row)) =
      (fun s : EpsilonRow => decide
        (s.1 % c.numStates = (c.state (c.normalizedInputSource row)).val ∧
          s.2.1 % c.numStackSymbols =
            (c.stackSymbol (c.normalizedInputTop row)).val)) := by
    funext s
    simp only [normalizedEpsilonSource, normalizedInputSource,
      normalizedEpsilonTop, normalizedInputTop, state, stackSymbol,
      Fin.val_mk, Nat.mod_mod]
  have hepsilonLookup : c.epsilonLookup
      (c.state (c.normalizedInputSource row))
      (c.stackSymbol (c.normalizedInputTop row)) = none := by
    unfold epsilonLookup
    rw [← hεpred, hepsilon]
    rfl
  rw [hepsilonLookup]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false]
  unfold inputLookup
  have hipred : (fun s : InputRow T => decide
      (s.1 % c.numStates = (c.state (c.normalizedInputSource row)).val ∧
        s.2.1 = row.2.1 ∧ s.2.2.1 % c.numStackSymbols =
          (c.stackSymbol (c.normalizedInputTop row)).val)) =
      c.sameInputKey row := by
    funext s
    simp only [sameInputKey, normalizedInputSource, normalizedInputTop,
      state, stackSymbol, Fin.val_mk, Nat.mod_mod]
  rw [hipred, hinput]
  simp only [Option.map_some, normalizedInputTarget,
    normalizedInputReplacement, state_normalized, replacement_normalized]

/-- Every defined decoded epsilon transition comes from an effective table row. -/
public theorem exists_effectiveEpsilonRow_of_transition (c : EncodedDPDA T)
    {q : Fin c.numStates} {Z : Fin c.numStackSymbols}
    {p : Fin c.numStates} {beta : List (Fin c.numStackSymbols)}
    (htransition : c.toDPDA.epsilon_transition q Z = some (p, beta)) :
    ∃ row ∈ c.effectiveEpsilonRows,
      c.normalizedEpsilonSource row = q.val ∧
      c.normalizedEpsilonTop row = Z.val ∧
      c.state (c.normalizedEpsilonTarget row) = p ∧
      c.replacement (c.normalizedEpsilonReplacement row) = beta := by
  change c.epsilonLookup q Z = some (p, beta) at htransition
  unfold epsilonLookup at htransition
  rw [Option.map_eq_some_iff] at htransition
  obtain ⟨row, hfind, hout⟩ := htransition
  have hrow : row ∈ c.epsilonRows := List.mem_of_find?_eq_some hfind
  have hmatch := List.find?_some hfind
  simp only [decide_eq_true_eq] at hmatch
  have hpred : c.sameEpsilonKey row = (fun s : EpsilonRow => decide
      (s.1 % c.numStates = q.val ∧
        s.2.1 % c.numStackSymbols = Z.val)) := by
    funext s
    simp [sameEpsilonKey, normalizedEpsilonSource, normalizedEpsilonTop,
      hmatch]
  have hselected : c.epsilonRows.find? (c.sameEpsilonKey row) = some row := by
    rw [hpred]
    exact hfind
  refine ⟨row, List.mem_filter.mpr ⟨hrow, ?_⟩,
    hmatch.1, hmatch.2, ?_⟩
  · simp [hselected]
  · simpa [normalizedEpsilonTarget, normalizedEpsilonReplacement] using hout

/-- Every defined decoded input transition comes from an effective table row. -/
public theorem exists_effectiveInputRow_of_transition (c : EncodedDPDA T)
    {q : Fin c.numStates} {a : T} {Z : Fin c.numStackSymbols}
    {p : Fin c.numStates} {beta : List (Fin c.numStackSymbols)}
    (htransition : c.toDPDA.transition q a Z = some (p, beta)) :
    ∃ row ∈ c.effectiveInputRows,
      c.normalizedInputSource row = q.val ∧ row.2.1 = a ∧
      c.normalizedInputTop row = Z.val ∧
      c.state (c.normalizedInputTarget row) = p ∧
      c.replacement (c.normalizedInputReplacement row) = beta := by
  change (if (c.epsilonLookup q Z).isSome then none
    else c.inputLookup q a Z) = some (p, beta) at htransition
  cases hepsilon : c.epsilonLookup q Z with
  | some out => simp [hepsilon] at htransition
  | none =>
      simp only [hepsilon, Option.isSome_none, Bool.false_eq_true, if_false]
        at htransition
      unfold inputLookup at htransition
      rw [Option.map_eq_some_iff] at htransition
      obtain ⟨row, hfind, hout⟩ := htransition
      have hrow : row ∈ c.inputRows := List.mem_of_find?_eq_some hfind
      have hmatch := List.find?_some hfind
      simp only [decide_eq_true_eq] at hmatch
      have hinputPred : c.sameInputKey row = (fun s : InputRow T => decide
          (s.1 % c.numStates = q.val ∧ s.2.1 = a ∧
            s.2.2.1 % c.numStackSymbols = Z.val)) := by
        funext s
        simp [sameInputKey, normalizedInputSource, normalizedInputTop, hmatch]
      have hinputSelected : c.inputRows.find? (c.sameInputKey row) = some row := by
        rw [hinputPred]
        exact hfind
      unfold epsilonLookup at hepsilon
      rw [Option.map_eq_none_iff] at hepsilon
      have hepsilonPred : (fun s : EpsilonRow => decide
          (c.normalizedEpsilonSource s = c.normalizedInputSource row ∧
            c.normalizedEpsilonTop s = c.normalizedInputTop row)) =
          (fun s : EpsilonRow => decide
            (s.1 % c.numStates = q.val ∧
              s.2.1 % c.numStackSymbols = Z.val)) := by
        funext s
        simp [normalizedEpsilonSource, normalizedInputSource,
          normalizedEpsilonTop, normalizedInputTop, hmatch]
      have hepsilonSelected : c.epsilonRows.find? (fun s : EpsilonRow => decide
          (c.normalizedEpsilonSource s = c.normalizedInputSource row ∧
            c.normalizedEpsilonTop s = c.normalizedInputTop row)) = none := by
        rw [hepsilonPred]
        exact hepsilon
      refine ⟨row, List.mem_filter.mpr ⟨hrow, ?_⟩,
        hmatch.1, hmatch.2.1, hmatch.2.2, ?_⟩
      · rw [decide_eq_true_eq]
        exact ⟨hepsilonSelected, hinputSelected⟩
      · simpa [normalizedInputTarget, normalizedInputReplacement] using hout

/-! ## Correctness of saturation for the erased pushdown system -/

/-- One move of the finite pushdown system obtained by erasing the input label
from every effective decoded transition. -/
public inductive RawErasedStep (c : EncodedDPDA T) :
    (ℕ × List ℕ) → (ℕ × List ℕ) → Prop
  | epsilon {row : EpsilonRow} {suffix : List ℕ}
      (hrow : row ∈ c.effectiveEpsilonRows) :
      RawErasedStep c
        (c.normalizedEpsilonSource row,
          c.normalizedEpsilonTop row :: suffix)
        (c.normalizedEpsilonTarget row,
          c.normalizedEpsilonReplacement row ++ suffix)
  | input {row : InputRow T} {suffix : List ℕ}
      (hrow : row ∈ c.effectiveInputRows) :
      RawErasedStep c
        (c.normalizedInputSource row,
          c.normalizedInputTop row :: suffix)
        (c.normalizedInputTarget row,
          c.normalizedInputReplacement row ++ suffix)

/-- Reflexive-transitive reachability in the input-erased pushdown system. -/
public abbrev RawErasedReaches (c : EncodedDPDA T) :=
  Relation.ReflTransGen c.RawErasedStep

/-- A P-automaton control is a target when it is the auxiliary sink, or when
the erased pushdown system can reach a rejecting control of the original DPDA. -/
@[expose] public def RawTarget (c : EncodedDPDA T) (q : ℕ)
    (gamma : List ℕ) : Prop :=
  q = c.sinkIndex ∨
    ∃ p delta, c.RawErasedReaches (q, gamma) (p, delta) ∧
      c.isRejectingIndex p = true

/-- Semantic meaning of a summary edge. -/
@[expose] public def RawSummarySemantic (c : EncodedDPDA T)
    (t : SummaryTriple) : Prop :=
  ∀ suffix, c.RawTarget t.2.2 suffix →
    c.RawTarget t.1 (t.2.1 :: suffix)

namespace RawSummaryPath

/-- Split a summary path after an initial segment of its stack word. -/
public theorem of_append_left {c : EncodedDPDA T} {R : List SummaryTriple}
    {p r : ℕ} {gamma delta : List ℕ}
    (h : RawSummaryPath c R p (gamma ++ delta) r) :
    ∃ middle, RawSummaryPath c R p gamma middle ∧
      RawSummaryPath c R middle delta r := by
  induction gamma generalizing p with
  | nil => exact ⟨p, .nil p, by simpa using h⟩
  | cons Z gamma ih =>
      cases h with
      | cons hmiddle hstep hrest =>
          obtain ⟨middle', hprefix, hsuffix⟩ := ih hrest
          exact ⟨middle', .cons hmiddle hstep hprefix, hsuffix⟩

/-- The endpoint of a summary path is a P-automaton state whenever its start is. -/
public theorem end_lt {c : EncodedDPDA T} {R : List SummaryTriple}
    {p r : ℕ} {gamma : List ℕ}
    (h : RawSummaryPath c R p gamma r) (hp : p < c.pStateCount) :
    r < c.pStateCount := by
  induction h with
  | nil => exact hp
  | cons hmiddle _ _ ih => exact ih hmiddle

/-- A path of semantically valid summaries preserves the target predicate. -/
public theorem preservesTarget {c : EncodedDPDA T} {R : List SummaryTriple}
    (hsemantic : ∀ t ∈ R, c.RawSummarySemantic t)
    {p r : ℕ} {gamma suffix : List ℕ}
    (hpath : RawSummaryPath c R p gamma r)
    (htarget : c.RawTarget r suffix) :
    c.RawTarget p
      (gamma.map (fun Z => Z % c.numStackSymbols) ++ suffix) := by
  induction hpath with
  | nil => simpa using htarget
  | @cons p middle r Z gamma _ hstep _ ih =>
      have hmiddleTarget : c.RawTarget middle
          (gamma.map (fun Z => Z % c.numStackSymbols) ++ suffix) := ih htarget
      simpa using hsemantic (p, Z % c.numStackSymbols, middle) hstep
        (gamma.map (fun Z => Z % c.numStackSymbols) ++ suffix) hmiddleTarget

end RawSummaryPath

private theorem rawTarget_of_rejecting (c : EncodedDPDA T)
    {q : ℕ} {gamma : List ℕ} (hq : c.isRejectingIndex q = true) :
    c.RawTarget q gamma := by
  right
  exact ⟨q, gamma, Relation.ReflTransGen.refl, hq⟩

private theorem rawTarget_of_step (c : EncodedDPDA T)
    {x y : ℕ × List ℕ} (hstep : c.RawErasedStep x y)
    (htarget : c.RawTarget y.1 y.2) : c.RawTarget x.1 x.2 := by
  rcases htarget with hsink | ⟨p, delta, hreach, hp⟩
  · exfalso
    cases hstep with
    | @epsilon row suffix hrow =>
        have hlt := Nat.mod_lt row.2.2.1 c.numStates_pos
        apply (Nat.ne_of_lt hlt)
        simpa [normalizedEpsilonTarget, sinkIndex] using hsink
    | @input row suffix hrow =>
        have hlt := Nat.mod_lt row.2.2.2.1 c.numStates_pos
        apply (Nat.ne_of_lt hlt)
        simpa [normalizedInputTarget, sinkIndex] using hsink
  · right
    exact ⟨p, delta, Relation.ReflTransGen.head hstep hreach, hp⟩

/-- Every edge in the computed least relation has its intended reachability
meaning. -/
public theorem leastSummaryRelation_semantic (c : EncodedDPDA T)
    {t : SummaryTriple} (ht : t ∈ c.leastSummaryRelation) :
    c.RawSummarySemantic t := by
  classical
  let semanticRelation := c.allSummaryTriples.filter fun u =>
    c.RawSummarySemantic u
  have hclosed : RawSummaryClosed c semanticRelation := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have hall := (List.mem_filter.mp hu).1
      refine List.mem_filter.mpr ⟨hall, ?_⟩
      rw [decide_eq_true_eq]
      rcases u with ⟨p, Z, r⟩
      have hbase := (List.mem_filter.mp hu).2
      simp only [decide_eq_true_eq] at hbase
      intro suffix _
      rcases hbase with ⟨rfl, rfl⟩ | ⟨hreject, rfl⟩
      · exact Or.inl rfl
      · exact rawTarget_of_rejecting c hreject
    · intro row hrow r hr hpath
      refine List.mem_filter.mpr ⟨epsilonSummary_mem_all c row hr, ?_⟩
      rw [decide_eq_true_eq]
      intro suffix htarget
      have htarget' := hpath.preservesTarget
        (fun u hu => of_decide_eq_true (List.mem_filter.mp hu).2) htarget
      apply rawTarget_of_step c (.epsilon hrow)
      simpa [normalizedEpsilonReplacement, List.map_map, Function.comp_def,
        Nat.mod_mod, List.append_assoc] using htarget'
    · intro row hrow r hr hpath
      refine List.mem_filter.mpr ⟨inputSummary_mem_all c row hr, ?_⟩
      rw [decide_eq_true_eq]
      intro suffix htarget
      have htarget' := hpath.preservesTarget
        (fun u hu => of_decide_eq_true (List.mem_filter.mp hu).2) htarget
      apply rawTarget_of_step c (.input hrow)
      simpa [normalizedInputReplacement, List.map_map, Function.comp_def,
        Nat.mod_mod, List.append_assoc] using htarget'
  have hmem := leastSummaryRelation_minimal c hclosed ht
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

private theorem sink_summary_path (c : EncodedDPDA T) (gamma : List ℕ) :
    RawSummaryPath c c.leastSummaryRelation c.sinkIndex gamma c.sinkIndex := by
  induction gamma with
  | nil => exact .nil c.sinkIndex
  | cons Z gamma ih =>
      refine .cons (by simp [pStateCount, sinkIndex]) ?_ ih
      apply (leastSummaryRelation_closed c).1
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · rw [mem_allSummaryTriples_iff]
        exact ⟨by simp [pStateCount, sinkIndex], Nat.mod_lt _ c.numStackSymbols_pos,
          by simp [pStateCount, sinkIndex]⟩
      · simp [sinkIndex]

private theorem rejecting_summary_path (c : EncodedDPDA T)
    {q : ℕ} (gamma : List ℕ) (hq : c.isRejectingIndex q = true) :
    ∃ r, (r = c.sinkIndex ∨ c.isRejectingIndex r = true) ∧
      RawSummaryPath c c.leastSummaryRelation q gamma r := by
  cases gamma with
  | nil => exact ⟨q, Or.inr hq, .nil q⟩
  | cons Z gamma =>
      refine ⟨c.sinkIndex, Or.inl rfl, .cons ?_ ?_ (sink_summary_path c gamma)⟩
      · simp [pStateCount, sinkIndex]
      · apply (leastSummaryRelation_closed c).1
        apply List.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · rw [mem_allSummaryTriples_iff]
          simp [isRejectingIndex] at hq
          exact ⟨hq.1.trans (by simp [pStateCount]),
            Nat.mod_lt _ c.numStackSymbols_pos, by simp [pStateCount, sinkIndex]⟩
        · simp [hq]

/-- An erased run to a rejecting state yields a path in the computed summary
relation. -/
public theorem summaryPath_of_rawErasedReaches (c : EncodedDPDA T)
    {q p : ℕ} {gamma delta : List ℕ}
    (hreach : c.RawErasedReaches (q, gamma) (p, delta))
    (hp : c.isRejectingIndex p = true) :
    ∃ r, (r = c.sinkIndex ∨ c.isRejectingIndex r = true) ∧
      RawSummaryPath c c.leastSummaryRelation q gamma r := by
  have main : ∀ {x y : ℕ × List ℕ}, c.RawErasedReaches x y →
      c.isRejectingIndex y.1 = true →
      ∃ r, (r = c.sinkIndex ∨ c.isRejectingIndex r = true) ∧
        RawSummaryPath c c.leastSummaryRelation x.1 x.2 r := by
    intro x y hreach hy
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact rejecting_summary_path c y.2 hy
    | @head x y hstep hrest ih =>
        obtain ⟨r, hr, hpath⟩ := ih
        cases hstep with
        | @epsilon row suffix hrow =>
            obtain ⟨middle, hreplacement, hsuffix⟩ :=
              hpath.of_append_left
            have hmiddle : middle < c.pStateCount :=
              hreplacement.end_lt ((Nat.mod_lt _ c.numStates_pos).trans
                (by simp [pStateCount]))
            refine ⟨r, hr, .cons hmiddle ?_ hsuffix⟩
            simpa [normalizedEpsilonTop, Nat.mod_mod] using
              (leastSummaryRelation_closed c).2.1 row hrow middle hmiddle hreplacement
        | @input row suffix hrow =>
            obtain ⟨middle, hreplacement, hsuffix⟩ :=
              hpath.of_append_left
            have hmiddle : middle < c.pStateCount :=
              hreplacement.end_lt ((Nat.mod_lt _ c.numStates_pos).trans
                (by simp [pStateCount]))
            refine ⟨r, hr, .cons hmiddle ?_ hsuffix⟩
            simpa [normalizedInputTop, Nat.mod_mod] using
              (leastSummaryRelation_closed c).2.2 row hrow middle hmiddle hreplacement
  exact main hreach hp

/-- The executable saturation test is exactly erased reachability of a rejecting
control from the initial pushdown configuration. -/
public theorem hasRejectingReach_eq_true_iff (c : EncodedDPDA T) :
    c.hasRejectingReach = true ↔
      ∃ p delta,
        c.RawErasedReaches
          (c.initialIndex % c.numStates, [c.startIndex % c.numStackSymbols])
          (p, delta) ∧ c.isRejectingIndex p = true := by
  simp only [hasRejectingReach, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    summaryPath_eq_true_iff]
  constructor
  · rintro ⟨r, hr, hpath, hsink | hreject⟩
    · have htarget : c.RawTarget r [] := Or.inl hsink
      have hinitial := hpath.preservesTarget
        (fun t ht => leastSummaryRelation_semantic c ht) htarget
      have hinitial' : c.RawTarget
          (c.initialIndex % c.numStates)
          [c.startIndex % c.numStackSymbols] := by
        simpa [Nat.mod_mod] using hinitial
      rcases hinitial' with hinitialSink | hreach
      · have hlt := Nat.mod_lt c.initialIndex c.numStates_pos
        simp [sinkIndex] at hinitialSink
        omega
      · exact hreach
    · have htarget : c.RawTarget r [] := rawTarget_of_rejecting c hreject
      have hinitial := hpath.preservesTarget
        (fun t ht => leastSummaryRelation_semantic c ht) htarget
      have hinitial' : c.RawTarget
          (c.initialIndex % c.numStates)
          [c.startIndex % c.numStackSymbols] := by
        simpa [Nat.mod_mod] using hinitial
      rcases hinitial' with hinitialSink | hreach
      · have hlt := Nat.mod_lt c.initialIndex c.numStates_pos
        simp [sinkIndex] at hinitialSink
        omega
      · exact hreach
  · rintro ⟨p, delta, hreach, hp⟩
    obtain ⟨r, hr, hpath⟩ := summaryPath_of_rawErasedReaches c hreach hp
    refine ⟨r, ?_, hpath, hr⟩
    rcases hr with rfl | hr
    · simp [pStateCount, sinkIndex]
    · simp [isRejectingIndex] at hr
      exact hr.1.trans (by simp [pStateCount])

/-! ## Correspondence with decoded DPDA runs -/

/-- Interpret a raw erased control/stack pair as a decoded DPDA configuration
with the supplied remaining input. -/
@[expose] public def decodeRawConf (c : EncodedDPDA T)
    (x : ℕ × List ℕ) (w : List T) : PDA.conf c.toDPDA.toPDA :=
  ⟨c.state x.1, w, c.replacement x.2⟩

private theorem effectiveEpsilonRow_reaches₁ (c : EncodedDPDA T)
    {row : EpsilonRow} (hrow : row ∈ c.effectiveEpsilonRows)
    (suffix : List ℕ) (w : List T) :
    @PDA.Reaches₁ _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRawConf
        (c.normalizedEpsilonSource row,
          c.normalizedEpsilonTop row :: suffix) w)
      (c.decodeRawConf
        (c.normalizedEpsilonTarget row,
          c.normalizedEpsilonReplacement row ++ suffix) w) := by
  cases w <;>
    simp [decodeRawConf, replacement, PDA.Reaches₁, PDA.step, DPDA.toPDA,
      effectiveEpsilonRow_transition c hrow, List.map_append]

private theorem effectiveInputRow_reaches₁ (c : EncodedDPDA T)
    {row : InputRow T} (hrow : row ∈ c.effectiveInputRows)
    (suffix : List ℕ) (w : List T) :
    @PDA.Reaches₁ _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRawConf
        (c.normalizedInputSource row,
          c.normalizedInputTop row :: suffix) (row.2.1 :: w))
      (c.decodeRawConf
        (c.normalizedInputTarget row,
          c.normalizedInputReplacement row ++ suffix) w) := by
  simp [decodeRawConf, replacement, PDA.Reaches₁, PDA.step, DPDA.toPDA,
    effectiveInputRow_transition c hrow, List.map_append]

/-- Every erased run spells some input word and is realized by the decoded
DPDA on that word. -/
public theorem exists_word_reaches_of_rawErasedReaches (c : EncodedDPDA T)
    {x y : ℕ × List ℕ} (hreach : c.RawErasedReaches x y) :
    ∃ w, @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRawConf x w) (c.decodeRawConf y []) := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], Relation.ReflTransGen.refl⟩
  | @head x y hstep hrest ih =>
      obtain ⟨w, hrun⟩ := ih
      cases hstep with
      | @epsilon row suffix hrow =>
          exact ⟨w, Relation.ReflTransGen.head
            (effectiveEpsilonRow_reaches₁ c hrow suffix w) hrun⟩
      | @input row suffix hrow =>
          exact ⟨row.2.1 :: w, Relation.ReflTransGen.head
            (effectiveInputRow_reaches₁ c hrow suffix w) hrun⟩

/-- Raw configurations whose indices are already canonical representatives. -/
@[expose] public def RawNormalized (c : EncodedDPDA T)
    (x : ℕ × List ℕ) : Prop :=
  x.1 < c.numStates ∧ ∀ Z ∈ x.2, Z < c.numStackSymbols

private theorem decodeRawConf_injective (c : EncodedDPDA T)
    {x y : ℕ × List ℕ} {w v : List T}
    (hx : c.RawNormalized x) (hy : c.RawNormalized y)
    (h : c.decodeRawConf x w = c.decodeRawConf y v) :
    x = y ∧ w = v := by
  have hw : w = v := congrArg PDA.conf.input h
  have hqFin : c.state x.1 = c.state y.1 := congrArg PDA.conf.state h
  have hq : x.1 = y.1 := by
    have := congrArg Fin.val hqFin
    simpa [state, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using this
  have hstack : c.replacement x.2 = c.replacement y.2 :=
    congrArg PDA.conf.stack h
  have hxmap : (c.replacement x.2).map Fin.val = x.2 := by
    simp only [replacement, List.map_map]
    calc
      x.2.map (Fin.val ∘ c.stackSymbol) = x.2.map id := by
        apply List.map_congr_left
        intro Z hZ
        simp [Function.comp_def, stackSymbol, Nat.mod_eq_of_lt (hx.2 Z hZ)]
      _ = x.2 := List.map_id x.2
  have hymap : (c.replacement y.2).map Fin.val = y.2 := by
    simp only [replacement, List.map_map]
    calc
      y.2.map (Fin.val ∘ c.stackSymbol) = y.2.map id := by
        apply List.map_congr_left
        intro Z hZ
        simp [Function.comp_def, stackSymbol, Nat.mod_eq_of_lt (hy.2 Z hZ)]
      _ = y.2 := List.map_id y.2
  have hgamma : x.2 = y.2 := by
    rw [← hxmap, hstack, hymap]
  exact ⟨Prod.ext hq hgamma, hw⟩

private theorem toPDA_transition_mem_iff (c : EncodedDPDA T)
    (q : Fin c.numStates) (a : T) (Z : Fin c.numStackSymbols)
    (p : Fin c.numStates) (beta : List (Fin c.numStackSymbols)) :
    (p, beta) ∈ c.toDPDA.toPDA.transition_fun q a Z ↔
      c.toDPDA.transition q a Z = some (p, beta) := by
  cases h : c.toDPDA.transition q a Z <;> simp [DPDA.toPDA, h]
  rename_i out
  rcases out with ⟨p', beta'⟩
  simp [Prod.ext_iff]
  constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

private theorem toPDA_epsilonTransition_mem_iff (c : EncodedDPDA T)
    (q : Fin c.numStates) (Z : Fin c.numStackSymbols)
    (p : Fin c.numStates) (beta : List (Fin c.numStackSymbols)) :
    (p, beta) ∈ c.toDPDA.toPDA.transition_fun' q Z ↔
      c.toDPDA.epsilon_transition q Z = some (p, beta) := by
  cases h : c.toDPDA.epsilon_transition q Z <;> simp [DPDA.toPDA, h]
  rename_i out
  rcases out with ⟨p', beta'⟩
  simp [Prod.ext_iff]
  constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

private theorem normalizedEpsilonResult (c : EncodedDPDA T)
    (row : EpsilonRow) {suffix : List ℕ}
    (hsuffix : ∀ Z ∈ suffix, Z < c.numStackSymbols) :
    c.RawNormalized
      (c.normalizedEpsilonTarget row,
        c.normalizedEpsilonReplacement row ++ suffix) := by
  refine ⟨Nat.mod_lt _ c.numStates_pos, ?_⟩
  intro Z hZ
  rw [List.mem_append] at hZ
  rcases hZ with hZ | hZ
  · rw [normalizedEpsilonReplacement, List.mem_map] at hZ
    obtain ⟨Z', _, rfl⟩ := hZ
    exact Nat.mod_lt _ c.numStackSymbols_pos
  · exact hsuffix Z hZ

private theorem normalizedInputResult (c : EncodedDPDA T)
    (row : InputRow T) {suffix : List ℕ}
    (hsuffix : ∀ Z ∈ suffix, Z < c.numStackSymbols) :
    c.RawNormalized
      (c.normalizedInputTarget row,
        c.normalizedInputReplacement row ++ suffix) := by
  refine ⟨Nat.mod_lt _ c.numStates_pos, ?_⟩
  intro Z hZ
  rw [List.mem_append] at hZ
  rcases hZ with hZ | hZ
  · rw [normalizedInputReplacement, List.mem_map] at hZ
    obtain ⟨Z', _, rfl⟩ := hZ
    exact Nat.mod_lt _ c.numStackSymbols_pos
  · exact hsuffix Z hZ

/-- Every decoded run between canonical raw configurations projects to an
input-erased run. -/
public theorem rawErasedReaches_of_reaches (c : EncodedDPDA T)
    {x y : ℕ × List ℕ} {w : List T}
    (hx : c.RawNormalized x) (hy : c.RawNormalized y)
    (hreach : @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRawConf x w) (c.decodeRawConf y [])) :
    c.RawErasedReaches x y := by
  let target := c.decodeRawConf y ([] : List T)
  have main : ∀ {d : PDA.conf c.toDPDA.toPDA},
      @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA d target →
      ∀ {z : ℕ × List ℕ} {v : List T}, c.RawNormalized z →
        d = c.decodeRawConf z v → c.RawErasedReaches z y := by
    intro d hrun
    induction hrun using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro z v hz hrep
        have hzy := decodeRawConf_injective c hz hy hrep.symm
        obtain ⟨rfl, rfl⟩ := hzy
        exact Relation.ReflTransGen.refl
    | @head d e hstep hrest ih =>
        intro z v hz hrep
        subst d
        rcases z with ⟨q, gamma⟩
        cases gamma with
        | nil =>
            simp [decodeRawConf, replacement, PDA.Reaches₁, PDA.step] at hstep
        | cons Z suffix =>
            have hq : q < c.numStates := hz.1
            have hZ : Z < c.numStackSymbols := hz.2 Z (by simp)
            have hsuffix : ∀ X ∈ suffix, X < c.numStackSymbols := by
              intro X hX
              exact hz.2 X (by simp [hX])
            rcases PDA.reaches₁_push hstep with hinput | hepsilon
            · obtain ⟨a, v', p, beta, rfl, he, hmem⟩ := hinput
              have htransition :=
                (toPDA_transition_mem_iff c (c.state q) a
                  (c.stackSymbol Z) p beta).mp hmem
              obtain ⟨row, hrow, hsource, ha, htop, htarget, hrepl⟩ :=
                exists_effectiveInputRow_of_transition c htransition
              have hsource' : c.normalizedInputSource row = q := by
                simpa [state, Nat.mod_eq_of_lt hq] using hsource
              have htop' : c.normalizedInputTop row = Z := by
                simpa [stackSymbol, Nat.mod_eq_of_lt hZ] using htop
              let next : ℕ × List ℕ :=
                (c.normalizedInputTarget row,
                  c.normalizedInputReplacement row ++ suffix)
              have hnext : c.RawNormalized next :=
                normalizedInputResult c row hsuffix
              have herep : e = c.decodeRawConf next v' := by
                rw [he]
                simp [next, decodeRawConf, replacement, List.map_append,
                  htarget, ← hrepl]
              have hrestRaw := ih hnext herep
              have hrawStep : c.RawErasedStep (q, Z :: suffix) next := by
                simpa [next, hsource', htop'] using
                  (RawErasedStep.input (c := c) hrow)
              exact Relation.ReflTransGen.head hrawStep hrestRaw
            · obtain ⟨p, beta, he, hmem⟩ := hepsilon
              have htransition :=
                (toPDA_epsilonTransition_mem_iff c (c.state q)
                  (c.stackSymbol Z) p beta).mp hmem
              obtain ⟨row, hrow, hsource, htop, htarget, hrepl⟩ :=
                exists_effectiveEpsilonRow_of_transition c htransition
              have hsource' : c.normalizedEpsilonSource row = q := by
                simpa [state, Nat.mod_eq_of_lt hq] using hsource
              have htop' : c.normalizedEpsilonTop row = Z := by
                simpa [stackSymbol, Nat.mod_eq_of_lt hZ] using htop
              let next : ℕ × List ℕ :=
                (c.normalizedEpsilonTarget row,
                  c.normalizedEpsilonReplacement row ++ suffix)
              have hnext : c.RawNormalized next :=
                normalizedEpsilonResult c row hsuffix
              have herep : e = c.decodeRawConf next v := by
                rw [he]
                simp [next, decodeRawConf, replacement, List.map_append,
                  htarget, ← hrepl]
              have hrestRaw := ih hnext herep
              have hrawStep : c.RawErasedStep (q, Z :: suffix) next := by
                simpa [next, hsource', htop'] using
                  (RawErasedStep.epsilon (c := c) hrow)
              exact Relation.ReflTransGen.head hrawStep hrestRaw
  apply main (d := c.decodeRawConf x w)
    (by simpa [target] using hreach) hx rfl

private theorem initialRawNormalized (c : EncodedDPDA T) :
    c.RawNormalized
      (c.initialIndex % c.numStates, [c.startIndex % c.numStackSymbols]) := by
  refine ⟨Nat.mod_lt _ c.numStates_pos, ?_⟩
  intro Z hZ
  simp only [List.mem_singleton] at hZ
  subst Z
  exact Nat.mod_lt _ c.numStackSymbols_pos

private theorem finValRawNormalized (c : EncodedDPDA T)
    (q : Fin c.numStates) (gamma : List (Fin c.numStackSymbols)) :
    c.RawNormalized (q.val, gamma.map Fin.val) := by
  refine ⟨q.isLt, ?_⟩
  intro Z hZ
  rw [List.mem_map] at hZ
  obtain ⟨Z', _, rfl⟩ := hZ
  exact Z'.isLt

@[simp] private theorem state_finVal (c : EncodedDPDA T)
    (q : Fin c.numStates) : c.state q.val = q := by
  apply Fin.ext
  simp [state, Nat.mod_eq_of_lt q.isLt]

@[simp] private theorem replacement_finVal (c : EncodedDPDA T)
    (gamma : List (Fin c.numStackSymbols)) :
    c.replacement (gamma.map Fin.val) = gamma := by
  simp only [replacement, List.map_map]
  calc
    gamma.map (c.stackSymbol ∘ Fin.val) = gamma.map id := by
      apply List.map_congr_left
      intro Z _
      apply Fin.ext
      simp [stackSymbol, Nat.mod_eq_of_lt Z.isLt]
    _ = gamma := List.map_id gamma

private theorem decodeFinValConf (c : EncodedDPDA T)
    (q : Fin c.numStates) (gamma : List (Fin c.numStackSymbols)) :
    c.decodeRawConf (q.val, gamma.map Fin.val) [] =
      (⟨q, [], gamma⟩ : PDA.conf c.toDPDA.toPDA) := by
  apply PDA.conf.ext <;>
    simp [decodeRawConf, state, replacement, stackSymbol, List.map_map,
      Function.comp_def, Nat.mod_eq_of_lt]

/-- Under the totality promise, erased reachability of a rejecting control is
exactly the existence of a counterexample to universality. -/
public theorem hasRejectingReach_eq_true_iff_exists_not_mem (c : EncodedDPDA T)
    (hc : c.Valid) :
    c.hasRejectingReach = true ↔ ∃ w, w ∉ c.language := by
  rw [hasRejectingReach_eq_true_iff]
  constructor
  · rintro ⟨p, delta, hraw, hp⟩
    obtain ⟨w, hrun⟩ := exists_word_reaches_of_rawErasedReaches c hraw
    have hp' := hp
    simp only [isRejectingIndex, decide_eq_true_eq] at hp'
    have hpState : c.state p ∉ c.toDPDA.final_states := by
      simpa [toDPDA, normalizedFinals, state,
        Nat.mod_eq_of_lt hp'.1] using hp'.2
    have hrun' : @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA
        ⟨c.toDPDA.initial_state, w, [c.toDPDA.start_symbol]⟩
        ⟨c.state p, [], c.replacement delta⟩ := by
      simpa [decodeRawConf, toDPDA, replacement] using hrun
    have hwComplement : w ∈ c.toDPDA.complement.acceptsByFinalState := by
      refine ⟨c.state p, ?_, c.replacement delta, ?_⟩
      · simpa [DPDA.complement] using hpState
      · exact (DPDA.complement_toPDA_reaches c.toDPDA _ _ _ _ _).2 hrun'
    have hcomplement := DPDA.complement_acceptsByFinalState c.toDPDA hc
    refine ⟨w, ?_⟩
    change w ∉ c.toDPDA.acceptsByFinalState
    rw [← Set.mem_compl_iff, ← hcomplement]
    exact hwComplement
  · rintro ⟨w, hw⟩
    have hcomplement := DPDA.complement_acceptsByFinalState c.toDPDA hc
    have hwComplement : w ∈ c.toDPDA.complement.acceptsByFinalState := by
      rw [hcomplement]
      exact hw
    obtain ⟨q, hq, gamma, hrunComplement⟩ := hwComplement
    have hrun : @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA
        ⟨c.toDPDA.initial_state, w, [c.toDPDA.start_symbol]⟩
        ⟨q, [], gamma⟩ :=
      (DPDA.complement_toPDA_reaches c.toDPDA _ _ _ _ _).1 hrunComplement
    have hrunRaw : c.RawErasedReaches
        (c.initialIndex % c.numStates, [c.startIndex % c.numStackSymbols])
        (q.val, gamma.map Fin.val) := by
      apply rawErasedReaches_of_reaches (w := w) c (initialRawNormalized c)
        (finValRawNormalized c q gamma)
      have hstart : c.decodeRawConf
          (c.initialIndex % c.numStates,
            [c.startIndex % c.numStackSymbols]) w =
          (⟨c.toDPDA.initial_state, w, [c.toDPDA.start_symbol]⟩ :
            PDA.conf c.toDPDA.toPDA) := by
        apply PDA.conf.ext <;>
          simp [decodeRawConf, toDPDA, replacement]
      have hend := decodeFinValConf c q gamma
      simpa only [hstart, hend] using hrun
    refine ⟨q.val, gamma.map Fin.val, hrunRaw, ?_⟩
    rw [isRejectingIndex, decide_eq_true_eq]
    refine ⟨q.isLt, ?_⟩
    have hqNotFinal : q ∉ c.toDPDA.final_states := by
      change q ∈ c.toDPDA.final_statesᶜ at hq
      exact hq
    change q.val ∉ c.normalizedFinals at hqNotFinal
    exact hqNotFinal

/-- The finite Boolean test decides universality on the promise that the code
denotes a total DPDA. -/
public theorem checkUniversal_eq_true_iff (c : EncodedDPDA T) (hc : c.Valid) :
    c.checkUniversal = true ↔ c.language = Set.univ := by
  constructor
  · intro hcheck
    apply Set.eq_univ_of_forall
    intro w
    by_contra hw
    have hreach := (hasRejectingReach_eq_true_iff_exists_not_mem c hc).2 ⟨w, hw⟩
    simp [checkUniversal, hreach] at hcheck
  · intro huniv
    have hnot : c.hasRejectingReach ≠ true := by
      intro hreach
      obtain ⟨w, hw⟩ :=
        (hasRejectingReach_eq_true_iff_exists_not_mem c hc).1 hreach
      have hwUniv : w ∈ (Set.univ : Language T) := Set.mem_univ w
      have : w ∈ c.language := huniv.symm ▸ hwUniv
      exact hw this
    have hfalse : c.hasRejectingReach = false := Bool.eq_false_of_not_eq_true hnot
    simp [checkUniversal, hfalse]

/-! ## Effective accepting-run certificates

Membership is semi-decided uniformly on *all* raw codes by searching for a finite
accepting run.  Configurations use raw natural-number indices, so certificates
have a fixed primitive-codable type independent of the code. -/

/-- A raw configuration records the control index, unread input, and stack. -/
public abbrev RawRunConf (T : Type) := ℕ × List T × List ℕ

/-- The canonical raw initial configuration on `w`. -/
@[expose] public def initialRunConf (c : EncodedDPDA T) (w : List T) : RawRunConf T :=
  (c.initialIndex % c.numStates, w, [c.startIndex % c.numStackSymbols])

/-- Decode a raw run configuration into the genuine DPDA configuration. -/
@[expose] public def decodeRunConf (c : EncodedDPDA T) (x : RawRunConf T) :
    PDA.conf c.toDPDA.toPDA :=
  c.decodeRawConf (x.1, x.2.2) x.2.1

/-- Boolean final-state acceptance for a canonical raw configuration. -/
@[expose] public def acceptingRunConf (c : EncodedDPDA T) (x : RawRunConf T) : Bool :=
  decide (x.2.1 = [] ∧ x.1 % c.numStates ∈ c.normalizedFinals)

/-- Does an effective epsilon row realize this raw certificate edge? -/
@[expose] public def epsilonRunStepMatches (c : EncodedDPDA T)
    (x y : RawRunConf T) (Z : ℕ) (suffix : List ℕ) (row : EpsilonRow) : Bool :=
  decide (x.1 = c.normalizedEpsilonSource row ∧
    Z = c.normalizedEpsilonTop row ∧
    y = (c.normalizedEpsilonTarget row, x.2.1,
      c.normalizedEpsilonReplacement row ++ suffix))

/-- Does an effective input row realize this raw certificate edge? -/
@[expose] public def inputRunStepMatches (c : EncodedDPDA T)
    (x y : RawRunConf T) (Z : ℕ) (suffix : List ℕ)
    (a : T) (w : List T) (row : InputRow T) : Bool :=
  decide (x.1 = c.normalizedInputSource row ∧
    Z = c.normalizedInputTop row ∧ row.2.1 = a ∧
    y = (c.normalizedInputTarget row, w,
      c.normalizedInputReplacement row ++ suffix))

/-- Check one certificate edge against the effective finite transition tables. -/
@[expose] public def checkRunStep (c : EncodedDPDA T)
    (x y : RawRunConf T) : Bool :=
  match x.2.2 with
  | [] => false
  | Z :: suffix =>
      (c.effectiveEpsilonRows.any fun row =>
        c.epsilonRunStepMatches x y Z suffix row) ||
      match x.2.1 with
      | [] => false
      | a :: w =>
          c.effectiveInputRows.any fun row =>
            c.inputRunStepMatches x y Z suffix a w row

/-! The executable membership search below follows the unique decoded run
directly.  Its state type is independent of the encoded machine, which is what
makes the search uniform over raw codes. -/

@[expose] public def epsilonRunEnabled (c : EncodedDPDA T)
    (q Z : ℕ) (row : EpsilonRow) : Bool :=
  decide (q = c.normalizedEpsilonSource row ∧
    Z = c.normalizedEpsilonTop row)

@[expose] public def inputRunEnabled (c : EncodedDPDA T)
    (q : ℕ) (a : T) (Z : ℕ) (row : InputRow T) : Bool :=
  decide (q = c.normalizedInputSource row ∧ row.2.1 = a ∧
    Z = c.normalizedInputTop row)

@[expose] public def epsilonRunResult (c : EncodedDPDA T)
    (v : List T) (suffix : List ℕ) (row : EpsilonRow) : RawRunConf T :=
  (c.normalizedEpsilonTarget row, v,
    c.normalizedEpsilonReplacement row ++ suffix)

@[expose] public def inputRunResult (c : EncodedDPDA T)
    (w : List T) (suffix : List ℕ) (row : InputRow T) : RawRunConf T :=
  (c.normalizedInputTarget row, w,
    c.normalizedInputReplacement row ++ suffix)

/-- The canonical next raw configuration.  Epsilon rows have priority, as in
the decoded DPDA, and the effective tables contain at most the selected row for
each transition key. -/
@[expose] public def nextRunConf (c : EncodedDPDA T)
    (x : RawRunConf T) : Option (RawRunConf T) :=
  match x.2.2 with
  | [] => none
  | Z :: suffix =>
      match c.effectiveEpsilonRows.find? (c.epsilonRunEnabled x.1 Z) with
      | some row => some (c.epsilonRunResult x.2.1 suffix row)
      | none =>
          match x.2.1 with
          | [] => none
          | a :: w =>
              (c.effectiveInputRows.find?
                (c.inputRunEnabled x.1 a Z)).map
                (c.inputRunResult w suffix)

/-- One total iteration of the raw machine; a halted configuration stutters. -/
@[expose] public def advanceRunConf (c : EncodedDPDA T)
    (x : RawRunConf T) : RawRunConf T :=
  (c.nextRunConf x).getD x

/-- The raw configuration after exactly `n` iterations, including the initial
configuration at fuel zero. -/
@[expose] public def runFuel (c : EncodedDPDA T)
    (x : RawRunConf T) : ℕ → RawRunConf T
  | 0 => x
  | n + 1 => c.advanceRunConf (c.runFuel x n)

/-- Does the unique decoded run accept after exactly `n` iterations? -/
@[expose] public def acceptsAtFuel (c : EncodedDPDA T)
    (w : List T) (n : ℕ) : Bool :=
  c.acceptingRunConf (c.runFuel (c.initialRunConf w) n)

private theorem checkRunStep_complete (c : EncodedDPDA T)
    {x : RawRunConf T}
    (hx : c.RawNormalized (x.1, x.2.2))
    {d : PDA.conf c.toDPDA.toPDA}
    (hstep : @PDA.Reaches₁ _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRunConf x) d) :
    ∃ y : RawRunConf T,
      c.RawNormalized (y.1, y.2.2) ∧
      c.checkRunStep x y = true ∧ d = c.decodeRunConf y := by
  rcases x with ⟨q, v, gamma⟩
  cases gamma with
  | nil =>
      simp [decodeRunConf, decodeRawConf, replacement, PDA.Reaches₁, PDA.step]
        at hstep
  | cons Z suffix =>
      have hq : q < c.numStates := hx.1
      have hZ : Z < c.numStackSymbols := hx.2 Z (by simp)
      have hsuffix : ∀ X ∈ suffix, X < c.numStackSymbols := by
        intro X hX
        exact hx.2 X (by simp [hX])
      rcases PDA.reaches₁_push hstep with hinput | hepsilon
      · obtain ⟨a, v', p, beta, rfl, he, hmem⟩ := hinput
        have htransition :=
          (toPDA_transition_mem_iff c (c.state q) a
            (c.stackSymbol Z) p beta).mp hmem
        obtain ⟨row, hrow, hsource, ha, htop, htarget, hrepl⟩ :=
          exists_effectiveInputRow_of_transition c htransition
        have hsource' : c.normalizedInputSource row = q := by
          simpa [state, Nat.mod_eq_of_lt hq] using hsource
        have htop' : c.normalizedInputTop row = Z := by
          simpa [stackSymbol, Nat.mod_eq_of_lt hZ] using htop
        let next : RawRunConf T :=
          (c.normalizedInputTarget row, v',
            c.normalizedInputReplacement row ++ suffix)
        have hnext : c.RawNormalized (next.1, next.2.2) :=
          normalizedInputResult c row hsuffix
        have herep : d = c.decodeRunConf next := by
          rw [he]
          simp [next, decodeRunConf, decodeRawConf, replacement, List.map_append,
            htarget, ← hrepl]
        refine ⟨next, hnext, ?_, herep⟩
        rw [checkRunStep, Bool.or_eq_true]
        right
        exact List.any_eq_true.mpr ⟨row, hrow, by
          simp [inputRunStepMatches, next, hsource', htop', ha]⟩
      · obtain ⟨p, beta, he, hmem⟩ := hepsilon
        have htransition :=
          (toPDA_epsilonTransition_mem_iff c (c.state q)
            (c.stackSymbol Z) p beta).mp hmem
        obtain ⟨row, hrow, hsource, htop, htarget, hrepl⟩ :=
          exists_effectiveEpsilonRow_of_transition c htransition
        have hsource' : c.normalizedEpsilonSource row = q := by
          simpa [state, Nat.mod_eq_of_lt hq] using hsource
        have htop' : c.normalizedEpsilonTop row = Z := by
          simpa [stackSymbol, Nat.mod_eq_of_lt hZ] using htop
        let next : RawRunConf T :=
          (c.normalizedEpsilonTarget row, v,
            c.normalizedEpsilonReplacement row ++ suffix)
        have hnext : c.RawNormalized (next.1, next.2.2) :=
          normalizedEpsilonResult c row hsuffix
        have herep : d = c.decodeRunConf next := by
          rw [he]
          simp [next, decodeRunConf, decodeRawConf, replacement, List.map_append,
            htarget, ← hrepl]
        refine ⟨next, hnext, ?_, herep⟩
        rw [checkRunStep, Bool.or_eq_true]
        left
        exact List.any_eq_true.mpr ⟨row, hrow, by
          simp [epsilonRunStepMatches, next, hsource', htop']⟩

private theorem nextRunConf_sound (c : EncodedDPDA T)
    {x y : RawRunConf T} (hnext : c.nextRunConf x = some y) :
    @PDA.Reaches₁ _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRunConf x) (c.decodeRunConf y) := by
  rcases x with ⟨q, v, gamma⟩
  cases gamma with
  | nil => simp [nextRunConf] at hnext
  | cons Z suffix =>
      cases hepsilon : c.effectiveEpsilonRows.find?
          (c.epsilonRunEnabled q Z) with
      | some row =>
          have henabled := List.find?_some hepsilon
          simp only [epsilonRunEnabled, decide_eq_true_eq] at henabled
          obtain ⟨rfl, rfl⟩ := henabled
          simp only [nextRunConf, hepsilon, Option.some.injEq] at hnext
          subst y
          simpa [epsilonRunResult] using
            effectiveEpsilonRow_reaches₁ c
              (List.mem_of_find?_eq_some hepsilon) suffix v
      | none =>
          cases v with
          | nil => simp [nextRunConf, hepsilon] at hnext
          | cons a w =>
              cases hinput : c.effectiveInputRows.find?
                  (c.inputRunEnabled q a Z) with
              | none => simp [nextRunConf, hepsilon, hinput] at hnext
              | some row =>
                  have henabled := List.find?_some hinput
                  simp only [inputRunEnabled, decide_eq_true_eq] at henabled
                  obtain ⟨rfl, rfl, rfl⟩ := henabled
                  simp only [nextRunConf, hepsilon, hinput, Option.map_some,
                    Option.some.injEq] at hnext
                  subst y
                  simpa [inputRunResult] using
                    effectiveInputRow_reaches₁ c
                      (List.mem_of_find?_eq_some hinput) suffix w

private theorem nextRunConf_normalized (c : EncodedDPDA T)
    {x y : RawRunConf T} (hx : c.RawNormalized (x.1, x.2.2))
    (hnext : c.nextRunConf x = some y) :
    c.RawNormalized (y.1, y.2.2) := by
  rcases x with ⟨q, v, gamma⟩
  cases gamma with
  | nil => simp [nextRunConf] at hnext
  | cons Z suffix =>
      have hsuffix : ∀ X ∈ suffix, X < c.numStackSymbols := by
        intro X hX
        exact hx.2 X (by simp [hX])
      cases hepsilon : c.effectiveEpsilonRows.find?
          (c.epsilonRunEnabled q Z) with
      | some row =>
          simp only [nextRunConf, hepsilon, Option.some.injEq] at hnext
          subst y
          simpa [epsilonRunResult] using
            normalizedEpsilonResult c row hsuffix
      | none =>
          cases v with
          | nil => simp [nextRunConf, hepsilon] at hnext
          | cons a w =>
              cases hinput : c.effectiveInputRows.find?
                  (c.inputRunEnabled q a Z) with
              | none => simp [nextRunConf, hepsilon, hinput] at hnext
              | some row =>
                  simp only [nextRunConf, hepsilon, hinput, Option.map_some,
                    Option.some.injEq] at hnext
                  subst y
                  simpa [inputRunResult] using
                    normalizedInputResult c row hsuffix

private theorem exists_nextRunConf_of_checkRunStep (c : EncodedDPDA T)
    {x y : RawRunConf T} (hcheck : c.checkRunStep x y = true) :
    ∃ z : RawRunConf T, c.nextRunConf x = some z := by
  rcases x with ⟨q, v, gamma⟩
  cases gamma with
  | nil => simp [checkRunStep] at hcheck
  | cons Z suffix =>
      rw [checkRunStep, Bool.or_eq_true] at hcheck
      cases hepsilon : c.effectiveEpsilonRows.find?
          (c.epsilonRunEnabled q Z) with
      | some row =>
          exact ⟨c.epsilonRunResult v suffix row, by
            simp [nextRunConf, hepsilon]⟩
      | none =>
          rcases hcheck with hepsilonMatch | hinputMatch
          · rw [List.any_eq_true] at hepsilonMatch
            obtain ⟨row, hrow, hmatch⟩ := hepsilonMatch
            simp only [epsilonRunStepMatches, decide_eq_true_eq] at hmatch
            have henabled : c.epsilonRunEnabled q Z row = true := by
              simp [epsilonRunEnabled, hmatch.1, hmatch.2.1]
            have hisSome : (c.effectiveEpsilonRows.find?
                (c.epsilonRunEnabled q Z)).isSome = true :=
              List.find?_isSome.mpr ⟨row, hrow, henabled⟩
            simp [hepsilon] at hisSome
          · cases v with
            | nil => simp at hinputMatch
            | cons a w =>
                rw [List.any_eq_true] at hinputMatch
                obtain ⟨row, hrow, hmatch⟩ := hinputMatch
                simp only [inputRunStepMatches, decide_eq_true_eq] at hmatch
                have henabled : c.inputRunEnabled q a Z row = true := by
                  simp [inputRunEnabled, hmatch.1, hmatch.2.2.1,
                    hmatch.2.1]
                have hisSome : (c.effectiveInputRows.find?
                    (c.inputRunEnabled q a Z)).isSome = true :=
                  List.find?_isSome.mpr ⟨row, hrow, henabled⟩
                cases hinput : c.effectiveInputRows.find?
                    (c.inputRunEnabled q a Z) with
                | none => simp [hinput] at hisSome
                | some selected =>
                    exact ⟨c.inputRunResult w suffix selected, by
                      simp [nextRunConf, hepsilon, hinput]⟩

private theorem nextRunConf_complete (c : EncodedDPDA T)
    {x : RawRunConf T} (hx : c.RawNormalized (x.1, x.2.2))
    {d : PDA.conf c.toDPDA.toPDA}
    (hstep : @PDA.Reaches₁ _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRunConf x) d) :
    ∃ y : RawRunConf T, c.nextRunConf x = some y ∧
      c.RawNormalized (y.1, y.2.2) ∧ c.decodeRunConf y = d := by
  obtain ⟨witness, _, hcheck, _⟩ := checkRunStep_complete c hx hstep
  obtain ⟨y, hnext⟩ := exists_nextRunConf_of_checkRunStep c hcheck
  refine ⟨y, hnext, nextRunConf_normalized c hx hnext, ?_⟩
  exact c.toDPDA.toPDA_step_deterministic
    (nextRunConf_sound c hnext) hstep

private theorem advanceRunConf_normalized (c : EncodedDPDA T)
    {x : RawRunConf T} (hx : c.RawNormalized (x.1, x.2.2)) :
    c.RawNormalized ((c.advanceRunConf x).1, (c.advanceRunConf x).2.2) := by
  cases hnext : c.nextRunConf x with
  | none => simpa [advanceRunConf, hnext] using hx
  | some y =>
      simpa [advanceRunConf, hnext] using
        nextRunConf_normalized c hx hnext

private theorem runFuel_normalized (c : EncodedDPDA T)
    {x : RawRunConf T} (hx : c.RawNormalized (x.1, x.2.2)) (n : ℕ) :
    c.RawNormalized ((c.runFuel x n).1, (c.runFuel x n).2.2) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      simpa [runFuel] using advanceRunConf_normalized c ih

private theorem runFuel_sound (c : EncodedDPDA T)
    (x : RawRunConf T) (n : ℕ) :
    @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA
      (c.decodeRunConf x) (c.decodeRunConf (c.runFuel x n)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      cases hnext : c.nextRunConf (c.runFuel x n) with
      | none => simpa [runFuel, advanceRunConf, hnext] using ih
      | some y =>
          have hstep := nextRunConf_sound c hnext
          have hreach := Relation.ReflTransGen.tail ih hstep
          simpa [runFuel, advanceRunConf, hnext] using hreach

private theorem runFuel_complete (c : EncodedDPDA T)
    {x : RawRunConf T} (hx : c.RawNormalized (x.1, x.2.2))
    {n : ℕ} {d : PDA.conf c.toDPDA.toPDA}
    (hreach : @PDA.ReachesIn _ _ _ _ _ _ c.toDPDA.toPDA n
      (c.decodeRunConf x) d) :
    c.decodeRunConf (c.runFuel x n) = d := by
  induction n generalizing d with
  | zero =>
      have hzero := PDA.reachesIn_zero hreach
      simpa [runFuel] using hzero
  | succ n ih =>
      obtain ⟨middle, hprefix, hlast⟩ :=
        PDA.reachesIn_iff_split_last.mpr hreach
      have hmiddle : c.decodeRunConf (c.runFuel x n) = middle :=
        ih hprefix
      have hstep : @PDA.Reaches₁ _ _ _ _ _ _ c.toDPDA.toPDA
          (c.decodeRunConf (c.runFuel x n)) d := by
        simpa [hmiddle] using
          (PDA.reaches₁_iff_reachesIn_one.mpr hlast)
      obtain ⟨y, hnext, _, hy⟩ := nextRunConf_complete c
        (runFuel_normalized c hx n) hstep
      simpa [runFuel, advanceRunConf, hnext] using hy

/-- A word belongs to the decoded language exactly when the unique raw run
accepts at some finite fuel.  Fuel zero is included, so accepting the empty
word in the initial configuration is represented directly. -/
public theorem exists_acceptsAtFuel_eq_true_iff (c : EncodedDPDA T)
    (w : List T) :
    (∃ n : ℕ, c.acceptsAtFuel w n = true) ↔ w ∈ c.language := by
  have hstart : c.decodeRunConf (c.initialRunConf w) =
      (⟨c.toDPDA.initial_state, w, [c.toDPDA.start_symbol]⟩ :
        PDA.conf c.toDPDA.toPDA) := by
    apply PDA.conf.ext <;>
      simp [decodeRunConf, initialRunConf, decodeRawConf, toDPDA, replacement]
  constructor
  · rintro ⟨n, haccept⟩
    let result := c.runFuel (c.initialRunConf w) n
    have hreach := runFuel_sound c (c.initialRunConf w) n
    have haccept' : result.2.1 = [] ∧
        result.1 % c.numStates ∈ c.normalizedFinals := by
      simpa [acceptsAtFuel, acceptingRunConf, result] using haccept
    change w ∈ c.toDPDA.acceptsByFinalState
    refine ⟨c.state result.1, haccept'.2,
      c.replacement result.2.2, ?_⟩
    change @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA
      ⟨c.toDPDA.initial_state, w, [c.toDPDA.start_symbol]⟩
      ⟨c.state result.1, [], c.replacement result.2.2⟩
    rw [← hstart]
    simpa [result, decodeRunConf, decodeRawConf, haccept'.1] using hreach
  · rintro ⟨q, hq, gamma, hreach⟩
    have hreach' : @PDA.Reaches _ _ _ _ _ _ c.toDPDA.toPDA
        (c.decodeRunConf (c.initialRunConf w)) ⟨q, [], gamma⟩ := by
      simpa only [hstart] using hreach
    obtain ⟨n, hcounted⟩ := PDA.reaches_iff_reachesIn.mp hreach'
    have hend := runFuel_complete c (initialRawNormalized c) hcounted
    let result := c.runFuel (c.initialRunConf w) n
    have hinput : result.2.1 = [] := by
      have h := congrArg PDA.conf.input hend
      simpa [result, decodeRunConf, decodeRawConf] using h
    have hstate : c.state result.1 = q := by
      have h := congrArg PDA.conf.state hend
      simpa [result, decodeRunConf, decodeRawConf] using h
    have hfinal : result.1 % c.numStates ∈ c.normalizedFinals := by
      have : c.state result.1 ∈ c.toDPDA.final_states := hstate.symm ▸ hq
      change (c.state result.1).val ∈ c.normalizedFinals at this
      simpa [state] using this
    exact ⟨n, by
      simp [acceptsAtFuel, acceptingRunConf, result, hinput, hfinal]⟩

/-! ## Effectivity of the finite analysis -/

section Computability

variable [Primcodable T]

private theorem primrec_list_foldl
    {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → S × B → S}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  exact Primrec.list_foldl hf hg hh

private theorem primrec_list_all
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have hnot : Primrec₂ (fun a b => !p a b) :=
    Primrec.not.comp hp
  have hidx : Primrec fun a => (f a).findIdx (fun b => !p a b) :=
    Primrec.list_findIdx hf hnot
  have hlength : Primrec fun a => (f a).length :=
    Primrec.list_length.comp hf
  have heq : Primrec fun a => decide
      ((f a).findIdx (fun b => !p a b) = (f a).length) :=
    ((Primrec.eq : PrimrecRel fun (m n : ℕ) => m = n).decide).comp
      hidx hlength
  apply Primrec.of_eq heq
  intro a
  apply Bool.eq_iff_iff.mpr
  simp [List.findIdx_eq_length, List.all_eq_true]

private theorem primrec_list_any_fast
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) := by
  have hidx : Primrec fun a => (f a).findIdx (p a) :=
    Primrec.list_findIdx hf hp
  have hlength : Primrec fun a => (f a).length :=
    Primrec.list_length.comp hf
  have hlt : Primrec fun a => decide
      ((f a).findIdx (p a) < (f a).length) :=
    (PrimrecRel.decide Primrec.nat_lt).comp hidx hlength
  apply Primrec.of_eq hlt
  intro a
  apply Bool.eq_iff_iff.mpr
  simp [List.findIdx_lt_length, List.any_eq_true]

private theorem primrec_list_filterBool
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) := by
  have hguard : Primrec₂ (fun a b =>
      bif p a b then some b else none) := by
    show Primrec (fun q : A × B =>
      bif p q.1 q.2 then some q.2 else none)
    exact Primrec.cond
      (hp.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  have hfilterMap := Primrec.listFilterMap hf hguard
  apply Primrec.of_eq hfilterMap
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
      cases h : p a b <;> simp [List.filter, h, ih]

private theorem primrec_list_find?
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  have hguard : Primrec₂ (fun a b =>
      bif p a b then some b else none) := by
    show Primrec (fun q : A × B =>
      bif p q.1 q.2 then some q.2 else none)
    exact Primrec.cond
      (hp.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  have hhead := Primrec.list_head?.comp (Primrec.listFilterMap hf hguard)
  apply Primrec.of_eq hhead
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
      cases h : p a b <;> simp [List.find?_cons, h, ih]

private theorem primrec_list_sublists
    {A : Type} [Primcodable A] : Primrec (@List.sublists A) := by
  have hstep : Primrec₂ (fun (_ : List A) (p : A × List (List A)) =>
      p.2.flatMap fun l => [l, p.1 :: l]) := by
    show Primrec (fun q : List A × (A × List (List A)) =>
      q.2.2.flatMap fun l => [l, q.2.1 :: l])
    refine Primrec.list_flatMap (Primrec.snd.comp (Primrec.snd)) ?_
    show Primrec₂ (fun (q : List A × (A × List (List A))) (l : List A) =>
      [l, q.2.1 :: l])
    exact Primrec.list_cons.comp Primrec.snd
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        (Primrec.const []))
  convert Primrec.list_foldr (Primrec.id) (Primrec.const ([[]] : List (List A)))
    hstep using 1

private theorem primrec_list_memBool
    {A : Type} [Primcodable A] [DecidableEq A] :
    Primrec₂ (fun (a : A) (l : List A) => decide (a ∈ l)) := by
  show Primrec (fun q : A × List A => decide (q.1 ∈ q.2))
  have hp : Primrec₂ (fun (q : A × List A) (a : A) => decide (q.1 = a)) := by
    show Primrec (fun p : (A × List A) × A => decide (p.1.1 = p.2))
    exact (PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hany := primrec_list_any_fast (hf := Primrec.snd) hp
  apply Primrec.of_eq hany
  intro ⟨a, l⟩
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.any, ih, Bool.decide_or]

private theorem numStates_primrec :
    Primrec (numStates : EncodedDPDA T → ℕ) := by
  unfold numStates EncodedDPDA
  exact Primrec.succ.comp Primrec.fst

private theorem numStackSymbols_primrec :
    Primrec (numStackSymbols : EncodedDPDA T → ℕ) := by
  unfold numStackSymbols EncodedDPDA
  exact Primrec.succ.comp (Primrec.fst.comp Primrec.snd)

private theorem initialIndex_primrec :
    Primrec (initialIndex : EncodedDPDA T → ℕ) := by
  unfold initialIndex EncodedDPDA
  exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem startIndex_primrec :
    Primrec (startIndex : EncodedDPDA T → ℕ) := by
  unfold startIndex EncodedDPDA
  exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem finalIndices_primrec :
    Primrec (finalIndices : EncodedDPDA T → List ℕ) := by
  unfold finalIndices EncodedDPDA
  exact Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem inputRows_primrec :
    Primrec (inputRows : EncodedDPDA T → List (InputRow T)) := by
  unfold inputRows EncodedDPDA
  exact Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private theorem epsilonRows_primrec :
    Primrec (epsilonRows : EncodedDPDA T → List EpsilonRow) := by
  unfold epsilonRows EncodedDPDA
  exact Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private theorem modList_primrec :
    Primrec₂ (fun (n : ℕ) (l : List ℕ) => l.map fun x => x % n) := by
  show Primrec (fun p : ℕ × List ℕ => p.2.map fun x => x % p.1)
  exact Primrec.list_map Primrec.snd
    (Primrec.nat_mod.comp Primrec.snd (Primrec.fst.comp Primrec.fst))

private theorem normalizedEpsilonSource_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : EpsilonRow) =>
      c.normalizedEpsilonSource r) := by
  exact Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
    (numStates_primrec.comp Primrec.fst)

private theorem normalizedEpsilonTop_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : EpsilonRow) =>
      c.normalizedEpsilonTop r) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (numStackSymbols_primrec.comp Primrec.fst)

private theorem normalizedEpsilonTarget_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : EpsilonRow) =>
      c.normalizedEpsilonTarget r) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (numStates_primrec.comp Primrec.fst)

private theorem normalizedEpsilonReplacement_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : EpsilonRow) =>
      c.normalizedEpsilonReplacement r) := by
  exact modList_primrec.comp
    (numStackSymbols_primrec.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem normalizedInputSource_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : InputRow T) =>
      c.normalizedInputSource r) := by
  exact Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
    (numStates_primrec.comp Primrec.fst)

private theorem normalizedInputTop_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : InputRow T) =>
      c.normalizedInputTop r) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (numStackSymbols_primrec.comp Primrec.fst)

private theorem normalizedInputTarget_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : InputRow T) =>
      c.normalizedInputTarget r) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (numStates_primrec.comp Primrec.fst)

private theorem normalizedInputReplacement_primrec :
    Primrec₂ (fun (c : EncodedDPDA T) (r : InputRow T) =>
      c.normalizedInputReplacement r) := by
  exact modList_primrec.comp
    (numStackSymbols_primrec.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private abbrev SelectionSizes := ℕ × ℕ
private abbrev EpsilonSelectionData := SelectionSizes × List EpsilonRow
private abbrev InputSelectionData (T : Type) :=
  SelectionSizes × (List EpsilonRow × List (InputRow T))

private def epsilonSelectionMatches (nm : SelectionSizes)
    (r s : EpsilonRow) : Bool :=
  decide (s.1 % nm.1 = r.1 % nm.1 ∧
    s.2.1 % nm.2 = r.2.1 % nm.2)

private def inputSelectionMatches (nm : SelectionSizes)
    (r s : InputRow T) : Bool :=
  decide (s.1 % nm.1 = r.1 % nm.1 ∧ s.2.1 = r.2.1 ∧
    s.2.2.1 % nm.2 = r.2.2.1 % nm.2)

private def epsilonInputSelectionMatches (nm : SelectionSizes)
    (r : InputRow T) (s : EpsilonRow) : Bool :=
  decide (s.1 % nm.1 = r.1 % nm.1 ∧
    s.2.1 % nm.2 = r.2.2.1 % nm.2)

private theorem epsilonSelectionMatches_primrec :
    Primrec₂ (fun (p : SelectionSizes × EpsilonRow) (s : EpsilonRow) =>
      epsilonSelectionMatches p.1 p.2 s) := by
  show Primrec (fun q : (SelectionSizes × EpsilonRow) × EpsilonRow =>
    epsilonSelectionMatches q.1.1 q.1.2 q.2)
  have hn : Primrec (fun q : (SelectionSizes × EpsilonRow) × EpsilonRow =>
      q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : (SelectionSizes × EpsilonRow) × EpsilonRow =>
      q.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hsourceS := Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd) hn
  have hsourceR := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hn
  have htopS := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hm
  have htopR := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))) hm
  apply Primrec.of_eq (Primrec.and.comp
    ((PrimrecRel.decide Primrec.eq).comp hsourceS hsourceR)
    ((PrimrecRel.decide Primrec.eq).comp htopS htopR))
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [epsilonSelectionMatches]

private theorem inputSelectionMatches_primrec :
    Primrec₂ (fun (p : SelectionSizes × InputRow T) (s : InputRow T) =>
      inputSelectionMatches p.1 p.2 s) := by
  show Primrec (fun q : (SelectionSizes × InputRow T) × InputRow T =>
    inputSelectionMatches q.1.1 q.1.2 q.2)
  have hn : Primrec (fun q : (SelectionSizes × InputRow T) × InputRow T =>
      q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : (SelectionSizes × InputRow T) × InputRow T =>
      q.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hsourceS := Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd) hn
  have hsourceR := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hn
  have hletterS : Primrec (fun q : (SelectionSizes × InputRow T) × InputRow T =>
      q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hletterR : Primrec (fun q : (SelectionSizes × InputRow T) × InputRow T =>
      q.1.2.2.1) := Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have htopS := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))) hm
  have htopR := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst)))) hm
  apply Primrec.of_eq (Primrec.and.comp
    ((PrimrecRel.decide Primrec.eq).comp hsourceS hsourceR)
    (Primrec.and.comp ((PrimrecRel.decide Primrec.eq).comp hletterS hletterR)
      ((PrimrecRel.decide Primrec.eq).comp htopS htopR)))
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [inputSelectionMatches]

private theorem epsilonInputSelectionMatches_primrec :
    Primrec₂ (fun (p : SelectionSizes × InputRow T) (s : EpsilonRow) =>
      epsilonInputSelectionMatches p.1 p.2 s) := by
  show Primrec (fun q : (SelectionSizes × InputRow T) × EpsilonRow =>
    epsilonInputSelectionMatches q.1.1 q.1.2 q.2)
  have hn : Primrec (fun q : (SelectionSizes × InputRow T) × EpsilonRow =>
      q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : (SelectionSizes × InputRow T) × EpsilonRow =>
      q.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hsourceS := Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd) hn
  have hsourceR := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hn
  have htopS := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hm
  have htopR := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst)))) hm
  apply Primrec.of_eq (Primrec.and.comp
    ((PrimrecRel.decide Primrec.eq).comp hsourceS hsourceR)
    ((PrimrecRel.decide Primrec.eq).comp htopS htopR))
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [epsilonInputSelectionMatches]

private theorem selectedEpsilonData_primrec :
    Primrec (fun p : EpsilonSelectionData × EpsilonRow =>
      p.1.2.find? (epsilonSelectionMatches p.1.1 p.2)) := by
  have hp : Primrec (fun q : (EpsilonSelectionData × EpsilonRow) × EpsilonRow =>
      epsilonSelectionMatches q.1.1.1 q.1.2 q.2) :=
    epsilonSelectionMatches_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact primrec_list_find?
    (Primrec.snd.comp Primrec.fst) hp.to₂

private theorem selectedInputData_primrec :
    Primrec (fun p : InputSelectionData T × InputRow T =>
      p.1.2.2.find? (inputSelectionMatches p.1.1 p.2)) := by
  have hp : Primrec (fun q : (InputSelectionData T × InputRow T) × InputRow T =>
      inputSelectionMatches q.1.1.1 q.1.2 q.2) := by
    have hn : Primrec (fun q : (InputSelectionData T × InputRow T) × InputRow T =>
        q.1.1.1.1) := Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hm : Primrec (fun q : (InputSelectionData T × InputRow T) × InputRow T =>
        q.1.1.1.2) := Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hsourceS := Primrec.nat_mod.comp
      (Primrec.fst.comp Primrec.snd) hn
    have hsourceR := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hn
    have hletterS : Primrec (fun q :
        (InputSelectionData T × InputRow T) × InputRow T => q.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hletterR : Primrec (fun q :
        (InputSelectionData T × InputRow T) × InputRow T => q.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have htopS := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hm
    have htopR := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst)))) hm
    apply Primrec.of_eq (Primrec.and.comp
      ((PrimrecRel.decide Primrec.eq).comp hsourceS hsourceR)
      (Primrec.and.comp ((PrimrecRel.decide Primrec.eq).comp hletterS hletterR)
        ((PrimrecRel.decide Primrec.eq).comp htopS htopR)))
    intro q
    apply Bool.eq_iff_iff.mpr
    simp [inputSelectionMatches]
  exact primrec_list_find?
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hp.to₂

private theorem selectedEpsilonForInputData_primrec :
    Primrec (fun p : InputSelectionData T × InputRow T =>
      p.1.2.1.find? (epsilonInputSelectionMatches p.1.1 p.2)) := by
  have hp : Primrec (fun q : (InputSelectionData T × InputRow T) × EpsilonRow =>
      epsilonInputSelectionMatches q.1.1.1 q.1.2 q.2) := by
    have hn : Primrec (fun q : (InputSelectionData T × InputRow T) × EpsilonRow =>
        q.1.1.1.1) := Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hm : Primrec (fun q : (InputSelectionData T × InputRow T) × EpsilonRow =>
        q.1.1.1.2) := Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hsourceS := Primrec.nat_mod.comp
      (Primrec.fst.comp Primrec.snd) hn
    have hsourceR := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hn
    have htopS := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hm
    have htopR := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst)))) hm
    apply Primrec.of_eq (Primrec.and.comp
      ((PrimrecRel.decide Primrec.eq).comp hsourceS hsourceR)
      ((PrimrecRel.decide Primrec.eq).comp htopS htopR))
    intro q
    apply Bool.eq_iff_iff.mpr
    simp [epsilonInputSelectionMatches]
  exact primrec_list_find?
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hp.to₂

private theorem effectiveEpsilonRows_primrec :
    Primrec (effectiveEpsilonRows : EncodedDPDA T → List EpsilonRow) := by
  have hselected : Primrec₂ (fun (d : EpsilonSelectionData) (r : EpsilonRow) =>
      decide (d.2.find? (epsilonSelectionMatches d.1 r) = some r)) :=
    ((Primrec.eq : PrimrecRel fun (x y : Option EpsilonRow) => x = y).decide).comp
      selectedEpsilonData_primrec.to₂ (Primrec.option_some.comp Primrec.snd)
  have hfilter : Primrec (fun d : EpsilonSelectionData =>
      d.2.filter fun r => decide
        (d.2.find? (epsilonSelectionMatches d.1 r) = some r)) :=
    primrec_list_filterBool Primrec.snd hselected
  have hdata : Primrec (fun c : EncodedDPDA T =>
      ((c.numStates, c.numStackSymbols), c.epsilonRows)) :=
    Primrec.pair (Primrec.pair numStates_primrec numStackSymbols_primrec)
      epsilonRows_primrec
  apply Primrec.of_eq (hfilter.comp hdata)
  intro c
  unfold effectiveEpsilonRows sameEpsilonKey normalizedEpsilonSource
    normalizedEpsilonTop epsilonSelectionMatches
  rfl

private theorem effectiveInputRows_primrec :
    Primrec (effectiveInputRows : EncodedDPDA T → List (InputRow T)) := by
  letI : DecidableEq (InputRow T) := inferInstance
  letI : DecidableEq (Option (InputRow T)) := inferInstance
  have hnone : Primrec₂ (fun (d : InputSelectionData T) (r : InputRow T) =>
      decide (d.2.1.find? (epsilonInputSelectionMatches d.1 r) = none)) :=
      ((Primrec.eq : PrimrecRel fun (x y : Option EpsilonRow) => x = y).decide).comp
        selectedEpsilonForInputData_primrec.to₂
        (Primrec.const (none : Option EpsilonRow))
  have hsome : Primrec₂ (fun (d : InputSelectionData T) (r : InputRow T) =>
      decide (d.2.2.find? (inputSelectionMatches d.1 r) = some r)) :=
      ((Primrec.eq : PrimrecRel fun (x y : Option (InputRow T)) => x = y).decide).comp
        selectedInputData_primrec.to₂ (Primrec.option_some.comp Primrec.snd)
  have hselected : Primrec₂ (fun (d : InputSelectionData T) (r : InputRow T) =>
      decide (d.2.1.find? (epsilonInputSelectionMatches d.1 r) = none ∧
        d.2.2.find? (inputSelectionMatches d.1 r) = some r)) := by
    apply Primrec.of_eq (Primrec.and.comp hnone hsome)
    intro p
    apply Bool.eq_iff_iff.mpr
    simp
  have hfilter : Primrec (fun d : InputSelectionData T =>
      d.2.2.filter fun r => decide
        (d.2.1.find? (epsilonInputSelectionMatches d.1 r) = none ∧
          d.2.2.find? (inputSelectionMatches d.1 r) = some r)) :=
    primrec_list_filterBool (Primrec.snd.comp Primrec.snd) hselected
  have hdata : Primrec (fun c : EncodedDPDA T =>
      ((c.numStates, c.numStackSymbols), (c.epsilonRows, c.inputRows))) :=
    Primrec.pair (Primrec.pair numStates_primrec numStackSymbols_primrec)
      (Primrec.pair epsilonRows_primrec inputRows_primrec)
  apply Primrec.of_eq (hfilter.comp hdata)
  intro c
  unfold effectiveInputRows sameInputKey normalizedEpsilonSource
    normalizedEpsilonTop normalizedInputSource normalizedInputTop
    epsilonInputSelectionMatches inputSelectionMatches
  rfl

private theorem pStateCount_primrec :
    Primrec (pStateCount : EncodedDPDA T → ℕ) := by
  exact Primrec.succ.comp numStates_primrec

private theorem sinkIndex_primrec :
    Primrec (sinkIndex : EncodedDPDA T → ℕ) := by
  exact numStates_primrec

private theorem normalizedFinals_primrec :
    Primrec (normalizedFinals : EncodedDPDA T → List ℕ) := by
  exact modList_primrec.comp numStates_primrec finalIndices_primrec

private theorem initialRunConf_primrec :
    Primrec₂ (initialRunConf : EncodedDPDA T → List T → RawRunConf T) := by
  show Primrec (fun p : EncodedDPDA T × List T => p.1.initialRunConf p.2)
  have hstate : Primrec (fun p : EncodedDPDA T × List T =>
      p.1.initialIndex % p.1.numStates) :=
    Primrec.nat_mod.comp (initialIndex_primrec.comp Primrec.fst)
      (numStates_primrec.comp Primrec.fst)
  have hstackSymbol : Primrec (fun p : EncodedDPDA T × List T =>
      p.1.startIndex % p.1.numStackSymbols) :=
    Primrec.nat_mod.comp (startIndex_primrec.comp Primrec.fst)
      (numStackSymbols_primrec.comp Primrec.fst)
  exact Primrec.pair hstate (Primrec.pair Primrec.snd
    (Primrec.list_cons.comp hstackSymbol (Primrec.const [])))

private theorem acceptingRunConf_primrec :
    Primrec₂ (acceptingRunConf : EncodedDPDA T → RawRunConf T → Bool) := by
  show Primrec (fun p : EncodedDPDA T × RawRunConf T =>
    p.1.acceptingRunConf p.2)
  have hinputNil : Primrec (fun p : EncodedDPDA T × RawRunConf T =>
      decide (p.2.2.1 = ([] : List T))) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const [])
  have hstate : Primrec (fun p : EncodedDPDA T × RawRunConf T =>
      p.2.1 % p.1.numStates) :=
    Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
      (numStates_primrec.comp Primrec.fst)
  have hfinal : Primrec (fun p : EncodedDPDA T × RawRunConf T =>
      decide (p.2.1 % p.1.numStates ∈ p.1.normalizedFinals)) :=
    primrec_list_memBool.comp hstate
      (normalizedFinals_primrec.comp Primrec.fst)
  apply Primrec.of_eq (Primrec.and.comp hinputNil hfinal)
  intro p
  simp [acceptingRunConf, Bool.decide_and]

/-! Compact data for the executable run.  The full encoded table is reduced
once; recursive iteration carries only the two moduli and the effective rows. -/

private def effectiveRunData (c : EncodedDPDA T) : InputSelectionData T :=
  ((c.numStates, c.numStackSymbols),
    (c.effectiveEpsilonRows, c.effectiveInputRows))

private def dataEpsilonEnabled (nm : SelectionSizes)
    (q Z : ℕ) (row : EpsilonRow) : Bool :=
  decide (q = row.1 % nm.1 ∧ Z = row.2.1 % nm.2)

private def dataInputEnabled (nm : SelectionSizes)
    (q : ℕ) (a : T) (Z : ℕ) (row : InputRow T) : Bool :=
  decide (q = row.1 % nm.1 ∧ row.2.1 = a ∧
    Z = row.2.2.1 % nm.2)

private def dataEpsilonResult (nm : SelectionSizes)
    (v : List T) (suffix : List ℕ) (row : EpsilonRow) : RawRunConf T :=
  (row.2.2.1 % nm.1, v,
    row.2.2.2.map (fun X => X % nm.2) ++ suffix)

private def dataInputResult (nm : SelectionSizes)
    (w : List T) (suffix : List ℕ) (row : InputRow T) : RawRunConf T :=
  (row.2.2.2.1 % nm.1, w,
    row.2.2.2.2.map (fun X => X % nm.2) ++ suffix)

private def nextRunConfData (d : InputSelectionData T)
    (x : RawRunConf T) : Option (RawRunConf T) :=
  match x.2.2 with
  | [] => none
  | Z :: suffix =>
      match d.2.1.find? (dataEpsilonEnabled d.1 x.1 Z) with
      | some row => some (dataEpsilonResult d.1 x.2.1 suffix row)
      | none =>
          match x.2.1 with
          | [] => none
          | a :: w =>
              (d.2.2.find? (dataInputEnabled d.1 x.1 a Z)).map
                (dataInputResult d.1 w suffix)

private def advanceRunConfData (d : InputSelectionData T)
    (x : RawRunConf T) : RawRunConf T :=
  (nextRunConfData d x).getD x

private def runFuelData (d : InputSelectionData T)
    (x : RawRunConf T) : ℕ → RawRunConf T
  | 0 => x
  | n + 1 => advanceRunConfData d (runFuelData d x n)

private theorem nextRunConfData_effectiveRunData (c : EncodedDPDA T)
    (x : RawRunConf T) :
    nextRunConfData (effectiveRunData c) x = c.nextRunConf x := by
  unfold nextRunConfData effectiveRunData nextRunConf dataEpsilonEnabled
    dataInputEnabled dataEpsilonResult dataInputResult epsilonRunEnabled
    inputRunEnabled epsilonRunResult inputRunResult normalizedEpsilonSource
    normalizedEpsilonTop normalizedEpsilonTarget
    normalizedEpsilonReplacement normalizedInputSource normalizedInputTop
    normalizedInputTarget normalizedInputReplacement
  rfl

private theorem runFuelData_effectiveRunData (c : EncodedDPDA T)
    (x : RawRunConf T) (n : ℕ) :
    runFuelData (effectiveRunData c) x n = c.runFuel x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [runFuelData, runFuel, advanceRunConfData, advanceRunConf, ih,
        nextRunConfData_effectiveRunData]

private theorem effectiveRunData_primrec :
    Primrec (effectiveRunData : EncodedDPDA T → InputSelectionData T) := by
  exact Primrec.pair
    (Primrec.pair numStates_primrec numStackSymbols_primrec)
    (Primrec.pair effectiveEpsilonRows_primrec effectiveInputRows_primrec)

private abbrev DataEpsilonEnabledContext := SelectionSizes × ℕ × ℕ

private theorem dataEpsilonEnabled_primrec :
    Primrec₂ (fun (p : DataEpsilonEnabledContext) (row : EpsilonRow) =>
      dataEpsilonEnabled p.1 p.2.1 p.2.2 row) := by
  show Primrec (fun q : DataEpsilonEnabledContext × EpsilonRow =>
    dataEpsilonEnabled q.1.1 q.1.2.1 q.1.2.2 q.2)
  have hn : Primrec (fun q : DataEpsilonEnabledContext × EpsilonRow =>
      q.1.1.1) := Primrec.fst.comp
    (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : DataEpsilonEnabledContext × EpsilonRow =>
      q.1.1.2) := Primrec.snd.comp
    (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun q : DataEpsilonEnabledContext × EpsilonRow =>
      q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hZ : Primrec (fun q : DataEpsilonEnabledContext × EpsilonRow =>
      q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hsource := Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd) hn
  have htop := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hm
  apply Primrec.of_eq (Primrec.and.comp
    ((PrimrecRel.decide Primrec.eq).comp hq hsource)
    ((PrimrecRel.decide Primrec.eq).comp hZ htop))
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [dataEpsilonEnabled]

private abbrev DataInputEnabledContext (T : Type) :=
  SelectionSizes × ℕ × T × ℕ

private theorem dataInputEnabled_primrec :
    Primrec₂ (fun (p : DataInputEnabledContext T) (row : InputRow T) =>
      dataInputEnabled p.1 p.2.1 p.2.2.1 p.2.2.2 row) := by
  show Primrec (fun q : DataInputEnabledContext T × InputRow T =>
    dataInputEnabled q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
  have hn : Primrec (fun q : DataInputEnabledContext T × InputRow T =>
      q.1.1.1) := Primrec.fst.comp
    (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : DataInputEnabledContext T × InputRow T =>
      q.1.1.2) := Primrec.snd.comp
    (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun q : DataInputEnabledContext T × InputRow T =>
      q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ha : Primrec (fun q : DataInputEnabledContext T × InputRow T =>
      q.1.2.2.1) := Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hZ : Primrec (fun q : DataInputEnabledContext T × InputRow T =>
      q.1.2.2.2) := Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hsource := Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd) hn
  have hletter : Primrec
      (fun q : DataInputEnabledContext T × InputRow T => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have htop := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))) hm
  apply Primrec.of_eq (Primrec.and.comp
    ((PrimrecRel.decide Primrec.eq).comp hq hsource)
    (Primrec.and.comp
      ((PrimrecRel.decide Primrec.eq).comp hletter ha)
      ((PrimrecRel.decide Primrec.eq).comp hZ htop)))
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [dataInputEnabled]

private abbrev DataResultContext (T : Type) :=
  SelectionSizes × List T × List ℕ

private theorem dataEpsilonResult_primrec :
    Primrec₂ (fun (p : DataResultContext T) (row : EpsilonRow) =>
      dataEpsilonResult p.1 p.2.1 p.2.2 row) := by
  show Primrec (fun q : DataResultContext T × EpsilonRow =>
    dataEpsilonResult q.1.1 q.1.2.1 q.1.2.2 q.2)
  have hn : Primrec (fun q : DataResultContext T × EpsilonRow =>
      q.1.1.1) := Primrec.fst.comp
    (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : DataResultContext T × EpsilonRow =>
      q.1.1.2) := Primrec.snd.comp
    (Primrec.fst.comp Primrec.fst)
  have htarget := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))) hn
  have hrowReplacement : Primrec
      (fun q : DataResultContext T × EpsilonRow =>
        (q.2.2.2.2 : List ℕ)) :=
    Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))
  have hmapped : Primrec
      (fun q : DataResultContext T × EpsilonRow =>
        List.map (fun X => X % q.1.1.2) q.2.2.2.2) :=
    modList_primrec.comp hm hrowReplacement
  have hsuffix : Primrec
      (fun q : DataResultContext T × EpsilonRow => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hreplacement : Primrec
      (fun q : DataResultContext T × EpsilonRow =>
        List.map (fun X => X % q.1.1.2) q.2.2.2.2 ++ q.1.2.2) :=
    Primrec.list_append.comp hmapped hsuffix
  have hresult := Primrec.pair htarget (Primrec.pair
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hreplacement)
  exact Primrec.of_eq hresult fun q => by rfl

private theorem dataInputResult_primrec :
    Primrec₂ (fun (p : DataResultContext T) (row : InputRow T) =>
      dataInputResult p.1 p.2.1 p.2.2 row) := by
  show Primrec (fun q : DataResultContext T × InputRow T =>
    dataInputResult q.1.1 q.1.2.1 q.1.2.2 q.2)
  have hn : Primrec (fun q : DataResultContext T × InputRow T =>
      q.1.1.1) := Primrec.fst.comp
    (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : DataResultContext T × InputRow T =>
      q.1.1.2) := Primrec.snd.comp
    (Primrec.fst.comp Primrec.fst)
  have htarget := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))) hn
  have hrowReplacement : Primrec
      (fun q : DataResultContext T × InputRow T =>
        (q.2.2.2.2.2 : List ℕ)) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))
  have hmapped : Primrec
      (fun q : DataResultContext T × InputRow T =>
        List.map (fun X => X % q.1.1.2) q.2.2.2.2.2) :=
    modList_primrec.comp hm hrowReplacement
  have hsuffix : Primrec
      (fun q : DataResultContext T × InputRow T => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hreplacement : Primrec
      (fun q : DataResultContext T × InputRow T =>
        List.map (fun X => X % q.1.1.2) q.2.2.2.2.2 ++ q.1.2.2) :=
    Primrec.list_append.comp hmapped hsuffix
  have hresult := Primrec.pair htarget (Primrec.pair
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hreplacement)
  exact Primrec.of_eq hresult fun q => by rfl

private abbrev DataRunContext (T : Type) :=
  InputSelectionData T × RawRunConf T

private abbrev DataStackRunContext (T : Type) :=
  DataRunContext T × ℕ × List ℕ

private abbrev DataInputRunContext (T : Type) :=
  DataStackRunContext T × T × List T

private def dataEpsilonFind (p : DataStackRunContext T) : Option EpsilonRow :=
  p.1.1.2.1.find? (dataEpsilonEnabled p.1.1.1 p.1.2.1 p.2.1)

private theorem dataEpsilonFind_primrec :
    Primrec (dataEpsilonFind : DataStackRunContext T → Option EpsilonRow) := by
  have hpredicate : Primrec₂
      (fun (p : DataStackRunContext T) (row : EpsilonRow) =>
        dataEpsilonEnabled p.1.1.1 p.1.2.1 p.2.1 row) := by
    show Primrec (fun q : DataStackRunContext T × EpsilonRow =>
      dataEpsilonEnabled q.1.1.1.1 q.1.1.2.1 q.1.2.1 q.2)
    have hn : Primrec (fun q : DataStackRunContext T × EpsilonRow =>
        q.1.1.1.1.1) := Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hm : Primrec (fun q : DataStackRunContext T × EpsilonRow =>
        q.1.1.1.1.2) := Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hq : Primrec (fun q : DataStackRunContext T × EpsilonRow =>
        q.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst))
    have hZ : Primrec (fun q : DataStackRunContext T × EpsilonRow =>
        q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hsource := Primrec.nat_mod.comp
      (Primrec.fst.comp Primrec.snd) hn
    have htop := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hm
    apply Primrec.of_eq (Primrec.and.comp
      ((PrimrecRel.decide Primrec.eq).comp hq hsource)
      ((PrimrecRel.decide Primrec.eq).comp hZ htop))
    intro q
    apply Bool.eq_iff_iff.mpr
    simp [dataEpsilonEnabled]
  have hrows : Primrec (fun p : DataStackRunContext T => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst))
  apply Primrec.of_eq
    (primrec_list_find? hrows hpredicate)
  intro p
  rfl

private def dataEpsilonSelectedResult
    (q : DataStackRunContext T × EpsilonRow) : RawRunConf T :=
  dataEpsilonResult q.1.1.1.1 q.1.1.2.2.1 q.1.2.2 q.2

private theorem dataEpsilonSelectedResult_computable :
    Computable (dataEpsilonSelectedResult :
      DataStackRunContext T × EpsilonRow → RawRunConf T) := by
  have hcontext : Computable
      (fun q : DataStackRunContext T × EpsilonRow =>
        (q.1.1.1.1, q.1.1.2.2.1, q.1.2.2)) :=
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to_comp
  have hresult := dataEpsilonResult_primrec.to_comp.comp hcontext Computable.snd
  apply Computable.of_eq hresult
  intro q
  rfl

private def dataEpsilonNext
    (p : DataStackRunContext T) : Option (RawRunConf T) :=
  (dataEpsilonFind p).map fun row => dataEpsilonSelectedResult (p, row)

private theorem dataEpsilonNext_computable :
    Computable (dataEpsilonNext :
      DataStackRunContext T → Option (RawRunConf T)) :=
  Computable.option_map dataEpsilonFind_primrec.to_comp
    dataEpsilonSelectedResult_computable.to₂

private def dataInputFind (q : DataInputRunContext T) : Option (InputRow T) :=
  q.1.1.1.2.2.find?
    (dataInputEnabled q.1.1.1.1 q.1.1.2.1 q.2.1 q.1.2.1)

private theorem dataInputFind_primrec :
    Primrec (dataInputFind : DataInputRunContext T → Option (InputRow T)) := by
  have hpredicate : Primrec₂
      (fun (q : DataInputRunContext T) (row : InputRow T) =>
        dataInputEnabled q.1.1.1.1 q.1.1.2.1 q.2.1 q.1.2.1 row) := by
    show Primrec (fun z : DataInputRunContext T × InputRow T =>
      dataInputEnabled z.1.1.1.1.1 z.1.1.1.2.1
        z.1.2.1 z.1.1.2.1 z.2)
    have hn : Primrec (fun z : DataInputRunContext T × InputRow T =>
        z.1.1.1.1.1.1) := Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.fst))))
    have hm : Primrec (fun z : DataInputRunContext T × InputRow T =>
        z.1.1.1.1.1.2) := Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.fst))))
    have hq : Primrec (fun z : DataInputRunContext T × InputRow T =>
        z.1.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have ha : Primrec (fun z : DataInputRunContext T × InputRow T =>
        z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hZ : Primrec (fun z : DataInputRunContext T × InputRow T =>
        z.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst))
    have hsource := Primrec.nat_mod.comp
      (Primrec.fst.comp Primrec.snd) hn
    have hletter : Primrec (fun z : DataInputRunContext T × InputRow T =>
        z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have htop := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd))) hm
    apply Primrec.of_eq (Primrec.and.comp
      ((PrimrecRel.decide Primrec.eq).comp hq hsource)
      (Primrec.and.comp
        ((PrimrecRel.decide Primrec.eq).comp hletter ha)
        ((PrimrecRel.decide Primrec.eq).comp hZ htop)))
    intro z
    apply Bool.eq_iff_iff.mpr
    simp [dataInputEnabled]
  have hrows : Primrec
      (fun q : DataInputRunContext T => q.1.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  apply Primrec.of_eq
    (primrec_list_find? hrows hpredicate)
  intro q
  rfl

private def dataInputSelectedResult
    (z : DataInputRunContext T × InputRow T) : RawRunConf T :=
  dataInputResult z.1.1.1.1.1 z.1.2.2 z.1.1.2.2 z.2

private theorem dataInputSelectedResult_computable :
    Computable (dataInputSelectedResult :
      DataInputRunContext T × InputRow T → RawRunConf T) := by
  have hcontext : Computable
      (fun z : DataInputRunContext T × InputRow T =>
        (z.1.1.1.1.1, z.1.2.2, z.1.1.2.2)) :=
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst))))).to_comp
  apply Computable.of_eq
    (dataInputResult_primrec.to_comp.comp hcontext Computable.snd)
  intro z
  rfl

private def dataInputNext (q : DataInputRunContext T) : Option (RawRunConf T) :=
  (dataInputFind q).map fun row => dataInputSelectedResult (q, row)

private theorem dataInputNext_computable :
    Computable (dataInputNext :
      DataInputRunContext T → Option (RawRunConf T)) :=
  Computable.option_map dataInputFind_primrec.to_comp
    dataInputSelectedResult_computable.to₂

private def dataInputNextFromStack
    (p : DataStackRunContext T) : Option (RawRunConf T) :=
  match p.1.2.2.1 with
  | [] => none
  | a :: w => dataInputNext (p, a, w)

private theorem dataInputNextFromStack_computable :
    Computable (dataInputNextFromStack :
      DataStackRunContext T → Option (RawRunConf T)) := by
  have hinput : Computable (fun p : DataStackRunContext T => p.1.2.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))).to_comp
  have hhead : Computable (fun p : DataStackRunContext T =>
      p.1.2.2.1.head?) :=
    Primrec.list_head?.to_comp.comp hinput
  have htail : Computable (fun p : DataStackRunContext T =>
      p.1.2.2.1.tail) :=
    Primrec.list_tail.to_comp.comp hinput
  have hsome : Computable₂
      (fun (p : DataStackRunContext T) (a : T) =>
        dataInputNext (p, a, p.1.2.2.1.tail)) := by
    apply Computable₂.mk
    have hcontext : Computable
        (fun q : DataStackRunContext T × T =>
          (q.1, q.2, q.1.1.2.2.1.tail)) :=
      Computable.pair Computable.fst
        (Computable.pair Computable.snd (htail.comp Computable.fst))
    exact dataInputNext_computable.comp hcontext
  apply (Computable.option_casesOn hhead (Computable.const none) hsome).of_eq
  intro p
  generalize hinput' : p.1.2.2.1 = input
  cases input <;> simp [dataInputNextFromStack, hinput']

private def nextRunConfDataAfterPop
    (p : DataStackRunContext T) : Option (RawRunConf T) :=
  dataEpsilonNext p <|> dataInputNextFromStack p

private theorem nextRunConfDataAfterPop_computable :
    Computable (nextRunConfDataAfterPop :
      DataStackRunContext T → Option (RawRunConf T)) := by
  exact Primrec.option_orElse.to_comp.comp
    dataEpsilonNext_computable dataInputNextFromStack_computable

private theorem nextRunConfData_computable :
    Computable (fun p : DataRunContext T => nextRunConfData p.1 p.2) := by
  have hstack : Computable (fun p : DataRunContext T => p.2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to_comp
  have hhead : Computable (fun p : DataRunContext T => p.2.2.2.head?) :=
    Primrec.list_head?.to_comp.comp hstack
  have htail : Computable (fun p : DataRunContext T => p.2.2.2.tail) :=
    Primrec.list_tail.to_comp.comp hstack
  have hsome : Computable₂ (fun (p : DataRunContext T) (Z : ℕ) =>
      nextRunConfDataAfterPop (p, Z, p.2.2.2.tail)) := by
    apply Computable₂.mk
    have hcontext : Computable
        (fun q : DataRunContext T × ℕ =>
          (q.1, q.2, q.1.2.2.2.tail)) :=
      Computable.pair Computable.fst
        (Computable.pair Computable.snd (htail.comp Computable.fst))
    exact nextRunConfDataAfterPop_computable.comp hcontext
  apply (Computable.option_casesOn hhead (Computable.const none) hsome).of_eq
  intro p
  generalize hstack' : p.2.2.2 = stack
  cases stack with
  | nil =>
      simp [nextRunConfData, hstack']
  | cons Z suffix =>
      cases hε : p.1.2.1.find?
          (dataEpsilonEnabled p.1.1 p.2.1 Z) with
      | none =>
          simp [nextRunConfData, nextRunConfDataAfterPop, dataEpsilonFind,
            dataEpsilonNext, dataInputNextFromStack, dataInputNext,
            dataInputFind, dataEpsilonSelectedResult,
            dataInputSelectedResult, hstack', hε]
      | some row =>
          simp [nextRunConfData, nextRunConfDataAfterPop, dataEpsilonFind,
            dataEpsilonNext, dataInputNextFromStack, dataInputNext,
            dataInputFind, dataEpsilonSelectedResult,
            dataInputSelectedResult, hstack', hε]

private theorem advanceRunConfData_computable :
    Computable (fun p : DataRunContext T => advanceRunConfData p.1 p.2) :=
  Computable.option_getD nextRunConfData_computable Computable.snd

private def advanceRunDataState (p : DataRunContext T) : DataRunContext T :=
  (p.1, advanceRunConfData p.1 p.2)

private theorem advanceRunDataState_computable :
    Computable (advanceRunDataState : DataRunContext T → DataRunContext T) := by
  exact Computable.pair Computable.fst advanceRunConfData_computable

private def defaultRunDataState : DataRunContext T :=
  (((1, 1), ([], [])), (0, [], []))

private def decodeRunDataCode (n : ℕ) : DataRunContext T :=
  (Encodable.decode (α := DataRunContext T) n).getD defaultRunDataState

private theorem decodeRunDataCode_computable :
    Computable (decodeRunDataCode : ℕ → DataRunContext T) := by
  exact Computable.option_getD
    (Computable.decode (α := DataRunContext T))
    (Computable.const (defaultRunDataState (T := T)))

private def advanceRunDataCode (T : Type) [DecidableEq T] [Primcodable T]
    (n : ℕ) : ℕ :=
  Encodable.encode (advanceRunDataState
    (decodeRunDataCode (T := T) n))

private theorem advanceRunDataCode_computable :
    Computable (advanceRunDataCode T) := by
  exact (@Computable.encode (DataRunContext T) _).comp
    (advanceRunDataState_computable.comp decodeRunDataCode_computable)

private def iterateRunCode (T : Type) [DecidableEq T] [Primcodable T]
    (p : ℕ × ℕ) : ℕ :=
  Nat.rec p.1 (fun _ code => advanceRunDataCode T code) p.2

private theorem iterateRunCode_computable :
    Computable (iterateRunCode T) := by
  have hstep : Computable₂ (fun (_ : ℕ × ℕ) (nr : ℕ × ℕ) =>
      advanceRunDataCode T nr.2) := by
    apply Computable₂.mk
    have hcode : Computable
        (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.2) :=
      Computable.snd.comp Computable.snd
    exact advanceRunDataCode_computable.comp hcode
  apply (Computable.nat_rec Computable.snd Computable.fst hstep).of_eq
  intro p
  rfl

private def iterateRunDataCode
    (p : DataRunContext T × ℕ) : ℕ :=
  iterateRunCode T (Encodable.encode p.1, p.2)

private theorem iterateRunDataCode_computable :
    Computable (iterateRunDataCode : DataRunContext T × ℕ → ℕ) := by
  have hencoded : Computable (fun p : DataRunContext T × ℕ =>
      Encodable.encode p.1) :=
    (@Computable.encode (DataRunContext T) _).comp Computable.fst
  have hinput : Computable (fun p : DataRunContext T × ℕ =>
      (Encodable.encode p.1, p.2)) :=
    Computable.pair hencoded Computable.snd
  exact iterateRunCode_computable.comp hinput

private theorem iterateRunDataCode_eq_encode
    (p : DataRunContext T × ℕ) :
    iterateRunDataCode p = Encodable.encode
      (p.1.1, runFuelData p.1.1 p.1.2 p.2) := by
  rcases p with ⟨state, n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      change advanceRunDataCode T (iterateRunDataCode (state, n)) =
        Encodable.encode
          (state.1, advanceRunConfData state.1
            (runFuelData state.1 state.2 n))
      rw [ih]
      simp [advanceRunDataCode, decodeRunDataCode, advanceRunDataState]

private theorem runFuelData_computable :
    Computable (fun p : DataRunContext T × ℕ =>
      runFuelData p.1.1 p.1.2 p.2) := by
  have hdecoded : Computable (fun p : DataRunContext T × ℕ =>
      (Encodable.decode (α := DataRunContext T)
        (iterateRunDataCode p)).getD p.1) :=
    Computable.option_getD
      (Computable.decode.comp iterateRunDataCode_computable)
      Computable.fst
  apply (Computable.snd.comp hdecoded).of_eq
  intro p
  rw [iterateRunDataCode_eq_encode]
  simp

private def acceptingRunConfData
    (p : (ℕ × List ℕ) × RawRunConf T) : Bool :=
  decide (p.2.2.1 = [] ∧ p.2.1 % p.1.1 ∈ p.1.2)

private theorem acceptingRunConfData_primrec :
    Primrec (acceptingRunConfData :
      (ℕ × List ℕ) × RawRunConf T → Bool) := by
  have hinputNil : Primrec (fun p : (ℕ × List ℕ) × RawRunConf T =>
      decide (p.2.2.1 = [])) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const [])
  have hstate : Primrec (fun p : (ℕ × List ℕ) × RawRunConf T =>
      p.2.1 % p.1.1) :=
    Primrec.nat_mod.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have hfinal : Primrec (fun p : (ℕ × List ℕ) × RawRunConf T =>
      decide (p.2.1 % p.1.1 ∈ p.1.2)) :=
    primrec_list_memBool.comp
      hstate (Primrec.snd.comp Primrec.fst)
  apply Primrec.of_eq (Primrec.and.comp hinputNil hfinal)
  intro p
  simp [acceptingRunConfData, Bool.decide_and]

private abbrev FuelAcceptanceData (T : Type) :=
  (List ℕ × DataRunContext T) × ℕ

private def acceptsFuelData (p : FuelAcceptanceData T) : Bool :=
  acceptingRunConfData
    ((p.1.2.1.1.1, p.1.1),
      runFuelData p.1.2.1 p.1.2.2 p.2)

private def fuelAcceptanceRunInput
    (p : FuelAcceptanceData T) : DataRunContext T × ℕ :=
  (p.1.2, p.2)

private theorem fuelAcceptanceRunInput_computable :
    Computable (fuelAcceptanceRunInput :
      FuelAcceptanceData T → DataRunContext T × ℕ) := by
  exact Computable.pair
    (Computable.snd.comp Computable.fst) Computable.snd

private def fuelAcceptanceRun
    (p : FuelAcceptanceData T) : RawRunConf T :=
  runFuelData p.1.2.1 p.1.2.2 p.2

private theorem fuelAcceptanceRun_computable :
    Computable (fuelAcceptanceRun :
      FuelAcceptanceData T → RawRunConf T) := by
  apply (runFuelData_computable.comp
    fuelAcceptanceRunInput_computable).of_eq
  intro p
  rfl

private def fuelAcceptanceMeta
    (p : FuelAcceptanceData T) : ℕ × List ℕ :=
  (p.1.2.1.1.1, p.1.1)

private theorem fuelAcceptanceMeta_computable :
    Computable (fuelAcceptanceMeta :
      FuelAcceptanceData T → ℕ × List ℕ) := by
  have hstates : Computable (fun p : FuelAcceptanceData T =>
      p.1.2.1.1.1) :=
    (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).to_comp
  have hfinals : Computable (fun p : FuelAcceptanceData T =>
      p.1.1) :=
    Computable.fst.comp Computable.fst
  exact Computable.pair hstates hfinals

private def fuelAcceptanceResultInput
    (p : FuelAcceptanceData T) : (ℕ × List ℕ) × RawRunConf T :=
  (fuelAcceptanceMeta p, fuelAcceptanceRun p)

private theorem fuelAcceptanceResultInput_computable :
    Computable (fuelAcceptanceResultInput :
      FuelAcceptanceData T → (ℕ × List ℕ) × RawRunConf T) := by
  exact Computable.pair fuelAcceptanceMeta_computable
    fuelAcceptanceRun_computable

private theorem acceptsFuelData_computable :
    Computable (acceptsFuelData : FuelAcceptanceData T → Bool) := by
  apply (acceptingRunConfData_primrec.to_comp.comp
    fuelAcceptanceResultInput_computable).of_eq
  intro p
  rfl

private def encodedFuelAcceptanceInput
    (p : (EncodedDPDA T × List T) × ℕ) : FuelAcceptanceData T :=
  ((p.1.1.normalizedFinals,
      (effectiveRunData p.1.1, p.1.1.initialRunConf p.1.2)), p.2)

private theorem encodedFuelAcceptanceInput_computable :
    Computable (encodedFuelAcceptanceInput :
      ((EncodedDPDA T × List T) × ℕ) → FuelAcceptanceData T) := by
  have hcode : Computable (fun p : (EncodedDPDA T × List T) × ℕ =>
      p.1.1) :=
    Computable.fst.comp Computable.fst
  have hword : Computable (fun p : (EncodedDPDA T × List T) × ℕ =>
      p.1.2) :=
    Computable.snd.comp Computable.fst
  have hinitial : Computable (fun p : (EncodedDPDA T × List T) × ℕ =>
      p.1.1.initialRunConf p.1.2) :=
    initialRunConf_primrec.to_comp.comp hcode hword
  have hrundata : Computable (fun p : (EncodedDPDA T × List T) × ℕ =>
      effectiveRunData p.1.1) :=
    effectiveRunData_primrec.to_comp.comp hcode
  have hstate : Computable (fun p : (EncodedDPDA T × List T) × ℕ =>
      (effectiveRunData p.1.1, p.1.1.initialRunConf p.1.2)) :=
    Computable.pair hrundata hinitial
  have hfinals : Computable (fun p : (EncodedDPDA T × List T) × ℕ =>
      p.1.1.normalizedFinals) :=
    normalizedFinals_primrec.to_comp.comp hcode
  exact Computable.pair
    (Computable.pair hfinals hstate) Computable.snd

private theorem acceptsFuelData_encoded_eq
    (p : (EncodedDPDA T × List T) × ℕ) :
    acceptsFuelData (encodedFuelAcceptanceInput p) =
      p.1.1.acceptsAtFuel p.1.2 p.2 := by
  change acceptingRunConfData
      ((p.1.1.numStates, p.1.1.normalizedFinals),
        runFuelData (effectiveRunData p.1.1)
          (p.1.1.initialRunConf p.1.2) p.2) =
    p.1.1.acceptsAtFuel p.1.2 p.2
  unfold acceptingRunConfData acceptsAtFuel acceptingRunConf
  rw [runFuelData_effectiveRunData]

private theorem acceptsAtFuel_computable :
    Computable (fun p : (EncodedDPDA T × List T) × ℕ =>
      p.1.1.acceptsAtFuel p.1.2 p.2) := by
  exact (acceptsFuelData_computable.comp
    encodedFuelAcceptanceInput_computable).of_eq acceptsFuelData_encoded_eq

/- The first direct computability proof carried the complete encoded table
through every finite-list callback.  It is retained temporarily for comparison,
but the compact proof below is the compiled one. -/
/-
private theorem isRejectingIndex_primrec :
    Primrec₂ (isRejectingIndex : EncodedDPDA T → ℕ → Bool) := by
  show Primrec (fun p : EncodedDPDA T × ℕ => p.1.isRejectingIndex p.2)
  have hlt : Primrec (fun p : EncodedDPDA T × ℕ =>
      decide (p.2 < p.1.numStates)) :=
    (PrimrecRel.decide Primrec.nat_lt).comp Primrec.snd
      (numStates_primrec.comp Primrec.fst)
  have hmem : Primrec (fun p : EncodedDPDA T × ℕ =>
      decide (p.2 ∈ p.1.normalizedFinals)) :=
    primrec_list_memBool.comp Primrec.snd
      (normalizedFinals_primrec.comp Primrec.fst)
  apply Primrec.of_eq (Primrec.and.comp hlt (Primrec.not.comp hmem))
  intro p
  apply Bool.eq_iff_iff.mpr
  simp [isRejectingIndex]

private theorem allSummaryTriples_primrec :
    Primrec (allSummaryTriples : EncodedDPDA T → List SummaryTriple) := by
  have hlast : Primrec₂
      (fun (ctx : (EncodedDPDA T × ℕ) × ℕ) (r : ℕ) =>
        (ctx.1.2, ctx.2, r)) := by
    show Primrec (fun q : ((EncodedDPDA T × ℕ) × ℕ) × ℕ =>
      (q.1.1.2, q.1.2, q.2))
    exact Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hforTop : Primrec₂
      (fun (ctx : EncodedDPDA T × ℕ) (Z : ℕ) =>
        (List.range ctx.1.pStateCount).map fun r =>
          (ctx.2, Z, r)) := by
    show Primrec (fun q : (EncodedDPDA T × ℕ) × ℕ =>
      (List.range q.1.1.pStateCount).map fun r =>
        (q.1.2, q.2, r))
    exact Primrec.list_map
      (Primrec.list_range.comp
        (pStateCount_primrec.comp (Primrec.fst.comp Primrec.fst))) hlast
  have hforSource : Primrec₂
      (fun (c : EncodedDPDA T) (p : ℕ) =>
        (List.range c.numStackSymbols).flatMap fun Z =>
          (List.range c.pStateCount).map fun r =>
            (p, Z, r)) := by
    show Primrec (fun q : EncodedDPDA T × ℕ =>
      (List.range q.1.numStackSymbols).flatMap fun Z =>
        (List.range q.1.pStateCount).map fun r =>
          (q.2, Z, r))
    exact Primrec.list_flatMap
      (Primrec.list_range.comp (numStackSymbols_primrec.comp Primrec.fst)) hforTop
  unfold allSummaryTriples
  exact Primrec.list_flatMap
    (Primrec.list_range.comp pStateCount_primrec) hforSource

private theorem baseSummaryTriples_primrec :
    Primrec (baseSummaryTriples : EncodedDPDA T → List SummaryTriple) := by
  apply primrec_list_filterBool allSummaryTriples_primrec
  show Primrec₂ (fun c (t : SummaryTriple) => decide
    ((t.1 = c.sinkIndex ∧ t.2.2 = c.sinkIndex) ∨
      (c.isRejectingIndex t.1 = true ∧ t.2.2 = c.sinkIndex)))
  have hpSink : Primrec (fun q : EncodedDPDA T × SummaryTriple =>
      decide (q.2.1 = q.1.sinkIndex)) :=
    (PrimrecRel.decide Primrec.eq).comp (Primrec.fst.comp Primrec.snd)
      (sinkIndex_primrec.comp Primrec.fst)
  have hrSink : Primrec (fun q : EncodedDPDA T × SummaryTriple =>
      decide (q.2.2.2 = q.1.sinkIndex)) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (sinkIndex_primrec.comp Primrec.fst)
  have hreject : Primrec (fun q : EncodedDPDA T × SummaryTriple =>
      q.1.isRejectingIndex q.2.1) :=
    isRejectingIndex_primrec.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  apply Primrec.of_eq (Primrec.or.comp
    (Primrec.and.comp hpSink hrSink)
    (Primrec.and.comp hreject hrSink))
  intro q
  simp [Bool.decide_and, Bool.decide_or]

private abbrev AdvanceContext (T : Type) :=
  (EncodedDPDA T × List SummaryTriple) × (List ℕ × ℕ)

private theorem advanceSummaryStates_primrec :
    Primrec (fun q : AdvanceContext T =>
      q.1.1.advanceSummaryStates q.1.2 q.2.1 q.2.2) := by
  have hstateList : Primrec (fun z : AdvanceContext T × ℕ => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hmod : Primrec (fun q : (AdvanceContext T × ℕ) × ℕ =>
      q.1.1.2.2 % q.1.1.1.1.numStackSymbols) :=
    Primrec.nat_mod.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (numStackSymbols_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have htriple : Primrec₂ (fun (z : AdvanceContext T × ℕ) (p : ℕ) =>
      (p, z.1.2.2 % z.1.1.1.numStackSymbols, z.2)) := by
    show Primrec (fun q : (AdvanceContext T × ℕ) × ℕ =>
      (q.2, q.1.1.2.2 % q.1.1.1.1.numStackSymbols,
        q.1.2))
    exact Primrec.pair Primrec.snd
      (Primrec.pair hmod (Primrec.snd.comp Primrec.fst))
  have hrelation : Primrec (fun z : AdvanceContext T × ℕ => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hmember : Primrec₂ (fun (z : AdvanceContext T × ℕ) (p : ℕ) =>
      decide ((p, z.1.2.2 % z.1.1.1.numStackSymbols, z.2) ∈
        z.1.1.2)) :=
    primrec_list_memBool.comp htriple (hrelation.comp Primrec.fst)
  have hpredicate : Primrec₂ (fun (q : AdvanceContext T) (middle : ℕ) =>
      q.2.1.any fun p => decide
        ((p, q.2.2 % q.1.1.numStackSymbols, middle) ∈ q.1.2)) := by
    show Primrec (fun z : AdvanceContext T × ℕ =>
      z.1.2.1.any fun p => decide
        ((p, z.1.2.2 % z.1.1.1.numStackSymbols, z.2) ∈
          z.1.1.2))
    exact primrec_list_any_fast hstateList hmember
  unfold advanceSummaryStates
  exact primrec_list_filterBool
    (Primrec.list_range.comp
      (pStateCount_primrec.comp (Primrec.fst.comp Primrec.fst))) hpredicate

private abbrev DestinationContext (T : Type) :=
  (EncodedDPDA T × List SummaryTriple) × (List ℕ × List ℕ)

private theorem summaryDestinations_primrec :
    Primrec (fun q : DestinationContext T =>
      q.1.1.summaryDestinations q.1.2 q.2.1 q.2.2) := by
  apply primrec_list_foldl
    (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  show Primrec₂ (fun (q : DestinationContext T) (sZ : List ℕ × ℕ) =>
    q.1.1.advanceSummaryStates q.1.2 sZ.1 sZ.2)
  show Primrec (fun p : DestinationContext T × (List ℕ × ℕ) =>
    p.1.1.1.advanceSummaryStates p.1.1.2 p.2.1 p.2.2)
  exact advanceSummaryStates_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

private abbrev PathContext (T : Type) :=
  (EncodedDPDA T × List SummaryTriple) × (ℕ × List ℕ × ℕ)

private theorem summaryPath_primrec :
    Primrec (fun q : PathContext T =>
      q.1.1.summaryPath q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
  have hstates : Primrec (fun q : PathContext T => [q.2.1]) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])
  have hdestInput : Primrec (fun q : PathContext T =>
      ((q.1.1, q.1.2), ([(q.2.1)], q.2.2.1))) :=
    Primrec.pair Primrec.fst
      (Primrec.pair hstates
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hdest : Primrec (fun q : PathContext T =>
      q.1.1.summaryDestinations q.1.2 [q.2.1] q.2.2.1) :=
    summaryDestinations_primrec.comp hdestInput
  unfold summaryPath
  exact primrec_list_memBool.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hdest

private abbrev ClosedContext (T : Type) :=
  EncodedDPDA T × List SummaryTriple

private theorem baseClosed_primrec :
    Primrec (fun q : ClosedContext T =>
      q.1.baseSummaryTriples.all fun t => decide (t ∈ q.2)) := by
  exact primrec_list_all
    (baseSummaryTriples_primrec.comp Primrec.fst)
    (primrec_list_memBool.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst))

private abbrev EpsilonClosureContext (T : Type) :=
  ClosedContext T × EpsilonRow

private theorem epsilonClosureRow_primrec :
    Primrec₂ (fun (q : ClosedContext T) (row : EpsilonRow) =>
      (List.range q.1.pStateCount).all fun r =>
        decide (q.1.summaryPath q.2 (q.1.normalizedEpsilonTarget row)
            (q.1.normalizedEpsilonReplacement row) r = true →
          (q.1.normalizedEpsilonSource row,
            q.1.normalizedEpsilonTop row, r) ∈ q.2)) := by
  show Primrec (fun e : EpsilonClosureContext T =>
    (List.range e.1.1.pStateCount).all fun r =>
      decide (e.1.1.summaryPath e.1.2 (e.1.1.normalizedEpsilonTarget e.2)
          (e.1.1.normalizedEpsilonReplacement e.2) r = true →
        (e.1.1.normalizedEpsilonSource e.2,
          e.1.1.normalizedEpsilonTop e.2, r) ∈ e.1.2))
  have hc : Primrec (fun q : EpsilonClosureContext T × ℕ => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hrow : Primrec (fun q : EpsilonClosureContext T × ℕ => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htarget := normalizedEpsilonTarget_primrec.comp hc hrow
  have hreplacement := normalizedEpsilonReplacement_primrec.comp hc hrow
  have hsource := normalizedEpsilonSource_primrec.comp hc hrow
  have htop := normalizedEpsilonTop_primrec.comp hc hrow
  have hpathInput : Primrec (fun q : EpsilonClosureContext T × ℕ =>
      ((q.1.1.1, q.1.1.2),
        (q.1.1.normalizedEpsilonTarget q.1.2,
          q.1.1.normalizedEpsilonReplacement q.1.2, q.2))) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair htarget (Primrec.pair hreplacement Primrec.snd))
  have hpath : Primrec (fun q : EpsilonClosureContext T × ℕ =>
      q.1.1.summaryPath q.1.2 (q.1.1.normalizedEpsilonTarget q.1.2)
        (q.1.1.normalizedEpsilonReplacement q.1.2) q.2) :=
    summaryPath_primrec.comp hpathInput
  have htriple : Primrec (fun q : EpsilonClosureContext T × ℕ =>
      (q.1.1.normalizedEpsilonSource q.1.2,
        q.1.1.normalizedEpsilonTop q.1.2, q.2)) :=
    Primrec.pair hsource (Primrec.pair htop Primrec.snd)
  have hrelation : Primrec (fun q : EpsilonClosureContext T × ℕ => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hmem : Primrec (fun q : EpsilonClosureContext T × ℕ => decide
      ((q.1.1.normalizedEpsilonSource q.1.2,
        q.1.1.normalizedEpsilonTop q.1.2, q.2) ∈ q.1.1.2)) :=
    primrec_list_memBool.comp htriple hrelation
  have hpredicate : Primrec₂ (fun (e : EpsilonClosureContext T) (r : ℕ) =>
      decide (e.1.1.summaryPath e.1.2 (e.1.1.normalizedEpsilonTarget e.2)
          (e.1.1.normalizedEpsilonReplacement e.2) r = true →
        (e.1.1.normalizedEpsilonSource e.2,
          e.1.1.normalizedEpsilonTop e.2, r) ∈ e.1.2)) := by
    show Primrec (fun q : EpsilonClosureContext T × ℕ => decide
      (q.1.1.summaryPath q.1.2 (q.1.1.normalizedEpsilonTarget q.1.2)
        (q.1.1.normalizedEpsilonReplacement q.1.2) q.2 = true →
        (q.1.1.normalizedEpsilonSource q.1.2,
          q.1.1.normalizedEpsilonTop q.1.2, q.2) ∈ q.1.1.2))
    apply Primrec.of_eq (Primrec.or.comp (Primrec.not.comp hpath) hmem)
    intro q
    cases h₁ : q.1.1.summaryPath q.1.2
      (q.1.1.normalizedEpsilonTarget q.1.2)
      (q.1.1.normalizedEpsilonReplacement q.1.2) q.2 <;>
        simp [h₁]
  exact primrec_list_all
    (Primrec.list_range.comp
      (pStateCount_primrec.comp (Primrec.fst.comp Primrec.fst))) hpredicate

private theorem epsilonClosed_primrec :
    Primrec (fun q : ClosedContext T =>
      q.1.effectiveEpsilonRows.all fun row =>
        (List.range q.1.pStateCount).all fun r =>
          decide (q.1.summaryPath q.2 (q.1.normalizedEpsilonTarget row)
              (q.1.normalizedEpsilonReplacement row) r = true →
            (q.1.normalizedEpsilonSource row,
              q.1.normalizedEpsilonTop row, r) ∈ q.2)) := by
  exact primrec_list_all
    (effectiveEpsilonRows_primrec.comp Primrec.fst)
    epsilonClosureRow_primrec

private abbrev InputClosureContext (T : Type) :=
  ClosedContext T × InputRow T

private theorem inputClosureRow_primrec :
    Primrec₂ (fun (q : ClosedContext T) (row : InputRow T) =>
      (List.range q.1.pStateCount).all fun r =>
        decide (q.1.summaryPath q.2 (q.1.normalizedInputTarget row)
            (q.1.normalizedInputReplacement row) r = true →
          (q.1.normalizedInputSource row,
            q.1.normalizedInputTop row, r) ∈ q.2)) := by
  show Primrec (fun e : InputClosureContext T =>
    (List.range e.1.1.pStateCount).all fun r =>
      decide (e.1.1.summaryPath e.1.2 (e.1.1.normalizedInputTarget e.2)
          (e.1.1.normalizedInputReplacement e.2) r = true →
        (e.1.1.normalizedInputSource e.2,
          e.1.1.normalizedInputTop e.2, r) ∈ e.1.2))
  have hc : Primrec (fun q : InputClosureContext T × ℕ => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hrow : Primrec (fun q : InputClosureContext T × ℕ => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htarget := normalizedInputTarget_primrec.comp hc hrow
  have hreplacement := normalizedInputReplacement_primrec.comp hc hrow
  have hsource := normalizedInputSource_primrec.comp hc hrow
  have htop := normalizedInputTop_primrec.comp hc hrow
  have hpathInput : Primrec (fun q : InputClosureContext T × ℕ =>
      ((q.1.1.1, q.1.1.2),
        (q.1.1.normalizedInputTarget q.1.2,
          q.1.1.normalizedInputReplacement q.1.2, q.2))) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair htarget (Primrec.pair hreplacement Primrec.snd))
  have hpath : Primrec (fun q : InputClosureContext T × ℕ =>
      q.1.1.summaryPath q.1.2 (q.1.1.normalizedInputTarget q.1.2)
        (q.1.1.normalizedInputReplacement q.1.2) q.2) :=
    summaryPath_primrec.comp hpathInput
  have htriple : Primrec (fun q : InputClosureContext T × ℕ =>
      (q.1.1.normalizedInputSource q.1.2,
        q.1.1.normalizedInputTop q.1.2, q.2)) :=
    Primrec.pair hsource (Primrec.pair htop Primrec.snd)
  have hrelation : Primrec (fun q : InputClosureContext T × ℕ => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hmem : Primrec (fun q : InputClosureContext T × ℕ => decide
      ((q.1.1.normalizedInputSource q.1.2,
        q.1.1.normalizedInputTop q.1.2, q.2) ∈ q.1.1.2)) :=
    primrec_list_memBool.comp htriple hrelation
  have hpredicate : Primrec₂ (fun (e : InputClosureContext T) (r : ℕ) =>
      decide (e.1.1.summaryPath e.1.2 (e.1.1.normalizedInputTarget e.2)
          (e.1.1.normalizedInputReplacement e.2) r = true →
        (e.1.1.normalizedInputSource e.2,
          e.1.1.normalizedInputTop e.2, r) ∈ e.1.2)) := by
    show Primrec (fun q : InputClosureContext T × ℕ => decide
      (q.1.1.summaryPath q.1.2 (q.1.1.normalizedInputTarget q.1.2)
        (q.1.1.normalizedInputReplacement q.1.2) q.2 = true →
        (q.1.1.normalizedInputSource q.1.2,
          q.1.1.normalizedInputTop q.1.2, q.2) ∈ q.1.1.2))
    apply Primrec.of_eq (Primrec.or.comp (Primrec.not.comp hpath) hmem)
    intro q
    cases h₁ : q.1.1.summaryPath q.1.2
      (q.1.1.normalizedInputTarget q.1.2)
      (q.1.1.normalizedInputReplacement q.1.2) q.2 <;>
        simp [h₁]
  exact primrec_list_all
    (Primrec.list_range.comp
      (pStateCount_primrec.comp (Primrec.fst.comp Primrec.fst))) hpredicate

private theorem inputClosed_primrec :
    Primrec (fun q : ClosedContext T =>
      q.1.effectiveInputRows.all fun row =>
        (List.range q.1.pStateCount).all fun r =>
          decide (q.1.summaryPath q.2 (q.1.normalizedInputTarget row)
              (q.1.normalizedInputReplacement row) r = true →
            (q.1.normalizedInputSource row,
              q.1.normalizedInputTop row, r) ∈ q.2)) := by
  exact primrec_list_all
    (effectiveInputRows_primrec.comp Primrec.fst)
    inputClosureRow_primrec

private theorem summaryClosed_primrec :
    Primrec₂ (summaryClosed : EncodedDPDA T → List SummaryTriple → Bool) := by
  show Primrec (fun q : ClosedContext T => q.1.summaryClosed q.2)
  apply Primrec.of_eq (Primrec.and.comp
    (Primrec.and.comp baseClosed_primrec epsilonClosed_primrec)
    inputClosed_primrec)
  intro q
  rfl

private abbrev LeastTripleContext (T : Type) :=
  EncodedDPDA T × SummaryTriple

private theorem leastTriplePredicate_primrec :
    Primrec₂ (fun (q : EncodedDPDA T) (t : SummaryTriple) =>
      q.allSummaryTriples.sublists.all fun R =>
        !q.summaryClosed R || decide (t ∈ R)) := by
  show Primrec (fun p : LeastTripleContext T =>
    p.1.allSummaryTriples.sublists.all fun R =>
      !p.1.summaryClosed R || decide (p.2 ∈ R))
  have hsubsets : Primrec (fun p : LeastTripleContext T =>
      p.1.allSummaryTriples.sublists) :=
    primrec_list_sublists.comp (allSummaryTriples_primrec.comp Primrec.fst)
  have hclosed : Primrec (fun q : LeastTripleContext T × List SummaryTriple =>
      q.1.1.summaryClosed q.2) :=
    summaryClosed_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hmem : Primrec (fun q : LeastTripleContext T × List SummaryTriple =>
      decide (q.1.2 ∈ q.2)) :=
    primrec_list_memBool.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hpredicate : Primrec₂ (fun (p : LeastTripleContext T)
      (R : List SummaryTriple) => !p.1.summaryClosed R || decide (p.2 ∈ R)) := by
    show Primrec (fun q : LeastTripleContext T × List SummaryTriple =>
      !q.1.1.summaryClosed q.2 || decide (q.1.2 ∈ q.2))
    exact Primrec.or.comp (Primrec.not.comp hclosed) hmem
  exact primrec_list_all hsubsets hpredicate

private theorem leastSummaryRelation_primrec :
    Primrec (leastSummaryRelation : EncodedDPDA T → List SummaryTriple) := by
  unfold leastSummaryRelation
  exact primrec_list_filterBool allSummaryTriples_primrec
    leastTriplePredicate_primrec

private theorem hasRejectingReach_primrec :
    Primrec (hasRejectingReach : EncodedDPDA T → Bool) := by
  have hinitial : Primrec (fun q : EncodedDPDA T × ℕ =>
      q.1.initialIndex % q.1.numStates) :=
    Primrec.nat_mod.comp (initialIndex_primrec.comp Primrec.fst)
      (numStates_primrec.comp Primrec.fst)
  have hstart : Primrec (fun q : EncodedDPDA T × ℕ =>
      q.1.startIndex % q.1.numStackSymbols) :=
    Primrec.nat_mod.comp (startIndex_primrec.comp Primrec.fst)
      (numStackSymbols_primrec.comp Primrec.fst)
  have hstack : Primrec (fun q : EncodedDPDA T × ℕ =>
      [q.1.startIndex % q.1.numStackSymbols]) :=
    Primrec.list_cons.comp hstart (Primrec.const [])
  have hpathInput : Primrec (fun q : EncodedDPDA T × ℕ =>
      ((q.1, q.1.leastSummaryRelation),
        (q.1.initialIndex % q.1.numStates,
          [q.1.startIndex % q.1.numStackSymbols], q.2))) :=
    Primrec.pair
      (Primrec.pair Primrec.fst
        (leastSummaryRelation_primrec.comp Primrec.fst))
      (Primrec.pair hinitial (Primrec.pair hstack Primrec.snd))
  have hpath : Primrec (fun q : EncodedDPDA T × ℕ =>
      q.1.summaryPath q.1.leastSummaryRelation
        (q.1.initialIndex % q.1.numStates)
        [q.1.startIndex % q.1.numStackSymbols] q.2) :=
    summaryPath_primrec.comp hpathInput
  have hsink : Primrec (fun q : EncodedDPDA T × ℕ =>
      decide (q.2 = q.1.sinkIndex)) :=
    (PrimrecRel.decide Primrec.eq).comp Primrec.snd
      (sinkIndex_primrec.comp Primrec.fst)
  have hreject : Primrec (fun q : EncodedDPDA T × ℕ =>
      q.1.isRejectingIndex q.2) :=
    isRejectingIndex_primrec.comp Primrec.fst Primrec.snd
  have hpredicate : Primrec₂ (fun (c : EncodedDPDA T) (r : ℕ) =>
      c.summaryPath c.leastSummaryRelation
          (c.initialIndex % c.numStates)
          [c.startIndex % c.numStackSymbols] r &&
        (decide (r = c.sinkIndex) || c.isRejectingIndex r)) := by
    show Primrec (fun q : EncodedDPDA T × ℕ =>
      q.1.summaryPath q.1.leastSummaryRelation
          (q.1.initialIndex % q.1.numStates)
          [q.1.startIndex % q.1.numStackSymbols] q.2 &&
        (decide (q.2 = q.1.sinkIndex) || q.1.isRejectingIndex q.2))
    exact Primrec.and.comp hpath (Primrec.or.comp hsink hreject)
  unfold hasRejectingReach
  exact primrec_list_any_fast
    (Primrec.list_range.comp pStateCount_primrec) hpredicate

/-- The finite universality checker is a total computable function of the raw
encoded DPDA table. -/
public theorem checkUniversal_computable :
    Computable (checkUniversal : EncodedDPDA T → Bool) := by
  exact (Primrec.not.comp hasRejectingReach_primrec).to_comp

-/

/-! The compiled saturation proof uses a compact parameter tuple.  In
particular, the large raw code is projected once, before any nested finite-list
iteration. -/

private abbrev SaturationCore (T : Type) :=
  InputSelectionData T × List ℕ

private abbrev SaturationData (T : Type) :=
  SaturationCore T × (ℕ × ℕ)

private def effectiveSaturationData
    (c : EncodedDPDA T) : SaturationData T :=
  ((effectiveRunData c, c.normalizedFinals),
    (c.initialIndex, c.startIndex))

private def dataPStateCount (nm : SelectionSizes) : ℕ := nm.1 + 1

private def dataIsRejectingIndex
    (nf : ℕ × List ℕ) (q : ℕ) : Bool :=
  decide (q < nf.1 ∧ q ∉ nf.2)

private def dataNormalizedEpsilonSource
    (nm : SelectionSizes) (row : EpsilonRow) : ℕ :=
  row.1 % nm.1

private def dataNormalizedEpsilonTop
    (nm : SelectionSizes) (row : EpsilonRow) : ℕ :=
  row.2.1 % nm.2

private def dataNormalizedEpsilonTarget
    (nm : SelectionSizes) (row : EpsilonRow) : ℕ :=
  row.2.2.1 % nm.1

private def dataNormalizedEpsilonReplacement
    (nm : SelectionSizes) (row : EpsilonRow) : List ℕ :=
  row.2.2.2.map fun Z => Z % nm.2

private def dataNormalizedInputSource
    (nm : SelectionSizes) (row : InputRow T) : ℕ :=
  row.1 % nm.1

private def dataNormalizedInputTop
    (nm : SelectionSizes) (row : InputRow T) : ℕ :=
  row.2.2.1 % nm.2

private def dataNormalizedInputTarget
    (nm : SelectionSizes) (row : InputRow T) : ℕ :=
  row.2.2.2.1 % nm.1

private def dataNormalizedInputReplacement
    (nm : SelectionSizes) (row : InputRow T) : List ℕ :=
  row.2.2.2.2.map fun Z => Z % nm.2

private def dataAllSummaryTriples
    (nm : SelectionSizes) : List SummaryTriple :=
  (List.range (dataPStateCount nm)).flatMap fun p =>
    (List.range nm.2).flatMap fun Z =>
      (List.range (dataPStateCount nm)).map fun r => (p, Z, r)

private def dataBaseSummaryTriples
    (d : SelectionSizes × List ℕ) : List SummaryTriple :=
  (dataAllSummaryTriples d.1).filter fun t =>
    decide ((t.1 = d.1.1 ∧ t.2.2 = d.1.1) ∨
      (dataIsRejectingIndex (d.1.1, d.2) t.1 = true ∧
        t.2.2 = d.1.1))

private def dataAdvanceSummaryStates (nm : SelectionSizes)
    (R : List SummaryTriple) (states : List ℕ) (Z : ℕ) : List ℕ :=
  (List.range (dataPStateCount nm)).filter fun middle =>
    states.any fun p => decide ((p, Z % nm.2, middle) ∈ R)

private def dataSummaryDestinations (nm : SelectionSizes)
    (R : List SummaryTriple) (states gamma : List ℕ) : List ℕ :=
  gamma.foldl (dataAdvanceSummaryStates nm R) states

private def dataSummaryPath (nm : SelectionSizes)
    (R : List SummaryTriple) (p : ℕ) (gamma : List ℕ) (r : ℕ) : Bool :=
  decide (r ∈ dataSummaryDestinations nm R [p] gamma)

private def dataSummaryClosed (d : SaturationCore T)
    (R : List SummaryTriple) : Bool :=
  ((dataBaseSummaryTriples (d.1.1, d.2)).all fun t => decide (t ∈ R)) &&
    (d.1.2.1.all fun row =>
      (List.range (dataPStateCount d.1.1)).all fun r =>
        decide (dataSummaryPath d.1.1 R
            (dataNormalizedEpsilonTarget d.1.1 row)
            (dataNormalizedEpsilonReplacement d.1.1 row) r = true →
          (dataNormalizedEpsilonSource d.1.1 row,
            dataNormalizedEpsilonTop d.1.1 row, r) ∈ R)) &&
    (d.1.2.2.all fun row =>
      (List.range (dataPStateCount d.1.1)).all fun r =>
        decide (dataSummaryPath d.1.1 R
            (dataNormalizedInputTarget d.1.1 row)
            (dataNormalizedInputReplacement d.1.1 row) r = true →
          (dataNormalizedInputSource d.1.1 row,
            dataNormalizedInputTop d.1.1 row, r) ∈ R))

private def dataLeastSummaryRelation
    (d : SaturationCore T) : List SummaryTriple :=
  (dataAllSummaryTriples d.1.1).filter fun t =>
    (dataAllSummaryTriples d.1.1).sublists.all fun R =>
      !dataSummaryClosed d R || decide (t ∈ R)

private def dataHasRejectingReach (d : SaturationData T) : Bool :=
  (List.range (dataPStateCount d.1.1.1)).any fun r =>
    dataSummaryPath d.1.1.1 (dataLeastSummaryRelation d.1)
        (d.2.1 % d.1.1.1.1) [d.2.2 % d.1.1.1.2] r &&
      (decide (r = d.1.1.1.1) ||
        dataIsRejectingIndex (d.1.1.1.1, d.1.2) r)

private def dataCheckUniversal (d : SaturationData T) : Bool :=
  !dataHasRejectingReach d

private theorem dataCheckUniversal_effectiveSaturationData
    (c : EncodedDPDA T) :
    dataCheckUniversal (effectiveSaturationData c) = c.checkUniversal := by
  rfl

private theorem effectiveSaturationData_primrec :
    Primrec (effectiveSaturationData :
      EncodedDPDA T → SaturationData T) := by
  exact Primrec.pair
    (Primrec.pair effectiveRunData_primrec normalizedFinals_primrec)
    (Primrec.pair initialIndex_primrec startIndex_primrec)

private theorem dataIsRejectingIndex_primrec :
    Primrec₂ (dataIsRejectingIndex :
      (ℕ × List ℕ) → ℕ → Bool) := by
  show Primrec (fun p : (ℕ × List ℕ) × ℕ =>
    dataIsRejectingIndex p.1 p.2)
  have hlt : Primrec (fun p : (ℕ × List ℕ) × ℕ =>
      decide (p.2 < p.1.1)) :=
    (PrimrecRel.decide Primrec.nat_lt).comp Primrec.snd
      (Primrec.fst.comp Primrec.fst)
  have hmem : Primrec (fun p : (ℕ × List ℕ) × ℕ =>
      decide (p.2 ∈ p.1.2)) :=
    primrec_list_memBool.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  apply Primrec.of_eq (Primrec.and.comp hlt (Primrec.not.comp hmem))
  intro p
  apply Bool.eq_iff_iff.mpr
  simp [dataIsRejectingIndex]

private theorem dataNormalizedEpsilonSource_primrec :
    Primrec₂ (dataNormalizedEpsilonSource :
      SelectionSizes → EpsilonRow → ℕ) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp Primrec.fst)

private theorem dataNormalizedEpsilonTop_primrec :
    Primrec₂ (dataNormalizedEpsilonTop :
      SelectionSizes → EpsilonRow → ℕ) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.fst)

private theorem dataNormalizedEpsilonTarget_primrec :
    Primrec₂ (dataNormalizedEpsilonTarget :
      SelectionSizes → EpsilonRow → ℕ) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp Primrec.fst)

private theorem dataNormalizedEpsilonReplacement_primrec :
    Primrec₂ (dataNormalizedEpsilonReplacement :
      SelectionSizes → EpsilonRow → List ℕ) := by
  exact modList_primrec.comp
    (Primrec.snd.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))

private theorem dataNormalizedInputSource_primrec :
    Primrec₂ (dataNormalizedInputSource :
      SelectionSizes → InputRow T → ℕ) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp Primrec.fst)

private theorem dataNormalizedInputTop_primrec :
    Primrec₂ (dataNormalizedInputTop :
      SelectionSizes → InputRow T → ℕ) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.fst)

private theorem dataNormalizedInputTarget_primrec :
    Primrec₂ (dataNormalizedInputTarget :
      SelectionSizes → InputRow T → ℕ) := by
  exact Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.fst.comp Primrec.fst)

private theorem dataNormalizedInputReplacement_primrec :
    Primrec₂ (dataNormalizedInputReplacement :
      SelectionSizes → InputRow T → List ℕ) := by
  exact modList_primrec.comp
    (Primrec.snd.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private theorem dataAllSummaryTriples_primrec :
    Primrec (dataAllSummaryTriples :
      SelectionSizes → List SummaryTriple) := by
  have hlast : Primrec₂
      (fun (ctx : (SelectionSizes × ℕ) × ℕ) (r : ℕ) =>
        (ctx.1.2, ctx.2, r)) := by
    show Primrec (fun q : ((SelectionSizes × ℕ) × ℕ) × ℕ =>
      (q.1.1.2, q.1.2, q.2))
    exact Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hforTop : Primrec₂
      (fun (ctx : SelectionSizes × ℕ) (Z : ℕ) =>
        (List.range (dataPStateCount ctx.1)).map fun r =>
          (ctx.2, Z, r)) := by
    show Primrec (fun q : (SelectionSizes × ℕ) × ℕ =>
      (List.range (q.1.1.1 + 1)).map fun r =>
        (q.1.2, q.2, r))
    exact Primrec.list_map
      (Primrec.list_range.comp
        (Primrec.succ.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) hlast
  have hforSource : Primrec₂
      (fun (nm : SelectionSizes) (p : ℕ) =>
        (List.range nm.2).flatMap fun Z =>
          (List.range (dataPStateCount nm)).map fun r =>
            (p, Z, r)) := by
    show Primrec (fun q : SelectionSizes × ℕ =>
      (List.range q.1.2).flatMap fun Z =>
        (List.range (q.1.1 + 1)).map fun r =>
          (q.2, Z, r))
    exact Primrec.list_flatMap
      (Primrec.list_range.comp
        (Primrec.snd.comp Primrec.fst)) hforTop
  unfold dataAllSummaryTriples dataPStateCount
  exact Primrec.list_flatMap
    (Primrec.list_range.comp
      (Primrec.succ.comp Primrec.fst)) hforSource

private theorem dataBaseSummaryTriples_primrec :
    Primrec (dataBaseSummaryTriples :
      (SelectionSizes × List ℕ) → List SummaryTriple) := by
  have hall : Primrec (fun d : SelectionSizes × List ℕ =>
      dataAllSummaryTriples d.1) :=
    dataAllSummaryTriples_primrec.comp Primrec.fst
  apply primrec_list_filterBool hall
  show Primrec₂ (fun (d : SelectionSizes × List ℕ)
      (t : SummaryTriple) => decide
    ((t.1 = d.1.1 ∧ t.2.2 = d.1.1) ∨
      (dataIsRejectingIndex (d.1.1, d.2) t.1 = true ∧
        t.2.2 = d.1.1)))
  have hsink : Primrec (fun q :
      (SelectionSizes × List ℕ) × SummaryTriple => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hpSink : Primrec (fun q :
      (SelectionSizes × List ℕ) × SummaryTriple =>
      decide (q.2.1 = q.1.1.1)) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp Primrec.snd) hsink
  have hrSink : Primrec (fun q :
      (SelectionSizes × List ℕ) × SummaryTriple =>
      decide (q.2.2.2 = q.1.1.1)) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hsink
  have hnf : Primrec (fun q :
      (SelectionSizes × List ℕ) × SummaryTriple =>
      (q.1.1.1, q.1.2)) :=
    Primrec.pair hsink (Primrec.snd.comp Primrec.fst)
  have hreject : Primrec (fun q :
      (SelectionSizes × List ℕ) × SummaryTriple =>
      dataIsRejectingIndex (q.1.1.1, q.1.2) q.2.1) :=
    dataIsRejectingIndex_primrec.comp hnf
      (Primrec.fst.comp Primrec.snd)
  apply Primrec.of_eq (Primrec.or.comp
    (Primrec.and.comp hpSink hrSink)
    (Primrec.and.comp hreject hrSink))
  intro q
  simp [Bool.decide_and, Bool.decide_or]

private abbrev DataAdvanceContext :=
  (SelectionSizes × List SummaryTriple) × (List ℕ × ℕ)

private def dataAdvancePredicate
    (q : DataAdvanceContext) (middle : ℕ) : Bool :=
  q.2.1.any fun p => decide
    ((p, q.2.2 % q.1.1.2, middle) ∈ q.1.2)

/- Expanded predicate proof, factored once more below.
private theorem dataAdvancePredicate_primrec_expanded :
    Primrec₂ dataAdvancePredicate := by
  show Primrec (fun z : DataAdvanceContext × ℕ =>
    dataAdvancePredicate z.1 z.2)
  have hstateList : Primrec (fun z : DataAdvanceContext × ℕ =>
      z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hmod : Primrec (fun q : (DataAdvanceContext × ℕ) × ℕ =>
      q.1.1.2.2 % q.1.1.1.1.2) :=
    Primrec.nat_mod.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have htriple : Primrec₂
      (fun (z : DataAdvanceContext × ℕ) (p : ℕ) =>
        (p, z.1.2.2 % z.1.1.1.2, z.2)) := by
    show Primrec (fun q : (DataAdvanceContext × ℕ) × ℕ =>
      (q.2, q.1.1.2.2 % q.1.1.1.1.2, q.1.2))
    exact Primrec.pair Primrec.snd
      (Primrec.pair hmod (Primrec.snd.comp Primrec.fst))
  have hrelation : Primrec (fun z : DataAdvanceContext × ℕ =>
      z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst))
  have hmember : Primrec₂
      (fun (z : DataAdvanceContext × ℕ) (p : ℕ) => decide
        ((p, z.1.2.2 % z.1.1.1.2, z.2) ∈ z.1.1.2)) :=
    primrec_list_memBool.comp htriple (hrelation.comp Primrec.fst)
  have hresult : Primrec (fun z : DataAdvanceContext × ℕ =>
      z.1.2.1.any fun p => decide
        ((p, z.1.2.2 % z.1.1.1.2, z.2) ∈ z.1.1.2)) :=
    primrec_list_any_fast hstateList hmember
  apply Primrec.of_eq hresult
  intro z
  rfl

-/

private def dataAdvanceMemberEval
    (p : List SummaryTriple × SummaryTriple) : Bool :=
  decide (p.2 ∈ p.1)

private theorem dataAdvanceMemberEval_primrec :
    Primrec dataAdvanceMemberEval := by
  apply Primrec.of_eq ((primrec_list_memBool (A := SummaryTriple)).comp
    (Primrec.snd : Primrec (fun p : List SummaryTriple × SummaryTriple => p.2))
    (Primrec.fst : Primrec (fun p : List SummaryTriple × SummaryTriple => p.1)))
  intro p
  apply Bool.eq_iff_iff.mpr
  simp [dataAdvanceMemberEval]

private abbrev DataAdvanceMemberContext :=
  (DataAdvanceContext × ℕ) × ℕ

private def dataAdvanceMemberStack
    (q : DataAdvanceMemberContext) : ℕ := q.1.1.2.2

private theorem dataAdvanceMemberStack_primrec :
    Primrec dataAdvanceMemberStack := by
  exact Primrec.snd.comp (Primrec.snd.comp
    (Primrec.fst.comp Primrec.fst))

private def dataAdvanceMemberModulus
    (q : DataAdvanceMemberContext) : ℕ := q.1.1.1.1.2

private theorem dataAdvanceMemberModulus_primrec :
    Primrec dataAdvanceMemberModulus := by
  exact Primrec.snd.comp (Primrec.fst.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))

private def dataAdvanceMemberSymbol
    (q : DataAdvanceMemberContext) : ℕ :=
  dataAdvanceMemberStack q % dataAdvanceMemberModulus q

private theorem dataAdvanceMemberSymbol_primrec :
    Primrec dataAdvanceMemberSymbol := by
  exact Primrec.nat_mod.comp dataAdvanceMemberStack_primrec
    dataAdvanceMemberModulus_primrec

private def dataAdvanceMemberMiddle
    (q : DataAdvanceMemberContext) : ℕ := q.1.2

private theorem dataAdvanceMemberMiddle_primrec :
    Primrec dataAdvanceMemberMiddle := by
  exact Primrec.snd.comp Primrec.fst

private def dataAdvanceMemberSource
    (q : DataAdvanceMemberContext) : ℕ := q.2

private theorem dataAdvanceMemberSource_primrec :
    Primrec dataAdvanceMemberSource := Primrec.snd

private def dataAdvanceMemberTriple
    (q : DataAdvanceMemberContext) : SummaryTriple :=
  (dataAdvanceMemberSource q, dataAdvanceMemberSymbol q,
    dataAdvanceMemberMiddle q)

private theorem dataAdvanceMemberTriple_primrec :
    Primrec dataAdvanceMemberTriple := by
  exact Primrec.pair dataAdvanceMemberSource_primrec
    (Primrec.pair dataAdvanceMemberSymbol_primrec
      dataAdvanceMemberMiddle_primrec)

private def dataAdvanceMemberRelation
    (q : DataAdvanceMemberContext) : List SummaryTriple := q.1.1.1.2

private theorem dataAdvanceMemberRelation_primrec :
    Primrec dataAdvanceMemberRelation := by
  exact Primrec.snd.comp (Primrec.fst.comp
    (Primrec.fst.comp Primrec.fst))

private def dataAdvanceMemberInput
    (q : (DataAdvanceContext × ℕ) × ℕ) :
    List SummaryTriple × SummaryTriple :=
  (dataAdvanceMemberRelation q, dataAdvanceMemberTriple q)

private theorem dataAdvanceMemberInput_primrec :
    Primrec dataAdvanceMemberInput := by
  exact Primrec.pair dataAdvanceMemberRelation_primrec
    dataAdvanceMemberTriple_primrec

private def dataAdvanceMember
    (z : DataAdvanceContext × ℕ) (p : ℕ) : Bool :=
  dataAdvanceMemberEval (dataAdvanceMemberInput (z, p))

private def dataSummaryTripleMember
    (p : List SummaryTriple × SummaryTriple) : Bool :=
  decide (p.2 ∈ p.1)

private theorem dataSummaryTripleMember_primrec :
    Primrec dataSummaryTripleMember := by
  show Primrec (fun p : List SummaryTriple × SummaryTriple =>
    decide (p.2 ∈ p.1))
  apply Primrec.of_eq ((primrec_list_memBool (A := SummaryTriple)).comp
    (Primrec.snd : Primrec (fun p : List SummaryTriple × SummaryTriple => p.2))
    (Primrec.fst : Primrec (fun p : List SummaryTriple × SummaryTriple => p.1)))
  intro p
  apply Bool.eq_iff_iff.mpr
  simp

private theorem dataAdvanceMember_primrec :
    Primrec₂ dataAdvanceMember := by
  show Primrec (fun q : (DataAdvanceContext × ℕ) × ℕ =>
    dataAdvanceMember q.1 q.2)
  apply (dataAdvanceMemberEval_primrec.comp
    dataAdvanceMemberInput_primrec).of_eq
  intro q
  rfl

private theorem dataAdvancePredicate_primrec :
    Primrec₂ dataAdvancePredicate := by
  show Primrec (fun z : DataAdvanceContext × ℕ =>
    dataAdvancePredicate z.1 z.2)
  have hstates : Primrec (fun z : DataAdvanceContext × ℕ =>
      z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hresult : Primrec (fun z : DataAdvanceContext × ℕ =>
      z.1.2.1.any (dataAdvanceMember z)) :=
    primrec_list_any_fast hstates dataAdvanceMember_primrec
  apply Primrec.of_eq hresult
  intro z
  rfl

private theorem dataAdvanceSummaryStates_primrec :
    Primrec (fun q : DataAdvanceContext =>
      dataAdvanceSummaryStates q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hrange : Primrec (fun q : DataAdvanceContext =>
      List.range (q.1.1.1 + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hresult : Primrec (fun q : DataAdvanceContext =>
      (List.range (q.1.1.1 + 1)).filter
        (dataAdvancePredicate q)) :=
    primrec_list_filterBool hrange dataAdvancePredicate_primrec
  apply Primrec.of_eq hresult
  intro q
  rfl

private abbrev DataDestinationContext :=
  (SelectionSizes × List SummaryTriple) × (List ℕ × List ℕ)

private theorem dataSummaryDestinations_primrec :
    Primrec (fun q : DataDestinationContext =>
      dataSummaryDestinations q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hstep : Primrec₂ (fun (q : DataDestinationContext)
      (sZ : List ℕ × ℕ) =>
        dataAdvanceSummaryStates q.1.1 q.1.2 sZ.1 sZ.2) := by
    show Primrec (fun p : DataDestinationContext × (List ℕ × ℕ) =>
      dataAdvanceSummaryStates p.1.1.1 p.1.1.2 p.2.1 p.2.2)
    exact dataAdvanceSummaryStates_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hresult : Primrec (fun q : DataDestinationContext =>
      q.2.2.foldl
        (fun states Z =>
          dataAdvanceSummaryStates q.1.1 q.1.2 states Z) q.2.1) :=
    primrec_list_foldl
      (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd) hstep
  apply Primrec.of_eq hresult
  intro q
  rfl

private abbrev DataPathContext :=
  (SelectionSizes × List SummaryTriple) × (ℕ × List ℕ × ℕ)

private theorem dataSummaryPath_primrec :
    Primrec (fun q : DataPathContext =>
      dataSummaryPath q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
  have hstates : Primrec (fun q : DataPathContext => [q.2.1]) :=
    Primrec.list_cons.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.const [])
  have hdestInput : Primrec (fun q : DataPathContext =>
      (q.1, ([q.2.1], q.2.2.1))) :=
    Primrec.pair Primrec.fst
      (Primrec.pair hstates
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hdest : Primrec (fun q : DataPathContext =>
      dataSummaryDestinations q.1.1 q.1.2 [q.2.1] q.2.2.1) :=
    dataSummaryDestinations_primrec.comp hdestInput
  unfold dataSummaryPath
  exact primrec_list_memBool.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hdest

private abbrev DataClosedContext (T : Type) :=
  SaturationCore T × List SummaryTriple

private def dataBaseParameter
    (q : DataClosedContext T) : SelectionSizes × List ℕ :=
  (q.1.1.1, q.1.2)

private theorem dataBaseParameter_primrec :
    Primrec (dataBaseParameter :
      DataClosedContext T → SelectionSizes × List ℕ) := by
  exact Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.snd.comp Primrec.fst)

private def dataClosedMember
    (q : DataClosedContext T) (t : SummaryTriple) : Bool :=
  dataAdvanceMemberEval (q.2, t)

private theorem dataClosedMember_primrec :
    Primrec₂ (dataClosedMember :
      DataClosedContext T → SummaryTriple → Bool) := by
  show Primrec (fun q : DataClosedContext T × SummaryTriple =>
    dataClosedMember q.1 q.2)
  have hinput : Primrec (fun q :
      DataClosedContext T × SummaryTriple => (q.1.2, q.2)) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact dataAdvanceMemberEval_primrec.comp hinput

private def dataBaseClosed (q : DataClosedContext T) : Bool :=
  (dataBaseSummaryTriples (dataBaseParameter q)).all
    (dataClosedMember q)

private theorem dataBaseClosed_primrec :
    Primrec (dataBaseClosed : DataClosedContext T → Bool) := by
  have hbase : Primrec (fun q : DataClosedContext T =>
      dataBaseSummaryTriples (dataBaseParameter q)) :=
    dataBaseSummaryTriples_primrec.comp dataBaseParameter_primrec
  exact primrec_list_all hbase dataClosedMember_primrec

private abbrev DataEpsilonClosureContext (T : Type) :=
  DataClosedContext T × EpsilonRow

private abbrev DataEpsilonClosurePointContext (T : Type) :=
  DataEpsilonClosureContext T × ℕ

private def dataEpsilonClosureSizes
    (q : DataEpsilonClosurePointContext T) : SelectionSizes :=
  q.1.1.1.1.1

private theorem dataEpsilonClosureSizes_primrec :
    Primrec (dataEpsilonClosureSizes :
      DataEpsilonClosurePointContext T → SelectionSizes) := by
  exact Primrec.fst.comp (Primrec.fst.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))

private def dataEpsilonClosureRelation
    (q : DataEpsilonClosurePointContext T) : List SummaryTriple :=
  q.1.1.2

private theorem dataEpsilonClosureRelation_primrec :
    Primrec (dataEpsilonClosureRelation :
      DataEpsilonClosurePointContext T → List SummaryTriple) := by
  have hresult : Primrec (fun q :
      DataEpsilonClosurePointContext T => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  apply Primrec.of_eq hresult
  intro q
  rfl

private def dataEpsilonClosureRowValue
    (q : DataEpsilonClosurePointContext T) : EpsilonRow :=
  q.1.2

private theorem dataEpsilonClosureRowValue_primrec :
    Primrec (dataEpsilonClosureRowValue :
      DataEpsilonClosurePointContext T → EpsilonRow) := by
  exact Primrec.snd.comp Primrec.fst

private def dataEpsilonClosureEndpoint
    (q : DataEpsilonClosurePointContext T) : ℕ := q.2

private theorem dataEpsilonClosureEndpoint_primrec :
    Primrec (dataEpsilonClosureEndpoint :
      DataEpsilonClosurePointContext T → ℕ) := Primrec.snd

private def dataEpsilonClosureTarget
    (q : DataEpsilonClosurePointContext T) : ℕ :=
  dataNormalizedEpsilonTarget (dataEpsilonClosureSizes q)
    (dataEpsilonClosureRowValue q)

private theorem dataEpsilonClosureTarget_primrec :
    Primrec (dataEpsilonClosureTarget :
      DataEpsilonClosurePointContext T → ℕ) := by
  exact dataNormalizedEpsilonTarget_primrec.comp
    dataEpsilonClosureSizes_primrec dataEpsilonClosureRowValue_primrec

private def dataEpsilonClosureReplacement
    (q : DataEpsilonClosurePointContext T) : List ℕ :=
  dataNormalizedEpsilonReplacement (dataEpsilonClosureSizes q)
    (dataEpsilonClosureRowValue q)

private theorem dataEpsilonClosureReplacement_primrec :
    Primrec (dataEpsilonClosureReplacement :
      DataEpsilonClosurePointContext T → List ℕ) := by
  exact dataNormalizedEpsilonReplacement_primrec.comp
    dataEpsilonClosureSizes_primrec dataEpsilonClosureRowValue_primrec

private def dataEpsilonClosureSource
    (q : DataEpsilonClosurePointContext T) : ℕ :=
  dataNormalizedEpsilonSource (dataEpsilonClosureSizes q)
    (dataEpsilonClosureRowValue q)

private theorem dataEpsilonClosureSource_primrec :
    Primrec (dataEpsilonClosureSource :
      DataEpsilonClosurePointContext T → ℕ) := by
  exact dataNormalizedEpsilonSource_primrec.comp
    dataEpsilonClosureSizes_primrec dataEpsilonClosureRowValue_primrec

private def dataEpsilonClosureTop
    (q : DataEpsilonClosurePointContext T) : ℕ :=
  dataNormalizedEpsilonTop (dataEpsilonClosureSizes q)
    (dataEpsilonClosureRowValue q)

private theorem dataEpsilonClosureTop_primrec :
    Primrec (dataEpsilonClosureTop :
      DataEpsilonClosurePointContext T → ℕ) := by
  exact dataNormalizedEpsilonTop_primrec.comp
    dataEpsilonClosureSizes_primrec dataEpsilonClosureRowValue_primrec

private def dataEpsilonClosurePathInput
    (q : DataEpsilonClosurePointContext T) : DataPathContext :=
  ((dataEpsilonClosureSizes q, dataEpsilonClosureRelation q),
    (dataEpsilonClosureTarget q, dataEpsilonClosureReplacement q,
      dataEpsilonClosureEndpoint q))

private theorem dataEpsilonClosurePathInput_primrec :
    Primrec (dataEpsilonClosurePathInput :
      DataEpsilonClosurePointContext T → DataPathContext) := by
  exact Primrec.pair
    (Primrec.pair dataEpsilonClosureSizes_primrec
      dataEpsilonClosureRelation_primrec)
    (Primrec.pair dataEpsilonClosureTarget_primrec
      (Primrec.pair dataEpsilonClosureReplacement_primrec
        dataEpsilonClosureEndpoint_primrec))

private def dataEpsilonClosurePath
    (q : DataEpsilonClosurePointContext T) : Bool :=
  dataSummaryPath (dataEpsilonClosureSizes q)
    (dataEpsilonClosureRelation q) (dataEpsilonClosureTarget q)
    (dataEpsilonClosureReplacement q) (dataEpsilonClosureEndpoint q)

private theorem dataEpsilonClosurePath_primrec :
    Primrec (dataEpsilonClosurePath :
      DataEpsilonClosurePointContext T → Bool) := by
  apply (dataSummaryPath_primrec.comp
    dataEpsilonClosurePathInput_primrec).of_eq
  intro q
  rfl

private def dataEpsilonClosureTriple
    (q : DataEpsilonClosurePointContext T) : SummaryTriple :=
  (dataEpsilonClosureSource q, dataEpsilonClosureTop q,
    dataEpsilonClosureEndpoint q)

private theorem dataEpsilonClosureTriple_primrec :
    Primrec (dataEpsilonClosureTriple :
      DataEpsilonClosurePointContext T → SummaryTriple) := by
  exact Primrec.pair dataEpsilonClosureSource_primrec
    (Primrec.pair dataEpsilonClosureTop_primrec
      dataEpsilonClosureEndpoint_primrec)

private def dataEpsilonClosureMemberInput
    (q : DataEpsilonClosurePointContext T) :
    List SummaryTriple × SummaryTriple :=
  (dataEpsilonClosureRelation q, dataEpsilonClosureTriple q)

private theorem dataEpsilonClosureMemberInput_primrec :
    Primrec (dataEpsilonClosureMemberInput :
      DataEpsilonClosurePointContext T →
        List SummaryTriple × SummaryTriple) := by
  exact Primrec.pair dataEpsilonClosureRelation_primrec
    dataEpsilonClosureTriple_primrec

private def dataEpsilonClosureMember
    (q : DataEpsilonClosurePointContext T) : Bool :=
  dataAdvanceMemberEval (dataEpsilonClosureMemberInput q)

private theorem dataEpsilonClosureMember_primrec :
    Primrec (dataEpsilonClosureMember :
      DataEpsilonClosurePointContext T → Bool) := by
  exact dataAdvanceMemberEval_primrec.comp
    dataEpsilonClosureMemberInput_primrec

private def dataEpsilonClosurePoint
    (q : DataEpsilonClosurePointContext T) : Bool :=
  decide (dataEpsilonClosurePath q = true →
    dataEpsilonClosureTriple q ∈ dataEpsilonClosureRelation q)

private theorem dataEpsilonClosurePoint_primrec :
    Primrec (dataEpsilonClosurePoint :
      DataEpsilonClosurePointContext T → Bool) := by
  have hresult : Primrec (fun q : DataEpsilonClosurePointContext T =>
      !dataEpsilonClosurePath q || dataEpsilonClosureMember q) :=
    Primrec.or.comp (Primrec.not.comp dataEpsilonClosurePath_primrec)
      dataEpsilonClosureMember_primrec
  apply Primrec.of_eq hresult
  intro q
  cases h : dataEpsilonClosurePath q <;>
    simp [dataEpsilonClosurePoint, dataEpsilonClosureMember,
      dataAdvanceMemberEval, dataEpsilonClosureMemberInput,
      dataEpsilonClosureTriple, dataEpsilonClosureRelation, h]

private def dataEpsilonClosureRow
    (q : DataEpsilonClosureContext T) : Bool :=
  (List.range (dataPStateCount q.1.1.1.1)).all fun r =>
    dataEpsilonClosurePoint (q, r)

private theorem dataEpsilonClosureRow_primrec :
    Primrec (dataEpsilonClosureRow :
      DataEpsilonClosureContext T → Bool) := by
  have hrange : Primrec (fun q : DataEpsilonClosureContext T =>
      List.range (q.1.1.1.1.1 + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp
        (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  have hpoint : Primrec₂
      (fun (q : DataEpsilonClosureContext T) (r : ℕ) =>
        dataEpsilonClosurePoint (q, r)) := by
    apply Primrec₂.mk
    exact dataEpsilonClosurePoint_primrec
  have hresult : Primrec (fun q : DataEpsilonClosureContext T =>
      (List.range (q.1.1.1.1.1 + 1)).all fun r =>
        dataEpsilonClosurePoint (q, r)) :=
    primrec_list_all hrange hpoint
  apply Primrec.of_eq hresult
  intro q
  rfl

private def dataEpsilonClosed (q : DataClosedContext T) : Bool :=
  q.1.1.2.1.all fun row => dataEpsilonClosureRow (q, row)

private theorem dataEpsilonClosed_primrec :
    Primrec (dataEpsilonClosed : DataClosedContext T → Bool) := by
  have hrows : Primrec (fun q : DataClosedContext T =>
      q.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst))
  have hrow : Primrec₂
      (fun (q : DataClosedContext T) (row : EpsilonRow) =>
        dataEpsilonClosureRow (q, row)) := by
    apply Primrec₂.mk
    exact dataEpsilonClosureRow_primrec
  exact primrec_list_all hrows hrow

private abbrev DataInputClosureContext (T : Type) :=
  DataClosedContext T × InputRow T

private abbrev DataInputClosurePointContext (T : Type) :=
  DataInputClosureContext T × ℕ

private def dataInputClosureSizes
    (q : DataInputClosurePointContext T) : SelectionSizes :=
  q.1.1.1.1.1

private theorem dataInputClosureSizes_primrec :
    Primrec (dataInputClosureSizes :
      DataInputClosurePointContext T → SelectionSizes) := by
  exact Primrec.fst.comp (Primrec.fst.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))

private def dataInputClosureRelation
    (q : DataInputClosurePointContext T) : List SummaryTriple :=
  q.1.1.2

private theorem dataInputClosureRelation_primrec :
    Primrec (dataInputClosureRelation :
      DataInputClosurePointContext T → List SummaryTriple) := by
  have hresult : Primrec (fun q : DataInputClosurePointContext T =>
      q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  apply Primrec.of_eq hresult
  intro q
  rfl

private def dataInputClosureRowValue
    (q : DataInputClosurePointContext T) : InputRow T :=
  q.1.2

private theorem dataInputClosureRowValue_primrec :
    Primrec (dataInputClosureRowValue :
      DataInputClosurePointContext T → InputRow T) := by
  exact Primrec.snd.comp Primrec.fst

private def dataInputClosureEndpoint
    (q : DataInputClosurePointContext T) : ℕ := q.2

private theorem dataInputClosureEndpoint_primrec :
    Primrec (dataInputClosureEndpoint :
      DataInputClosurePointContext T → ℕ) := Primrec.snd

private def dataInputClosureTarget
    (q : DataInputClosurePointContext T) : ℕ :=
  dataNormalizedInputTarget (dataInputClosureSizes q)
    (dataInputClosureRowValue q)

private theorem dataInputClosureTarget_primrec :
    Primrec (dataInputClosureTarget :
      DataInputClosurePointContext T → ℕ) := by
  exact dataNormalizedInputTarget_primrec.comp
    dataInputClosureSizes_primrec dataInputClosureRowValue_primrec

private def dataInputClosureReplacement
    (q : DataInputClosurePointContext T) : List ℕ :=
  dataNormalizedInputReplacement (dataInputClosureSizes q)
    (dataInputClosureRowValue q)

private theorem dataInputClosureReplacement_primrec :
    Primrec (dataInputClosureReplacement :
      DataInputClosurePointContext T → List ℕ) := by
  exact dataNormalizedInputReplacement_primrec.comp
    dataInputClosureSizes_primrec dataInputClosureRowValue_primrec

private def dataInputClosureSource
    (q : DataInputClosurePointContext T) : ℕ :=
  dataNormalizedInputSource (dataInputClosureSizes q)
    (dataInputClosureRowValue q)

private theorem dataInputClosureSource_primrec :
    Primrec (dataInputClosureSource :
      DataInputClosurePointContext T → ℕ) := by
  exact dataNormalizedInputSource_primrec.comp
    dataInputClosureSizes_primrec dataInputClosureRowValue_primrec

private def dataInputClosureTop
    (q : DataInputClosurePointContext T) : ℕ :=
  dataNormalizedInputTop (dataInputClosureSizes q)
    (dataInputClosureRowValue q)

private theorem dataInputClosureTop_primrec :
    Primrec (dataInputClosureTop :
      DataInputClosurePointContext T → ℕ) := by
  exact dataNormalizedInputTop_primrec.comp
    dataInputClosureSizes_primrec dataInputClosureRowValue_primrec

private def dataInputClosurePathInput
    (q : DataInputClosurePointContext T) : DataPathContext :=
  ((dataInputClosureSizes q, dataInputClosureRelation q),
    (dataInputClosureTarget q, dataInputClosureReplacement q,
      dataInputClosureEndpoint q))

private theorem dataInputClosurePathInput_primrec :
    Primrec (dataInputClosurePathInput :
      DataInputClosurePointContext T → DataPathContext) := by
  exact Primrec.pair
    (Primrec.pair dataInputClosureSizes_primrec
      dataInputClosureRelation_primrec)
    (Primrec.pair dataInputClosureTarget_primrec
      (Primrec.pair dataInputClosureReplacement_primrec
        dataInputClosureEndpoint_primrec))

private def dataInputClosurePath
    (q : DataInputClosurePointContext T) : Bool :=
  dataSummaryPath (dataInputClosureSizes q)
    (dataInputClosureRelation q) (dataInputClosureTarget q)
    (dataInputClosureReplacement q) (dataInputClosureEndpoint q)

private theorem dataInputClosurePath_primrec :
    Primrec (dataInputClosurePath :
      DataInputClosurePointContext T → Bool) := by
  apply (dataSummaryPath_primrec.comp
    dataInputClosurePathInput_primrec).of_eq
  intro q
  rfl

private def dataInputClosureTriple
    (q : DataInputClosurePointContext T) : SummaryTriple :=
  (dataInputClosureSource q, dataInputClosureTop q,
    dataInputClosureEndpoint q)

private theorem dataInputClosureTriple_primrec :
    Primrec (dataInputClosureTriple :
      DataInputClosurePointContext T → SummaryTriple) := by
  exact Primrec.pair dataInputClosureSource_primrec
    (Primrec.pair dataInputClosureTop_primrec
      dataInputClosureEndpoint_primrec)

private def dataInputClosureMemberInput
    (q : DataInputClosurePointContext T) :
    List SummaryTriple × SummaryTriple :=
  (dataInputClosureRelation q, dataInputClosureTriple q)

private theorem dataInputClosureMemberInput_primrec :
    Primrec (dataInputClosureMemberInput :
      DataInputClosurePointContext T →
        List SummaryTriple × SummaryTriple) := by
  exact Primrec.pair dataInputClosureRelation_primrec
    dataInputClosureTriple_primrec

private def dataInputClosureMember
    (q : DataInputClosurePointContext T) : Bool :=
  dataAdvanceMemberEval (dataInputClosureMemberInput q)

private theorem dataInputClosureMember_primrec :
    Primrec (dataInputClosureMember :
      DataInputClosurePointContext T → Bool) := by
  exact dataAdvanceMemberEval_primrec.comp
    dataInputClosureMemberInput_primrec

private def dataInputClosurePoint
    (q : DataInputClosurePointContext T) : Bool :=
  decide (dataInputClosurePath q = true →
    dataInputClosureTriple q ∈ dataInputClosureRelation q)

private theorem dataInputClosurePoint_primrec :
    Primrec (dataInputClosurePoint :
      DataInputClosurePointContext T → Bool) := by
  have hresult : Primrec (fun q : DataInputClosurePointContext T =>
      !dataInputClosurePath q || dataInputClosureMember q) :=
    Primrec.or.comp (Primrec.not.comp dataInputClosurePath_primrec)
      dataInputClosureMember_primrec
  apply Primrec.of_eq hresult
  intro q
  cases h : dataInputClosurePath q <;>
    simp [dataInputClosurePoint, dataInputClosureMember,
      dataAdvanceMemberEval, dataInputClosureMemberInput,
      dataInputClosureTriple, dataInputClosureRelation, h]

private def dataInputClosureRow
    (q : DataInputClosureContext T) : Bool :=
  (List.range (dataPStateCount q.1.1.1.1)).all fun r =>
    dataInputClosurePoint (q, r)

private theorem dataInputClosureRow_primrec :
    Primrec (dataInputClosureRow :
      DataInputClosureContext T → Bool) := by
  have hrange : Primrec (fun q : DataInputClosureContext T =>
      List.range (q.1.1.1.1.1 + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp
        (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  have hpoint : Primrec₂
      (fun (q : DataInputClosureContext T) (r : ℕ) =>
        dataInputClosurePoint (q, r)) := by
    apply Primrec₂.mk
    exact dataInputClosurePoint_primrec
  have hresult : Primrec (fun q : DataInputClosureContext T =>
      (List.range (q.1.1.1.1.1 + 1)).all fun r =>
        dataInputClosurePoint (q, r)) :=
    primrec_list_all hrange hpoint
  apply Primrec.of_eq hresult
  intro q
  rfl

private def dataInputClosed (q : DataClosedContext T) : Bool :=
  q.1.1.2.2.all fun row => dataInputClosureRow (q, row)

private theorem dataInputClosed_primrec :
    Primrec (dataInputClosed : DataClosedContext T → Bool) := by
  have hrows : Primrec (fun q : DataClosedContext T =>
      q.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst))
  have hrow : Primrec₂
      (fun (q : DataClosedContext T) (row : InputRow T) =>
        dataInputClosureRow (q, row)) := by
    apply Primrec₂.mk
    exact dataInputClosureRow_primrec
  exact primrec_list_all hrows hrow

private theorem dataSummaryClosed_primrec :
    Primrec₂ (dataSummaryClosed :
      SaturationCore T → List SummaryTriple → Bool) := by
  show Primrec (fun q : DataClosedContext T =>
    dataSummaryClosed q.1 q.2)
  have hresult : Primrec (fun q : DataClosedContext T =>
      (dataBaseClosed q && dataEpsilonClosed q) &&
        dataInputClosed q) :=
    Primrec.and.comp
      (Primrec.and.comp dataBaseClosed_primrec dataEpsilonClosed_primrec)
      dataInputClosed_primrec
  apply Primrec.of_eq hresult
  intro q
  rfl

private abbrev DataLeastTripleContext (T : Type) :=
  SaturationCore T × SummaryTriple

private def dataCoreAllSummaryTriples
    (d : SaturationCore T) : List SummaryTriple :=
  dataAllSummaryTriples d.1.1

private theorem dataCoreAllSummaryTriples_primrec :
    Primrec (dataCoreAllSummaryTriples :
      SaturationCore T → List SummaryTriple) := by
  exact dataAllSummaryTriples_primrec.comp
    (Primrec.fst.comp Primrec.fst)

private def dataLeastClosedPredicate
    (p : DataLeastTripleContext T) (R : List SummaryTriple) : Bool :=
  !dataSummaryClosed p.1 R ||
    dataAdvanceMemberEval (R, p.2)

private theorem dataLeastClosedPredicate_primrec :
    Primrec₂ (dataLeastClosedPredicate :
      DataLeastTripleContext T → List SummaryTriple → Bool) := by
  show Primrec (fun q :
      DataLeastTripleContext T × List SummaryTriple =>
    dataLeastClosedPredicate q.1 q.2)
  have hclosed : Primrec (fun q :
      DataLeastTripleContext T × List SummaryTriple =>
      dataSummaryClosed q.1.1 q.2) :=
    dataSummaryClosed_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hmemberInput : Primrec (fun q :
      DataLeastTripleContext T × List SummaryTriple =>
      (q.2, q.1.2)) :=
    Primrec.pair Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  have hmember : Primrec (fun q :
      DataLeastTripleContext T × List SummaryTriple =>
      dataAdvanceMemberEval (q.2, q.1.2)) :=
    dataAdvanceMemberEval_primrec.comp hmemberInput
  exact Primrec.or.comp (Primrec.not.comp hclosed) hmember

private def dataLeastTriplePredicate
    (p : DataLeastTripleContext T) : Bool :=
  (dataCoreAllSummaryTriples p.1).sublists.all
    (dataLeastClosedPredicate p)

private theorem dataLeastTriplePredicate_primrec :
    Primrec (dataLeastTriplePredicate :
      DataLeastTripleContext T → Bool) := by
  have hsubsets : Primrec (fun p : DataLeastTripleContext T =>
      (dataCoreAllSummaryTriples p.1).sublists) :=
    primrec_list_sublists.comp
      (dataCoreAllSummaryTriples_primrec.comp Primrec.fst)
  exact primrec_list_all hsubsets dataLeastClosedPredicate_primrec

private theorem dataLeastSummaryRelation_primrec :
    Primrec (dataLeastSummaryRelation :
      SaturationCore T → List SummaryTriple) := by
  have hresult : Primrec (fun d : SaturationCore T =>
      (dataCoreAllSummaryTriples d).filter fun t =>
        dataLeastTriplePredicate (d, t)) :=
    primrec_list_filterBool dataCoreAllSummaryTriples_primrec
      dataLeastTriplePredicate_primrec.to₂
  apply Primrec.of_eq hresult
  intro d
  rfl

/-- The least finite pushdown-summary relation is primitive recursive in the
raw encoded transition table. -/
public theorem leastSummaryRelation_primrec :
    Primrec
      (leastSummaryRelation : EncodedDPDA T → List SummaryTriple) := by
  have hdata : Primrec (fun c : EncodedDPDA T =>
      dataLeastSummaryRelation (effectiveSaturationData c).1) :=
    dataLeastSummaryRelation_primrec.comp
      (Primrec.fst.comp effectiveSaturationData_primrec)
  apply hdata.of_eq
  intro c
  rfl

/-- The least finite pushdown-summary relation is a total computable function
of the raw encoded transition table.  This public projection is useful to
effective preprocessing passes which need the summary itself, rather than only
the final universality bit computed from it. -/
public theorem leastSummaryRelation_computable :
    Computable
      (leastSummaryRelation : EncodedDPDA T → List SummaryTriple) :=
  leastSummaryRelation_primrec.to_comp

private abbrev DataReachPointContext (T : Type) :=
  SaturationData T × ℕ

private def dataReachCore
    (q : DataReachPointContext T) : SaturationCore T := q.1.1

private theorem dataReachCore_primrec :
    Primrec (dataReachCore :
      DataReachPointContext T → SaturationCore T) := by
  exact Primrec.fst.comp Primrec.fst

private def dataReachSizes
    (q : DataReachPointContext T) : SelectionSizes := q.1.1.1.1

private theorem dataReachSizes_primrec :
    Primrec (dataReachSizes :
      DataReachPointContext T → SelectionSizes) := by
  exact Primrec.fst.comp (Primrec.fst.comp
    (Primrec.fst.comp Primrec.fst))

private def dataReachFinals
    (q : DataReachPointContext T) : List ℕ := q.1.1.2

private theorem dataReachFinals_primrec :
    Primrec (dataReachFinals :
      DataReachPointContext T → List ℕ) := by
  exact Primrec.snd.comp (Primrec.fst.comp Primrec.fst)

private def dataReachInitial
    (q : DataReachPointContext T) : ℕ := q.1.2.1

private theorem dataReachInitial_primrec :
    Primrec (dataReachInitial :
      DataReachPointContext T → ℕ) := by
  exact Primrec.fst.comp (Primrec.snd.comp Primrec.fst)

private def dataReachStart
    (q : DataReachPointContext T) : ℕ := q.1.2.2

private theorem dataReachStart_primrec :
    Primrec (dataReachStart :
      DataReachPointContext T → ℕ) := by
  exact Primrec.snd.comp (Primrec.snd.comp Primrec.fst)

private def dataReachEndpoint
    (q : DataReachPointContext T) : ℕ := q.2

private theorem dataReachEndpoint_primrec :
    Primrec (dataReachEndpoint :
      DataReachPointContext T → ℕ) := Primrec.snd

private def dataReachLeastRelation
    (q : DataReachPointContext T) : List SummaryTriple :=
  dataLeastSummaryRelation (dataReachCore q)

private theorem dataReachLeastRelation_primrec :
    Primrec (dataReachLeastRelation :
      DataReachPointContext T → List SummaryTriple) := by
  exact dataLeastSummaryRelation_primrec.comp dataReachCore_primrec

private def dataReachNormalizedInitial
    (q : DataReachPointContext T) : ℕ :=
  dataReachInitial q % (dataReachSizes q).1

private theorem dataReachNormalizedInitial_primrec :
    Primrec (dataReachNormalizedInitial :
      DataReachPointContext T → ℕ) := by
  exact Primrec.nat_mod.comp dataReachInitial_primrec
    (Primrec.fst.comp dataReachSizes_primrec)

private def dataReachNormalizedStart
    (q : DataReachPointContext T) : ℕ :=
  dataReachStart q % (dataReachSizes q).2

private theorem dataReachNormalizedStart_primrec :
    Primrec (dataReachNormalizedStart :
      DataReachPointContext T → ℕ) := by
  exact Primrec.nat_mod.comp dataReachStart_primrec
    (Primrec.snd.comp dataReachSizes_primrec)

private def dataReachStack
    (q : DataReachPointContext T) : List ℕ :=
  [dataReachNormalizedStart q]

private theorem dataReachStack_primrec :
    Primrec (dataReachStack :
      DataReachPointContext T → List ℕ) := by
  exact Primrec.list_cons.comp dataReachNormalizedStart_primrec
    (Primrec.const [])

private def dataReachPathInput
    (q : DataReachPointContext T) : DataPathContext :=
  ((dataReachSizes q, dataReachLeastRelation q),
    (dataReachNormalizedInitial q, dataReachStack q,
      dataReachEndpoint q))

private theorem dataReachPathInput_primrec :
    Primrec (dataReachPathInput :
      DataReachPointContext T → DataPathContext) := by
  exact Primrec.pair
    (Primrec.pair dataReachSizes_primrec dataReachLeastRelation_primrec)
    (Primrec.pair dataReachNormalizedInitial_primrec
      (Primrec.pair dataReachStack_primrec dataReachEndpoint_primrec))

private def dataReachPath
    (q : DataReachPointContext T) : Bool :=
  dataSummaryPath (dataReachSizes q) (dataReachLeastRelation q)
    (dataReachNormalizedInitial q) (dataReachStack q)
    (dataReachEndpoint q)

private theorem dataReachPath_primrec :
    Primrec (dataReachPath : DataReachPointContext T → Bool) := by
  apply (dataSummaryPath_primrec.comp dataReachPathInput_primrec).of_eq
  intro q
  rfl

private def dataReachSink
    (q : DataReachPointContext T) : Bool :=
  decide (dataReachEndpoint q = (dataReachSizes q).1)

private theorem dataReachSink_primrec :
    Primrec (dataReachSink : DataReachPointContext T → Bool) := by
  exact (PrimrecRel.decide Primrec.eq).comp dataReachEndpoint_primrec
    (Primrec.fst.comp dataReachSizes_primrec)

private def dataReachRejectingParameter
    (q : DataReachPointContext T) : ℕ × List ℕ :=
  ((dataReachSizes q).1, dataReachFinals q)

private theorem dataReachRejectingParameter_primrec :
    Primrec (dataReachRejectingParameter :
      DataReachPointContext T → ℕ × List ℕ) := by
  exact Primrec.pair
    (Primrec.fst.comp dataReachSizes_primrec) dataReachFinals_primrec

private def dataReachRejecting
    (q : DataReachPointContext T) : Bool :=
  dataIsRejectingIndex (dataReachRejectingParameter q)
    (dataReachEndpoint q)

private theorem dataReachRejecting_primrec :
    Primrec (dataReachRejecting :
      DataReachPointContext T → Bool) := by
  exact dataIsRejectingIndex_primrec.comp
    dataReachRejectingParameter_primrec dataReachEndpoint_primrec

private def dataReachPoint
    (q : DataReachPointContext T) : Bool :=
  dataReachPath q && (dataReachSink q || dataReachRejecting q)

private theorem dataReachPoint_primrec :
    Primrec (dataReachPoint : DataReachPointContext T → Bool) := by
  exact Primrec.and.comp dataReachPath_primrec
    (Primrec.or.comp dataReachSink_primrec dataReachRejecting_primrec)

private theorem dataHasRejectingReach_primrec :
    Primrec (dataHasRejectingReach : SaturationData T → Bool) := by
  have hrange : Primrec (fun d : SaturationData T =>
      List.range (d.1.1.1.1 + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp
        (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))))
  have hpoint : Primrec₂
      (fun (d : SaturationData T) (r : ℕ) =>
        dataReachPoint (d, r)) := by
    apply Primrec₂.mk
    exact dataReachPoint_primrec
  have hresult : Primrec (fun d : SaturationData T =>
      (List.range (d.1.1.1.1 + 1)).any fun r =>
        dataReachPoint (d, r)) :=
    primrec_list_any_fast hrange hpoint
  apply Primrec.of_eq hresult
  intro d
  rfl

private theorem dataCheckUniversal_primrec :
    Primrec (dataCheckUniversal : SaturationData T → Bool) := by
  apply (Primrec.not.comp dataHasRejectingReach_primrec).of_eq
  intro d
  rfl

/-- The finite universality checker is a total computable function of the raw
encoded DPDA table. -/
public theorem checkUniversal_computable :
    Computable (checkUniversal : EncodedDPDA T → Bool) := by
  have hdata : Computable (fun c : EncodedDPDA T =>
      dataCheckUniversal (effectiveSaturationData c)) :=
    dataCheckUniversal_primrec.to_comp.comp
      effectiveSaturationData_primrec.to_comp
  apply hdata.of_eq
  intro c
  exact dataCheckUniversal_effectiveSaturationData c


/-- Membership in the language of a raw encoded DPDA is recursively enumerable,
uniformly in both the finite table code and the word. -/
public theorem language_membershipSemiDecidable :
    MembershipSemiDecidable (language : EncodedDPDA T → Language T) := by
  have hfuel : REPred (fun p : EncodedDPDA T × List T =>
      ∃ n : ℕ, p.1.acceptsAtFuel p.2 n = true) := by
    have hsearch : Partrec (fun p : EncodedDPDA T × List T =>
        Nat.rfind (fun n => Part.some (p.1.acceptsAtFuel p.2 n))) := by
      have htest : Computable₂
          (fun (p : EncodedDPDA T × List T) (n : ℕ) =>
            p.1.acceptsAtFuel p.2 n) :=
        acceptsAtFuel_computable.to₂
      exact Partrec.rfind htest.partrec₂
    exact hsearch.dom_re.of_eq fun p => by
      simp [Nat.rfind_dom]
  exact hfuel.of_eq fun p => exists_acceptsAtFuel_eq_true_iff p.1 p.2

/-- The finite Boolean universality checker is a partial-recursive evaluator
which is total and correct on the semantic total-DPDA promise. -/
public theorem universality_computablePredOnPromise :
    ComputablePredOnPromise (Valid : EncodedDPDA T → Prop)
      (fun c => language c = Set.univ) := by
  refine ⟨fun c => Part.some (checkUniversal c),
    checkUniversal_computable.partrec, ?_⟩
  intro c hc
  refine ⟨Part.some_dom _, ?_⟩
  have hcorrect := checkUniversal_eq_true_iff c hc
  constructor
  · intro huniv
    exact Part.mem_some_iff.mpr (hcorrect.mpr huniv).symm
  · intro hmem
    exact hcorrect.mp (Part.mem_some_iff.mp hmem).symm

/-- **Universality of deterministic context-free languages is uniformly
decidable from a finite encoded DPDA**, under the promise that the machine is a
total decider. -/
public theorem dcf_computableUniversality :
    ComputableUniversality DCF (language : EncodedDPDA T → Language T)
      (valid := Valid) :=
  ⟨language_characterizesOn, language_membershipSemiDecidable,
    universality_computablePredOnPromise⟩

end Computability

end DCFEncodedDPDA.EncodedDPDA
