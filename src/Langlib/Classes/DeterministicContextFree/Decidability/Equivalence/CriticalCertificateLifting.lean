module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkers

@[expose]
public section

/-!
# Replaying certificates in a critical-marker extension

Adding the fresh critical constants is conservative on terms over the original
rank table.  This file packages that fact at the level used by the finite-basis
calculus: structural and ground checks lift, original steps are preserved, and
an original certificate can be replayed with every observable label embedded
into the extended alphabet.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Extending a rank table on the right preserves structural well-formedness. -/
public theorem WellFormed.appendRanks
    {term : RegularTerm} {ranks extra : List ℕ} {variableBound : ℕ}
    (hterm : term.WellFormed ranks variableBound) :
    term.WellFormed (ranks ++ extra) variableBound := by
  unfold WellFormed wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨hterm.1, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hwell := (List.all_eq_true.mp hterm.2) node hnode
  cases node with
  | inl x => simpa [nodeWellFormedCode] using hwell
  | inr application =>
      rcases application with ⟨X, children⟩
      simp only [nodeWellFormedCode] at hwell ⊢
      cases hrank : ranks[X]? with
      | none => simp [hrank] at hwell
      | some rank =>
          have hX : X < ranks.length :=
            (List.getElem?_eq_some_iff.mp hrank).1
          rw [List.getElem?_append_left hX, hrank]
          simpa [hrank] using hwell

/-- Extending a rank table on the right preserves runtime shape validity. -/
public theorem ShapeWellFormed.appendRanks
    {term : RegularTerm} {ranks extra : List ℕ}
    (hterm : term.ShapeWellFormed ranks) :
    term.ShapeWellFormed (ranks ++ extra) := by
  unfold ShapeWellFormed shapeWellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨hterm.1, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hwell := (List.all_eq_true.mp hterm.2) node hnode
  cases node with
  | inl x => simpa [nodeShapeWellFormedCode] using hwell
  | inr application =>
      rcases application with ⟨X, children⟩
      simp only [nodeShapeWellFormedCode] at hwell ⊢
      cases hrank : ranks[X]? with
      | none => simp [hrank] at hwell
      | some rank =>
          have hX : X < ranks.length :=
            (List.getElem?_eq_some_iff.mp hrank).1
          rw [List.getElem?_append_left hX, hrank]
          simpa [hrank] using hwell

/-- Extending the rank table preserves groundness of an original term. -/
public theorem Ground.appendRanks
    {term : RegularTerm} {ranks extra : List ℕ}
    (hterm : term.Ground ranks) :
    term.Ground (ranks ++ extra) :=
  ⟨hterm.1.appendRanks, hterm.2⟩

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Original well-formed schemas remain well formed after adding markers. -/
public theorem basisPairWellFormedCode_withCriticalMarkers
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (pair : BasisPair)
    (hpair : g.basisPairWellFormedCode pair = true) :
    (g.withCriticalMarkers count).basisPairWellFormedCode pair = true := by
  unfold basisPairWellFormedCode at hpair ⊢
  rw [Bool.and_eq_true] at hpair ⊢
  exact ⟨RegularTerm.WellFormed.appendRanks hpair.1,
    RegularTerm.WellFormed.appendRanks hpair.2⟩

/-- Original ground arguments remain ground after adding markers. -/
public theorem groundArgumentsCode_withCriticalMarkers
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (arguments : List RegularTerm)
    (harguments : g.groundArgumentsCode arguments = true) :
    (g.withCriticalMarkers count).groundArgumentsCode arguments = true := by
  unfold groundArgumentsCode at harguments ⊢
  apply List.all_eq_true.mpr
  intro argument hargument
  apply (RegularTerm.groundCode_eq_true_iff _ _).mpr
  exact ((RegularTerm.groundCode_eq_true_iff _ _).mp
    ((List.all_eq_true.mp harguments) argument hargument)).appendRanks

/-- Original ground pairs remain ground after adding markers. -/
public theorem groundPairCode_withCriticalMarkers
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (left right : RegularTerm)
    (hpair : g.groundPairCode left right = true) :
    (g.withCriticalMarkers count).groundPairCode left right = true := by
  unfold groundPairCode at hpair ⊢
  rw [Bool.and_eq_true] at hpair ⊢
  constructor <;>
    apply (RegularTerm.groundCode_eq_true_iff _ _).mpr
  · exact ((RegularTerm.groundCode_eq_true_iff _ _).mp hpair.1).appendRanks
  · exact ((RegularTerm.groundCode_eq_true_iff _ _).mp hpair.2).appendRanks

/-- A fresh marker action cannot rewrite a term whose reachable tree uses only
symbols from the original rank table. -/
public theorem withCriticalMarkers_step?_fresh_of_ground
    (g : EncodedFirstOrderGrammar Action) (count marker : ℕ)
    {term : RegularTerm} (hground : term.Ground g.ranks) :
    (g.withCriticalMarkers count).step? (.inl (.inr marker)) term = none := by
  obtain ⟨support, _hsupport, hwitness⟩ := hground.2
  obtain ⟨X, children, hrootNode, _hchildren⟩ :=
    hwitness.2 term.root hwitness.1
  have hroot : term.rootApplication? = some (X, children) := by
    simp [RegularTerm.rootApplication?, RegularTerm.rootNode?, hrootNode]
  have hshape := hground.1
  unfold RegularTerm.ShapeWellFormed
    RegularTerm.shapeWellFormedCode at hshape
  rw [Bool.and_eq_true] at hshape
  have hnodeMem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hrootNode
  have hnodeWell := (List.all_eq_true.mp hshape.2) _ hnodeMem
  simp only [RegularTerm.nodeShapeWellFormedCode] at hnodeWell
  cases hrank : g.ranks[X]? with
  | none => simp [hrank] at hnodeWell
  | some rank =>
    have hX : X < g.ranks.length :=
      (List.getElem?_eq_some_iff.mp hrank).1
    change (g.withCriticalMarkers count).rootRewrite? (.inr marker) term = none
    unfold rootRewrite?
    rw [hroot]
    simp only
    rw [g.withCriticalMarkers_ruleLookup_markerAction_originalSymbol
      count marker X hX]
    rfl

@[simp] public theorem withCriticalMarkers_step?_originalAction
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (action : Action) (term : RegularTerm) :
    (g.withCriticalMarkers count).step? (.inl (.inl action)) term =
      g.step? (.inl action) term := by
  simpa only [liftCriticalLabel] using
    g.withCriticalMarkers_step?_lift count (.inl action) term

@[simp] public theorem withCriticalMarkers_step?_variable
    (g : EncodedFirstOrderGrammar Action) (count x : ℕ)
    (term : RegularTerm) :
    (g.withCriticalMarkers count).step? (.inr x) term =
      g.step? (.inr x) term := by
  simpa only [liftCriticalLabel] using
    g.withCriticalMarkers_step?_lift count (.inr x) term

/-- At depth one, trace agreement of original ground terms is unchanged by a
critical-marker extension. -/
public theorem traceApprox_one_withCriticalMarkers_iff
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    {left right : RegularTerm}
    (hleftGround : left.Ground g.ranks)
    (hrightGround : right.Ground g.ranks) :
    (g.withCriticalMarkers count).TraceApprox 1 left right ↔
      g.TraceApprox 1 left right := by
  constructor
  · intro hextended label
    have hrel := hextended (liftCriticalLabel label)
    rw [g.withCriticalMarkers_step?_lift count label left,
      g.withCriticalMarkers_step?_lift count label right] at hrel
    simpa [TraceApprox] using hrel
  · intro horiginal label
    cases label with
    | inl extendedAction =>
        cases extendedAction with
        | inl action =>
            have hrel := horiginal (.inl action)
            rw [g.withCriticalMarkers_step?_originalAction count action left,
              g.withCriticalMarkers_step?_originalAction count action right]
            simpa [TraceApprox] using hrel
        | inr marker =>
            rw [g.withCriticalMarkers_step?_fresh_of_ground count marker
                hleftGround,
              g.withCriticalMarkers_step?_fresh_of_ground count marker
                hrightGround]
            exact .none
    | inr x =>
        have hrel := horiginal (.inr x)
        rw [g.withCriticalMarkers_step?_variable count x left,
          g.withCriticalMarkers_step?_variable count x right]
        simpa [TraceApprox] using hrel

/-- Boolean depth-one comparison is literally preserved on original ground
terms. -/
public theorem traceApproxCode_one_withCriticalMarkers
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    {left right : RegularTerm}
    (hleftGround : left.Ground g.ranks)
    (hrightGround : right.Ground g.ranks) :
    (g.withCriticalMarkers count).traceApproxCode 1 left right =
      g.traceApproxCode 1 left right := by
  rw [Bool.eq_iff_iff, g.traceApproxCode_eq_true_iff,
    (g.withCriticalMarkers count).traceApproxCode_eq_true_iff]
  exact g.traceApprox_one_withCriticalMarkers_iff count
    hleftGround hrightGround

/-- Enabled labels at an original ground term are exactly the embedded
original enabled labels. -/
public theorem mem_enabledLabels_withCriticalMarkers_iff
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    {term : RegularTerm} (hground : term.Ground g.ranks)
    (label : Label (Action ⊕ ℕ)) :
    label ∈ (g.withCriticalMarkers count).enabledLabels term ↔
      ∃ original : Label Action,
        label = liftCriticalLabel original ∧
          original ∈ g.enabledLabels term := by
  rw [(g.withCriticalMarkers count).mem_enabledLabels_iff]
  constructor
  · intro hstep
    cases label with
    | inl extendedAction =>
        cases extendedAction with
        | inl action =>
            refine ⟨.inl action, rfl, ?_⟩
            rw [g.mem_enabledLabels_iff]
            simpa only [g.withCriticalMarkers_step?_originalAction]
              using hstep
        | inr marker =>
            rw [g.withCriticalMarkers_step?_fresh_of_ground count marker
              hground] at hstep
            simp at hstep
    | inr x =>
        refine ⟨.inr x, rfl, ?_⟩
        rw [g.mem_enabledLabels_iff]
        simpa only [g.withCriticalMarkers_step?_variable] using hstep
  · rintro ⟨original, rfl, horiginal⟩
    rw [g.mem_enabledLabels_iff] at horiginal
    simpa only [g.withCriticalMarkers_step?_lift] using horiginal

/-- Embed every word carried by a certificate judgment into the extended
observable alphabet. -/
@[expose] public def liftCriticalJudgment :
    CertificateJudgment Action → CertificateJudgment (Action ⊕ ℕ)
  | .pair word left right =>
      .pair (word.map liftCriticalLabel) left right
  | .nop word => .nop (word.map liftCriticalLabel)
  | .fail => .fail

omit [DecidableEq Action] in
private theorem ground_left_of_groundPairCode
    {g : EncodedFirstOrderGrammar Action} {left right : RegularTerm}
    (hpair : g.groundPairCode left right = true) :
    left.Ground g.ranks := by
  unfold groundPairCode at hpair
  rw [Bool.and_eq_true] at hpair
  exact (RegularTerm.groundCode_eq_true_iff _ _).mp hpair.1

omit [DecidableEq Action] in
private theorem ground_right_of_groundPairCode
    {g : EncodedFirstOrderGrammar Action} {left right : RegularTerm}
    (hpair : g.groundPairCode left right = true) :
    right.Ground g.ranks := by
  unfold groundPairCode at hpair
  rw [Bool.and_eq_true] at hpair
  exact (RegularTerm.groundCode_eq_true_iff _ _).mp hpair.2

/-- Every original finite-basis derivation can be replayed verbatim in a
critical-marker extension after embedding its observable words. -/
public theorem CertificateDerivable.withCriticalMarkers
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment)
    (count : ℕ) :
    CertificateDerivable (g.withCriticalMarkers count)
      initialLeft initialRight basis (liftCriticalJudgment judgment) := by
  induction h with
  | «axiom» hground =>
      exact .axiom (g.groundPairCode_withCriticalMarkers count
        initialLeft initialRight hground)
  | @transition word left right left' right' label hpair happrox
      hleft hright hground ih =>
      have hpairGround := groundPairCode_of_pair_derivable hpair
      have hleftGround := ground_left_of_groundPairCode hpairGround
      have hrightGround := ground_right_of_groundPairCode hpairGround
      have happrox' :
          (g.withCriticalMarkers count).traceApproxCode 1 left right = true := by
        rw [g.traceApproxCode_one_withCriticalMarkers count
          hleftGround hrightGround]
        exact happrox
      have hleft' :
          (g.withCriticalMarkers count).step?
              (liftCriticalLabel label) left = some left' := by
        rw [g.withCriticalMarkers_step?_lift count label left]
        exact hleft
      have hright' :
          (g.withCriticalMarkers count).step?
              (liftCriticalLabel label) right = some right' := by
        rw [g.withCriticalMarkers_step?_lift count label right]
        exact hright
      have hground' := g.groundPairCode_withCriticalMarkers count
        left' right' hground
      simpa [liftCriticalJudgment, List.map_append] using
        (CertificateDerivable.transition ih happrox' hleft' hright' hground')
  | @limit word shorterWord outerLeft outerRight shorterLeft shorterRight
      outerContext replacementContext focus houter hshorter
      houterContext hreplacementContext hfocus hnontrivial hlength
      houterMatch hshorterLeft hshorterRight hground ihOuter ihShorter =>
      have houterContext' : outerContext.WellFormed
          (g.withCriticalMarkers count).ranks 1 := by
        exact RegularTerm.WellFormed.appendRanks houterContext
      have hreplacementContext' : replacementContext.WellFormed
          (g.withCriticalMarkers count).ranks 1 := by
        exact RegularTerm.WellFormed.appendRanks hreplacementContext
      have hfocus' : focus.groundCode
          (g.withCriticalMarkers count).ranks = true := by
        apply (RegularTerm.groundCode_eq_true_iff _ _).mpr
        exact ((RegularTerm.groundCode_eq_true_iff _ _).mp hfocus).appendRanks
      have hlength' :
          (shorterWord.map liftCriticalLabel).length <
            (word.map liftCriticalLabel).length := by
        simpa using hlength
      have hground' := g.groundPairCode_withCriticalMarkers count
        (outerContext.instantiate [replacementContext.unaryLimit])
        outerRight hground
      simpa [liftCriticalJudgment, List.map_append] using
        (CertificateDerivable.limit ihOuter ihShorter
          houterContext' hreplacementContext' hfocus' hnontrivial
          hlength' houterMatch hshorterLeft hshorterRight hground')
  | symmetry hpair ih =>
      simpa [liftCriticalJudgment] using CertificateDerivable.symmetry ih
  | @basis word left right pairRef schema arguments hpair hschema hnonempty
      hschemaWellFormed hargumentCount harguments hleft hright ih =>
      have hnonempty' : word.map liftCriticalLabel ≠ [] := by
        simpa using hnonempty
      have hschemaWellFormed' :=
        g.basisPairWellFormedCode_withCriticalMarkers count schema
          hschemaWellFormed
      have harguments' :=
        g.groundArgumentsCode_withCriticalMarkers count arguments harguments
      exact CertificateDerivable.basis ih hschema hnonempty'
        hschemaWellFormed' hargumentCount harguments' hleft hright
  | @progression word left right hpair happrox hchildren ihPair ihChildren =>
      have hpairGround := groundPairCode_of_pair_derivable hpair
      have hleftGround := ground_left_of_groundPairCode hpairGround
      have hrightGround := ground_right_of_groundPairCode hpairGround
      have happrox' :
          (g.withCriticalMarkers count).traceApproxCode 1 left right = true := by
        rw [g.traceApproxCode_one_withCriticalMarkers count
          hleftGround hrightGround]
        exact happrox
      apply CertificateDerivable.progression ihPair happrox'
      intro extendedLabel hextended
      obtain ⟨originalLabel, rfl, horiginal⟩ :=
        (g.mem_enabledLabels_withCriticalMarkers_iff count
          hleftGround extendedLabel).mp hextended
      simpa [liftCriticalJudgment, List.map_append] using
        ihChildren originalLabel horiginal
  | @rejection word left right hpair hreject ih =>
      have hpairGround := groundPairCode_of_pair_derivable hpair
      have hleftGround := ground_left_of_groundPairCode hpairGround
      have hrightGround := ground_right_of_groundPairCode hpairGround
      have hreject' :
          (g.withCriticalMarkers count).traceApproxCode 1 left right = false := by
        rw [g.traceApproxCode_one_withCriticalMarkers count
          hleftGround hrightGround]
        exact hreject
      exact CertificateDerivable.rejection ih hreject'

end EncodedFirstOrderGrammar

end DCFEquivalence
