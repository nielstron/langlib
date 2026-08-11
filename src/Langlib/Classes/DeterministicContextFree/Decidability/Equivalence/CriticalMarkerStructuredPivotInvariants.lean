module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerStructuredPivotStairAssembly

@[expose]
public section

/-!
# Marker-free invariants for structured pivot stairs

The marker-stable structured stair constructor asks for four low-level facts:
the pivot residual schemas and active depth-one heads are ranked by the
original grammar, and the outer stem and balancing segment are lifted original
words.  This module packages a more operational invariant which supplies all
four facts automatically.

A finite head is marker-free when every application symbol lies below the end
of the original rank table.  A word is marker-free when it contains no fresh
marker action.  Extended groundness then proves original ranking of the finite
heads, while the elementary label dichotomy proves that every marker-free word
is the lift of an original word.
-/

namespace DCFEquivalence

namespace FiniteHead

/-- Every application symbol in a finite head lies in the given initial
symbol interval. -/
@[expose] public def SymbolsBelow (bound : ℕ) : FiniteHead → Prop
  | .var _ => True
  | .app symbol children =>
      symbol < bound ∧
        ∀ child ∈ children, child.SymbolsBelow bound

/-- Ranking by an extended table restricts to the original prefix whenever
the finite head contains no symbol from the extension. -/
public theorem rankedBy_prefix_of_symbolsBelow
    {head : FiniteHead} {ranks extra : List ℕ}
    (hranked : head.RankedBy (ranks ++ extra))
    (hbelow : head.SymbolsBelow ranks.length) :
    head.RankedBy ranks := by
  cases head with
  | var index =>
      simp [RankedBy]
  | app symbol children =>
      simp only [RankedBy, SymbolsBelow] at hranked hbelow ⊢
      constructor
      · rw [List.getElem?_append_left hbelow.1] at hranked
        exact hranked.1
      · intro child hchild
        exact rankedBy_prefix_of_symbolsBelow
          (hranked.2 child hchild) (hbelow.2 child hchild)
termination_by head

/-- Shifting boundary variables does not change any application symbol. -/
public theorem symbolsBelow_shiftVariables
    {head : FiniteHead} {bound offset : ℕ}
    (hbelow : head.SymbolsBelow bound) :
    (head.shiftVariables offset).SymbolsBelow bound := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ head ∈ heads, head.SymbolsBelow bound) →
        ∀ head ∈ heads,
          (head.shiftVariables offset).SymbolsBelow bound) with
  | var index =>
      simp [shiftVariables, SymbolsBelow]
  | app symbol children ih =>
      simp only [SymbolsBelow] at hbelow
      rw [shiftVariables, SymbolsBelow]
      constructor
      · exact hbelow.1
      · intro child hchild
        obtain ⟨original, horiginal, rfl⟩ :=
          List.mem_map.mp hchild
        exact ih hbelow.2 original horiginal
  | nil => aesop
  | cons head heads ihHead ihHeads => aesop

end FiniteHead

namespace DepthPrefix

/-- Collecting and renumbering child heads preserves a symbol bound. -/
public theorem collectHeads_symbolsBelow
    {children : List DepthPrefix} {bound offset : ℕ}
    (hchildren : ∀ child ∈ children,
      child.head.SymbolsBelow bound) :
    ∀ head ∈ collectHeads children offset,
      head.SymbolsBelow bound := by
  induction children generalizing offset with
  | nil =>
      simp [collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | hhead
      · exact FiniteHead.symbolsBelow_shiftVariables
          (hchildren child (by simp))
      · apply ih
        · intro item hitem
          exact hchildren item (by simp [hitem])
        · exact hhead

end DepthPrefix

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A successful lifted original step at an application root certifies that
the root symbol belongs to the original rank table. -/
public theorem withCriticalMarkers_rootSymbol_lt_of_lifted_step
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (count : ℕ) {source target : RegularTerm}
    {X : ℕ} {children : List ℕ} {label : Label Action}
    (hroot : source.rootApplication? = some (X, children))
    (hstep : (g.withCriticalMarkers count).step?
      (liftCriticalLabel label) source = some target) :
    X < g.ranks.length := by
  rw [withCriticalMarkers_step?_lift] at hstep
  cases label with
  | inl action =>
      change g.rootRewrite? action source = some target at hstep
      unfold rootRewrite? at hstep
      rw [hroot] at hstep
      obtain ⟨rhs, hrule, _htarget⟩ :=
        Option.map_eq_some_iff.mp hstep
      obtain ⟨rank, hrank, _hrhs⟩ :=
        selected_rhs_wellFormed hg hrule
      exact (List.getElem?_eq_some_iff.mp hrank).1
  | inr x =>
      have hrootNode :
          source.rootNode? = some (.inr (X, children)) := by
        simpa [RegularTerm.rootNode?] using
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
      unfold step? at hstep
      rw [hrootNode] at hstep
      contradiction

/-- At depth one the finite prefix retains only the root application symbol;
all immediate successors are boundary variables. -/
public theorem RegularTerm.depthPrefix_one_head_symbolsBelow
    {term : RegularTerm} {X : ℕ} {children : List ℕ} {bound : ℕ}
    (hroot : term.rootApplication? = some (X, children))
    (hX : X < bound) :
    (term.depthPrefix 1).head.SymbolsBelow bound := by
  rw [show 1 = 0 + 1 by omega,
    RegularTerm.depthPrefix_succ_of_rootApplication hroot 0]
  unfold DepthPrefix.assemble
  simp only
  rw [FiniteHead.SymbolsBelow]
  constructor
  · exact hX
  · intro child hchild
    apply DepthPrefix.collectHeads_symbolsBelow
      (children := children.map fun child =>
        (term.withRoot child).depthPrefix 0)
    · intro decomposition hdecomposition
      obtain ⟨index, _hindex, rfl⟩ :=
        List.mem_map.mp hdecomposition
      simp [RegularTerm.depthPrefix_zero,
        FiniteHead.SymbolsBelow]
    · exact hchild

/-- A word over a critical-marker extension contains no fresh marker action.
Original actions and variable labels are both allowed. -/
@[expose] public def NoCriticalMarkerActions
    (word : List (Label (Action ⊕ ℕ))) : Prop :=
  ∀ marker, (.inl (.inr marker) : Label (Action ⊕ ℕ)) ∉ word

omit [DecidableEq Action] in
/-- Concatenating marker-free words remains marker-free. -/
public theorem NoCriticalMarkerActions.append
    {left right : List (Label (Action ⊕ ℕ))}
    (hleft : NoCriticalMarkerActions left)
    (hright : NoCriticalMarkerActions right) :
    NoCriticalMarkerActions (left ++ right) := by
  intro marker hmarker
  rw [List.mem_append] at hmarker
  exact hmarker.elim (hleft marker) (hright marker)

omit [DecidableEq Action] in
/-- Each factor of a marker-free concatenation is marker-free. -/
public theorem NoCriticalMarkerActions.left_of_append
    {left right : List (Label (Action ⊕ ℕ))}
    (hword : NoCriticalMarkerActions (left ++ right)) :
    NoCriticalMarkerActions left := by
  intro marker hmarker
  exact hword marker (List.mem_append_left right hmarker)

omit [DecidableEq Action] in
public theorem NoCriticalMarkerActions.right_of_append
    {left right : List (Label (Action ⊕ ℕ))}
    (hword : NoCriticalMarkerActions (left ++ right)) :
    NoCriticalMarkerActions right := by
  intro marker hmarker
  exact hword marker (List.mem_append_right left hmarker)

omit [DecidableEq Action] in
/-- Taking a prefix or suffix cannot introduce a marker action. -/
public theorem NoCriticalMarkerActions.take
    {word : List (Label (Action ⊕ ℕ))}
    (hword : NoCriticalMarkerActions word) (length : ℕ) :
    NoCriticalMarkerActions (word.take length) := by
  intro marker hmarker
  exact hword marker (List.mem_of_mem_take hmarker)

omit [DecidableEq Action] in
public theorem NoCriticalMarkerActions.drop
    {word : List (Label (Action ⊕ ℕ))}
    (hword : NoCriticalMarkerActions word) (length : ℕ) :
    NoCriticalMarkerActions (word.drop length) := by
  intro marker hmarker
  exact hword marker (List.mem_of_mem_drop hmarker)

/-- A word over the extension is pointwise the canonical lift of one original
word. -/
@[expose] public def IsLiftedCriticalWord
    (word : List (Label (Action ⊕ ℕ))) : Prop :=
  ∃ originalWord : List (Label Action),
    word = originalWord.map liftCriticalLabel

omit [DecidableEq Action] in
/-- Every extended word is either an original lift or contains a fresh marker
action. -/
public theorem isLiftedCriticalWord_or_exists_markerAction
    (word : List (Label (Action ⊕ ℕ))) :
    IsLiftedCriticalWord word ∨
      ∃ marker, (.inl (.inr marker) : Label (Action ⊕ ℕ)) ∈ word := by
  induction word with
  | nil =>
      exact Or.inl ⟨[], rfl⟩
  | cons label word ih =>
      cases label with
      | inl action =>
          cases action with
          | inl originalAction =>
              rcases ih with hlifted | hmarker
              · obtain ⟨originalWord, hword⟩ := hlifted
                exact Or.inl
                  ⟨(.inl originalAction : Label Action) :: originalWord,
                    by simp [hword, liftCriticalLabel]⟩
              · obtain ⟨marker, hmarker⟩ := hmarker
                exact Or.inr ⟨marker, by simp [hmarker]⟩
          | inr marker =>
              exact Or.inr ⟨marker, by simp⟩
      | inr x =>
          rcases ih with hlifted | hmarker
          · obtain ⟨originalWord, hword⟩ := hlifted
            exact Or.inl
              ⟨(.inr x : Label Action) :: originalWord,
                by simp [hword, liftCriticalLabel]⟩
          · obtain ⟨marker, hmarker⟩ := hmarker
            exact Or.inr ⟨marker, by simp [hmarker]⟩

omit [DecidableEq Action] in
/-- Absence of marker actions is exactly the condition needed to reconstruct
an original word. -/
public theorem isLiftedCriticalWord_of_noCriticalMarkerActions
    {word : List (Label (Action ⊕ ℕ))}
    (hword : NoCriticalMarkerActions word) :
    IsLiftedCriticalWord word := by
  rcases isLiftedCriticalWord_or_exists_markerAction word with
      hlifted | ⟨marker, hmarker⟩
  · exact hlifted
  · exact (hword marker) hmarker |>.elim

omit [DecidableEq Action] in
/-- A lifted concatenation splits into lifted left and right factors. -/
public theorem exists_originalWords_of_append_isLifted
    {left right : List (Label (Action ⊕ ℕ))}
    (hlifted : IsLiftedCriticalWord (left ++ right)) :
    ∃ leftOriginal rightOriginal : List (Label Action),
      left = leftOriginal.map liftCriticalLabel ∧
        right = rightOriginal.map liftCriticalLabel := by
  obtain ⟨originalWord, hword⟩ := hlifted
  induction left generalizing originalWord with
  | nil =>
      exact ⟨[], originalWord, rfl, by simpa using hword⟩
  | cons label left ih =>
      cases originalWord with
      | nil =>
          simp at hword
      | cons originalLabel originalWord =>
          simp only [List.cons_append, List.map_cons,
            List.cons.injEq] at hword
          obtain ⟨hlabel, htail⟩ := hword
          obtain ⟨leftOriginal, rightOriginal,
              hleft, hright⟩ := ih originalWord htail
          exact
            ⟨originalLabel :: leftOriginal, rightOriginal,
              by simp [hlabel, hleft], hright⟩

omit [DecidableEq Action] in
/-- A list of ordinary extension actions whose ordinary labels form a lifted
original word consists entirely of injected original actions. -/
public theorem exists_originalActions_of_map_inl_eq_map_liftCriticalLabel
    {extendedActions : List (Action ⊕ ℕ)}
    {originalWord : List (Label Action)}
    (hword :
      extendedActions.map Sum.inl =
        originalWord.map liftCriticalLabel) :
    ∃ originalActions : List Action,
      extendedActions = originalActions.map Sum.inl ∧
        originalWord = originalActions.map Sum.inl := by
  induction extendedActions generalizing originalWord with
  | nil =>
      simp only [List.map_nil] at hword
      have horiginal : originalWord = [] :=
        List.map_eq_nil_iff.mp hword.symm
      subst originalWord
      exact ⟨[], rfl, rfl⟩
  | cons extendedAction extendedActions ih =>
      cases originalWord with
      | nil => simp at hword
      | cons originalLabel originalWord =>
          simp only [List.map_cons, List.cons.injEq] at hword
          rcases hword with ⟨hhead, htail⟩
          cases extendedAction with
          | inl action =>
              cases originalLabel with
              | inl originalAction =>
                  simp only [liftCriticalLabel,
                    Sum.inl.injEq] at hhead
                  subst originalAction
                  obtain ⟨actions, hextended, horiginal⟩ :=
                    ih htail
                  exact ⟨action :: actions, by
                    simp [hextended], by simp [horiginal]⟩
              | inr x =>
                  simp [liftCriticalLabel] at hhead
          | inr marker =>
              cases originalLabel <;>
                simp [liftCriticalLabel] at hhead

omit [DecidableEq Action] in
/-- An ordinary-action word in the extension which contains no fresh marker
action consists entirely of injected original actions. -/
public theorem exists_originalActions_of_noCriticalMarkerActions
    {extendedActions : List (Action ⊕ ℕ)}
    (hword :
      NoCriticalMarkerActions (extendedActions.map Sum.inl)) :
    ∃ originalActions : List Action,
      extendedActions = originalActions.map Sum.inl := by
  obtain ⟨originalWord, hlifted⟩ :=
    isLiftedCriticalWord_of_noCriticalMarkerActions hword
  obtain ⟨originalActions, hextended, _horiginal⟩ :=
    exists_originalActions_of_map_inl_eq_map_liftCriticalLabel
      hlifted
  exact ⟨originalActions, hextended⟩

/-- Every exact path segment ending no later than a marker-free accumulated
endpoint is marker-free. -/
public theorem TracePath.segmentWord_noCriticalMarkerActions_of_endpoint
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    {start length endpoint : ℕ}
    (hfit : start + length ≤ endpoint)
    (hendpoint :
      NoCriticalMarkerActions (path.word endpoint)) :
    NoCriticalMarkerActions (path.segmentWord start length) := by
  have hstart : start ≤ endpoint := by omega
  let total := endpoint - start
  have hlength : length ≤ total := by
    dsimp [total]
    omega
  have htotal : start + total = endpoint := by
    dsimp [total]
    omega
  have htake :
      (path.segmentWord start total).take length =
        path.segmentWord start length :=
    path.take_segmentWord start hlength
  have hlarge :
      NoCriticalMarkerActions (path.segmentWord start total) := by
    have hfull :
        path.word endpoint =
          path.word start ++ path.segmentWord start total := by
      simpa [htotal] using path.word_add start total
    rw [hfull] at hendpoint
    exact hendpoint.right_of_append
  rw [← htake]
  exact hlarge.take length

/-- An ordinary-action run in a marker extension from an original schema is
an ordinary-action run of the original grammar. -/
public theorem exists_original_runActions_of_withCriticalMarkers
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity : ℕ} {source residual : RegularTerm}
    {actions : List (Action ⊕ ℕ)}
    (hsource : source.WellFormed g.ranks arity)
    (hrun : (g.withCriticalMarkers count).runActions?
      actions source = some residual) :
    ∃ originalActions : List Action,
      actions = originalActions.map Sum.inl ∧
        g.runActions? originalActions source = some residual := by
  have hrunLabels :
      (g.withCriticalMarkers count).run?
        (actions.map Sum.inl) source = some residual := by
    simpa [runActions?] using hrun
  obtain ⟨originalWord, hword, horiginalRun⟩ :=
    (withCriticalMarkers_run?_some_iff_original g hg count
      (RegularTerm.usesOriginalSymbols_of_wellFormed hsource)).mp
      hrunLabels
  obtain ⟨originalActions, hactions, horiginalWord⟩ :=
    exists_originalActions_of_map_inl_eq_map_liftCriticalLabel
      hword
  refine ⟨originalActions, hactions, ?_⟩
  rw [horiginalWord] at horiginalRun
  simpa [runActions?] using horiginalRun

/-- Original schema well-formedness is preserved by a successful symbolic
ordinary-action run in a critical-marker extension. -/
public theorem runActions?_preserves_wellFormed_original
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity : ℕ} {source residual : RegularTerm}
    {actions : List (Action ⊕ ℕ)}
    (hsource : source.WellFormed g.ranks arity)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hrun : (g.withCriticalMarkers count).runActions?
      actions source = some residual) :
    residual.WellFormed g.ranks arity := by
  obtain ⟨originalActions, _hactions, horiginalRun⟩ :=
    exists_original_runActions_of_withCriticalMarkers
      hg hsource hrun
  exact g.runActions?_preserves_wellFormed_padded
    hg hpadding originalActions hsource horiginalRun

namespace TracePath.StructuredPivotChain

/-- Along the selected structured suffix, either every endpoint prefix is
marker-free or some endpoint prefix already contains a fresh marker action.
Turning the second branch into `EventuallyMarkerStableOpenSound` requires a
separate coverage theorem relating that marker event to the current symbolic
row. -/
public theorem endpointMarkerActionDichotomy
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (start : ℕ) :
    (∀ j, NoCriticalMarkerActions
      (path.word (chain.levels (start + j)))) ∨
      ∃ j marker,
        (.inl (.inr marker) : Label (Action ⊕ ℕ)) ∈
          path.word (chain.levels (start + j)) := by
  classical
  by_cases hall : ∀ j, NoCriticalMarkerActions
      (path.word (chain.levels (start + j)))
  · exact Or.inl hall
  · right
    obtain ⟨j, hj⟩ := not_forall.mp hall
    unfold NoCriticalMarkerActions at hj
    push_neg at hj
    obtain ⟨marker, hmarker⟩ := hj
    exact ⟨j, marker, hmarker⟩

/-- If the selected endpoint prefix contains no marker action, then the
depth-one active head of that row uses only original symbols.  The balancing
word is nonempty; its first successful step cannot start with a marker action,
so the active root is an original ranked symbol. -/
public theorem activeHead_symbolsBelow_of_endpoint_noMarkerActions
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (hbound : 0 < bound) (index : ℕ)
    (hendpoint : NoCriticalMarkerActions
      (path.word (chain.levels index))) :
    let step := (chain.states index).incoming
    ((SelectedBalancingSegment.active step.selected).depthPrefix 1)
      |>.head.SymbolsBelow g.ranks.length := by
  let state := chain.states index
  let step := state.incoming
  let active := SelectedBalancingSegment.active step.selected
  let segment := SelectedBalancingSegment.asSegment step.selected
  let segmentWord :=
    (state.source.continuationPath
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial).segmentWord step.offset bound
  have hwordEq :
      step.outerStem ++ segmentWord =
        path.word (chain.levels index) := by
    simpa [state, step, segmentWord, levels] using
      step.outerStem_append_labels
  have hsegmentNoMarker :
      NoCriticalMarkerActions segmentWord := by
    intro marker hmarker
    apply hendpoint marker
    rw [← hwordEq]
    simp [hmarker]
  have hsegmentNonempty : segmentWord ≠ [] := by
    simpa [segment, segmentWord] using segment.word_ne_nil hbound
  obtain ⟨label, suffix, hsegmentCons⟩ :=
    List.exists_cons_of_ne_nil hsegmentNonempty
  have hrun := segment.active_run
  change (g.withCriticalMarkers count).run?
      segmentWord active = some segment.active_target at hrun
  rw [hsegmentCons, run?_cons] at hrun
  cases hfirst :
      (g.withCriticalMarkers count).step? label active with
  | none =>
      simp [hfirst] at hrun
  | some next =>
      have hroot := step.active_ground.exists_rootApplication
      obtain ⟨X, children, hactiveRoot⟩ := hroot
      have hX : X < g.ranks.length := by
        cases label with
        | inl action =>
            cases action with
            | inl originalAction =>
                exact
                  withCriticalMarkers_rootSymbol_lt_of_lifted_step
                    (label := (.inl originalAction : Label Action))
                    hg count hactiveRoot (by
                      simpa [active, liftCriticalLabel] using hfirst)
            | inr marker =>
                exfalso
                exact (hsegmentNoMarker marker) (by
                  rw [hsegmentCons]
                  simp)
        | inr x =>
            exact
              withCriticalMarkers_rootSymbol_lt_of_lifted_step
                (label := (.inr x : Label Action))
                hg count hactiveRoot (by
                  simpa [active, liftCriticalLabel] using hfirst)
      simpa [state, step, active] using
        RegularTerm.depthPrefix_one_head_symbolsBelow
          hactiveRoot hX

/-- Endpoint marker-freeness directly supplies the original-rank
well-formedness of the selected active depth-one prefix. -/
public theorem activePrefixOriginal_of_endpoint_noMarkerActions
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (hbound : 0 < bound) (index : ℕ)
    (hendpoint : NoCriticalMarkerActions
      (path.word (chain.levels index))) :
    let step := (chain.states index).incoming
    ((SelectedBalancingSegment.active step.selected).depthPrefix 1)
      |>.head.toRegularTerm.WellFormed g.ranks
        (((SelectedBalancingSegment.active step.selected).depthPrefix 1)
          |>.schemaArity (g.withCriticalMarkers count).ranks) := by
  let step := (chain.states index).incoming
  let active := SelectedBalancingSegment.active step.selected
  let decomposition := active.depthPrefix 1
  have hextendedRanked : decomposition.head.RankedBy
      (g.withCriticalMarkers count).ranks :=
    RegularTerm.depthPrefix_head_rankedBy step.active_ground 1
  have horiginalRanked : decomposition.head.RankedBy g.ranks := by
    apply FiniteHead.rankedBy_prefix_of_symbolsBelow
      (extra := List.replicate count 0)
    · simpa only [withCriticalMarkers_ranks] using hextendedRanked
    · simpa [step, active, decomposition] using
        chain.activeHead_symbolsBelow_of_endpoint_noMarkerActions
          (hg := hg) hbound index hendpoint
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid active 1
  have hwell :=
    decomposition.head_wellFormed_schemaArity
      hvalid horiginalRanked
  have harity :
      decomposition.schemaArity g.ranks =
        decomposition.schemaArity
          (g.withCriticalMarkers count).ranks := by
    unfold DepthPrefix.schemaArity
    rw [withCriticalMarkers_rankMax]
  change decomposition.head.toRegularTerm.WellFormed g.ranks
    (decomposition.schemaArity
      (g.withCriticalMarkers count).ranks)
  rw [← harity]
  exact hwell

/-- A marker-free selected endpoint splits at the structured balancing
boundary into an original outer stem and an original balancing segment. -/
public theorem exists_originalStemAndSegment_of_endpoint_noMarkerActions
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (index : ℕ)
    (hendpoint : NoCriticalMarkerActions
      (path.word (chain.levels index))) :
    let state := chain.states index
    let step := state.incoming
    ∃ originalStem originalSegment : List (Label Action),
      step.outerStem = originalStem.map liftCriticalLabel ∧
        (state.source.continuationPath
          (g.withCriticalMarkers_wellFormed hg count)
          hground hinitial).segmentWord step.offset bound =
            originalSegment.map liftCriticalLabel := by
  let state := chain.states index
  let step := state.incoming
  have hendpointLifted :
      IsLiftedCriticalWord
        (path.word (chain.levels index)) :=
    isLiftedCriticalWord_of_noCriticalMarkerActions hendpoint
  have happend :
      step.outerStem ++
          (state.source.continuationPath
            (g.withCriticalMarkers_wellFormed hg count)
            hground hinitial).segmentWord step.offset bound =
        path.word (chain.levels index) := by
    simpa [state, step] using step.outerStem_append_labels
  apply exists_originalWords_of_append_isLifted
  rw [happend]
  exact hendpointLifted

/-- The exact marker-stability data consumed by the structured stair
constructor. -/
public structure MarkerStableStructuredPivotPremises
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalExposureRebase)
    {filler : RegularTerm}
    (presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j))) where
  pivotSchemaOriginal : ∀ j,
    (presentation.schema j).WellFormed
      g.ranks presentation.arity
  activePrefixOriginal : ∀ j,
    let index := rebase.start + j
    let step := (chain.states index).incoming
    ((SelectedBalancingSegment.active step.selected).depthPrefix 1)
      |>.head.toRegularTerm.WellFormed g.ranks
        (((SelectedBalancingSegment.active step.selected).depthPrefix 1)
          |>.schemaArity (g.withCriticalMarkers count).ranks)
  originalStem : ℕ → List (Label Action)
  originalSegment : ℕ → List (Label Action)
  stem_eq : ∀ j,
    let index := rebase.start + j
    let step := (chain.states index).incoming
    step.outerStem = (originalStem j).map liftCriticalLabel
  segment_eq : ∀ j,
    let index := rebase.start + j
    let state := chain.states index
    let step := state.incoming
    (state.source.continuationPath
        (g.withCriticalMarkers_wellFormed hg count)
        hground hinitial).segmentWord step.offset bound =
      (originalSegment j).map liftCriticalLabel

/-- Marker-freeness of the two relevant finite heads and of the selected
absolute path prefixes.  These three operational facts imply all low-level
marker-stable stair premises. -/
public structure MarkerFreeStructuredPivotSuffix
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalExposureRebase)
    {filler : RegularTerm}
    (presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j))) where
  baseHead_symbolsBelow :
    (rebase.base.depthPrefix presentation.depth).head.SymbolsBelow
      g.ranks.length
  activeHead_symbolsBelow : ∀ j,
    let index := rebase.start + j
    let step := (chain.states index).incoming
    ((SelectedBalancingSegment.active step.selected).depthPrefix 1)
      |>.head.SymbolsBelow g.ranks.length
  endpoint_noMarkerActions : ∀ j,
    NoCriticalMarkerActions
      (path.word (chain.levels (rebase.start + j)))

namespace MarkerFreeStructuredPivotSuffix

/-- Endpoint marker-freeness automatically supplies the depth-one active-head
condition.  Only marker-freeness of the fixed rebased base prefix remains as
an independent structural premise. -/
public def of_endpointNoMarkerActions
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    {rebase : trajectory.MaximalExposureRebase}
    {filler : RegularTerm}
    {presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j))}
    (hbound : 0 < bound)
    (hbase :
      (rebase.base.depthPrefix presentation.depth).head.SymbolsBelow
        g.ranks.length)
    (hendpoint : ∀ j, NoCriticalMarkerActions
      (path.word (chain.levels (rebase.start + j)))) :
    MarkerFreeStructuredPivotSuffix
      (hg := hg) chain trajectory rebase presentation :=
  { baseHead_symbolsBelow := hbase
    activeHead_symbolsBelow := fun j =>
      chain.activeHead_symbolsBelow_of_endpoint_noMarkerActions
        (hg := hg) hbound (rebase.start + j) (hendpoint j)
    endpoint_noMarkerActions := hendpoint }

/-- A marker-free fixed base makes every fixed-tail residual schema an
original-rank schema. -/
public theorem pivotSchemaOriginal
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    {rebase : trajectory.MaximalExposureRebase}
    {filler : RegularTerm}
    {presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j))}
    (markerFree : MarkerFreeStructuredPivotSuffix
      (hg := hg) chain trajectory rebase presentation)
    (j : ℕ) :
    (presentation.schema j).WellFormed
      g.ranks presentation.arity := by
  let decomposition := rebase.base.depthPrefix presentation.depth
  have hextendedRanked : decomposition.head.RankedBy
      (g.withCriticalMarkers count).ranks :=
    RegularTerm.depthPrefix_head_rankedBy
      presentation.base_ground presentation.depth
  have horiginalRanked : decomposition.head.RankedBy g.ranks := by
    apply FiniteHead.rankedBy_prefix_of_symbolsBelow
      (extra := List.replicate count 0)
    · simpa only [withCriticalMarkers_ranks] using hextendedRanked
    · exact markerFree.baseHead_symbolsBelow
  have hsource :
      decomposition.head.toRegularTerm.WellFormed
        g.ranks presentation.arity := by
    have hvalid : decomposition.Valid :=
      RegularTerm.depthPrefix_valid rebase.base presentation.depth
    have hwell :=
      decomposition.head_wellFormed_schemaArity
        hvalid horiginalRanked
    have harity :
        decomposition.schemaArity g.ranks =
          presentation.arity := by
      change decomposition.schemaArity g.ranks =
        decomposition.schemaArity
          (g.withCriticalMarkers count).ranks
      unfold DepthPrefix.schemaArity
      rw [withCriticalMarkers_rankMax]
    rw [← harity]
    exact hwell
  have hpadding : g.ranks.foldr max 0 ≤ presentation.arity := by
    rw [← withCriticalMarkers_rankMax g count]
    exact presentation.rankMax_le_arity
  exact runActions?_preserves_wellFormed_original
    hg hsource hpadding (presentation.residual j).symbolic_run

/-- Marker-freeness of each selected active depth-one head supplies the
original-rank active-prefix premise. -/
public theorem activePrefixOriginal
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    {rebase : trajectory.MaximalExposureRebase}
    {filler : RegularTerm}
    {presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j))}
    (markerFree : MarkerFreeStructuredPivotSuffix
      (hg := hg) chain trajectory rebase presentation)
    (j : ℕ) :
    let index := rebase.start + j
    let step := (chain.states index).incoming
    ((SelectedBalancingSegment.active step.selected).depthPrefix 1)
      |>.head.toRegularTerm.WellFormed g.ranks
        (((SelectedBalancingSegment.active step.selected).depthPrefix 1)
          |>.schemaArity (g.withCriticalMarkers count).ranks) := by
  let index := rebase.start + j
  let step := (chain.states index).incoming
  let active := SelectedBalancingSegment.active step.selected
  let decomposition := active.depthPrefix 1
  have hextendedRanked : decomposition.head.RankedBy
      (g.withCriticalMarkers count).ranks :=
    RegularTerm.depthPrefix_head_rankedBy step.active_ground 1
  have horiginalRanked : decomposition.head.RankedBy g.ranks := by
    apply FiniteHead.rankedBy_prefix_of_symbolsBelow
      (extra := List.replicate count 0)
    · simpa only [withCriticalMarkers_ranks] using hextendedRanked
    · simpa [index, step, active, decomposition] using
        markerFree.activeHead_symbolsBelow j
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid active 1
  have hwell :=
    decomposition.head_wellFormed_schemaArity
      hvalid horiginalRanked
  have harity :
      decomposition.schemaArity g.ranks =
        decomposition.schemaArity
          (g.withCriticalMarkers count).ranks := by
    unfold DepthPrefix.schemaArity
    rw [withCriticalMarkers_rankMax]
  change decomposition.head.toRegularTerm.WellFormed g.ranks
    (decomposition.schemaArity
      (g.withCriticalMarkers count).ranks)
  rw [← harity]
  exact hwell

/-- Marker-free endpoint words split at the exact structured balancing
boundary into an original outer stem and an original segment word. -/
public theorem exists_originalStemAndSegment
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    {rebase : trajectory.MaximalExposureRebase}
    {filler : RegularTerm}
    {presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j))}
    (markerFree : MarkerFreeStructuredPivotSuffix
      (hg := hg) chain trajectory rebase presentation)
    (j : ℕ) :
    let index := rebase.start + j
    let state := chain.states index
    let step := state.incoming
    ∃ originalStem originalSegment : List (Label Action),
      step.outerStem = originalStem.map liftCriticalLabel ∧
        (state.source.continuationPath
          (g.withCriticalMarkers_wellFormed hg count)
          hground hinitial).segmentWord step.offset bound =
            originalSegment.map liftCriticalLabel := by
  let index := rebase.start + j
  let state := chain.states index
  let step := state.incoming
  have hendpoint :
      IsLiftedCriticalWord
        (path.word (chain.levels index)) :=
    isLiftedCriticalWord_of_noCriticalMarkerActions
      (markerFree.endpoint_noMarkerActions j)
  have happend :
      step.outerStem ++
          (state.source.continuationPath
            (g.withCriticalMarkers_wellFormed hg count)
            hground hinitial).segmentWord step.offset bound =
        path.word (chain.levels index) := by
    simpa [index, state, step] using step.outerStem_append_labels
  apply exists_originalWords_of_append_isLifted
  rw [happend]
  exact hendpoint

/-- The operational marker-free invariant supplies exactly the six fields
consumed by the marker-stable structured stair assembly. -/
public noncomputable def toMarkerStablePremises
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    {rebase : trajectory.MaximalExposureRebase}
    {filler : RegularTerm}
    {presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j))}
    (markerFree : MarkerFreeStructuredPivotSuffix
      (hg := hg) chain trajectory rebase presentation) :
    MarkerStableStructuredPivotPremises
      (hg := hg) chain trajectory rebase presentation := by
  let originalStem := fun j =>
    Classical.choose (markerFree.exists_originalStemAndSegment j)
  let originalSegment := fun j =>
    Classical.choose (Classical.choose_spec
      (markerFree.exists_originalStemAndSegment j))
  exact
    { pivotSchemaOriginal := markerFree.pivotSchemaOriginal
      activePrefixOriginal := markerFree.activePrefixOriginal
      originalStem := originalStem
      originalSegment := originalSegment
      stem_eq := fun j =>
        (Classical.choose_spec (Classical.choose_spec
          (markerFree.exists_originalStemAndSegment j))).1
      segment_eq := fun j =>
        (Classical.choose_spec (Classical.choose_spec
          (markerFree.exists_originalStemAndSegment j))).2 }

end MarkerFreeStructuredPivotSuffix

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
