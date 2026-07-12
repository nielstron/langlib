module

public import Langlib.Automata.DeterministicPushdown.Totalization.Saturation
public import Langlib.Automata.DeterministicPushdown.Totalization.StackSummary
public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Utilities.ClosurePredicates
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Pi

@[expose]
public section

/-!
# Deterministic context-free right quotients by regular languages

For a DPDA configuration `(q, gamma)` and a DFA state `d`, the set of stacks from
which some continuation accepted by the DFA leads the DPDA to a final state is
regular.  We obtain its stack DFA by P-automaton saturation.  The quotient DPDA
then simulates the original machine while storing, below every stack symbol, the
transition summary of all these stack DFAs.  Consequently the finite control can
decide at every input boundary whether an admissible accepting continuation exists.

The construction is uniform in every finite input alphabet; it does not use a
distinguished letter or a fixed finite witness alphabet.
-/

open PDA Language Set List

noncomputable section

namespace DCFRightQuotient

variable {Q T S sigma : Type}
variable [Fintype Q] [Fintype T] [Fintype S] [Fintype sigma]

/-! ## Saturation for regular continuations -/

/-- A saturation rule replaces one top stack symbol while changing control. -/
private def Rule (C A : Type) := C -> A -> C -> List A -> Prop

/-- A stack-reading relation is saturated when every rule replacement path can
be summarized by a single relation edge. -/
private def Saturated {C A : Type} (rules : Rule C A)
    (R : DPDA.PAutState C -> A -> DPDA.PAutState C -> Prop) : Prop :=
  forall {c c' : C} {Z : A} {beta : List A} {r : DPDA.PAutState C},
    rules c Z c' beta ->
    DPDA.RelPath R (DPDA.PAutState.control c') beta r ->
    R (DPDA.PAutState.control c) Z r

/-- Least saturated stack-reading relation containing `base`. -/
private def saturationRel {C A : Type} (rules : Rule C A)
    (base : DPDA.PAutState C -> A -> DPDA.PAutState C -> Prop) :
    DPDA.PAutState C -> A -> DPDA.PAutState C -> Prop :=
  fun p Z r => forall R,
    (forall {p Z r}, base p Z r -> R p Z r) ->
    Saturated rules R -> R p Z r

private theorem base_subset_saturationRel {C A : Type} (rules : Rule C A)
    {base : DPDA.PAutState C -> A -> DPDA.PAutState C -> Prop} :
    forall {p Z r}, base p Z r -> saturationRel rules base p Z r := by
  intro p Z r hbase R hsub _
  exact hsub hbase

private theorem saturationRel_saturated {C A : Type} (rules : Rule C A)
    (base : DPDA.PAutState C -> A -> DPDA.PAutState C -> Prop) :
    Saturated rules (saturationRel rules base) := by
  intro c c' Z beta r hrule hpath R hbase hsat
  exact hsat hrule (DPDA.RelPath.mono (fun h => h R hbase hsat) hpath)

/-- Rules for an arbitrary continuation: epsilon moves preserve the DFA state;
input moves advance it by the consumed letter. -/
private def suffixRules (M : DPDA Q T S) (D : DFA T sigma) : Rule (Q × sigma) S :=
  fun c Z c' beta =>
    (M.epsilon_transition c.1 Z = some (c'.1, beta) /\ c'.2 = c.2) \/
    exists a : T, M.transition c.1 a Z = some (c'.1, beta) /\
      c'.2 = D.step c.2 a

/-- Target edges: a source-final/DFA-final control enters the sink, after which
the uninspected stack suffix is ignored. -/
private def suffixTargetBase (M : DPDA Q T S) (D : DFA T sigma) :
    DPDA.PAutState (Q × sigma) -> S -> DPDA.PAutState (Q × sigma) -> Prop
  | .inl c, _, .inr () => c.1 ∈ M.final_states /\ c.2 ∈ D.accept
  | .inr (), _, .inr () => True
  | _, _, _ => False

private def suffixTargetAccept (M : DPDA Q T S) (D : DFA T sigma) :
    Set (DPDA.PAutState (Q × sigma))
  | .inl c => c.1 ∈ M.final_states /\ c.2 ∈ D.accept
  | .inr () => True

private def suffixSaturationRel (M : DPDA Q T S) (D : DFA T sigma) :=
  saturationRel (suffixRules M D) (suffixTargetBase M D)

/-- The stack DFA deciding whether `M`, from `(q, gamma)`, has an accepting
continuation whose word takes `D` from `d` to a final state. -/
private def suffixDFA (M : DPDA Q T S) (D : DFA T sigma) (q : Q) (d : sigma) :
    DFA S (Set (DPDA.PAutState (Q × sigma))) :=
  DPDA.relDFA (suffixSaturationRel M D)
    (DPDA.PAutState.control (q, d)) (suffixTargetAccept M D)

/-- Semantic meaning of a state in the continuation P-automaton. -/
private def SuffixTarget (M : DPDA Q T S) (D : DFA T sigma) :
    DPDA.PAutState (Q × sigma) -> List S -> Prop
  | .inl (q, d), gamma =>
      exists y qf gammaf,
        @PDA.Reaches Q T S _ _ _ M.toPDA
          ⟨q, y, gamma⟩ ⟨qf, [], gammaf⟩ /\
        D.evalFrom d y ∈ D.accept /\ qf ∈ M.final_states
  | .inr (), _ => True

private theorem suffixTarget_nil_iff (M : DPDA Q T S) (D : DFA T sigma)
    (r : DPDA.PAutState (Q × sigma)) :
    SuffixTarget M D r [] <-> r ∈ suffixTargetAccept M D := by
  cases r with
  | inl c =>
      rcases c with ⟨q, d⟩
      constructor
      · rintro ⟨y, qf, gammaf, hreach, hD, hqf⟩
        have hempty := PDA.reaches_on_empty_stack (pda := M.toPDA) hreach
        rcases hempty with ⟨rfl, rfl, rfl⟩
        simpa using And.intro hqf hD
      · rintro ⟨hq, hd⟩
        exact ⟨[], q, [], Relation.ReflTransGen.refl, by simpa, hq⟩
  | inr u =>
      cases u
      constructor <;> intro _ <;> trivial

private theorem suffixSinkPath (M : DPDA Q T S) (D : DFA T sigma) (gamma : List S) :
    DPDA.RelPath (suffixSaturationRel M D)
      (DPDA.PAutState.sink : DPDA.PAutState (Q × sigma)) gamma DPDA.PAutState.sink := by
  induction gamma with
  | nil => exact DPDA.RelPath.nil _
  | cons Z gamma ih =>
      exact DPDA.RelPath.cons
        (base_subset_saturationRel (suffixRules M D) (base := suffixTargetBase M D) (by
          simp [suffixTargetBase, DPDA.PAutState.sink])) ih

private theorem suffixRel_preservesTarget (M : DPDA Q T S) (D : DFA T sigma) :
    DPDA.RelationPreservesTarget (suffixSaturationRel M D) (SuffixTarget M D) := by
  intro p r Z hrel delta htarget
  let semanticRel : DPDA.PAutState (Q × sigma) -> S ->
      DPDA.PAutState (Q × sigma) -> Prop :=
    fun p Z r => forall delta, SuffixTarget M D r delta -> SuffixTarget M D p (Z :: delta)
  have hbase : forall {p Z r}, suffixTargetBase M D p Z r -> semanticRel p Z r := by
    intro p Z r h delta _
    cases p with
    | inl c =>
        cases r with
        | inl c' => simp [suffixTargetBase] at h
        | inr u =>
            cases u
            rcases c with ⟨q, d⟩
            exact ⟨[], q, Z :: delta, Relation.ReflTransGen.refl,
              by simpa using h.2, h.1⟩
    | inr u =>
        cases u
        cases r with
        | inl c => simp [suffixTargetBase] at h
        | inr u => cases u; trivial
  have hsat : Saturated (suffixRules M D) semanticRel := by
    intro c c' Z beta r hrule hpath delta htarget
    have hafter : SuffixTarget M D (DPDA.PAutState.control c') (beta ++ delta) :=
      DPDA.RelPath.preservesTarget (R := semanticRel) (Target := SuffixTarget M D)
        (by intro p r Z h delta ht; exact h delta ht) hpath htarget
    rcases c with ⟨q, d⟩
    rcases c' with ⟨q', d'⟩
    rcases hafter with ⟨y, qf, gammaf, hreach, hD, hqf⟩
    rcases hrule with hε | ⟨a, ha, hd'⟩
    · rcases hε with ⟨hε, rfl⟩
      refine ⟨y, qf, gammaf, Relation.ReflTransGen.head ?_ hreach, hD, hqf⟩
      cases y <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε]
    · change d' = D.step d a at hd'
      subst d'
      refine ⟨a :: y, qf, gammaf, Relation.ReflTransGen.head ?_ hreach, ?_, hqf⟩
      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, ha]
      · simpa [DFA.evalFrom] using hD
  exact hrel semanticRel hbase hsat delta htarget

private theorem suffixRel_path_sound (M : DPDA Q T S) (D : DFA T sigma)
    {p r : DPDA.PAutState (Q × sigma)} {gamma delta : List S}
    (hpath : DPDA.RelPath (suffixSaturationRel M D) p gamma r)
    (htarget : SuffixTarget M D r delta) :
    SuffixTarget M D p (gamma ++ delta) :=
  DPDA.RelPath.preservesTarget
    (R := suffixSaturationRel M D) (Target := SuffixTarget M D)
    (suffixRel_preservesTarget M D) hpath htarget

private theorem suffixDFA_sound (M : DPDA Q T S) (D : DFA T sigma)
    (q : Q) (d : sigma) (gamma : List S) :
    gamma ∈ (suffixDFA M D q d).accepts ->
      exists y qf gammaf,
        @PDA.Reaches Q T S _ _ _ M.toPDA
          ⟨q, y, gamma⟩ ⟨qf, [], gammaf⟩ /\
        D.evalFrom d y ∈ D.accept /\ qf ∈ M.final_states := by
  intro h
  obtain ⟨r, hr, hpath⟩ := (DPDA.relDFA_accepts_iff (R := suffixSaturationRel M D)).1 h
  have ht : SuffixTarget M D r [] := (suffixTarget_nil_iff M D r).2 hr
  simpa [SuffixTarget] using suffixRel_path_sound M D hpath ht

private theorem suffixPath_of_final (M : DPDA Q T S) (D : DFA T sigma)
    {q : Q} {d : sigma} {gamma : List S}
    (hq : q ∈ M.final_states) (hd : d ∈ D.accept) :
    exists r, r ∈ suffixTargetAccept M D /\
      DPDA.RelPath (suffixSaturationRel M D)
        (DPDA.PAutState.control (q, d)) gamma r := by
  cases gamma with
  | nil => exact ⟨DPDA.PAutState.control (q, d), ⟨hq, hd⟩, DPDA.RelPath.nil _⟩
  | cons Z gamma =>
      refine ⟨DPDA.PAutState.sink, trivial, DPDA.RelPath.cons ?_ (suffixSinkPath M D gamma)⟩
      exact base_subset_saturationRel (suffixRules M D) (base := suffixTargetBase M D) (by
        simpa [suffixTargetBase, DPDA.PAutState.control, DPDA.PAutState.sink] using And.intro hq hd)

private theorem mem_source_transition_iff (M : DPDA Q T S)
    (q : Q) (a : T) (Z : S) (p : Q) (beta : List S) :
    (p, beta) ∈ M.toPDA.transition_fun q a Z <->
      M.transition q a Z = some (p, beta) := by
  cases h : M.transition q a Z <;> simp [DPDA.toPDA, h]
  exact eq_comm

private theorem mem_source_epsilon_iff (M : DPDA Q T S)
    (q : Q) (Z : S) (p : Q) (beta : List S) :
    (p, beta) ∈ M.toPDA.transition_fun' q Z <->
      M.epsilon_transition q Z = some (p, beta) := by
  cases h : M.epsilon_transition q Z <;> simp [DPDA.toPDA, h]
  exact eq_comm

private theorem suffixPath_complete_aux (M : DPDA Q T S) (D : DFA T sigma)
    {c0 cf : PDA.conf M.toPDA} (hreach : PDA.Reaches c0 cf) :
    cf.input = [] -> cf.state ∈ M.final_states ->
    forall d, D.evalFrom d c0.input ∈ D.accept ->
      exists r, r ∈ suffixTargetAccept M D /\
        DPDA.RelPath (suffixSaturationRel M D)
          (DPDA.PAutState.control (c0.state, d)) c0.stack r := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hempty hfinal d hd
      rw [hempty] at hd
      exact suffixPath_of_final M D hfinal (by simpa using hd)
  | @head c0 c1 hstep hrest ih =>
      intro hempty hfinal d hd
      rcases c0 with ⟨q0, input0, stack0⟩
      cases stack0 with
      | nil =>
          exact False.elim ((PDA.reachesIn_one_on_empty_stack
            (pda := M.toPDA)) ((PDA.reaches₁_iff_reachesIn_one).mp hstep))
      | cons Z delta =>
          obtain ⟨a, rest, p, beta, hinput, hc1, htrans⟩ |
              ⟨p, beta, hc1, heps⟩ := PDA.reaches₁_push hstep
          · subst input0
            subst c1
            have htrans' : M.transition q0 a Z = some (p, beta) :=
              (mem_source_transition_iff M q0 a Z p beta).1 htrans
            obtain ⟨r, hr, hpath⟩ := ih hempty hfinal (D.step d a) (by
              simpa [DFA.evalFrom] using hd)
            obtain ⟨mid, hbeta, hdelta⟩ := DPDA.RelPath.of_append_left hpath
            change DPDA.RelPath (suffixSaturationRel M D)
              (DPDA.PAutState.control (p, D.step d a)) beta mid at hbeta
            have hrule : suffixRules M D (q0, d) Z (p, D.step d a) beta :=
              Or.inr ⟨a, htrans', rfl⟩
            have hedge : suffixSaturationRel M D
                (DPDA.PAutState.control (q0, d)) Z mid :=
              (saturationRel_saturated (suffixRules M D) (suffixTargetBase M D))
                hrule hbeta
            exact ⟨r, hr, DPDA.RelPath.cons hedge hdelta⟩
          · subst c1
            have heps' : M.epsilon_transition q0 Z = some (p, beta) :=
              (mem_source_epsilon_iff M q0 Z p beta).1 heps
            obtain ⟨r, hr, hpath⟩ := ih hempty hfinal d hd
            obtain ⟨mid, hbeta, hdelta⟩ := DPDA.RelPath.of_append_left hpath
            change DPDA.RelPath (suffixSaturationRel M D)
              (DPDA.PAutState.control (p, d)) beta mid at hbeta
            have hrule : suffixRules M D (q0, d) Z (p, d) beta :=
              Or.inl ⟨heps', rfl⟩
            have hedge : suffixSaturationRel M D
                (DPDA.PAutState.control (q0, d)) Z mid :=
              (saturationRel_saturated (suffixRules M D) (suffixTargetBase M D))
                hrule hbeta
            exact ⟨r, hr, DPDA.RelPath.cons hedge hdelta⟩

private theorem suffixPath_complete (M : DPDA Q T S) (D : DFA T sigma)
    {q qf : Q} {d : sigma} {y : List T} {gamma gammaf : List S}
    (hreach : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨q, y, gamma⟩ ⟨qf, [], gammaf⟩)
    (hd : D.evalFrom d y ∈ D.accept) (hqf : qf ∈ M.final_states) :
    exists r, r ∈ suffixTargetAccept M D /\
      DPDA.RelPath (suffixSaturationRel M D)
        (DPDA.PAutState.control (q, d)) gamma r :=
  suffixPath_complete_aux M D hreach rfl hqf d hd

private theorem suffixDFA_complete (M : DPDA Q T S) (D : DFA T sigma)
    (q : Q) (d : sigma) (gamma : List S) :
    (exists y qf gammaf,
      @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨q, y, gamma⟩ ⟨qf, [], gammaf⟩ /\
      D.evalFrom d y ∈ D.accept /\ qf ∈ M.final_states) ->
      gamma ∈ (suffixDFA M D q d).accepts := by
  rintro ⟨y, qf, gammaf, hreach, hD, hqf⟩
  obtain ⟨r, hr, hpath⟩ := suffixPath_complete M D hreach hD hqf
  exact (DPDA.relDFA_accepts_iff (R := suffixSaturationRel M D)).2 ⟨r, hr, hpath⟩

private theorem suffixDFA_correct (M : DPDA Q T S) (D : DFA T sigma)
    (q : Q) (d : sigma) (gamma : List S) :
    gamma ∈ (suffixDFA M D q d).accepts <->
      exists y qf gammaf,
        @PDA.Reaches Q T S _ _ _ M.toPDA
          ⟨q, y, gamma⟩ ⟨qf, [], gammaf⟩ /\
        D.evalFrom d y ∈ D.accept /\ qf ∈ M.final_states :=
  ⟨suffixDFA_sound M D q d gamma, suffixDFA_complete M D q d gamma⟩

/-! ## Stack-summary DPDA -/

private abbrev LookState (Q sigma : Type) := Set (DPDA.PAutState (Q × sigma))

/-- Simultaneous transition summaries for the continuation stack DFA at every
source control state. -/
private def Summary (Q sigma : Type) := Q -> LookState Q sigma -> LookState Q sigma

private noncomputable instance : Fintype (Summary Q sigma) := by
  classical
  unfold Summary LookState
  infer_instance

private def Summary.id : Summary Q sigma := fun _ x => x

private def Summary.above (M : DPDA Q T S) (D : DFA T sigma)
    (below : Summary Q sigma) (beta : List S) : Summary Q sigma :=
  fun q => below q ∘ (suffixDFA M D q D.start).stackSummary beta

private def Summary.Represents (M : DPDA Q T S) (D : DFA T sigma)
    (summary : Summary Q sigma) (gamma : List S) : Prop :=
  forall q, summary q = (suffixDFA M D q D.start).stackSummary gamma

private theorem Summary.represents_id (M : DPDA Q T S) (D : DFA T sigma) :
    Summary.Represents M D Summary.id [] := by
  intro q
  funext x
  rfl

private theorem Summary.Represents.above (M : DPDA Q T S) (D : DFA T sigma)
    {below : Summary Q sigma} {delta : List S}
    (h : Summary.Represents M D below delta) (beta : List S) :
    Summary.Represents M D (Summary.above M D below beta) (beta ++ delta) := by
  intro q
  funext x
  unfold Summary.above
  rw [h q]
  simp [DFA.stackSummary_append]

private abbrev AnnSymbol (Q S sigma : Type) := S × Summary Q sigma

private def annotate (M : DPDA Q T S) (D : DFA T sigma)
    (below : Summary Q sigma) : List S -> List (AnnSymbol Q S sigma)
  | [] => []
  | Z :: beta => (Z, Summary.above M D below beta) :: annotate M D below beta

private def eraseAnn : List (AnnSymbol Q S sigma) -> List S := List.map Prod.fst

@[simp] private theorem eraseAnn_annotate (M : DPDA Q T S) (D : DFA T sigma)
    (below : Summary Q sigma) (beta : List S) :
    eraseAnn (annotate M D below beta) = beta := by
  induction beta with
  | nil => rfl
  | cons Z beta ih =>
      change (annotate M D below (Z :: beta)).map Prod.fst = Z :: beta
      rw [annotate, List.map_cons]
      exact congrArg (List.cons Z) (by simpa only [eraseAnn] using ih)

private theorem eraseAnn_append (gamma delta : List (AnnSymbol Q S sigma)) :
    eraseAnn (gamma ++ delta) = eraseAnn gamma ++ eraseAnn delta := by
  simp [eraseAnn]

private def WellAnnotated (M : DPDA Q T S) (D : DFA T sigma) :
    List (AnnSymbol Q S sigma) -> Prop
  | [] => True
  | (_, below) :: rest =>
      Summary.Represents M D below (eraseAnn rest) /\ WellAnnotated M D rest

private theorem wellAnnotated_annotate_append (M : DPDA Q T S) (D : DFA T sigma)
    {below : Summary Q sigma} {rest : List (AnnSymbol Q S sigma)}
    (hbelow : Summary.Represents M D below (eraseAnn rest))
    (hrest : WellAnnotated M D rest) (beta : List S) :
    WellAnnotated M D (annotate M D below beta ++ rest) := by
  induction beta with
  | nil => exact hrest
  | cons Z beta ih =>
      rw [annotate]
      constructor
      · change Summary.Represents M D (Summary.above M D below beta)
          (eraseAnn (annotate M D below beta ++ rest))
        rw [eraseAnn_append, eraseAnn_annotate]
        exact hbelow.above M D beta
      · exact ih

private def fullSummary (M : DPDA Q T S) (D : DFA T sigma) :
    List (AnnSymbol Q S sigma) -> Summary Q sigma
  | [] => Summary.id
  | (Z, below) :: _ => Summary.above M D below [Z]

private theorem fullSummary_represents (M : DPDA Q T S) (D : DFA T sigma)
    {stack : List (AnnSymbol Q S sigma)} (h : WellAnnotated M D stack) :
    Summary.Represents M D (fullSummary M D stack) (eraseAnn stack) := by
  cases stack with
  | nil => exact Summary.represents_id M D
  | cons top rest =>
      rcases top with ⟨Z, below⟩
      exact h.1.above M D [Z]

private def acceptsContinuation (M : DPDA Q T S) (D : DFA T sigma)
    (q : Q) (summary : Summary Q sigma) : Prop :=
  summary q (suffixDFA M D q D.start).start ∈ (suffixDFA M D q D.start).accept

private def acceptBit (M : DPDA Q T S) (D : DFA T sigma)
    (q : Q) (summary : Summary Q sigma) : Bool :=
  by
    classical
    exact if acceptsContinuation M D q summary then true else false

private theorem acceptBit_eq_true_iff (M : DPDA Q T S) (D : DFA T sigma)
    (q : Q) (summary : Summary Q sigma) :
    acceptBit M D q summary = true <-> acceptsContinuation M D q summary := by
  classical
  simp [acceptBit]

private theorem acceptsContinuation_correct (M : DPDA Q T S) (D : DFA T sigma)
    {q : Q} {summary : Summary Q sigma} {gamma : List S}
    (h : Summary.Represents M D summary gamma) :
    acceptsContinuation M D q summary <->
      exists y qf gammaf,
        @PDA.Reaches Q T S _ _ _ M.toPDA
          ⟨q, y, gamma⟩ ⟨qf, [], gammaf⟩ /\
        y ∈ D.accepts /\ qf ∈ M.final_states := by
  unfold acceptsContinuation
  rw [h q]
  change gamma ∈ (suffixDFA M D q D.start).accepts <-> _
  rw [suffixDFA_correct M D q D.start gamma]
  simp [DFA.mem_accepts, DFA.eval]

/-- The quotient DPDA.  Its Boolean control component is the continuation query
for the current source state and annotated stack. -/
private def quotientDPDA (M : DPDA Q T S) (D : DFA T sigma) :
    DPDA (Q × Bool) T (AnnSymbol Q S sigma) where
  initial_state :=
    (M.initial_state,
      acceptBit M D M.initial_state (Summary.above M D Summary.id [M.start_symbol]))
  start_symbol := (M.start_symbol, Summary.id)
  final_states := {st | st.2 = true}
  transition st a top :=
    match M.transition st.1 a top.1 with
    | none => none
    | some (q', beta) =>
        some ((q', acceptBit M D q' (Summary.above M D top.2 beta)),
          annotate M D top.2 beta)
  epsilon_transition st top :=
    match M.epsilon_transition st.1 top.1 with
    | none => none
    | some (q', beta) =>
        some ((q', acceptBit M D q' (Summary.above M D top.2 beta)),
          annotate M D top.2 beta)
  no_mixed := by
    intro st top hε a
    have hsrc : M.epsilon_transition st.1 top.1 ≠ none := by
      intro hnone
      simp [hnone] at hε
    have := M.no_mixed st.1 top.1 hsrc a
    simp [this]

private def projectConf (M : DPDA Q T S) (D : DFA T sigma) :
    PDA.conf (quotientDPDA M D).toPDA -> PDA.conf M.toPDA
  | ⟨st, input, stack⟩ => ⟨st.1, input, eraseAnn stack⟩

private def GoodConf (M : DPDA Q T S) (D : DFA T sigma)
    (c : PDA.conf (quotientDPDA M D).toPDA) : Prop :=
  WellAnnotated M D c.stack /\
    c.state.2 = acceptBit M D c.state.1 (fullSummary M D c.stack)

private theorem initial_good (M : DPDA Q T S) (D : DFA T sigma) (input : List T) :
    GoodConf M D
      ⟨(quotientDPDA M D).initial_state, input,
        [(quotientDPDA M D).start_symbol]⟩ := by
  constructor
  · exact ⟨Summary.represents_id M D, trivial⟩
  · rfl

private theorem step_projects (M : DPDA Q T S) (D : DFA T sigma)
    {c c' : PDA.conf (quotientDPDA M D).toPDA}
    (hstep : PDA.Reaches₁ c c') :
    PDA.Reaches₁ (projectConf M D c) (projectConf M D c') := by
  rcases c with ⟨⟨q, b⟩, input, stack⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at hstep
  | cons top rest =>
      rcases top with ⟨Z, below⟩
      obtain ⟨a, input', st', betaAnn, hinput, hc', hmem⟩ |
          ⟨st', betaAnn, hc', hmem⟩ := PDA.reaches₁_push hstep
      · subst input
        subst c'
        cases ht : M.transition q a Z with
        | none => simp [quotientDPDA, DPDA.toPDA, ht] at hmem
        | some out =>
            rcases out with ⟨p, beta⟩
            have hout : (st', betaAnn) =
                ((p, acceptBit M D p (Summary.above M D below beta)),
                  annotate M D below beta) := by
              simpa only [quotientDPDA, DPDA.toPDA, ht, Set.mem_singleton_iff] using hmem
            rcases hout with ⟨rfl, rfl⟩
            simp [projectConf, eraseAnn, PDA.Reaches₁, PDA.step, DPDA.toPDA, ht]
            simpa only [eraseAnn] using eraseAnn_annotate M D below beta
      · subst c'
        cases hε : M.epsilon_transition q Z with
        | none => simp [quotientDPDA, DPDA.toPDA, hε] at hmem
        | some out =>
            rcases out with ⟨p, beta⟩
            have hout : (st', betaAnn) =
                ((p, acceptBit M D p (Summary.above M D below beta)),
                  annotate M D below beta) := by
              simpa only [quotientDPDA, DPDA.toPDA, hε, Set.mem_singleton_iff] using hmem
            rcases hout with ⟨rfl, rfl⟩
            cases input <;>
              simp [projectConf, eraseAnn, PDA.Reaches₁, PDA.step, DPDA.toPDA, hε]
            all_goals simpa only [eraseAnn] using eraseAnn_annotate M D below beta

private theorem reaches_projects (M : DPDA Q T S) (D : DFA T sigma)
    {c c' : PDA.conf (quotientDPDA M D).toPDA}
    (h : PDA.Reaches c c') :
    PDA.Reaches (projectConf M D c) (projectConf M D c') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih (step_projects M D hs)

private theorem replacement_good (M : DPDA Q T S) (D : DFA T sigma)
    {below : Summary Q sigma} {rest : List (AnnSymbol Q S sigma)}
    (hbelow : Summary.Represents M D below (eraseAnn rest))
    (hrest : WellAnnotated M D rest) (p : Q) (beta : List S) (input : List T) :
    GoodConf M D
      ⟨(p, acceptBit M D p (Summary.above M D below beta)), input,
        annotate M D below beta ++ rest⟩ := by
  have hwell := wellAnnotated_annotate_append M D hbelow hrest beta
  constructor
  · exact hwell
  · have hfull := fullSummary_represents M D hwell
    have hexpect := hbelow.above M D beta
    rw [eraseAnn_append, eraseAnn_annotate] at hfull
    have heq : fullSummary M D (annotate M D below beta ++ rest) =
        Summary.above M D below beta := by
      funext q x
      exact (congrFun (hfull q) x).trans (congrFun (hexpect q) x).symm
    rw [heq]

private theorem step_preserves_good (M : DPDA Q T S) (D : DFA T sigma)
    {c c' : PDA.conf (quotientDPDA M D).toPDA}
    (hc : GoodConf M D c) (hstep : PDA.Reaches₁ c c') : GoodConf M D c' := by
  rcases c with ⟨⟨q, b⟩, input, stack⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at hstep
  | cons top rest =>
      rcases top with ⟨Z, below⟩
      have hbelow := hc.1.1
      have hrest := hc.1.2
      obtain ⟨a, input', st', betaAnn, hinput, hc', hmem⟩ |
          ⟨st', betaAnn, hc', hmem⟩ := PDA.reaches₁_push hstep
      · subst input
        subst c'
        cases ht : M.transition q a Z with
        | none => simp [quotientDPDA, DPDA.toPDA, ht] at hmem
        | some out =>
            rcases out with ⟨p, beta⟩
            have hout : (st', betaAnn) =
                ((p, acceptBit M D p (Summary.above M D below beta)),
                  annotate M D below beta) := by
              simpa only [quotientDPDA, DPDA.toPDA, ht, Set.mem_singleton_iff] using hmem
            rcases hout with ⟨rfl, rfl⟩
            exact replacement_good M D hbelow hrest p beta input'
      · subst c'
        cases hε : M.epsilon_transition q Z with
        | none => simp [quotientDPDA, DPDA.toPDA, hε] at hmem
        | some out =>
            rcases out with ⟨p, beta⟩
            have hout : (st', betaAnn) =
                ((p, acceptBit M D p (Summary.above M D below beta)),
                  annotate M D below beta) := by
              simpa only [quotientDPDA, DPDA.toPDA, hε, Set.mem_singleton_iff] using hmem
            rcases hout with ⟨rfl, rfl⟩
            exact replacement_good M D hbelow hrest p beta input

private theorem reaches_preserves_good (M : DPDA Q T S) (D : DFA T sigma)
    {c c' : PDA.conf (quotientDPDA M D).toPDA}
    (hc : GoodConf M D c) (h : PDA.Reaches c c') : GoodConf M D c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact step_preserves_good M D ih hs

private theorem step_lifts (M : DPDA Q T S) (D : DFA T sigma)
    {c : PDA.conf (quotientDPDA M D).toPDA} (hc : GoodConf M D c)
    {d' : PDA.conf M.toPDA} (hstep : PDA.Reaches₁ (projectConf M D c) d') :
    exists c', PDA.Reaches₁ c c' /\ projectConf M D c' = d' /\ GoodConf M D c' := by
  rcases c with ⟨⟨q, b⟩, input, stack⟩
  cases stack with
  | nil => simp [projectConf, eraseAnn, PDA.Reaches₁, PDA.step] at hstep
  | cons top rest =>
      rcases top with ⟨Z, below⟩
      obtain ⟨a, input', p, beta, hinput, hd', hmem⟩ |
          ⟨p, beta, hd', hmem⟩ := PDA.reaches₁_push hstep
      · change input = a :: input' at hinput
        subst input
        subst d'
        have ht : M.transition q a Z = some (p, beta) :=
          (mem_source_transition_iff M q a Z p beta).1 hmem
        let c' : PDA.conf (quotientDPDA M D).toPDA :=
          ⟨(p, acceptBit M D p (Summary.above M D below beta)), input',
            annotate M D below beta ++ rest⟩
        have hs : PDA.Reaches₁
            (⟨(q, b), a :: input', (Z, below) :: rest⟩ :
              PDA.conf (quotientDPDA M D).toPDA) c' := by
          simp [c', PDA.Reaches₁, PDA.step, quotientDPDA, DPDA.toPDA, ht]
        refine ⟨c', hs, ?_, step_preserves_good M D hc hs⟩
        apply PDA.conf.ext <;> simp [c', projectConf, eraseAnn]
        simpa only [eraseAnn] using eraseAnn_annotate M D below beta
      · subst d'
        have hε : M.epsilon_transition q Z = some (p, beta) :=
          (mem_source_epsilon_iff M q Z p beta).1 hmem
        let c' : PDA.conf (quotientDPDA M D).toPDA :=
          ⟨(p, acceptBit M D p (Summary.above M D below beta)), input,
            annotate M D below beta ++ rest⟩
        have hs : PDA.Reaches₁
            (⟨(q, b), input, (Z, below) :: rest⟩ :
              PDA.conf (quotientDPDA M D).toPDA) c' := by
          cases input <;> simp [c', PDA.Reaches₁, PDA.step, quotientDPDA, DPDA.toPDA, hε]
        refine ⟨c', hs, ?_, step_preserves_good M D hc hs⟩
        apply PDA.conf.ext <;> simp [c', projectConf, eraseAnn]
        simpa only [eraseAnn] using eraseAnn_annotate M D below beta

private theorem reaches_lifts (M : DPDA Q T S) (D : DFA T sigma)
    {c : PDA.conf (quotientDPDA M D).toPDA} (hc : GoodConf M D c)
    {d' : PDA.conf M.toPDA} (h : PDA.Reaches (projectConf M D c) d') :
    exists c', PDA.Reaches c c' /\ projectConf M D c' = d' /\ GoodConf M D c' := by
  induction h with
  | refl => exact ⟨c, Relation.ReflTransGen.refl, rfl, hc⟩
  | tail _ hs ih =>
      obtain ⟨cmid, hmid, rfl, hgood⟩ := ih
      obtain ⟨c', hstep, hproj, hgood'⟩ := step_lifts M D hgood hs
      exact ⟨c', Relation.ReflTransGen.tail hmid hstep, hproj, hgood'⟩

/-! A run consuming `w ++ y` has a boundary configuration after exactly `w` has
been consumed.  Epsilon moves may occur on either side of that boundary. -/
private theorem reaches_split_suffix_aux (M : DPDA Q T S)
    {c0 cf : PDA.conf M.toPDA} (h : PDA.Reaches c0 cf) :
    forall (w y : List T), c0.input = w ++ y -> cf.input = [] ->
      exists cm : PDA.conf M.toPDA,
        cm.input = y /\ PDA.Reaches c0 cm /\ PDA.Reaches cm cf := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro w y hinput hempty
      have hnil : w = [] /\ y = [] := List.append_eq_nil_iff.mp (hinput.symm.trans hempty)
      rcases hnil with ⟨rfl, rfl⟩
      exact ⟨cf, hempty, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @head c0 c1 hs hrest ih =>
      intro w y hinput hempty
      cases w with
      | nil =>
          exact ⟨c0, by simpa using hinput, Relation.ReflTransGen.refl,
            Relation.ReflTransGen.head hs hrest⟩
      | cons a w =>
          rcases c0 with ⟨q0, input0, stack0⟩
          change input0 = a :: (w ++ y) at hinput
          subst input0
          cases stack0 with
          | nil =>
              exact False.elim ((PDA.reachesIn_one_on_empty_stack
                (pda := M.toPDA)) ((PDA.reaches₁_iff_reachesIn_one).mp hs))
          | cons Z delta =>
              obtain ⟨a', rest, p, beta, hin, hc1, htrans⟩ |
                  ⟨p, beta, hc1, heps⟩ := PDA.reaches₁_push hs
              · have ha : a' = a := (List.cons.inj hin).1.symm
                have hrestEq : rest = w ++ y := (List.cons.inj hin).2.symm
                subst a'
                subst rest
                subst c1
                obtain ⟨cm, hcminput, hpre, hpost⟩ := ih w y rfl hempty
                exact ⟨cm, hcminput, Relation.ReflTransGen.head hs hpre, hpost⟩
              · subst c1
                obtain ⟨cm, hcminput, hpre, hpost⟩ := ih (a :: w) y rfl hempty
                exact ⟨cm, hcminput, Relation.ReflTransGen.head hs hpre, hpost⟩

private theorem reaches_split_suffix (M : DPDA Q T S)
    {q qf : Q} {w y : List T} {gamma gammaf : List S}
    (h : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨q, w ++ y, gamma⟩ ⟨qf, [], gammaf⟩) :
    exists qm gammam,
      @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨q, w ++ y, gamma⟩ ⟨qm, y, gammam⟩ /\
      @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨qm, y, gammam⟩ ⟨qf, [], gammaf⟩ := by
  obtain ⟨cm, hcminput, hpre, hpost⟩ := reaches_split_suffix_aux M h w y rfl rfl
  rcases cm with ⟨qm, inputm, gammam⟩
  change inputm = y at hcminput
  subst inputm
  exact ⟨qm, gammam, hpre, hpost⟩

private theorem quotientDPDA_correct (M : DPDA Q T S) (D : DFA T sigma) :
    (quotientDPDA M D).acceptsByFinalState = M.acceptsByFinalState / D.accepts := by
  ext w
  constructor
  · rintro ⟨st, hfinal, stack, hreach⟩
    have hgood0 := initial_good M D w
    have hgood := reaches_preserves_good M D hgood0 hreach
    have hsource := reaches_projects M D hreach
    rcases st with ⟨q, b⟩
    have hb : b = true := hfinal
    have hcont : acceptsContinuation M D q (fullSummary M D stack) := by
      apply (acceptBit_eq_true_iff M D q _).1
      exact hgood.2.symm.trans hb
    obtain ⟨y, qf, gammaf, hsuffix, hy, hqf⟩ :=
      (acceptsContinuation_correct M D (fullSummary_represents M D hgood.1)).1 hcont
    refine ⟨y, hy, qf, hqf, gammaf, ?_⟩
    have hprefix : @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨M.initial_state, w ++ y, [M.start_symbol]⟩
        ⟨q, y, eraseAnn stack⟩ := by
      exact (PDA.unconsumed_input y).1 (by simpa [projectConf, quotientDPDA] using hsource)
    exact Relation.ReflTransGen.trans hprefix hsuffix
  · rintro ⟨y, hy, qf, hqf, gammaf, haccept⟩
    obtain ⟨qm, gammam, hpreApp, hsuffix⟩ := reaches_split_suffix M haccept
    have hpre : @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨qm, [], gammam⟩ := by
      exact (PDA.unconsumed_input y).2 hpreApp
    let c0 : PDA.conf (quotientDPDA M D).toPDA :=
      ⟨(quotientDPDA M D).initial_state, w, [(quotientDPDA M D).start_symbol]⟩
    have hgood0 : GoodConf M D c0 := by simpa [c0] using initial_good M D w
    have hproject0 : projectConf M D c0 =
        (⟨M.initial_state, w, [M.start_symbol]⟩ : PDA.conf M.toPDA) := by
      simp [c0, projectConf, quotientDPDA, eraseAnn]
    rw [← hproject0] at hpre
    obtain ⟨cmid, hlift, hproj, hgood⟩ := reaches_lifts M D hgood0 hpre
    rcases cmid with ⟨⟨qmid, bmid⟩, inputmid, stackmid⟩
    have hqmid : qmid = qm := congrArg PDA.conf.state hproj
    have hinputmid : inputmid = [] := congrArg PDA.conf.input hproj
    have herase : eraseAnn stackmid = gammam := congrArg PDA.conf.stack hproj
    subst qmid
    subst inputmid
    change WellAnnotated M D stackmid /\
      bmid = acceptBit M D qm (fullSummary M D stackmid) at hgood
    have hsummary := fullSummary_represents M D hgood.1
    have hcont : acceptsContinuation M D qm (fullSummary M D stackmid) :=
      (acceptsContinuation_correct M D hsummary).2
        ⟨y, qf, gammaf, by simpa [herase] using hsuffix, hy, hqf⟩
    have hb : bmid = true := by
      exact hgood.2.trans ((acceptBit_eq_true_iff M D qm _).2 hcont)
    refine ⟨(qm, bmid), ?_, stackmid, by simpa [c0] using hlift⟩
    change bmid = true
    exact hb

end DCFRightQuotient

/-! ## Class-level closure theorem -/

variable {T : Type} [Fintype T]

/-- A deterministic context-free language is closed under right quotient by a
regular language, uniformly over every finite alphabet. -/
public theorem is_DCF_rightQuotient_regular {L R : Language T}
    (hL : is_DCF L) (hR : R.IsRegular) : is_DCF (L / R) := by
  rcases hL with ⟨Q, S, hQ, hS, M, rfl⟩
  letI : Fintype Q := hQ
  letI : Fintype S := hS
  rcases hR with ⟨sigma, hsigma, D, hD⟩
  letI : Fintype sigma := hsigma
  refine ⟨Q × Bool, DCFRightQuotient.AnnSymbol Q S sigma,
    inferInstance, inferInstance, DCFRightQuotient.quotientDPDA M D, ?_⟩
  rw [DCFRightQuotient.quotientDPDA_correct M D, hD]

/-- The class of deterministic context-free languages is closed under right
quotient with regular languages, for an arbitrary finite alphabet. -/
public theorem DCF_closedUnderRightQuotientWithRegular :
    ClosedUnderRightQuotientWithRegular (α := T) is_DCF :=
  fun _L hL _R hR => is_DCF_rightQuotient_regular hL hR

end
