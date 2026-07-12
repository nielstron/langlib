module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowWork.Trace

@[expose]
public section

/-!
# Replacement and prefix soundness for Aho's row checker

Inversion of nonproductive and productive prefixes, one-symbol replacement, and two-symbol
replacement.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Nonproductive replacement -/

private theorem replaceOneFalse_prefix_iff
    (oldFocus newFocus : WorkSym g) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    replaceOneEdge false oldFocus newFocus .prefix next hist old new ↔
      (next = .prefix ∧ SameInactiveSome old new) ∨
      (next = .stage1 ∧ Boundary old new) := by
  cases next <;> simp [replaceOneEdge, prefixEdge]

private theorem replaceOne_stage1_iff
    (productive : Bool) (oldFocus newFocus : WorkSym g)
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    replaceOneEdge productive oldFocus newFocus .stage1 next hist old new ↔
      next = .suffixSame ∧ old = active oldFocus ∧ new = active newFocus := by
  cases next <;> simp [replaceOneEdge, prefixEdge]

private theorem replaceOne_suffixSame_iff
    (productive : Bool) (oldFocus newFocus : WorkSym g)
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    replaceOneEdge productive oldFocus newFocus .suffixSame next hist old new ↔
      next = .suffixSame ∧ sameSuffix old new := by
  cases next <;> simp [replaceOneEdge, prefixEdge]

/-- Generic inversion for a nonproductive one-symbol replacement. -/
private theorem WorkTrace.decodeReplaceOneFalse
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus newFocus : WorkSym g)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧
          replaceOneEdge false oldFocus newFocus phase next hist old new)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .prefix)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (alpha beta : List (WorkSym g)) (k : ℕ),
      CertEnabled g cert ∧
      oldProjection rows =
        (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
          beta.map inactive ++ List.replicate k none ∧
      newProjection rows =
        (alpha.map inactive ++ [inactive .dollar, active newFocus]) ++
          beta.map inactive ++ List.replicate k none := by
  induction h with
  | nil =>
      have : False := by simp [workScanDone, hphase] at hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have hwork := (hshape state.phase next state.history old new).mp hedge.2.2.2.2
      rcases hwork with ⟨henabled, hedgeShape⟩
      have hprefix := (replaceOneFalse_prefix_iff oldFocus newFocus next
        state.history old new).mp (by simpa [hphase] using hedgeShape)
      rcases hprefix with hcopy | hboundary
      · rcases hcopy with ⟨rfl, z, hold, hnew⟩
        subst old
        subst new
        rcases ih rfl hdone with ⟨alpha, beta, k, _henabledTail, holdRows, hnewRows⟩
        refine ⟨z :: alpha, beta, k, henabled, ?_, ?_⟩
        · simpa [oldProjection, inactive, List.append_assoc] using
            congrArg (fun xs => inactive z :: xs) holdRows
        · simpa [newProjection, inactive, List.append_assoc] using
            congrArg (fun xs => inactive z :: xs) hnewRows
      · rcases hboundary with ⟨rfl, hold, hnew⟩
        subst old
        subst new
        cases htail with
        | nil => simp [workScanDone, advanceWorkState] at hdone
        | @cons _stage old new next rows result hedgeFocus htailSuffix =>
            have hfocusWork :=
              (hshape (advanceWorkState state (inactive WorkSym.dollar)
                (inactive WorkSym.dollar) .stage1).phase next
                (advanceWorkState state (inactive WorkSym.dollar)
                  (inactive WorkSym.dollar) .stage1).history old new).mp
                hedgeFocus.2.2.2.2
            have hfocus := (replaceOne_stage1_iff false oldFocus newFocus next
              (advanceWorkState state (inactive WorkSym.dollar)
                (inactive WorkSym.dollar) .stage1).history old new).mp (by
                simpa [advanceWorkState] using hfocusWork.2)
            rcases hfocus with ⟨rfl, rfl, rfl⟩
            have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
                (old new : Option (WorkSlot g)),
                WorkEdge g cert .suffixSame next hist old new →
                  next = .suffixSame ∧ sameSuffix old new := by
              intro next hist old new hedge'
              have h' := (hshape .suffixSame next hist old new).mp hedge'
              exact (replaceOne_suffixSame_iff false oldFocus newFocus next hist old new).mp h'.2
            rcases htailSuffix.decodeSuffixSame rfl hsuffix hdone with
              ⟨beta, k, holdRows, hnewRows⟩
            refine ⟨[], beta, k, henabled, ?_, ?_⟩
            · simpa [oldProjection, inactive, active, List.append_assoc] using
                congrArg (fun xs => inactive WorkSym.dollar :: active oldFocus :: xs) holdRows
            · simpa [newProjection, inactive, active, List.append_assoc] using
                congrArg (fun xs => inactive WorkSym.dollar :: active newFocus :: xs) hnewRows

private theorem WorkTraceAccepts.decodeReplaceOneFalse
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus newFocus : WorkSym g)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧
          replaceOneEdge false oldFocus newFocus phase next hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (alpha beta : List (WorkSym g)) (k : ℕ),
      CertEnabled g cert ∧
      old = (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
          beta.map inactive ++ List.replicate k none ∧
      new = (alpha.map inactive ++ [inactive .dollar, active newFocus]) ++
          beta.map inactive ++ List.replicate k none := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.decodeReplaceOneFalse oldFocus newFocus hshape rfl hdone with
    ⟨alpha, beta, k, henabled, holdRows, hnewRows⟩
  refine ⟨alpha, beta, k, henabled, ?_, ?_⟩
  · exact hold.symm.trans (by simpa [oldProjection] using holdRows)
  · exact hnew.symm.trans (by simpa [newProjection] using hnewRows)

/-- Soundness of the logical checker for the skipped-push replacement. -/
public theorem workTraceAccepts_plainPushSkip_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A B : g.nt} {f : g.flag}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.plainPushSkip A B f) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.plainPushSkip A B f) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.plainPushSkip A B f) phase next hist x y ↔
        CertEnabled g (.plainPushSkip A B f) ∧
          replaceOneEdge false (.plain A) (.plain B) phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeReplaceOneFalse (.plain A) (.plain B) hshape with
    ⟨alpha, beta, k, hpush, hold, hnew⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .plain A, beta⟩
  let newCursor : WorkCursor g := ⟨alpha ++ [.dollar], .plain B, beta⟩
  refine ⟨oldCursor, newCursor, k, k, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hpush, alpha, beta, rfl, rfl⟩

/-! ## Productive prefix inversion -/

/-- The scan history agrees with the last copied symbol of a prefix, when one exists. -/
public def CopiedHistory (alpha : List (WorkSym g)) (hist : WorkHistory g) : Prop :=
  match alpha.reverse with
  | [] => hist.old1 = none ∧ hist.new1 = none
  | z :: _ => hist.old1 = some (inactive z) ∧ hist.new1 = some (inactive z)

/-- Invariant carried while a productive prefix is copied and selectively marked. -/
public def ProductivePrefixInv (alpha : List (WorkSym g))
    (state : WorkScanState g) : Prop :=
  state.phase = .prefix ∧ state.oldEnded = false ∧ state.newEnded = false ∧
    CopiedHistory alpha state.history

/-- The initial work scan satisfies the productive-prefix invariant for the empty prefix. -/
public theorem productivePrefixInv_initial (g : IndexedGrammar T) :
    ProductivePrefixInv ([] : List (WorkSym g)) (initialWorkScan g) := by
  simp [ProductivePrefixInv, CopiedHistory, initialWorkScan]

private theorem ProductivePrefixInv.copy
    {g : IndexedGrammar T} {alpha : List (WorkSym g)} {state : WorkScanState g}
    (h : ProductivePrefixInv alpha state) (z : WorkSym g) :
    ProductivePrefixInv (alpha ++ [z])
      (advanceWorkState state (inactive z) (inactive z) .prefix) := by
  rcases h with ⟨hphase, holdEnd, hnewEnd, _hhist⟩
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [advanceWorkState, holdEnd, inactive]
  · simp [advanceWorkState, hnewEnd, inactive]
  · simp [CopiedHistory, advanceWorkState, updateHistory, List.reverse_append]

private theorem ProductivePrefixInv.mark_eq_self_of_boundary
    {g : IndexedGrammar T} {alpha : List (WorkSym g)} {state : WorkScanState g}
    (h : ProductivePrefixInv alpha state)
    (hboundary : ProductiveBoundaryOK state.history) :
    markProductivePrefix alpha = alpha := by
  rcases h with ⟨_hphase, _holdEnd, _hnewEnd, hhist⟩
  cases hrev : alpha.reverse with
  | nil =>
      simp [markProductivePrefix, hrev]
  | cons z zs =>
      have halpha : alpha = zs.reverse ++ [z] := by
        rw [← List.reverse_reverse alpha, hrev]
        simp
      subst alpha
      simp only [CopiedHistory, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.reverse_reverse] at hhist
      rcases hhist with ⟨hold, hnew⟩
      cases z with
      | index R d =>
          have heq : inactive (WorkSym.index R d) =
              inactive (WorkSym.index R d.markUsed) := by
            simpa [ProductiveBoundaryOK, hold, hnew] using hboundary
          have hsym : WorkSym.index R d = WorkSym.index R d.markUsed := by
            have hslot : (⟨false, WorkSym.index R d⟩ : WorkSlot g) =
                ⟨false, WorkSym.index R d.markUsed⟩ := by
              exact Option.some.inj (by simpa [inactive] using heq)
            exact congrArg WorkSlot.symbol hslot
          rw [markProductivePrefix_append_index]
          simp [hsym]
      | terminal a =>
          exact markProductivePrefix_append_nonindex _ _ (by simp)
      | plain A =>
          exact markProductivePrefix_append_nonindex _ _ (by simp)
      | live A =>
          exact markProductivePrefix_append_nonindex _ _ (by simp)
      | dollar =>
          exact markProductivePrefix_append_nonindex _ _ (by simp)
      | close =>
          exact markProductivePrefix_append_nonindex _ _ (by simp)
      | hash =>
          exact markProductivePrefix_append_nonindex _ _ (by simp)

private theorem prefixEdge_true_prefix_iff
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    prefixEdge true .prefix next hist old new ↔
      (next = .prefix ∧ SameInactiveSome old new) ∨
      (next = .marked ∧ ProductiveMarked old new) ∨
      (next = .stage1 ∧ Boundary old new ∧ ProductiveBoundaryOK hist) := by
  cases next <;> simp [prefixEdge]

private theorem prefixEdge_true_marked_iff
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    prefixEdge true .marked next hist old new ↔
      next = .stage1 ∧ Boundary old new := by
  cases next <;> simp [prefixEdge]

/-- Split a productive scan immediately after its `$` boundary, retaining the exact
`markProductivePrefix` relation on the scanned prefix. -/
public theorem WorkTrace.splitProductivePrefix
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (hproductive : cert.productive = true)
    {alpha : List (WorkSym g)} {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hinv : ProductivePrefixInv alpha state)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (delta newDelta : List (WorkSym g))
      (rest : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
      (stage : WorkScanState g),
      CertEnabled g cert ∧
      markProductivePrefix (alpha ++ delta) = alpha ++ newDelta ∧
      oldProjection rows = delta.map inactive ++ [inactive .dollar] ++
        oldProjection rest ∧
      newProjection rows = newDelta.map inactive ++ [inactive .dollar] ++
        newProjection rest ∧
      stage.phase = .stage1 ∧ WorkTrace g cert stage rest result := by
  induction h generalizing alpha with
  | nil =>
      have : False := by
        simp [workScanDone, hinv.1] at hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have hprefixWork := (workEdge_prefix_iff g cert state.phase next state.history
        old new (Or.inl hinv.1)).mp hedge.2.2.2.2
      have hprefix : prefixEdge true .prefix next state.history old new := by
        simpa [hinv.1, hproductive] using hprefixWork.2
      rcases (prefixEdge_true_prefix_iff next state.history old new).mp hprefix with
        hcopy | hmarked | hboundary
      · rcases hcopy with ⟨rfl, z, hold, hnew⟩
        subst old
        subst new
        rcases ih (hinv.copy z) hdone with
          ⟨delta, newDelta, rest, stage, _henabledTail, hmark,
            holdRows, hnewRows, hstage, hrest⟩
        refine ⟨z :: delta, z :: newDelta, rest, stage, hprefixWork.1, ?_, ?_, ?_,
          hstage, hrest⟩
        · simpa [List.append_assoc] using hmark
        · simpa [oldProjection, inactive, List.append_assoc] using
            congrArg (fun xs => inactive z :: xs) holdRows
        · simpa [newProjection, inactive, List.append_assoc] using
            congrArg (fun xs => inactive z :: xs) hnewRows
      · rcases hmarked with ⟨rfl, R, d, hold, hnew⟩
        subst old
        subst new
        cases htail with
        | nil => simp [workScanDone, advanceWorkState] at hdone
        | @cons _stage old new next rows result hedgeBoundary hrest =>
            have hboundaryWork := (workEdge_prefix_iff g cert .marked next
              (advanceWorkState state (inactive (WorkSym.index R d))
                (inactive (WorkSym.index R d.markUsed)) .marked).history old new
              (Or.inr rfl)).mp hedgeBoundary.2.2.2.2
            have hboundary' := (prefixEdge_true_marked_iff next
              (advanceWorkState state (inactive (WorkSym.index R d))
                (inactive (WorkSym.index R d.markUsed)) .marked).history old new).mp (by
                  simpa [hproductive] using hboundaryWork.2)
            rcases hboundary' with ⟨rfl, hold, hnew⟩
            subst old
            subst new
            refine ⟨[WorkSym.index R d], [WorkSym.index R d.markUsed], rows,
              advanceWorkState
                (advanceWorkState state (inactive (WorkSym.index R d))
                  (inactive (WorkSym.index R d.markUsed)) .marked)
                (inactive WorkSym.dollar) (inactive WorkSym.dollar) .stage1,
              hprefixWork.1, ?_, ?_, ?_, rfl, hrest⟩
            · simp [markProductivePrefix_append_index]
            · simp [oldProjection, inactive]
            · simp [newProjection, inactive]
      · rcases hboundary with ⟨rfl, hbound, hboundaryOK⟩
        rcases hbound with ⟨hold, hnew⟩
        subst old
        subst new
        refine ⟨[], [], rows,
          advanceWorkState state (inactive WorkSym.dollar)
            (inactive WorkSym.dollar) .stage1,
          hprefixWork.1, ?_, ?_, ?_, rfl, htail⟩
        · simpa using hinv.mark_eq_self_of_boundary hboundaryOK
        · simp [oldProjection, inactive]
        · simp [newProjection, inactive]

private theorem WorkTraceAccepts.decodeReplaceOneProductive
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus newFocus : WorkSym g)
    (hproductive : cert.productive = true)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧
          replaceOneEdge true oldFocus newFocus phase next hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (alpha beta : List (WorkSym g)) (k : ℕ),
      CertEnabled g cert ∧
      old = (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
          beta.map inactive ++ List.replicate k none ∧
      new = ((markProductivePrefix alpha).map inactive ++
          [inactive .dollar, active newFocus]) ++
          beta.map inactive ++ List.replicate k none := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitProductivePrefix hproductive (productivePrefixInv_initial g) hdone with
    ⟨alpha, newAlpha, rest, stage, henabled, hmark,
      holdPrefix, hnewPrefix, hstage, hrest⟩
  cases hrest with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage oldFocusSlot newFocusSlot next suffixRows result hedgeFocus htail =>
      have hfocusWork :=
        (hshape stage.phase next stage.history oldFocusSlot newFocusSlot).mp
          hedgeFocus.2.2.2.2
      have hfocus := (replaceOne_stage1_iff true oldFocus newFocus next
        stage.history oldFocusSlot newFocusSlot).mp (by simpa [hstage] using hfocusWork.2)
      rcases hfocus with ⟨rfl, rfl, rfl⟩
      have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
          (x y : Option (WorkSlot g)),
          WorkEdge g cert .suffixSame next hist x y →
            next = .suffixSame ∧ sameSuffix x y := by
        intro next hist x y hedge'
        have h' := (hshape .suffixSame next hist x y).mp hedge'
        exact (replaceOne_suffixSame_iff true oldFocus newFocus next hist x y).mp h'.2
      rcases htail.decodeSuffixSame rfl hsuffix hdone with
        ⟨beta, k, holdSuffix, hnewSuffix⟩
      have holdSuffix' : suffixRows.map (fun r => r.1) =
          beta.map inactive ++ List.replicate k none := by
        simpa [oldProjection] using holdSuffix
      have hnewSuffix' : suffixRows.map (fun r => r.2.1) =
          beta.map inactive ++ List.replicate k none := by
        simpa [newProjection] using hnewSuffix
      have hmark' : markProductivePrefix alpha = newAlpha := by
        simpa using hmark
      refine ⟨alpha, beta, k, henabled, ?_, ?_⟩
      · rw [← hold]
        calc
          oldProjection rows =
              alpha.map inactive ++ [inactive WorkSym.dollar] ++
                oldProjection ((active oldFocus, active newFocus, .suffixSame) :: suffixRows) :=
            holdPrefix
          _ = (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
                beta.map inactive ++ List.replicate k none := by
            simp only [oldProjection, List.map_cons]
            rw [holdSuffix']
            simp [List.append_assoc]
      · rw [← hnew]
        calc
          newProjection rows =
              newAlpha.map inactive ++ [inactive WorkSym.dollar] ++
                newProjection ((active oldFocus, active newFocus, .suffixSame) :: suffixRows) :=
            hnewPrefix
          _ = ((markProductivePrefix alpha).map inactive ++
                [inactive .dollar, active newFocus]) ++
                beta.map inactive ++ List.replicate k none := by
            simp only [newProjection, List.map_cons]
            rw [hnewSuffix', hmark']
            simp [List.append_assoc]

/-- Soundness of the logical checker for a productive terminal replacement. -/
public theorem workTraceAccepts_plainTerminal_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A : g.nt} {a : T}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.plainTerminal A a) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.plainTerminal A a) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.plainTerminal A a) phase next hist x y ↔
        CertEnabled g (.plainTerminal A a) ∧
          replaceOneEdge true (.plain A) (.terminal a) phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeReplaceOneProductive (.plain A) (.terminal a) rfl hshape with
    ⟨alpha, beta, k, hterminal, hold, hnew⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .plain A, beta⟩
  let newCursor : WorkCursor g :=
    ⟨markProductivePrefix alpha ++ [.dollar], .terminal a, beta⟩
  refine ⟨oldCursor, newCursor, k, k, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hterminal, alpha, beta, rfl, rfl⟩

/-! ## Shared nonproductive-prefix split -/

private theorem prefixEdge_false_prefix_iff
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    prefixEdge false .prefix next hist old new ↔
      (next = .prefix ∧ SameInactiveSome old new) ∨
      (next = .stage1 ∧ Boundary old new) := by
  cases next <;> simp [prefixEdge]

/-- Split a nonproductive scan at its `$` boundary, preserving the copied prefix exactly. -/
public theorem WorkTrace.splitNonproductivePrefix
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (hproductive : cert.productive = false)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .prefix)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (alpha : List (WorkSym g))
      (rest : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
      (stage : WorkScanState g),
      CertEnabled g cert ∧
      oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
        oldProjection rest ∧
      newProjection rows = alpha.map inactive ++ [inactive .dollar] ++
        newProjection rest ∧
      stage.phase = .stage1 ∧ WorkTrace g cert stage rest result := by
  induction h with
  | nil =>
      have : False := by simp [workScanDone, hphase] at hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have hprefixWork := (workEdge_prefix_iff g cert state.phase next state.history
        old new (Or.inl hphase)).mp hedge.2.2.2.2
      have hprefix : prefixEdge false .prefix next state.history old new := by
        simpa [hphase, hproductive] using hprefixWork.2
      rcases (prefixEdge_false_prefix_iff next state.history old new).mp hprefix with
        hcopy | hboundary
      · rcases hcopy with ⟨rfl, z, hold, hnew⟩
        subst old
        subst new
        rcases ih rfl hdone with
          ⟨alpha, rest, stage, _henabledTail, holdRows, hnewRows, hstage, hrest⟩
        refine ⟨z :: alpha, rest, stage, hprefixWork.1, ?_, ?_, hstage, hrest⟩
        · simpa [oldProjection, inactive, List.append_assoc] using
            congrArg (fun xs => inactive z :: xs) holdRows
        · simpa [newProjection, inactive, List.append_assoc] using
            congrArg (fun xs => inactive z :: xs) hnewRows
      · rcases hboundary with ⟨rfl, hold, hnew⟩
        subst old
        subst new
        exact ⟨[], rows,
          advanceWorkState state (inactive WorkSym.dollar)
            (inactive WorkSym.dollar) .stage1,
          hprefixWork.1, by simp [oldProjection, inactive],
          by simp [newProjection, inactive], rfl, htail⟩

/-! ## Two-symbol replacement -/

private theorem replaceTwo_stage1_iff
    (oldFocus newFocus oldNext newNext : WorkSym g)
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    replaceTwoEdge oldFocus newFocus oldNext newNext .stage1 next hist old new ↔
      next = .stage2 ∧ old = active oldFocus ∧ new = active newFocus := by
  cases next <;> simp [replaceTwoEdge, prefixEdge]

private theorem replaceTwo_stage2_iff
    (oldFocus newFocus oldNext newNext : WorkSym g)
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    replaceTwoEdge oldFocus newFocus oldNext newNext .stage2 next hist old new ↔
      next = .suffixSame ∧ old = inactive oldNext ∧ new = inactive newNext := by
  cases next <;> simp [replaceTwoEdge, prefixEdge]

private theorem replaceTwo_suffixSame_iff
    (oldFocus newFocus oldNext newNext : WorkSym g)
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    replaceTwoEdge oldFocus newFocus oldNext newNext .suffixSame next hist old new ↔
      next = .suffixSame ∧ sameSuffix old new := by
  cases next <;> simp [replaceTwoEdge, prefixEdge]

private theorem WorkTraceAccepts.decodeReplaceTwo
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus newFocus oldNext newNext : WorkSym g)
    (hproductive : cert.productive = false)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧
          replaceTwoEdge oldFocus newFocus oldNext newNext phase next hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (alpha beta : List (WorkSym g)) (k : ℕ),
      CertEnabled g cert ∧
      old = (alpha.map inactive ++ [inactive .dollar, active oldFocus,
          inactive oldNext]) ++ beta.map inactive ++ List.replicate k none ∧
      new = (alpha.map inactive ++ [inactive .dollar, active newFocus,
          inactive newNext]) ++ beta.map inactive ++ List.replicate k none := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitNonproductivePrefix hproductive rfl hdone with
    ⟨alpha, rest, stage, henabled, holdPrefix, hnewPrefix, hstage, hrest⟩
  cases hrest with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage old₁ new₁ next₁ rows₁ result hedge₁ tail₁ =>
      have hw₁ := (hshape stage.phase next₁ stage.history old₁ new₁).mp hedge₁.2.2.2.2
      have he₁ := (replaceTwo_stage1_iff oldFocus newFocus oldNext newNext next₁
        stage.history old₁ new₁).mp (by simpa [hstage] using hw₁.2)
      rcases he₁ with ⟨rfl, rfl, rfl⟩
      cases tail₁ with
      | nil => simp [workScanDone, advanceWorkState] at hdone
      | @cons _stage₂ old₂ new₂ next₂ suffixRows result hedge₂ htail =>
          let stage₂ := advanceWorkState stage (active oldFocus) (active newFocus) .stage2
          have hw₂ := (hshape stage₂.phase next₂ stage₂.history old₂ new₂).mp
            hedge₂.2.2.2.2
          have he₂ := (replaceTwo_stage2_iff oldFocus newFocus oldNext newNext next₂
            stage₂.history old₂ new₂).mp (by simpa [stage₂, advanceWorkState] using hw₂.2)
          rcases he₂ with ⟨rfl, rfl, rfl⟩
          have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
              (x y : Option (WorkSlot g)),
              WorkEdge g cert .suffixSame next hist x y →
                next = .suffixSame ∧ sameSuffix x y := by
            intro next hist x y hedge'
            have hw := (hshape .suffixSame next hist x y).mp hedge'
            exact (replaceTwo_suffixSame_iff oldFocus newFocus oldNext newNext
              next hist x y).mp hw.2
          rcases htail.decodeSuffixSame rfl hsuffix hdone with
            ⟨beta, k, holdSuffix, hnewSuffix⟩
          have holdSuffix' : suffixRows.map (fun r => r.1) =
              beta.map inactive ++ List.replicate k none := by
            simpa [oldProjection] using holdSuffix
          have hnewSuffix' : suffixRows.map (fun r => r.2.1) =
              beta.map inactive ++ List.replicate k none := by
            simpa [newProjection] using hnewSuffix
          refine ⟨alpha, beta, k, henabled, ?_, ?_⟩
          · rw [← hold]
            calc
              rows.map (fun r => r.1) = alpha.map inactive ++ [inactive .dollar] ++
                  oldProjection
                    ((active oldFocus, active newFocus, .stage2) ::
                      (inactive oldNext, inactive newNext, .suffixSame) :: suffixRows) := by
                simpa [oldProjection] using holdPrefix
              _ = (alpha.map inactive ++ [inactive .dollar, active oldFocus,
                    inactive oldNext]) ++ beta.map inactive ++
                    List.replicate k none := by
                simp only [oldProjection, List.map_cons]
                rw [holdSuffix']
                simp [List.append_assoc]
          · rw [← hnew]
            calc
              rows.map (fun r => r.2.1) = alpha.map inactive ++ [inactive .dollar] ++
                  newProjection
                    ((active oldFocus, active newFocus, .stage2) ::
                      (inactive oldNext, inactive newNext, .suffixSame) :: suffixRows) := by
                simpa [newProjection] using hnewPrefix
              _ = (alpha.map inactive ++ [inactive .dollar, active newFocus,
                    inactive newNext]) ++ beta.map inactive ++
                    List.replicate k none := by
                simp only [newProjection, List.map_cons]
                rw [hnewSuffix']
                simp [List.append_assoc]

public theorem workTraceAccepts_livePushCompress_sound
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {R : CFlag g} {d : IndexMark}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.livePushCompress A B f R d) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.livePushCompress A B f R d) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.livePushCompress A B f R d) phase next hist x y ↔
        CertEnabled g (.livePushCompress A B f R d) ∧
          replaceTwoEdge (.live A) (.live B) (.index R d)
            (.index (cflagComp g (cflagBase g f) R) d) phase next hist x y := by
    intro phase next hist x y
    simp [WorkEdge, CertEnabled, and_assoc]
  rcases h.decodeReplaceTwo (.live A) (.live B) (.index R d)
      (.index (cflagComp g (cflagBase g f) R) d) rfl hshape with
    ⟨alpha, beta, k, henabled, hold, hnew⟩
  let oldCursor : WorkCursor g :=
    ⟨alpha ++ [.dollar], .live A, .index R d :: beta⟩
  let newCursor : WorkCursor g :=
    ⟨alpha ++ [.dollar], .live B,
      .index (cflagComp g (cflagBase g f) R) d :: beta⟩
  refine ⟨oldCursor, newCursor, k, k, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨henabled.1, henabled.2, alpha, beta, rfl, rfl⟩

end Aho
end IndexedGrammar
