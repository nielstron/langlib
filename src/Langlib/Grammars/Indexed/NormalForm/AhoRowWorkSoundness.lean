module

public import Langlib.Grammars.Indexed.NormalForm.AhoRowTrace
public import Langlib.Grammars.Indexed.NormalForm.AhoRowInputCorrectness

@[expose]
public section

/-!
# Soundness of Aho's logical-slot row checker

The synchronized checker operates on padded lists of marked work slots.  This file inverts an
accepting logical-slot trace: the non-padding prefixes are the marked encodings of two cursors,
and those cursors satisfy exactly the work-tape clause named by the chosen composite certificate.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- The work-cursor component of `CertStep`, with input-head metadata omitted. -/
public noncomputable def CertWorkStep (g : IndexedGrammar T) [Fintype g.nt] :
    CompositeCert g → WorkCursor g → WorkCursor g → Prop
  | .plainBinary A B C, old, new =>
      AugBinary g A B C ∧ ∃ alpha beta,
        old = ⟨alpha ++ [.dollar], .plain A, beta⟩ ∧
        new = ⟨markProductivePrefix alpha ++ [.dollar], .plain B, .plain C :: beta⟩
  | .plainTerminal A a, old, new =>
      AugTerminal g A a ∧ ∃ alpha beta,
        old = ⟨alpha ++ [.dollar], .plain A, beta⟩ ∧
        new = ⟨markProductivePrefix alpha ++ [.dollar], .terminal a, beta⟩
  | .plainPushSkip A B f, old, new =>
      AugPush g A B f ∧ ∃ alpha beta,
        old = ⟨alpha ++ [.dollar], .plain A, beta⟩ ∧
        new = ⟨alpha ++ [.dollar], .plain B, beta⟩
  | .plainPushUse A B f, old, new =>
      AugPush g A B f ∧ ∃ alpha beta,
        old = ⟨alpha ++ [.dollar], .plain A, beta⟩ ∧
        new = ⟨alpha ++ [.dollar], .live B,
          .index (cflagBase g f) .firstPending :: beta⟩
  | .liveBinaryBoth A B C, old, new =>
      AugBinary g A B C ∧ ∃ alpha Z beta,
        old = ⟨alpha ++ [.dollar], .live A, Z :: beta⟩ ∧
        new = ⟨markProductivePrefix alpha ++ [.dollar], .live B, .live C :: Z :: beta⟩
  | .liveBinaryLeft A B C, old, new =>
      AugBinary g A B C ∧ ∃ alpha Z beta,
        old = ⟨alpha ++ [.dollar], .live A, Z :: beta⟩ ∧
        new = ⟨markProductivePrefix alpha ++ [.dollar], .live B, .plain C :: Z :: beta⟩
  | .liveBinaryRight A B C, old, new =>
      AugBinary g A B C ∧ ∃ alpha Z beta,
        old = ⟨alpha ++ [.dollar], .live A, Z :: beta⟩ ∧
        new = ⟨markProductivePrefix alpha ++ [.dollar], .plain B, .live C :: Z :: beta⟩
  | .livePushFresh A B f, old, new =>
      AugPush g A B f ∧ ∃ alpha Z beta,
        old = ⟨alpha ++ [.dollar], .live A, Z :: beta⟩ ∧
        new = ⟨alpha ++ [.dollar], .live B,
          .index (cflagBase g f) .laterPending :: Z :: beta⟩
  | .livePushCompress A B f R d, old, new =>
      AugPush g A B f ∧ (cflagComp g (cflagBase g f) R).Nonempty ∧ ∃ alpha beta,
        old = ⟨alpha ++ [.dollar], .live A, .index R d :: beta⟩ ∧
        new = ⟨alpha ++ [.dollar], .live B,
          .index (cflagComp g (cflagBase g f) R) d :: beta⟩
  | .popPlain R d A B, old, new =>
      R A B = true ∧
        ((∃ alpha beta gamma,
            IndexFree beta ∧
            old = ⟨alpha ++ [.dollar], .live A, beta ++ .index R d :: gamma⟩ ∧
            new = ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
              .plain B, .close :: gamma⟩) ∨
          (∃ alpha gamma,
            old = ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩ ∧
            new = ⟨alpha ++ [.dollar], .plain B, gamma⟩))
  | .popLive R d A B, old, new =>
      R A B = true ∧ d.later = true ∧
        ((∃ alpha beta gamma,
            IndexFree beta ∧
            old = ⟨alpha ++ [.dollar], .live A, beta ++ .index R d :: gamma⟩ ∧
            new = ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
              .live B, .close :: gamma⟩) ∨
          (∃ alpha gamma,
            old = ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩ ∧
            new = ⟨alpha ++ [.dollar], .live B, gamma⟩))
  | .matchTerminal a, old, new =>
      ∃ alpha Z beta,
        old = ⟨alpha ++ [.dollar], .terminal a, Z :: beta⟩ ∧
        new = ⟨alpha ++ [.dollar], Z, beta⟩
  | .eraseIndex R d, old, new =>
      d.erasable = true ∧ ∃ alpha Z beta,
        old = ⟨alpha ++ [.dollar], .index R d, Z :: beta⟩ ∧
        new = ⟨alpha ++ [.dollar], Z, beta⟩
  | .returnFrame, old, new =>
      ∃ alpha Z beta gamma,
        Z ≠ .dollar ∧ DollarFree beta ∧
        old = ⟨alpha ++ [.dollar, Z] ++ beta ++ [.dollar], .close, gamma⟩ ∧
        new = ⟨alpha ++ [.dollar], Z, beta ++ gamma⟩

/-! ## Canonical padding extracted from a valid trace -/

private theorem WorkTrace.old_none_of_ended
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (h : WorkTrace g cert state rows result) (hended : state.oldEnded = true) :
    rows.map (fun r => r.1) = List.replicate rows.length none := by
  induction h with
  | nil => rfl
  | @cons state old new next rows result hedge htail ih =>
      have hold : old = none := by
        rcases hedge.2.2.1 with hfalse | hnone
        · simp [hended] at hfalse
        · exact hnone
      subst old
      simp only [List.map_cons, List.length_cons, List.replicate_succ, List.cons.injEq]
      refine ⟨trivial, ih ?_⟩
      simp [advanceWorkState, hended]

private theorem WorkTrace.new_none_of_ended
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (h : WorkTrace g cert state rows result) (hended : state.newEnded = true) :
    rows.map (fun r => r.2.1) = List.replicate rows.length none := by
  induction h with
  | nil => rfl
  | @cons state old new next rows result hedge htail ih =>
      have hnew : new = none := by
        rcases hedge.2.2.2.1 with hfalse | hnone
        · simp [hended] at hfalse
        · exact hnone
      subst new
      simp only [List.map_cons, List.length_cons, List.replicate_succ, List.cons.injEq]
      refine ⟨trivial, ih ?_⟩
      simp [advanceWorkState, hended]

private theorem WorkTrace.old_canonical
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (h : WorkTrace g cert state rows result) (hended : state.oldEnded = false) :
    ∃ (slots : List (WorkSlot g)) (k : ℕ),
      rows.map (fun r => r.1) = slots.map some ++ List.replicate k none := by
  induction h with
  | nil => exact ⟨[], 0, rfl⟩
  | @cons state old new next rows result hedge htail ih =>
      cases old with
      | none =>
          have htailNone := htail.old_none_of_ended (by
            simp [advanceWorkState, hended])
          refine ⟨[], rows.length + 1, ?_⟩
          simp only [List.map_cons, htailNone, List.map_nil, List.nil_append]
          exact List.replicate_succ.symm
      | some slot =>
          rcases ih (by simp [advanceWorkState, hended]) with ⟨slots, k, hslots⟩
          exact ⟨slot :: slots, k, by simp [hslots]⟩

private theorem WorkTrace.new_canonical
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (h : WorkTrace g cert state rows result) (hended : state.newEnded = false) :
    ∃ (slots : List (WorkSlot g)) (k : ℕ),
      rows.map (fun r => r.2.1) = slots.map some ++ List.replicate k none := by
  induction h with
  | nil => exact ⟨[], 0, rfl⟩
  | @cons state old new next rows result hedge htail ih =>
      cases new with
      | none =>
          have htailNone := htail.new_none_of_ended (by
            simp [advanceWorkState, hended])
          refine ⟨[], rows.length + 1, ?_⟩
          simp only [List.map_cons, htailNone, List.map_nil, List.nil_append]
          exact List.replicate_succ.symm
      | some slot =>
          rcases ih (by simp [advanceWorkState, hended]) with ⟨slots, k, hslots⟩
          exact ⟨slot :: slots, k, by simp [hslots]⟩

/-- Both projections of a trace from the initial work state have canonical `some* none*` form. -/
public theorem WorkTrace.projections_canonical
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (h : WorkTrace g cert (initialWorkScan g) rows result) :
    ∃ (oldSlots newSlots : List (WorkSlot g)) (kOld kNew : ℕ),
      rows.map (fun r => r.1) = oldSlots.map some ++ List.replicate kOld none ∧
      rows.map (fun r => r.2.1) = newSlots.map some ++ List.replicate kNew none := by
  rcases h.old_canonical rfl with ⟨oldSlots, kOld, hold⟩
  rcases h.new_canonical rfl with ⟨newSlots, kNew, hnew⟩
  exact ⟨oldSlots, newSlots, kOld, kNew, hold, hnew⟩

/-! ## Generic suffix inversions -/

private def oldProjection
    (rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)) :
    List (Option (WorkSlot g)) :=
  rows.map fun r => r.1

private def newProjection
    (rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)) :
    List (Option (WorkSlot g)) :=
  rows.map fun r => r.2.1

/-- In the equal-suffix phase, the remaining non-padding symbols are the same inactive word on
both tracks. -/
private theorem WorkTrace.decodeSuffixSame
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixSame)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixSame next hist old new →
        next = .suffixSame ∧ sameSuffix old new)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g)) (k : ℕ),
      oldProjection rows = beta.map inactive ++ List.replicate k none ∧
      newProjection rows = beta.map inactive ++ List.replicate k none := by
  induction h with
  | nil => exact ⟨[], 0, rfl, rfl⟩
  | @cons state old new next rows result hedge htail ih =>
      have hedge' := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases hedge' with ⟨rfl, hsamen⟩
      rcases hsamen with ⟨holdnew, hinactive⟩
      subst new
      cases old with
      | none =>
          have holdTail := htail.old_none_of_ended (by
            simp [advanceWorkState])
          have hnewTail := htail.new_none_of_ended (by
            simp [advanceWorkState])
          refine ⟨[], rows.length + 1, ?_, ?_⟩
          · simp only [oldProjection, List.map_cons, holdTail, List.map_nil,
              List.nil_append]
            exact List.replicate_succ.symm
          · simp only [newProjection, List.map_cons, hnewTail, List.map_nil,
              List.nil_append]
            exact List.replicate_succ.symm
      | some slot =>
          have hslot : slot = ⟨false, slot.symbol⟩ := by
            cases slot with
            | mk active symbol =>
                simp [InactiveOpt] at hinactive
                subst active
                rfl
          rcases ih rfl hdone with ⟨beta, k, hold, hnew⟩
          refine ⟨slot.symbol :: beta, k, ?_, ?_⟩
          · simp only [oldProjection, List.map_cons, List.map_cons]
            rw [hslot]
            simpa [inactive] using congrArg (fun xs => (some ⟨false, slot.symbol⟩) :: xs) hold
          · simp only [newProjection, List.map_cons, List.map_cons]
            rw [hslot]
            simpa [inactive] using congrArg (fun xs => (some ⟨false, slot.symbol⟩) :: xs) hnew

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
      have : False := by simpa [workScanDone, hphase] using hdone
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

private def CopiedHistory (alpha : List (WorkSym g)) (hist : WorkHistory g) : Prop :=
  match alpha.reverse with
  | [] => hist.old1 = none ∧ hist.new1 = none
  | z :: _ => hist.old1 = some (inactive z) ∧ hist.new1 = some (inactive z)

private def ProductivePrefixInv (alpha : List (WorkSym g))
    (state : WorkScanState g) : Prop :=
  state.phase = .prefix ∧ state.oldEnded = false ∧ state.newEnded = false ∧
    CopiedHistory alpha state.history

private theorem productivePrefixInv_initial (g : IndexedGrammar T) :
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
          have hidem : d.markUsed.markUsed = d.markUsed := by cases d <;> rfl
          simpa [hsym, hidem]
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
private theorem WorkTrace.splitProductivePrefix
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
        simpa [workScanDone, hinv.1] using hdone
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
            · simp [markProductivePrefix_append_index, List.append_assoc]
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

private theorem WorkTrace.splitNonproductivePrefix
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
      have : False := by simpa [workScanDone, hphase] using hdone
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

/-! ## One-slot right shifts -/

private theorem insertOne_suffixPlus1_iff
    (productive : Bool) (oldFocus newFocus inserted : WorkSym g)
    (needOldSome : Bool) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    insertOneEdge productive oldFocus newFocus inserted needOldSome
        .suffixPlus1 next hist old new ↔
      next = .suffixPlus1 ∧ plus1Suffix hist old new := by
  cases next <;> simp [insertOneEdge, prefixEdge]

private theorem WorkTrace.decodePlus1None
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixPlus1)
    (hcarry : state.history.old1 = some none)
    (holdEnded : state.oldEnded = true)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus1 next hist old new →
        next = .suffixPlus1 ∧ plus1Suffix hist old new)
    (h : WorkTrace g cert state rows result) :
    oldProjection rows = List.replicate rows.length none ∧
      newProjection rows = List.replicate rows.length none := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons state old new next rows result hedge htail ih =>
      have hold : old = none := by
        rcases hedge.2.2.1 with hfalse | hnone
        · simp [holdEnded] at hfalse
        · exact hnone
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, _holdInactive, _hnewInactive, hshift⟩
      have hnew : new = none := by simpa [hcarry] using hshift.symm
      subst old
      subst new
      rcases ih rfl (by simp [advanceWorkState, updateHistory])
          (by simp [advanceWorkState]) with
        ⟨holdTail, hnewTail⟩
      constructor
      · simp only [oldProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, holdTail⟩
      · simp only [newProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, hnewTail⟩

private theorem WorkTrace.decodePlus1Some
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (z : WorkSym g)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixPlus1)
    (hcarry : state.history.old1 = some (inactive z))
    (holdEnded : state.oldEnded = false)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus1 next hist old new →
        next = .suffixPlus1 ∧ plus1Suffix hist old new)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g)) (k : ℕ),
      oldProjection rows = beta.map inactive ++ List.replicate (k + 1) none ∧
      newProjection rows = inactive z :: beta.map inactive ++ List.replicate k none := by
  induction h generalizing z with
  | nil =>
      have : False := by
        simp [workScanDone, hphase, lastOldNone, hcarry] at hdone
        simp [inactive] at hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, holdInactive, _hnewInactive, hshift⟩
      have hnew : new = inactive z := by simpa [hcarry] using hshift.symm
      subst new
      cases old with
      | none =>
          have htailNone := htail.decodePlus1None rfl (by
            simp [advanceWorkState, updateHistory]) (by simp [advanceWorkState]) hsuffix
          rcases htailNone with ⟨holdTail, hnewTail⟩
          have holdTail' : rows.map (fun r => r.1) =
              List.replicate rows.length none := by
            simpa [oldProjection] using holdTail
          have hnewTail' : rows.map (fun r => r.2.1) =
              List.replicate rows.length none := by
            simpa [newProjection] using hnewTail
          refine ⟨[], rows.length, ?_, ?_⟩
          · simp only [oldProjection, List.map_cons, List.map_nil, List.nil_append,
              List.length_cons]
            rw [holdTail']
            exact List.replicate_succ.symm
          · simp only [newProjection, List.map_cons, List.map_nil, List.nil_append]
            rw [hnewTail']
            rfl
      | some slot =>
          cases slot with
          | mk activeFlag symbol =>
              simp [InactiveOpt] at holdInactive
              subst activeFlag
              rcases ih symbol rfl (by simp [advanceWorkState, updateHistory, inactive])
                  (by simpa [advanceWorkState, inactive, holdEnded]) hdone with
                ⟨beta, k, holdTail, hnewTail⟩
              refine ⟨symbol :: beta, k, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_cons]
                simpa [inactive] using
                  congrArg (fun xs => inactive symbol :: xs) holdTail
              · simp only [newProjection, List.map_cons, List.map_cons]
                simpa [inactive] using
                  congrArg (fun xs => inactive z :: xs) hnewTail

private theorem insertOne_stage1_iff
    (productive : Bool) (oldFocus newFocus inserted : WorkSym g)
    (needOldSome : Bool) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    insertOneEdge productive oldFocus newFocus inserted needOldSome
        .stage1 next hist old new ↔
      next = .stage2 ∧ old = active oldFocus ∧ new = active newFocus := by
  cases next <;> simp [insertOneEdge, prefixEdge]

private theorem insertOne_stage2_iff
    (productive : Bool) (oldFocus newFocus inserted : WorkSym g)
    (needOldSome : Bool) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    insertOneEdge productive oldFocus newFocus inserted needOldSome
        .stage2 next hist old new ↔
      next = .suffixPlus1 ∧
        (if needOldSome then InactiveSome old else InactiveOpt old) ∧
        new = inactive inserted := by
  cases next <;> simp [insertOneEdge, prefixEdge]

private theorem WorkTrace.decodeInsertAfterStage
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (productive : Bool) (oldFocus newFocus inserted : WorkSym g)
    (needOldSome : Bool)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧ insertOneEdge productive oldFocus newFocus inserted
          needOldSome phase next hist old new)
    {stage result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hstage : stage.phase = .stage1)
    (h : WorkTrace g cert stage rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g)) (kOld kNew : ℕ),
      oldProjection rows = active oldFocus :: beta.map inactive ++
        List.replicate kOld none ∧
      newProjection rows = active newFocus :: inactive inserted ::
        beta.map inactive ++ List.replicate kNew none ∧
      (needOldSome = true → ∃ z gamma, beta = z :: gamma) := by
  cases h with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage old₁ new₁ next₁ rows₁ result hedge₁ tail₁ =>
      have hw₁ := (hshape stage.phase next₁ stage.history old₁ new₁).mp hedge₁.2.2.2.2
      have he₁ := (insertOne_stage1_iff productive oldFocus newFocus inserted
        needOldSome next₁ stage.history old₁ new₁).mp (by simpa [hstage] using hw₁.2)
      rcases he₁ with ⟨rfl, rfl, rfl⟩
      have hstageOldEnded : stage.oldEnded = false := by
        rcases hedge₁.2.2.1 with hfalse | hnone
        · exact hfalse
        · simp [active] at hnone
      cases tail₁ with
      | nil => simp [workScanDone, advanceWorkState] at hdone
      | @cons _stage₂ carry new₂ next₂ suffixRows result hedge₂ htail =>
          let stage₂ := advanceWorkState stage (active oldFocus) (active newFocus) .stage2
          have hw₂ := (hshape stage₂.phase next₂ stage₂.history carry new₂).mp
            hedge₂.2.2.2.2
          have he₂ := (insertOne_stage2_iff productive oldFocus newFocus inserted
            needOldSome next₂ stage₂.history carry new₂).mp (by
              simpa [stage₂, advanceWorkState] using hw₂.2)
          rcases he₂ with ⟨rfl, hcarryOK, rfl⟩
          have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
              (x y : Option (WorkSlot g)),
              WorkEdge g cert .suffixPlus1 next hist x y →
                next = .suffixPlus1 ∧ plus1Suffix hist x y := by
            intro next hist x y hedge'
            have hw := (hshape .suffixPlus1 next hist x y).mp hedge'
            exact (insertOne_suffixPlus1_iff productive oldFocus newFocus inserted
              needOldSome next hist x y).mp hw.2
          cases carry with
          | none =>
              have hneedFalse : needOldSome = false := by
                cases needOldSome with
                | false => rfl
                | true =>
                    rcases hcarryOK with ⟨z, hz⟩
                    simp [inactive] at hz
              have hnone := htail.decodePlus1None rfl (by
                simp [stage₂, advanceWorkState, updateHistory])
                (by simp [stage₂, advanceWorkState]) hsuffix
              rcases hnone with ⟨holdTail, hnewTail⟩
              have holdTail' : suffixRows.map (fun r => r.1) =
                  List.replicate suffixRows.length none := by
                simpa [oldProjection] using holdTail
              have hnewTail' : suffixRows.map (fun r => r.2.1) =
                  List.replicate suffixRows.length none := by
                simpa [newProjection] using hnewTail
              refine ⟨[], suffixRows.length + 1, suffixRows.length, ?_, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_nil, List.nil_append]
                rw [holdTail']
                rw [List.replicate_succ]
                rfl
              · simp only [newProjection, List.map_cons, List.map_nil, List.nil_append]
                rw [hnewTail']
                rfl
              · simp [hneedFalse]
          | some slot =>
              cases slot with
              | mk activeFlag symbol =>
                  have hinactive : activeFlag = false := by
                    cases needOldSome with
                    | false => simpa [InactiveOpt] using hcarryOK
                    | true =>
                        rcases hcarryOK with ⟨z, hz⟩
                        have hslot : activeFlag = false ∧ symbol = z := by
                          simpa [inactive] using hz
                        exact hslot.1
                  subst activeFlag
                  have hplus := htail.decodePlus1Some symbol rfl (by
                    simp [stage₂, advanceWorkState, updateHistory, inactive])
                    (by simp [stage₂, advanceWorkState, inactive, active, hstageOldEnded])
                    hsuffix hdone
                  rcases hplus with ⟨beta, k, holdTail, hnewTail⟩
                  have holdTail' : suffixRows.map (fun r => r.1) =
                      beta.map inactive ++ List.replicate (k + 1) none := by
                    simpa [oldProjection] using holdTail
                  have hnewTail' : suffixRows.map (fun r => r.2.1) =
                      inactive symbol :: beta.map inactive ++ List.replicate k none := by
                    simpa [newProjection] using hnewTail
                  refine ⟨symbol :: beta, k + 1, k, ?_, ?_, ?_⟩
                  · simp only [oldProjection, List.map_cons, List.map_cons]
                    rw [holdTail']
                    simp [inactive, List.append_assoc]
                  · simp only [newProjection, List.map_cons, List.map_cons]
                    rw [hnewTail']
                    simp [inactive, List.append_assoc]
                  · intro _
                    exact ⟨symbol, beta, rfl⟩

/-! ## Completed one-slot insertion inversions -/

private theorem WorkTraceAccepts.decodeInsertNonproductive
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus newFocus inserted : WorkSym g) (needOldSome : Bool)
    (hproductive : cert.productive = false)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧ insertOneEdge false oldFocus newFocus inserted
          needOldSome phase next hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (alpha beta : List (WorkSym g)) (kOld kNew : ℕ),
      CertEnabled g cert ∧
      old = (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
        beta.map inactive ++ List.replicate kOld none ∧
      new = (alpha.map inactive ++
          [inactive .dollar, active newFocus, inactive inserted]) ++
        beta.map inactive ++ List.replicate kNew none ∧
      (needOldSome = true → ∃ z gamma, beta = z :: gamma) := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitNonproductivePrefix hproductive rfl hdone with
    ⟨alpha, rest, stage, henabled, holdPrefix, hnewPrefix, hstage, hrest⟩
  rcases hrest.decodeInsertAfterStage false oldFocus newFocus inserted needOldSome
      hshape hstage hdone with ⟨beta, kOld, kNew, holdRest, hnewRest, hnonempty⟩
  refine ⟨alpha, beta, kOld, kNew, henabled, ?_, ?_, hnonempty⟩
  · rw [← hold]
    calc
      oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          oldProjection rest := holdPrefix
      _ = (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
          beta.map inactive ++ List.replicate kOld none := by
        rw [holdRest]
        simp [List.append_assoc]
  · rw [← hnew]
    calc
      newProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          newProjection rest := hnewPrefix
      _ = (alpha.map inactive ++
            [inactive .dollar, active newFocus, inactive inserted]) ++
          beta.map inactive ++ List.replicate kNew none := by
        rw [hnewRest]
        simp [List.append_assoc]

private theorem WorkTraceAccepts.decodeInsertProductive
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus newFocus inserted : WorkSym g) (needOldSome : Bool)
    (hproductive : cert.productive = true)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧ insertOneEdge true oldFocus newFocus inserted
          needOldSome phase next hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (alpha beta : List (WorkSym g)) (kOld kNew : ℕ),
      CertEnabled g cert ∧
      old = (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
        beta.map inactive ++ List.replicate kOld none ∧
      new = ((markProductivePrefix alpha).map inactive ++
          [inactive .dollar, active newFocus, inactive inserted]) ++
        beta.map inactive ++ List.replicate kNew none ∧
      (needOldSome = true → ∃ z gamma, beta = z :: gamma) := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitProductivePrefix hproductive (productivePrefixInv_initial g) hdone with
    ⟨alpha, newAlpha, rest, stage, henabled, hmark,
      holdPrefix, hnewPrefix, hstage, hrest⟩
  rcases hrest.decodeInsertAfterStage true oldFocus newFocus inserted needOldSome
      hshape hstage hdone with ⟨beta, kOld, kNew, holdRest, hnewRest, hnonempty⟩
  have hmark' : markProductivePrefix alpha = newAlpha := by simpa using hmark
  refine ⟨alpha, beta, kOld, kNew, henabled, ?_, ?_, hnonempty⟩
  · rw [← hold]
    calc
      oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          oldProjection rest := holdPrefix
      _ = (alpha.map inactive ++ [inactive .dollar, active oldFocus]) ++
          beta.map inactive ++ List.replicate kOld none := by
        rw [holdRest]
        simp [List.append_assoc]
  · rw [← hnew]
    calc
      newProjection rows = newAlpha.map inactive ++ [inactive .dollar] ++
          newProjection rest := hnewPrefix
      _ = ((markProductivePrefix alpha).map inactive ++
            [inactive .dollar, active newFocus, inactive inserted]) ++
          beta.map inactive ++ List.replicate kNew none := by
        rw [hnewRest, hmark']
        simp [List.append_assoc]

public theorem workTraceAccepts_plainBinary_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A B C : g.nt}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.plainBinary A B C) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.plainBinary A B C) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.plainBinary A B C) phase next hist x y ↔
        CertEnabled g (.plainBinary A B C) ∧
          insertOneEdge true (.plain A) (.plain B) (.plain C) false
            phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeInsertProductive (.plain A) (.plain B) (.plain C) false rfl hshape with
    ⟨alpha, beta, kOld, kNew, hbinary, hold, hnew, _⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .plain A, beta⟩
  let newCursor : WorkCursor g := ⟨markProductivePrefix alpha ++ [.dollar],
    .plain B, .plain C :: beta⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hbinary, alpha, beta, rfl, rfl⟩

public theorem workTraceAccepts_plainPushUse_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A B : g.nt} {f : g.flag}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.plainPushUse A B f) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.plainPushUse A B f) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.plainPushUse A B f) phase next hist x y ↔
        CertEnabled g (.plainPushUse A B f) ∧
          insertOneEdge false (.plain A) (.live B)
            (.index (cflagBase g f) .firstPending) false phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeInsertNonproductive (.plain A) (.live B)
      (.index (cflagBase g f) .firstPending) false rfl hshape with
    ⟨alpha, beta, kOld, kNew, hpush, hold, hnew, _⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .plain A, beta⟩
  let newCursor : WorkCursor g := ⟨alpha ++ [.dollar], .live B,
    .index (cflagBase g f) .firstPending :: beta⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hpush, alpha, beta, rfl, rfl⟩

public theorem workTraceAccepts_livePushFresh_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A B : g.nt} {f : g.flag}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.livePushFresh A B f) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.livePushFresh A B f) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.livePushFresh A B f) phase next hist x y ↔
        CertEnabled g (.livePushFresh A B f) ∧
          insertOneEdge false (.live A) (.live B)
            (.index (cflagBase g f) .laterPending) true phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeInsertNonproductive (.live A) (.live B)
      (.index (cflagBase g f) .laterPending) true rfl hshape with
    ⟨alpha, beta, kOld, kNew, hpush, hold, hnew, hnonempty⟩
  rcases hnonempty rfl with ⟨Z, gamma, rfl⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .live A, Z :: gamma⟩
  let newCursor : WorkCursor g := ⟨alpha ++ [.dollar], .live B,
    .index (cflagBase g f) .laterPending :: Z :: gamma⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hpush, alpha, Z, gamma, rfl, rfl⟩

public theorem workTraceAccepts_liveBinaryBoth_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A B C : g.nt}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.liveBinaryBoth A B C) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.liveBinaryBoth A B C) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.liveBinaryBoth A B C) phase next hist x y ↔
        CertEnabled g (.liveBinaryBoth A B C) ∧
          insertOneEdge true (.live A) (.live B) (.live C) true phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeInsertProductive (.live A) (.live B) (.live C) true rfl hshape with
    ⟨alpha, tail, kOld, kNew, hbinary, hold, hnew, hnonempty⟩
  rcases hnonempty rfl with ⟨Z, beta, rfl⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .live A, Z :: beta⟩
  let newCursor : WorkCursor g := ⟨markProductivePrefix alpha ++ [.dollar],
    .live B, .live C :: Z :: beta⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hbinary, alpha, Z, beta, rfl, rfl⟩

public theorem workTraceAccepts_liveBinaryLeft_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A B C : g.nt}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.liveBinaryLeft A B C) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.liveBinaryLeft A B C) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.liveBinaryLeft A B C) phase next hist x y ↔
        CertEnabled g (.liveBinaryLeft A B C) ∧
          insertOneEdge true (.live A) (.live B) (.plain C) true phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeInsertProductive (.live A) (.live B) (.plain C) true rfl hshape with
    ⟨alpha, tail, kOld, kNew, hbinary, hold, hnew, hnonempty⟩
  rcases hnonempty rfl with ⟨Z, beta, rfl⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .live A, Z :: beta⟩
  let newCursor : WorkCursor g := ⟨markProductivePrefix alpha ++ [.dollar],
    .live B, .plain C :: Z :: beta⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hbinary, alpha, Z, beta, rfl, rfl⟩

public theorem workTraceAccepts_liveBinaryRight_sound
    {g : IndexedGrammar T} [Fintype g.nt] {A B C : g.nt}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.liveBinaryRight A B C) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.liveBinaryRight A B C) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.liveBinaryRight A B C) phase next hist x y ↔
        CertEnabled g (.liveBinaryRight A B C) ∧
          insertOneEdge true (.live A) (.plain B) (.live C) true phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeInsertProductive (.live A) (.plain B) (.live C) true rfl hshape with
    ⟨alpha, tail, kOld, kNew, hbinary, hold, hnew, hnonempty⟩
  rcases hnonempty rfl with ⟨Z, beta, rfl⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .live A, Z :: beta⟩
  let newCursor : WorkCursor g := ⟨markProductivePrefix alpha ++ [.dollar],
    .plain B, .live C :: Z :: beta⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨hbinary, alpha, Z, beta, rfl, rfl⟩

/-! ## One-slot left shifts -/

private theorem deleteOne_suffixMinus1_iff
    (focusOK : Option (WorkSlot g) → Prop)
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    deleteOneEdge focusOK .suffixMinus1 next hist old new ↔
      next = .suffixMinus1 ∧ minus1Suffix hist old new := by
  cases next <;> simp [deleteOneEdge, prefixEdge]

private theorem WorkTrace.decodeMinus1None
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixMinus1)
    (hcarry : state.history.new1 = some none)
    (hnewEnded : state.newEnded = true)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus1 next hist old new →
        next = .suffixMinus1 ∧ minus1Suffix hist old new)
    (h : WorkTrace g cert state rows result) :
    oldProjection rows = List.replicate rows.length none ∧
      newProjection rows = List.replicate rows.length none := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons state old new next rows result hedge htail ih =>
      have hnew : new = none := by
        rcases hedge.2.2.2.1 with hfalse | hnone
        · simp [hnewEnded] at hfalse
        · exact hnone
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, _holdInactive, _hnewInactive, hshift⟩
      have hold : old = none := by simpa [hcarry] using hshift.symm
      subst old
      subst new
      rcases ih rfl (by simp [advanceWorkState, updateHistory])
          (by simp [advanceWorkState]) with ⟨holdTail, hnewTail⟩
      constructor
      · simp only [oldProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, holdTail⟩
      · simp only [newProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, hnewTail⟩

private theorem WorkTrace.decodeMinus1Some
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (z : WorkSym g)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixMinus1)
    (hcarry : state.history.new1 = some (inactive z))
    (hnewEnded : state.newEnded = false)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus1 next hist old new →
        next = .suffixMinus1 ∧ minus1Suffix hist old new)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g)) (k : ℕ),
      oldProjection rows = inactive z :: beta.map inactive ++ List.replicate k none ∧
      newProjection rows = beta.map inactive ++ List.replicate (k + 1) none := by
  induction h generalizing z with
  | nil =>
      have : False := by
        simp [workScanDone, hphase, lastNewNone, hcarry, inactive] at hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, _holdInactive, hnewInactive, hshift⟩
      have hold : old = inactive z := by simpa [hcarry] using hshift.symm
      subst old
      cases new with
      | none =>
          have htailNone := htail.decodeMinus1None rfl (by
            simp [advanceWorkState, updateHistory]) (by simp [advanceWorkState]) hsuffix
          rcases htailNone with ⟨holdTail, hnewTail⟩
          have holdTail' : rows.map (fun r => r.1) =
              List.replicate rows.length none := by
            simpa [oldProjection] using holdTail
          have hnewTail' : rows.map (fun r => r.2.1) =
              List.replicate rows.length none := by
            simpa [newProjection] using hnewTail
          refine ⟨[], rows.length, ?_, ?_⟩
          · simp only [oldProjection, List.map_cons, List.map_nil, List.nil_append]
            rw [holdTail']
            rfl
          · simp only [newProjection, List.map_cons, List.map_nil, List.nil_append,
              List.length_cons]
            rw [hnewTail']
            exact List.replicate_succ.symm
      | some slot =>
          cases slot with
          | mk activeFlag symbol =>
              simp [InactiveOpt] at hnewInactive
              subst activeFlag
              rcases ih symbol rfl (by simp [advanceWorkState, updateHistory, inactive])
                  (by simpa [advanceWorkState, inactive, hnewEnded]) hdone with
                ⟨beta, k, holdTail, hnewTail⟩
              refine ⟨symbol :: beta, k, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_cons]
                simpa [inactive] using
                  congrArg (fun xs => inactive z :: xs) holdTail
              · simp only [newProjection, List.map_cons, List.map_cons]
                simpa [inactive] using
                  congrArg (fun xs => inactive symbol :: xs) hnewTail

private theorem deleteOne_stage1_iff
    (oldFocus : WorkSym g) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    deleteOneEdge (fun x => x = active oldFocus) .stage1 next hist old new ↔
      next = .minus1First ∧ old = active oldFocus ∧ ∃ z, new = active z := by
  cases next <;> simp [deleteOneEdge, prefixEdge]

private theorem deleteOne_minus1First_iff
    (oldFocus : WorkSym g) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    deleteOneEdge (fun x => x = active oldFocus) .minus1First next hist old new ↔
      next = .suffixMinus1 ∧ sameSymbolFirstMinus1 hist old new := by
  cases next <;> simp [deleteOneEdge, prefixEdge]

private theorem WorkTrace.decodeDeleteAfterStage
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus : WorkSym g)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧
          deleteOneEdge (fun x => x = active oldFocus) phase next hist old new)
    {stage result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hstage : stage.phase = .stage1)
    (h : WorkTrace g cert stage rows result)
    (hdone : workScanDone result = true) :
    ∃ (Z : WorkSym g) (beta : List (WorkSym g)) (kOld kNew : ℕ),
      oldProjection rows = active oldFocus :: inactive Z ::
        beta.map inactive ++ List.replicate kOld none ∧
      newProjection rows = active Z :: beta.map inactive ++
        List.replicate kNew none := by
  cases h with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage old₁ new₁ next₁ rows₁ result hedge₁ tail₁ =>
      have hw₁ := (hshape stage.phase next₁ stage.history old₁ new₁).mp
        hedge₁.2.2.2.2
      have he₁ := (deleteOne_stage1_iff oldFocus next₁ stage.history old₁ new₁).mp
        (by simpa [hstage] using hw₁.2)
      rcases he₁ with ⟨rfl, rfl, Z, rfl⟩
      have hstageNewEnded : stage.newEnded = false := by
        rcases hedge₁.2.2.2.1 with hfalse | hnone
        · exact hfalse
        · simp [active] at hnone
      cases tail₁ with
      | nil => simp [workScanDone, advanceWorkState] at hdone
      | @cons _minus old₂ new₂ next₂ suffixRows result hedge₂ htail =>
          let minusState := advanceWorkState stage (active oldFocus) (active Z) .minus1First
          have hw₂ := (hshape minusState.phase next₂ minusState.history old₂ new₂).mp
            hedge₂.2.2.2.2
          have he₂ := (deleteOne_minus1First_iff oldFocus next₂ minusState.history
            old₂ new₂).mp (by simpa [minusState, advanceWorkState] using hw₂.2)
          rcases he₂ with ⟨rfl, hnewInactive, z, rfl, hsame⟩
          have hz : z = Z := by
            simpa [minusState, advanceWorkState, updateHistory, active] using hsame.symm
          subst z
          have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
              (x y : Option (WorkSlot g)),
              WorkEdge g cert .suffixMinus1 next hist x y →
                next = .suffixMinus1 ∧ minus1Suffix hist x y := by
            intro next hist x y hedge'
            have hw := (hshape .suffixMinus1 next hist x y).mp hedge'
            exact (deleteOne_suffixMinus1_iff
              (fun x => x = active oldFocus) next hist x y).mp hw.2
          cases new₂ with
          | none =>
              have hnone := htail.decodeMinus1None rfl (by
                simp [minusState, advanceWorkState, updateHistory])
                (by simp [minusState, advanceWorkState]) hsuffix
              rcases hnone with ⟨holdTail, hnewTail⟩
              have holdTail' : suffixRows.map (fun r => r.1) =
                  List.replicate suffixRows.length none := by
                simpa [oldProjection] using holdTail
              have hnewTail' : suffixRows.map (fun r => r.2.1) =
                  List.replicate suffixRows.length none := by
                simpa [newProjection] using hnewTail
              refine ⟨Z, [], suffixRows.length, suffixRows.length + 1, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_nil, List.nil_append]
                rw [holdTail']
                rfl
              · simp only [newProjection, List.map_cons, List.map_nil, List.nil_append]
                rw [hnewTail', List.replicate_succ]
                rfl
          | some slot =>
              cases slot with
              | mk activeFlag symbol =>
                  simp [InactiveOpt] at hnewInactive
                  subst activeFlag
                  have hminus := htail.decodeMinus1Some symbol rfl (by
                    simp [minusState, advanceWorkState, updateHistory, inactive])
                    (by simp [minusState, advanceWorkState, inactive, active,
                      hstageNewEnded])
                    hsuffix hdone
                  rcases hminus with ⟨beta, k, holdTail, hnewTail⟩
                  have holdTail' : suffixRows.map (fun r => r.1) =
                      inactive symbol :: beta.map inactive ++ List.replicate k none := by
                    simpa [oldProjection] using holdTail
                  have hnewTail' : suffixRows.map (fun r => r.2.1) =
                      beta.map inactive ++ List.replicate (k + 1) none := by
                    simpa [newProjection] using hnewTail
                  refine ⟨Z, symbol :: beta, k, k + 1, ?_, ?_⟩
                  · simp only [oldProjection, List.map_cons]
                    rw [holdTail']
                    rfl
                  · simp only [newProjection, List.map_cons]
                    rw [hnewTail']
                    rfl

private theorem WorkTraceAccepts.decodeDeleteOne
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (oldFocus : WorkSym g) (hproductive : cert.productive = false)
    (hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert phase next hist old new ↔
        CertEnabled g cert ∧
          deleteOneEdge (fun x => x = active oldFocus) phase next hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (alpha : List (WorkSym g)) (Z : WorkSym g)
      (beta : List (WorkSym g)) (kOld kNew : ℕ),
      CertEnabled g cert ∧
      old = (alpha.map inactive ++
          [inactive .dollar, active oldFocus, inactive Z]) ++
        beta.map inactive ++ List.replicate kOld none ∧
      new = (alpha.map inactive ++ [inactive .dollar, active Z]) ++
        beta.map inactive ++ List.replicate kNew none := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitNonproductivePrefix hproductive rfl hdone with
    ⟨alpha, rest, stage, henabled, holdPrefix, hnewPrefix, hstage, hrest⟩
  rcases hrest.decodeDeleteAfterStage oldFocus hshape hstage hdone with
    ⟨Z, beta, kOld, kNew, holdRest, hnewRest⟩
  refine ⟨alpha, Z, beta, kOld, kNew, henabled, ?_, ?_⟩
  · rw [← hold]
    calc
      oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          oldProjection rest := holdPrefix
      _ = (alpha.map inactive ++
            [inactive .dollar, active oldFocus, inactive Z]) ++
          beta.map inactive ++ List.replicate kOld none := by
        rw [holdRest]
        simp [List.append_assoc]
  · rw [← hnew]
    calc
      newProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          newProjection rest := hnewPrefix
      _ = (alpha.map inactive ++ [inactive .dollar, active Z]) ++
          beta.map inactive ++ List.replicate kNew none := by
        rw [hnewRest]
        simp [List.append_assoc]

public theorem workTraceAccepts_matchTerminal_sound
    {g : IndexedGrammar T} [Fintype g.nt] {a : T}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.matchTerminal a) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.matchTerminal a) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.matchTerminal a) phase next hist x y ↔
        CertEnabled g (.matchTerminal a) ∧
          deleteOneEdge (fun x => x = active (.terminal a)) phase next hist x y := by
    intro phase next hist x y
    simp [WorkEdge, CertEnabled]
  rcases h.decodeDeleteOne (.terminal a) rfl hshape with
    ⟨alpha, Z, beta, kOld, kNew, _henabled, hold, hnew⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .terminal a, Z :: beta⟩
  let newCursor : WorkCursor g := ⟨alpha ++ [.dollar], Z, beta⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨alpha, Z, beta, rfl, rfl⟩

public theorem workTraceAccepts_eraseIndex_sound
    {g : IndexedGrammar T} [Fintype g.nt] {R : CFlag g} {d : IndexMark}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.eraseIndex R d) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.eraseIndex R d) oldCursor newCursor := by
  have hshape : ∀ (phase next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.eraseIndex R d) phase next hist x y ↔
        CertEnabled g (.eraseIndex R d) ∧
          deleteOneEdge (fun x => x = active (.index R d)) phase next hist x y := by
    intro phase next hist x y
    rfl
  rcases h.decodeDeleteOne (.index R d) rfl hshape with
    ⟨alpha, Z, beta, kOld, kNew, herase, hold, hnew⟩
  let oldCursor : WorkCursor g := ⟨alpha ++ [.dollar], .index R d, Z :: beta⟩
  let newCursor : WorkCursor g := ⟨alpha ++ [.dollar], Z, beta⟩
  refine ⟨oldCursor, newCursor, kOld, kNew, ?_, ?_, ?_⟩
  · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hold
  · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
      List.map_map, Function.comp_def, List.append_assoc] using hnew
  · exact ⟨herase, alpha, Z, beta, rfl, rfl⟩

/-! ## Two-slot right shifts used by pop -/

private theorem WorkTrace.decodePlus2None
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixPlus2)
    (hcarry1 : state.history.old1 = some none)
    (hcarry2 : state.history.old2 = some none)
    (holdEnded : state.oldEnded = true)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    (h : WorkTrace g cert state rows result) :
    oldProjection rows = List.replicate rows.length none ∧
      newProjection rows = List.replicate rows.length none := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons state old new next rows result hedge htail ih =>
      have hold : old = none := by
        rcases hedge.2.2.1 with hfalse | hnone
        · simp [holdEnded] at hfalse
        · exact hnone
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, _holdInactive, _hnewInactive, hshift⟩
      have hnew : new = none := by simpa [hcarry2] using hshift.symm
      subst old
      subst new
      rcases ih rfl (by simp [advanceWorkState, updateHistory, hcarry1])
          (by simp [advanceWorkState, updateHistory, hcarry1])
          (by simp [advanceWorkState]) with ⟨holdTail, hnewTail⟩
      constructor
      · simp only [oldProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, holdTail⟩
      · simp only [newProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, hnewTail⟩

private theorem WorkTrace.decodePlus2Mixed
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (z : WorkSym g)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixPlus2)
    (hcarry1 : state.history.old1 = some none)
    (hcarry2 : state.history.old2 = some (inactive z))
    (holdEnded : state.oldEnded = true)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ k,
      oldProjection rows = List.replicate (k + 1) none ∧
      newProjection rows = inactive z :: List.replicate k none := by
  cases h with
  | nil =>
      simp [workScanDone, hphase, lastTwoOldNone, hcarry1, hcarry2, inactive] at hdone
  | @cons state old new next rows result hedge htail =>
      have hold : old = none := by
        rcases hedge.2.2.1 with hfalse | hnone
        · simp [holdEnded] at hfalse
        · exact hnone
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, _holdInactive, _hnewInactive, hshift⟩
      have hnew : new = inactive z := by simpa [hcarry2] using hshift.symm
      subst old
      subst new
      have hnone := htail.decodePlus2None rfl (by
        simp [advanceWorkState, updateHistory]) (by
        simp [advanceWorkState, updateHistory, hcarry1])
        (by simp [advanceWorkState]) hsuffix
      rcases hnone with ⟨holdTail, hnewTail⟩
      refine ⟨rows.length, ?_, ?_⟩
      · simpa [oldProjection, List.replicate_succ] using
          congrArg (fun xs => none :: xs) holdTail
      · simpa [newProjection] using
          congrArg (fun xs => inactive z :: xs) hnewTail

private theorem WorkTrace.decodePlus2Some
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (z₀ z₁ : WorkSym g)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixPlus2)
    (hcarry1 : state.history.old1 = some (inactive z₁))
    (hcarry2 : state.history.old2 = some (inactive z₀))
    (holdEnded : state.oldEnded = false)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g)) (k : ℕ),
      oldProjection rows = beta.map inactive ++ List.replicate (k + 2) none ∧
      newProjection rows = inactive z₀ :: inactive z₁ ::
        beta.map inactive ++ List.replicate k none := by
  induction h generalizing z₀ z₁ with
  | nil =>
      have : False := by
        simp [workScanDone, hphase, lastTwoOldNone, hcarry1, hcarry2, inactive] at hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, holdInactive, _hnewInactive, hshift⟩
      have hnew : new = inactive z₀ := by simpa [hcarry2] using hshift.symm
      subst new
      cases old with
      | none =>
          have hmixed := htail.decodePlus2Mixed z₁ rfl (by
            simp [advanceWorkState, updateHistory]) (by
            simp [advanceWorkState, updateHistory, hcarry1])
            (by simp [advanceWorkState]) hsuffix hdone
          rcases hmixed with ⟨k, holdTail, hnewTail⟩
          refine ⟨[], k, ?_, ?_⟩
          · simpa [oldProjection, List.replicate_succ] using
              congrArg (fun xs => none :: xs) holdTail
          · simpa [newProjection] using
              congrArg (fun xs => inactive z₀ :: xs) hnewTail
      | some slot =>
          cases slot with
          | mk activeFlag symbol =>
              simp [InactiveOpt] at holdInactive
              subst activeFlag
              rcases ih z₁ symbol rfl (by
                  simp [advanceWorkState, updateHistory, inactive]) (by
                  simp [advanceWorkState, updateHistory, hcarry1])
                  (by simpa [advanceWorkState, inactive, holdEnded]) hdone with
                ⟨beta, k, holdTail, hnewTail⟩
              refine ⟨symbol :: beta, k, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_cons]
                simpa [inactive] using
                  congrArg (fun xs => inactive symbol :: xs) holdTail
              · simp only [newProjection, List.map_cons, List.map_cons]
                simpa [inactive] using
                  congrArg (fun xs => inactive z₀ :: xs) hnewTail

private theorem WorkTrace.decodeInsertTwoAfterStage2
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (newFocus : WorkSym g)
    (hstage2Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage2 next hist old new →
        next = .stage3 ∧ InactiveOpt old ∧ new = active newFocus)
    (hstage3Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage3 next hist old new →
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    {stage result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hstage : stage.phase = .stage2)
    (h : WorkTrace g cert stage rows result)
    (hdone : workScanDone result = true) :
    ∃ (gamma : List (WorkSym g)) (k : ℕ),
      oldProjection rows = gamma.map inactive ++ List.replicate (k + 2) none ∧
      newProjection rows = active newFocus :: inactive .close ::
        gamma.map inactive ++ List.replicate k none := by
  cases h with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage carry₀ new₀ next₀ rows₀ result hedge₀ tail₀ =>
      have he₀ := hstage2Edge next₀ stage.history carry₀ new₀ (by
        simpa [hstage] using hedge₀.2.2.2.2)
      rcases he₀ with ⟨rfl, hcarry₀, rfl⟩
      cases tail₀ with
      | nil => simp [workScanDone, advanceWorkState] at hdone
      | @cons _stage3 carry₁ new₁ next₁ suffixRows result hedge₁ htail =>
          let stage3 := advanceWorkState stage carry₀ (active newFocus) .stage3
          have he₁ := hstage3Edge next₁ stage3.history carry₁ new₁ (by
            simpa [stage3, advanceWorkState] using hedge₁.2.2.2.2)
          rcases he₁ with ⟨rfl, hcarry₁, rfl⟩
          cases carry₀ with
          | none =>
              have hcarry₁none : carry₁ = none := by
                rcases hedge₁.2.2.1 with hfalse | hnone
                · simp [stage3, advanceWorkState] at hfalse
                · exact hnone
              subst carry₁
              have hnone := htail.decodePlus2None rfl (by
                simp [stage3, advanceWorkState, updateHistory]) (by
                simp [stage3, advanceWorkState, updateHistory])
                (by simp [stage3, advanceWorkState]) hsuffix
              rcases hnone with ⟨holdTail, hnewTail⟩
              refine ⟨[], suffixRows.length, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_nil, List.nil_append]
                have holdTail' : suffixRows.map (fun r => r.1) =
                    List.replicate suffixRows.length none := by
                  simpa [oldProjection] using holdTail
                rw [holdTail', show suffixRows.length + 2 =
                  (suffixRows.length + 1) + 1 by omega, List.replicate_succ,
                  List.replicate_succ]
              · simp only [newProjection, List.map_cons, List.map_nil, List.nil_append]
                have hnewTail' : suffixRows.map (fun r => r.2.1) =
                    List.replicate suffixRows.length none := by
                  simpa [newProjection] using hnewTail
                rw [hnewTail']
                rfl
          | some slot₀ =>
              cases slot₀ with
              | mk active₀ z₀ =>
                  simp [InactiveOpt] at hcarry₀
                  subst active₀
                  have hstageOldEnded : stage.oldEnded = false := by
                    rcases hedge₀.2.2.1 with hfalse | hnone
                    · exact hfalse
                    · simp [inactive] at hnone
                  cases carry₁ with
                  | none =>
                      have hmixed := htail.decodePlus2Mixed z₀ rfl (by
                        simp [stage3, advanceWorkState, updateHistory]) (by
                        simp [stage3, advanceWorkState, updateHistory, inactive])
                        (by simp [stage3, advanceWorkState]) hsuffix hdone
                      rcases hmixed with ⟨k, holdTail, hnewTail⟩
                      refine ⟨[z₀], k, ?_, ?_⟩
                      · simpa [oldProjection, inactive, List.replicate_succ] using
                          congrArg (fun xs => inactive z₀ :: none :: xs) holdTail
                      · simpa [newProjection, inactive] using
                          congrArg (fun xs => active newFocus :: inactive .close :: xs)
                            hnewTail
                  | some slot₁ =>
                      cases slot₁ with
                      | mk active₁ z₁ =>
                          simp [InactiveOpt] at hcarry₁
                          subst active₁
                          have hsome := htail.decodePlus2Some z₀ z₁ rfl (by
                            simp [stage3, advanceWorkState, updateHistory, inactive]) (by
                            simp [stage3, advanceWorkState, updateHistory, inactive])
                            (by simp [stage3, advanceWorkState, inactive, hstageOldEnded])
                            hsuffix hdone
                          rcases hsome with ⟨gamma, k, holdTail, hnewTail⟩
                          refine ⟨z₀ :: z₁ :: gamma, k, ?_, ?_⟩
                          · simpa [oldProjection, inactive] using
                              congrArg (fun xs => inactive z₀ :: inactive z₁ :: xs)
                                holdTail
                          · simpa [newProjection, inactive] using
                              congrArg (fun xs => active newFocus :: inactive .close :: xs)
                                hnewTail

private theorem WorkTrace.false_of_popBeta_new1_none
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {R : CFlag g} {d : IndexMark}
    (hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .popBeta next hist old new →
        (next = .popBeta ∧ InactiveNonIndex old ∧
          hist.new1 = some old ∧ InactiveOpt new) ∨
        (next = .stage2 ∧ old = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧
          new = inactive .dollar))
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .popBeta)
    (hhist : state.history.new1 = some none)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) : False := by
  cases h with
  | nil => simpa [workScanDone, hphase] using hdone
  | @cons state old new next rows result hedge htail =>
      have hc := hpop next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases hc with hloop | hboundary
      · rcases hloop with ⟨_rfl, _hnonindex, hprev, _hnew⟩
        have : old = none := by simpa [hhist] using hprev.symm
        subst old
        rcases _hnonindex with ⟨z, hz, _⟩
        simp [inactive] at hz
      · rcases hboundary with ⟨_rfl, _hold, hprev, _hnew⟩
        simp [hhist, inactive] at hprev

private theorem WorkTrace.decodePopBeta
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (R : CFlag g) (d : IndexMark) (seed : WorkSym g)
    (hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .popBeta next hist old new →
        (next = .popBeta ∧ InactiveNonIndex old ∧
          hist.new1 = some old ∧ InactiveOpt new) ∨
        (next = .stage2 ∧ old = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧
          new = inactive .dollar))
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .popBeta)
    (hhist : state.history.new1 = some (inactive seed))
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g))
      (rest : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
      (stage2 : WorkScanState g),
      IndexFree beta ∧
      oldProjection rows = beta.map inactive ++ [inactive (.index R d)] ++
        oldProjection rest ∧
      inactive seed :: newProjection rows = beta.map inactive ++
        [inactive (.index R d.markUsed), inactive .dollar] ++
          newProjection rest ∧
      stage2.phase = .stage2 ∧ WorkTrace g cert stage2 rest result := by
  induction h generalizing seed with
  | nil =>
      have : False := by simpa [workScanDone, hphase] using hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have hc := hpop next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases hc with hloop | hboundary
      · rcases hloop with ⟨rfl, hnonindex, hprev, hnewInactive⟩
        have hold : old = inactive seed := by simpa [hhist] using hprev.symm
        subst old
        cases new with
        | none =>
            exact (htail.false_of_popBeta_new1_none hpop rfl (by
              simp [advanceWorkState, updateHistory]) hdone).elim
        | some slot =>
            cases slot with
            | mk activeFlag symbol =>
                simp [InactiveOpt] at hnewInactive
                subst activeFlag
                rcases ih symbol rfl (by
                    simp [advanceWorkState, updateHistory, inactive]) hdone with
                  ⟨beta, rest, stage2, hfree, holdRows, hnewRows, hstage2, hrest⟩
                refine ⟨seed :: beta, rest, stage2, ?_, ?_, ?_, hstage2, hrest⟩
                · intro R' d' hmem
                  simp only [List.mem_cons] at hmem
                  rcases hmem with hseed | htailMem
                  · subst seed
                    rcases hnonindex with ⟨z, hz, hzNonIndex⟩
                    have : z = .index R' d' := by
                      simpa [inactive] using Option.some.inj hz.symm
                    subst z
                    have hbad : (true : Bool) = false := by
                      simpa [WorkSym.isIndex] using hzNonIndex
                    exact Bool.noConfusion hbad
                  · exact hfree R' d' htailMem
                · simpa [oldProjection, inactive, List.append_assoc] using
                    congrArg (fun xs => inactive seed :: xs) holdRows
                · simpa [newProjection, inactive, List.append_assoc] using
                    congrArg (fun xs => inactive seed :: inactive symbol :: xs) hnewRows
      · rcases hboundary with ⟨rfl, rfl, hprev, rfl⟩
        have hseed : seed = .index R d.markUsed := by
          have heq : some (inactive seed) =
              some (inactive (.index R d.markUsed)) := hhist.symm.trans hprev
          simpa [inactive] using heq
        subst seed
        refine ⟨[], rows,
          advanceWorkState state (inactive (.index R d)) (inactive .dollar) .stage2,
          ?_, ?_, ?_, rfl, htail⟩
        · intro R' d' hmem
          simp at hmem
        · simp [oldProjection]
        · simp [newProjection]

private theorem WorkTrace.decodePopAfterStage1
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (R : CFlag g) (d : IndexMark) (A : g.nt) (newFocus : WorkSym g)
    (hstage1Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage1 next hist old new →
        next = .popBeta ∧ old = active (.live A) ∧ InactiveSome new)
    (hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .popBeta next hist old new →
        (next = .popBeta ∧ InactiveNonIndex old ∧
          hist.new1 = some old ∧ InactiveOpt new) ∨
        (next = .stage2 ∧ old = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧
          new = inactive .dollar))
    (hstage2Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage2 next hist old new →
        next = .stage3 ∧ InactiveOpt old ∧ new = active newFocus)
    (hstage3Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage3 next hist old new →
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    {stage result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hstage : stage.phase = .stage1)
    (h : WorkTrace g cert stage rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta gamma : List (WorkSym g)) (k : ℕ),
      IndexFree beta ∧
      oldProjection rows = active (.live A) :: beta.map inactive ++
        inactive (.index R d) :: gamma.map inactive ++ List.replicate (k + 2) none ∧
      newProjection rows = beta.map inactive ++
        [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
          inactive .close] ++ gamma.map inactive ++ List.replicate k none := by
  cases h with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage old₀ new₀ next₀ rows₀ result hedge₀ htail₀ =>
      have he₀ := hstage1Edge next₀ stage.history old₀ new₀ (by
        simpa [hstage] using hedge₀.2.2.2.2)
      rcases he₀ with ⟨rfl, rfl, seed, rfl⟩
      let popState := advanceWorkState stage (active (.live A)) (inactive seed) .popBeta
      rcases htail₀.decodePopBeta R d seed hpop rfl (by
          simp [popState, advanceWorkState, updateHistory]) hdone with
        ⟨beta, rest, stage2, hfree, holdBeta, hnewBeta, hstage2, hrest⟩
      rcases hrest.decodeInsertTwoAfterStage2 newFocus hstage2Edge hstage3Edge hsuffix
          hstage2 hdone with ⟨gamma, k, holdGamma, hnewGamma⟩
      refine ⟨beta, gamma, k, hfree, ?_, ?_⟩
      · calc
          oldProjection ((active (.live A), inactive seed, .popBeta) :: rows₀) =
              active (.live A) :: oldProjection rows₀ := rfl
          _ = active (.live A) :: (beta.map inactive ++
              [inactive (.index R d)] ++ oldProjection rest) := by rw [holdBeta]
          _ = active (.live A) :: beta.map inactive ++ inactive (.index R d) ::
              gamma.map inactive ++ List.replicate (k + 2) none := by
            rw [holdGamma]
            simp [List.append_assoc]
      · calc
          newProjection ((active (.live A), inactive seed, .popBeta) :: rows₀) =
              inactive seed :: newProjection rows₀ := rfl
          _ = beta.map inactive ++
              [inactive (.index R d.markUsed), inactive .dollar] ++
                newProjection rest := hnewBeta
          _ = beta.map inactive ++
              [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
                inactive .close] ++ gamma.map inactive ++ List.replicate k none := by
            rw [hnewGamma]
            simp [List.append_assoc]

private theorem WorkTraceAccepts.decodePop
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (R : CFlag g) (d : IndexMark) (A : g.nt) (newFocus : WorkSym g)
    (hproductive : cert.productive = false)
    (hstage1Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage1 next hist old new →
        next = .popBeta ∧ old = active (.live A) ∧ InactiveSome new)
    (hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .popBeta next hist old new →
        (next = .popBeta ∧ InactiveNonIndex old ∧
          hist.new1 = some old ∧ InactiveOpt new) ∨
        (next = .stage2 ∧ old = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧
          new = inactive .dollar))
    (hstage2Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage2 next hist old new →
        next = .stage3 ∧ InactiveOpt old ∧ new = active newFocus)
    (hstage3Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage3 next hist old new →
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (alpha beta gamma : List (WorkSym g)) (k : ℕ),
      CertEnabled g cert ∧ IndexFree beta ∧
      old = (alpha.map inactive ++ [inactive .dollar, active (.live A)]) ++
        beta.map inactive ++ inactive (.index R d) :: gamma.map inactive ++
          List.replicate (k + 2) none ∧
      new = (alpha.map inactive ++ [inactive .dollar]) ++ beta.map inactive ++
        [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
          inactive .close] ++ gamma.map inactive ++ List.replicate k none := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitNonproductivePrefix hproductive rfl hdone with
    ⟨alpha, rest, stage, henabled, holdPrefix, hnewPrefix, hstage, hrest⟩
  rcases hrest.decodePopAfterStage1 R d A newFocus hstage1Edge hpop hstage2Edge
      hstage3Edge hsuffix hstage hdone with
    ⟨beta, gamma, k, hfree, holdRest, hnewRest⟩
  refine ⟨alpha, beta, gamma, k, henabled, hfree, ?_, ?_⟩
  · rw [← hold]
    calc
      oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          oldProjection rest := holdPrefix
      _ = (alpha.map inactive ++ [inactive .dollar, active (.live A)]) ++
          beta.map inactive ++ inactive (.index R d) :: gamma.map inactive ++
            List.replicate (k + 2) none := by
        rw [holdRest]
        simp [List.append_assoc]
  · rw [← hnew]
    calc
      newProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          newProjection rest := hnewPrefix
      _ = (alpha.map inactive ++ [inactive .dollar]) ++ beta.map inactive ++
          [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
            inactive .close] ++ gamma.map inactive ++ List.replicate k none := by
        rw [hnewRest]
        simp [List.append_assoc]

/-! The ephemeral implementation of a pop replaces the focus and erases the immediately
adjacent index.  It deliberately uses `minus1First`, distinct from the framed pop's `stage2`,
so an accepting scan cannot splice the two implementations. -/

private theorem WorkTrace.decodePopEitherAfterStage1
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (R : CFlag g) (d : IndexMark) (A : g.nt) (newFocus : WorkSym g)
    (hstage1Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage1 next hist old new →
        (next = .popBeta ∧ old = active (.live A) ∧ InactiveSome new) ∨
        (next = .minus1First ∧ old = active (.live A) ∧
          new = active newFocus))
    (hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .popBeta next hist old new →
        (next = .popBeta ∧ InactiveNonIndex old ∧
          hist.new1 = some old ∧ InactiveOpt new) ∨
        (next = .stage2 ∧ old = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧
          new = inactive .dollar))
    (hstage2Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage2 next hist old new →
        next = .stage3 ∧ InactiveOpt old ∧ new = active newFocus)
    (hstage3Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage3 next hist old new →
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close)
    (hplus : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    (hminusFirst : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .minus1First next hist old new →
        next = .suffixMinus1 ∧ old = inactive (.index R d) ∧ InactiveOpt new)
    (hminus : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus1 next hist old new →
        next = .suffixMinus1 ∧ minus1Suffix hist old new)
    {stage result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hstage : stage.phase = .stage1)
    (h : WorkTrace g cert stage rows result)
    (hdone : workScanDone result = true) :
    (∃ (beta gamma : List (WorkSym g)) (k : ℕ),
      IndexFree beta ∧
      oldProjection rows = active (.live A) :: beta.map inactive ++
        inactive (.index R d) :: gamma.map inactive ++ List.replicate (k + 2) none ∧
      newProjection rows = beta.map inactive ++
        [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
          inactive .close] ++ gamma.map inactive ++ List.replicate k none) ∨
    (∃ (gamma : List (WorkSym g)) (k : ℕ),
      oldProjection rows = active (.live A) :: inactive (.index R d) ::
        gamma.map inactive ++ List.replicate k none ∧
      newProjection rows = active newFocus :: gamma.map inactive ++
        List.replicate (k + 1) none) := by
  cases h with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage old₀ new₀ next₀ rows₀ result hedge₀ htail₀ =>
      have he₀ := hstage1Edge next₀ stage.history old₀ new₀ (by
        simpa [hstage] using hedge₀.2.2.2.2)
      rcases he₀ with hframed | herase
      · rcases hframed with ⟨rfl, rfl, seed, rfl⟩
        let popState :=
          advanceWorkState stage (active (.live A)) (inactive seed) .popBeta
        rcases htail₀.decodePopBeta R d seed hpop rfl (by
            simp [popState, advanceWorkState, updateHistory]) hdone with
          ⟨beta, rest, stage2, hfree, holdBeta, hnewBeta, hstage2, hrest⟩
        rcases hrest.decodeInsertTwoAfterStage2 newFocus hstage2Edge hstage3Edge hplus
            hstage2 hdone with ⟨gamma, k, holdGamma, hnewGamma⟩
        refine Or.inl ⟨beta, gamma, k, hfree, ?_, ?_⟩
        · calc
            oldProjection ((active (.live A), inactive seed, .popBeta) :: rows₀) =
                active (.live A) :: oldProjection rows₀ := rfl
            _ = active (.live A) :: (beta.map inactive ++
                [inactive (.index R d)] ++ oldProjection rest) := by rw [holdBeta]
            _ = active (.live A) :: beta.map inactive ++ inactive (.index R d) ::
                gamma.map inactive ++ List.replicate (k + 2) none := by
              rw [holdGamma]
              simp [List.append_assoc]
        · calc
            newProjection ((active (.live A), inactive seed, .popBeta) :: rows₀) =
                inactive seed :: newProjection rows₀ := rfl
            _ = beta.map inactive ++
                [inactive (.index R d.markUsed), inactive .dollar] ++
                  newProjection rest := hnewBeta
            _ = beta.map inactive ++
                [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
                  inactive .close] ++ gamma.map inactive ++ List.replicate k none := by
              rw [hnewGamma]
              simp [List.append_assoc]
      · rcases herase with ⟨rfl, rfl, rfl⟩
        have hstageNewEnded : stage.newEnded = false := by
          rcases hedge₀.2.2.2.1 with hfalse | hnone
          · exact hfalse
          · simp [active] at hnone
        let minusState :=
          advanceWorkState stage (active (.live A)) (active newFocus) .minus1First
        cases htail₀ with
        | nil => simp [workScanDone, minusState, advanceWorkState] at hdone
        | @cons _minus old₁ new₁ next₁ suffixRows result hedge₁ htail =>
            have he₁ := hminusFirst next₁ minusState.history old₁ new₁ (by
              simpa [minusState, advanceWorkState] using hedge₁.2.2.2.2)
            rcases he₁ with ⟨rfl, rfl, hnewInactive⟩
            cases new₁ with
            | none =>
                have hnone := htail.decodeMinus1None rfl (by
                  simp [minusState, advanceWorkState, updateHistory])
                  (by simp [minusState, advanceWorkState]) hminus
                rcases hnone with ⟨holdTail, hnewTail⟩
                have holdTail' : suffixRows.map (fun r => r.1) =
                    List.replicate suffixRows.length none := by
                  simpa [oldProjection] using holdTail
                have hnewTail' : suffixRows.map (fun r => r.2.1) =
                    List.replicate suffixRows.length none := by
                  simpa [newProjection] using hnewTail
                refine Or.inr ⟨[], suffixRows.length, ?_, ?_⟩
                · simp only [oldProjection, List.map_cons, List.map_nil,
                  List.nil_append]
                  rw [holdTail']
                  simp
                · simp only [newProjection, List.map_cons, List.map_nil,
                  List.nil_append]
                  rw [hnewTail', List.replicate_succ]
                  simp
            | some slot =>
                cases slot with
                | mk activeFlag symbol =>
                    simp [InactiveOpt] at hnewInactive
                    subst activeFlag
                    have hdecoded := htail.decodeMinus1Some symbol rfl (by
                      simp [minusState, advanceWorkState, updateHistory, inactive])
                      (by simp [minusState, advanceWorkState, inactive, active,
                        hstageNewEnded]) hminus hdone
                    rcases hdecoded with ⟨gamma, k, holdTail, hnewTail⟩
                    have holdTail' : suffixRows.map (fun r => r.1) =
                        inactive symbol :: gamma.map inactive ++ List.replicate k none := by
                      simpa [oldProjection] using holdTail
                    have hnewTail' : suffixRows.map (fun r => r.2.1) =
                        gamma.map inactive ++ List.replicate (k + 1) none := by
                      simpa [newProjection] using hnewTail
                    refine Or.inr ⟨symbol :: gamma, k, ?_, ?_⟩
                    · simp only [oldProjection, List.map_cons]
                      rw [holdTail']
                      simp
                    · simp only [newProjection, List.map_cons]
                      rw [hnewTail']
                      simp [inactive]

private theorem WorkTraceAccepts.decodePopEither
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (R : CFlag g) (d : IndexMark) (A : g.nt) (newFocus : WorkSym g)
    (hproductive : cert.productive = false)
    (hstage1Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage1 next hist old new →
        (next = .popBeta ∧ old = active (.live A) ∧ InactiveSome new) ∨
        (next = .minus1First ∧ old = active (.live A) ∧
          new = active newFocus))
    (hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .popBeta next hist old new →
        (next = .popBeta ∧ InactiveNonIndex old ∧
          hist.new1 = some old ∧ InactiveOpt new) ∨
        (next = .stage2 ∧ old = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧
          new = inactive .dollar))
    (hstage2Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage2 next hist old new →
        next = .stage3 ∧ InactiveOpt old ∧ new = active newFocus)
    (hstage3Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage3 next hist old new →
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close)
    (hplus : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixPlus2 next hist old new →
        next = .suffixPlus2 ∧ plus2Suffix hist old new)
    (hminusFirst : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .minus1First next hist old new →
        next = .suffixMinus1 ∧ old = inactive (.index R d) ∧ InactiveOpt new)
    (hminus : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus1 next hist old new →
        next = .suffixMinus1 ∧ minus1Suffix hist old new)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    (∃ (alpha beta gamma : List (WorkSym g)) (k : ℕ),
      CertEnabled g cert ∧ IndexFree beta ∧
      old = (alpha.map inactive ++ [inactive .dollar, active (.live A)]) ++
        beta.map inactive ++ inactive (.index R d) :: gamma.map inactive ++
          List.replicate (k + 2) none ∧
      new = (alpha.map inactive ++ [inactive .dollar]) ++ beta.map inactive ++
        [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
          inactive .close] ++ gamma.map inactive ++ List.replicate k none) ∨
    (∃ (alpha gamma : List (WorkSym g)) (k : ℕ),
      CertEnabled g cert ∧
      old = (alpha.map inactive ++
          [inactive .dollar, active (.live A), inactive (.index R d)]) ++
        gamma.map inactive ++ List.replicate k none ∧
      new = (alpha.map inactive ++ [inactive .dollar, active newFocus]) ++
        gamma.map inactive ++ List.replicate (k + 1) none) := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitNonproductivePrefix hproductive rfl hdone with
    ⟨alpha, rest, stage, henabled, holdPrefix, hnewPrefix, hstage, hrest⟩
  rcases hrest.decodePopEitherAfterStage1 R d A newFocus hstage1Edge hpop
      hstage2Edge hstage3Edge hplus hminusFirst hminus hstage hdone with
    hframed | herase
  · rcases hframed with ⟨beta, gamma, k, hfree, holdRest, hnewRest⟩
    refine Or.inl ⟨alpha, beta, gamma, k, henabled, hfree, ?_, ?_⟩
    · rw [← hold]
      calc
        oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
            oldProjection rest := holdPrefix
        _ = (alpha.map inactive ++ [inactive .dollar, active (.live A)]) ++
            beta.map inactive ++ inactive (.index R d) :: gamma.map inactive ++
              List.replicate (k + 2) none := by
          rw [holdRest]
          simp [List.append_assoc]
    · rw [← hnew]
      calc
        newProjection rows = alpha.map inactive ++ [inactive .dollar] ++
            newProjection rest := hnewPrefix
        _ = (alpha.map inactive ++ [inactive .dollar]) ++ beta.map inactive ++
            [inactive (.index R d.markUsed), inactive .dollar, active newFocus,
              inactive .close] ++ gamma.map inactive ++ List.replicate k none := by
          rw [hnewRest]
          simp [List.append_assoc]
  · rcases herase with ⟨gamma, k, holdRest, hnewRest⟩
    refine Or.inr ⟨alpha, gamma, k, henabled, ?_, ?_⟩
    · rw [← hold]
      calc
        oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
            oldProjection rest := holdPrefix
        _ = (alpha.map inactive ++
              [inactive .dollar, active (.live A), inactive (.index R d)]) ++
            gamma.map inactive ++ List.replicate k none := by
          rw [holdRest]
          simp [List.append_assoc]
    · rw [← hnew]
      calc
        newProjection rows = alpha.map inactive ++ [inactive .dollar] ++
            newProjection rest := hnewPrefix
        _ = (alpha.map inactive ++ [inactive .dollar, active newFocus]) ++
            gamma.map inactive ++ List.replicate (k + 1) none := by
          rw [hnewRest]
          simp [List.append_assoc]

private theorem popPlain_stage1_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .stage1 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        ((next = .popBeta ∧ old = active (.live A) ∧ InactiveSome new) ∨
          (next = .minus1First ∧ old = active (.live A) ∧
            new = active (.plain B))) := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popPlain_popBeta_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .popBeta next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        ((next = .popBeta ∧ InactiveNonIndex old ∧
            hist.new1 = some old ∧ InactiveOpt new) ∨
          (next = .stage2 ∧ old = inactive (.index R d) ∧
            hist.new1 = some (inactive (.index R d.markUsed)) ∧
            new = inactive .dollar)) := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popPlain_stage2_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .stage2 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        next = .stage3 ∧ InactiveOpt old ∧ new = active (.plain B) := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popPlain_stage3_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .stage3 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popPlain_suffixPlus2_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .suffixPlus2 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        next = .suffixPlus2 ∧ plus2Suffix hist old new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popPlain_minus1First_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .minus1First next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧ next = .suffixMinus1 ∧
        old = inactive (.index R d) ∧ InactiveOpt new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popPlain_suffixMinus1_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .suffixMinus1 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧ next = .suffixMinus1 ∧
        minus1Suffix hist old new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

public theorem workTraceAccepts_popPlain_sound
    {g : IndexedGrammar T} [Fintype g.nt]
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.popPlain R d A B) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.popPlain R d A B) oldCursor newCursor := by
  have hstage1 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popPlain R d A B) .stage1 next hist x y →
        (next = .popBeta ∧ x = active (.live A) ∧ InactiveSome y) ∨
        (next = .minus1First ∧ x = active (.live A) ∧
          y = active (.plain B)) := by
    intro next hist x y hedge
    exact (popPlain_stage1_iff g R d A B next hist x y).mp hedge |>.2
  have hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popPlain R d A B) .popBeta next hist x y →
        (next = .popBeta ∧ InactiveNonIndex x ∧ hist.new1 = some x ∧ InactiveOpt y) ∨
        (next = .stage2 ∧ x = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧ y = inactive .dollar) := by
    intro next hist x y hedge
    exact (popPlain_popBeta_iff g R d A B next hist x y).mp hedge |>.2
  have hstage2 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popPlain R d A B) .stage2 next hist x y →
        next = .stage3 ∧ InactiveOpt x ∧ y = active (.plain B) := by
    intro next hist x y hedge
    exact (popPlain_stage2_iff g R d A B next hist x y).mp hedge |>.2
  have hstage3 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popPlain R d A B) .stage3 next hist x y →
        next = .suffixPlus2 ∧ InactiveOpt x ∧ y = inactive .close := by
    intro next hist x y hedge
    exact (popPlain_stage3_iff g R d A B next hist x y).mp hedge |>.2
  have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popPlain R d A B) .suffixPlus2 next hist x y →
        next = .suffixPlus2 ∧ plus2Suffix hist x y := by
    intro next hist x y hedge
    exact (popPlain_suffixPlus2_iff g R d A B next hist x y).mp hedge |>.2
  have hminusFirst : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popPlain R d A B) .minus1First next hist x y →
        next = .suffixMinus1 ∧ x = inactive (.index R d) ∧ InactiveOpt y := by
    intro next hist x y hedge
    exact (popPlain_minus1First_iff g R d A B next hist x y).mp hedge |>.2
  have hminus : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popPlain R d A B) .suffixMinus1 next hist x y →
        next = .suffixMinus1 ∧ minus1Suffix hist x y := by
    intro next hist x y hedge
    exact (popPlain_suffixMinus1_iff g R d A B next hist x y).mp hedge |>.2
  rcases h.decodePopEither R d A (.plain B) rfl hstage1 hpop hstage2 hstage3
      hsuffix hminusFirst hminus with hframed | herase
  · rcases hframed with ⟨alpha, beta, gamma, k, hedge, hfree, hold, hnew⟩
    let oldCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar], .live A, beta ++ .index R d :: gamma⟩
    let newCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .plain B, .close :: gamma⟩
    refine ⟨oldCursor, newCursor, k + 2, k, ?_, ?_, ?_⟩
    · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hold
    · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hnew
    · exact ⟨hedge, Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩
  · rcases herase with ⟨alpha, gamma, k, hedge, hold, hnew⟩
    let oldCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩
    let newCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar], .plain B, gamma⟩
    refine ⟨oldCursor, newCursor, k, k + 1, ?_, ?_, ?_⟩
    · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hold
    · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hnew
    · exact ⟨hedge, Or.inr ⟨alpha, gamma, rfl, rfl⟩⟩

private theorem popLive_stage1_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popLive R d A B) .stage1 next hist old new ↔
      CertEnabled g (.popLive R d A B) ∧
        ((next = .popBeta ∧ old = active (.live A) ∧ InactiveSome new) ∨
          (next = .minus1First ∧ old = active (.live A) ∧
            new = active (.live B))) := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popLive_popBeta_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popLive R d A B) .popBeta next hist old new ↔
      CertEnabled g (.popLive R d A B) ∧
        ((next = .popBeta ∧ InactiveNonIndex old ∧
            hist.new1 = some old ∧ InactiveOpt new) ∨
          (next = .stage2 ∧ old = inactive (.index R d) ∧
            hist.new1 = some (inactive (.index R d.markUsed)) ∧
            new = inactive .dollar)) := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popLive_stage2_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popLive R d A B) .stage2 next hist old new ↔
      CertEnabled g (.popLive R d A B) ∧
        next = .stage3 ∧ InactiveOpt old ∧ new = active (.live B) := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popLive_stage3_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popLive R d A B) .stage3 next hist old new ↔
      CertEnabled g (.popLive R d A B) ∧
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popLive_suffixPlus2_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popLive R d A B) .suffixPlus2 next hist old new ↔
      CertEnabled g (.popLive R d A B) ∧
        next = .suffixPlus2 ∧ plus2Suffix hist old new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popLive_minus1First_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popLive R d A B) .minus1First next hist old new ↔
      CertEnabled g (.popLive R d A B) ∧ next = .suffixMinus1 ∧
        old = inactive (.index R d) ∧ InactiveOpt new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

private theorem popLive_suffixMinus1_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popLive R d A B) .suffixMinus1 next hist old new ↔
      CertEnabled g (.popLive R d A B) ∧ next = .suffixMinus1 ∧
        minus1Suffix hist old new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge, and_assoc]

public theorem workTraceAccepts_popLive_sound
    {g : IndexedGrammar T} [Fintype g.nt]
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g (.popLive R d A B) old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g (.popLive R d A B) oldCursor newCursor := by
  have hstage1 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popLive R d A B) .stage1 next hist x y →
        (next = .popBeta ∧ x = active (.live A) ∧ InactiveSome y) ∨
        (next = .minus1First ∧ x = active (.live A) ∧
          y = active (.live B)) := by
    intro next hist x y hedge
    exact (popLive_stage1_iff g R d A B next hist x y).mp hedge |>.2
  have hpop : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popLive R d A B) .popBeta next hist x y →
        (next = .popBeta ∧ InactiveNonIndex x ∧ hist.new1 = some x ∧ InactiveOpt y) ∨
        (next = .stage2 ∧ x = inactive (.index R d) ∧
          hist.new1 = some (inactive (.index R d.markUsed)) ∧ y = inactive .dollar) := by
    intro next hist x y hedge
    exact (popLive_popBeta_iff g R d A B next hist x y).mp hedge |>.2
  have hstage2 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popLive R d A B) .stage2 next hist x y →
        next = .stage3 ∧ InactiveOpt x ∧ y = active (.live B) := by
    intro next hist x y hedge
    exact (popLive_stage2_iff g R d A B next hist x y).mp hedge |>.2
  have hstage3 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popLive R d A B) .stage3 next hist x y →
        next = .suffixPlus2 ∧ InactiveOpt x ∧ y = inactive .close := by
    intro next hist x y hedge
    exact (popLive_stage3_iff g R d A B next hist x y).mp hedge |>.2
  have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popLive R d A B) .suffixPlus2 next hist x y →
        next = .suffixPlus2 ∧ plus2Suffix hist x y := by
    intro next hist x y hedge
    exact (popLive_suffixPlus2_iff g R d A B next hist x y).mp hedge |>.2
  have hminusFirst : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popLive R d A B) .minus1First next hist x y →
        next = .suffixMinus1 ∧ x = inactive (.index R d) ∧ InactiveOpt y := by
    intro next hist x y hedge
    exact (popLive_minus1First_iff g R d A B next hist x y).mp hedge |>.2
  have hminus : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g (.popLive R d A B) .suffixMinus1 next hist x y →
        next = .suffixMinus1 ∧ minus1Suffix hist x y := by
    intro next hist x y hedge
    exact (popLive_suffixMinus1_iff g R d A B next hist x y).mp hedge |>.2
  rcases h.decodePopEither R d A (.live B) rfl hstage1 hpop hstage2 hstage3
      hsuffix hminusFirst hminus with hframed | herase
  · rcases hframed with ⟨alpha, beta, gamma, k, hedge, hfree, hold, hnew⟩
    let oldCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar], .live A, beta ++ .index R d :: gamma⟩
    let newCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .live B, .close :: gamma⟩
    refine ⟨oldCursor, newCursor, k + 2, k, ?_, ?_, ?_⟩
    · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hold
    · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hnew
    · exact ⟨hedge.1, hedge.2,
        Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩
  · rcases herase with ⟨alpha, gamma, k, hedge, hold, hnew⟩
    let oldCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩
    let newCursor : WorkCursor g :=
      ⟨alpha ++ [.dollar], .live B, gamma⟩
    refine ⟨oldCursor, newCursor, k, k + 1, ?_, ?_, ?_⟩
    · simpa [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hold
    · simpa [newCursor, WorkCursor.slots, inactive, active, List.map_append,
        List.map_map, Function.comp_def, List.append_assoc] using hnew
    · exact ⟨hedge.1, hedge.2, Or.inr ⟨alpha, gamma, rfl, rfl⟩⟩

/-! ## Two-slot left shifts used by frame return -/

private theorem WorkTrace.decodeMinus2None
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixMinus2)
    (hcarry1 : state.history.new1 = some none)
    (hcarry2 : state.history.new2 = some none)
    (hnewEnded : state.newEnded = true)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus2 next hist old new →
        next = .suffixMinus2 ∧ minus2Suffix hist old new)
    (h : WorkTrace g cert state rows result) :
    oldProjection rows = List.replicate rows.length none ∧
      newProjection rows = List.replicate rows.length none := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons state old new next rows result hedge htail ih =>
      have hnew : new = none := by
        rcases hedge.2.2.2.1 with hfalse | hnone
        · simp [hnewEnded] at hfalse
        · exact hnone
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, _holdInactive, _hnewInactive, hshift⟩
      have hold : old = none := by simpa [hcarry2] using hshift.symm
      subst old
      subst new
      rcases ih rfl (by simp [advanceWorkState, updateHistory])
          (by simp [advanceWorkState, updateHistory, hcarry1])
          (by simp [advanceWorkState]) with ⟨holdTail, hnewTail⟩
      constructor
      · simp only [oldProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, holdTail⟩
      · simp only [newProjection, List.map_cons, List.length_cons, List.replicate_succ,
          List.cons.injEq]
        exact ⟨trivial, hnewTail⟩

private theorem WorkTrace.decodeMinus2Mixed
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (z : WorkSym g)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixMinus2)
    (hcarry1 : state.history.new1 = some none)
    (hcarry2 : state.history.new2 = some (inactive z))
    (hnewEnded : state.newEnded = true)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus2 next hist old new →
        next = .suffixMinus2 ∧ minus2Suffix hist old new)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ k,
      oldProjection rows = inactive z :: List.replicate k none ∧
      newProjection rows = List.replicate (k + 1) none := by
  cases h with
  | nil =>
      simp [workScanDone, hphase, lastTwoNewNone, hcarry1, hcarry2, inactive] at hdone
  | @cons state old new next rows result hedge htail =>
      have hnew : new = none := by
        rcases hedge.2.2.2.1 with hfalse | hnone
        · simp [hnewEnded] at hfalse
        · exact hnone
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, _holdInactive, _hnewInactive, hshift⟩
      have hold : old = inactive z := by simpa [hcarry2] using hshift.symm
      subst old
      subst new
      have hnone := htail.decodeMinus2None rfl (by
        simp [advanceWorkState, updateHistory]) (by
        simp [advanceWorkState, updateHistory, hcarry1])
        (by simp [advanceWorkState]) hsuffix
      rcases hnone with ⟨holdTail, hnewTail⟩
      refine ⟨rows.length, ?_, ?_⟩
      · simpa [oldProjection] using
          congrArg (fun xs => inactive z :: xs) holdTail
      · simpa [newProjection, List.replicate_succ] using
          congrArg (fun xs => none :: xs) hnewTail

private theorem WorkTrace.decodeMinus2Some
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (z₀ z₁ : WorkSym g)
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .suffixMinus2)
    (hcarry1 : state.history.new1 = some (inactive z₁))
    (hcarry2 : state.history.new2 = some (inactive z₀))
    (hnewEnded : state.newEnded = false)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus2 next hist old new →
        next = .suffixMinus2 ∧ minus2Suffix hist old new)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g)) (k : ℕ),
      oldProjection rows = inactive z₀ :: inactive z₁ ::
        beta.map inactive ++ List.replicate k none ∧
      newProjection rows = beta.map inactive ++ List.replicate (k + 2) none := by
  induction h generalizing z₀ z₁ with
  | nil =>
      have : False := by
        simp [workScanDone, hphase, lastTwoNewNone, hcarry1, hcarry2, inactive] at hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have he := hsuffix next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases he with ⟨rfl, holdInactive, hnewInactive, hshift⟩
      have hold : old = inactive z₀ := by simpa [hcarry2] using hshift.symm
      subst old
      cases new with
      | none =>
          have hmixed := htail.decodeMinus2Mixed z₁ rfl (by
            simp [advanceWorkState, updateHistory]) (by
            simp [advanceWorkState, updateHistory, hcarry1])
            (by simp [advanceWorkState]) hsuffix hdone
          rcases hmixed with ⟨k, holdTail, hnewTail⟩
          refine ⟨[], k, ?_, ?_⟩
          · simpa [oldProjection] using
              congrArg (fun xs => inactive z₀ :: xs) holdTail
          · simpa [newProjection, List.replicate_succ] using
              congrArg (fun xs => none :: xs) hnewTail
      | some slot =>
          cases slot with
          | mk activeFlag symbol =>
              simp [InactiveOpt] at hnewInactive
              subst activeFlag
              rcases ih z₁ symbol rfl (by
                  simp [advanceWorkState, updateHistory, inactive]) (by
                  simp [advanceWorkState, updateHistory, hcarry1])
                  (by simpa [advanceWorkState, inactive, hnewEnded]) hdone with
                ⟨beta, k, holdTail, hnewTail⟩
              refine ⟨symbol :: beta, k, ?_, ?_⟩
              · simpa [oldProjection, inactive] using
                  congrArg (fun xs => inactive z₀ :: xs) holdTail
              · simpa [newProjection, inactive] using
                  congrArg (fun xs => inactive symbol :: xs) hnewTail

private theorem WorkTrace.decodeDeleteTwoAfterStage2
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (carry₀ : Option (WorkSlot g))
    (hstage2Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage2 next hist old new →
        next = .suffixMinus2 ∧ old = active .close ∧ InactiveOpt new)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus2 next hist old new →
        next = .suffixMinus2 ∧ minus2Suffix hist old new)
    {stage result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hstage : stage.phase = .stage2)
    (hcarry₀ : stage.history.new1 = some carry₀)
    (hcarry₀Inactive : InactiveOpt carry₀)
    (hnewEnded : stage.newEnded = carry₀.isNone)
    (h : WorkTrace g cert stage rows result)
    (hdone : workScanDone result = true) :
    ∃ (gamma : List (WorkSym g)) (k : ℕ),
      oldProjection rows = active .close :: gamma.map inactive ++
        List.replicate k none ∧
      carry₀ :: newProjection rows = gamma.map inactive ++
        List.replicate (k + 2) none := by
  cases h with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage old₁ carry₁ next₁ suffixRows result hedge₁ htail =>
      have he₁ := hstage2Edge next₁ stage.history old₁ carry₁ (by
        simpa [hstage] using hedge₁.2.2.2.2)
      rcases he₁ with ⟨rfl, rfl, hcarry₁Inactive⟩
      cases carry₀ with
      | none =>
          have hcarry₁none : carry₁ = none := by
            rcases hedge₁.2.2.2.1 with hfalse | hnone
            · simp [hnewEnded] at hfalse
            · exact hnone
          subst carry₁
          have hnone := htail.decodeMinus2None rfl (by
            simp [advanceWorkState, updateHistory]) (by
            simp [advanceWorkState, updateHistory, hcarry₀])
            (by simp [advanceWorkState, hnewEnded]) hsuffix
          rcases hnone with ⟨holdTail, hnewTail⟩
          refine ⟨[], suffixRows.length, ?_, ?_⟩
          · simpa [oldProjection] using
              congrArg (fun xs => active WorkSym.close :: xs) holdTail
          · have hnewTail' : suffixRows.map (fun r => r.2.1) =
                List.replicate suffixRows.length none := by
              simpa [newProjection] using hnewTail
            simp only [newProjection, List.map_cons, List.map_nil, List.nil_append]
            rw [hnewTail', show suffixRows.length + 2 =
              (suffixRows.length + 1) + 1 by omega, List.replicate_succ,
              List.replicate_succ]
      | some slot₀ =>
          cases slot₀ with
          | mk active₀ z₀ =>
              simp [InactiveOpt] at hcarry₀Inactive
              subst active₀
              cases carry₁ with
              | none =>
                  have hmixed := htail.decodeMinus2Mixed z₀ rfl (by
                    simp [advanceWorkState, updateHistory]) (by
                    simp [advanceWorkState, updateHistory, hcarry₀, inactive])
                    (by simp [advanceWorkState]) hsuffix hdone
                  rcases hmixed with ⟨k, holdTail, hnewTail⟩
                  refine ⟨[z₀], k, ?_, ?_⟩
                  · simpa [oldProjection, inactive] using
                      congrArg (fun xs => active WorkSym.close :: xs) holdTail
                  · simpa [newProjection, inactive, List.replicate_succ] using
                      congrArg (fun xs => inactive z₀ :: none :: xs) hnewTail
              | some slot₁ =>
                  cases slot₁ with
                  | mk active₁ z₁ =>
                      simp [InactiveOpt] at hcarry₁Inactive
                      subst active₁
                      have hsome := htail.decodeMinus2Some z₀ z₁ rfl (by
                        simp [advanceWorkState, updateHistory, inactive]) (by
                        simp [advanceWorkState, updateHistory, hcarry₀, inactive])
                        (by simp [advanceWorkState, inactive, hnewEnded]) hsuffix hdone
                      rcases hsome with ⟨gamma, k, holdTail, hnewTail⟩
                      refine ⟨z₀ :: z₁ :: gamma, k, ?_, ?_⟩
                      · simpa [oldProjection, inactive] using
                          congrArg (fun xs => active WorkSym.close :: xs) holdTail
                      · simpa [newProjection, inactive] using
                          congrArg (fun xs => inactive z₀ :: inactive z₁ :: xs)
                            hnewTail

private theorem WorkTrace.false_of_returnBeta_oldEnded
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (hreturn : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .returnBeta next hist old new →
        (next = .returnBeta ∧ sameSuffix old new ∧ old ≠ inactive .dollar) ∨
        (next = .stage2 ∧ old = inactive .dollar ∧ InactiveOpt new))
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .returnBeta)
    (holdEnded : state.oldEnded = true)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) : False := by
  induction h with
  | nil => simpa [workScanDone, hphase] using hdone
  | @cons state old new next rows result hedge htail ih =>
      have hold : old = none := by
        rcases hedge.2.2.1 with hfalse | hnone
        · simp [holdEnded] at hfalse
        · exact hnone
      have hc := hreturn next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases hc with hloop | hboundary
      · rcases hloop with ⟨rfl, _hsame, _hne⟩
        exact ih rfl (by simp [advanceWorkState, holdEnded, hold]) hdone
      · rcases hboundary with ⟨_rfl, hboundary, _⟩
        simp [hold, inactive] at hboundary

private theorem WorkTrace.decodeReturnBeta
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (hreturn : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .returnBeta next hist old new →
        (next = .returnBeta ∧ sameSuffix old new ∧ old ≠ inactive .dollar) ∨
        (next = .stage2 ∧ old = inactive .dollar ∧ InactiveOpt new))
    {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hphase : state.phase = .returnBeta)
    (h : WorkTrace g cert state rows result)
    (hdone : workScanDone result = true) :
    ∃ (beta : List (WorkSym g)) (carry₀ : Option (WorkSlot g))
      (rest : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
      (stage2 : WorkScanState g),
      DollarFree beta ∧ InactiveOpt carry₀ ∧
      oldProjection rows = beta.map inactive ++ [inactive .dollar] ++
        oldProjection rest ∧
      newProjection rows = beta.map inactive ++ carry₀ :: newProjection rest ∧
      stage2.phase = .stage2 ∧ stage2.history.new1 = some carry₀ ∧
      stage2.newEnded = carry₀.isNone ∧ WorkTrace g cert stage2 rest result := by
  induction h with
  | nil =>
      have : False := by simpa [workScanDone, hphase] using hdone
      exact this.elim
  | @cons state old new next rows result hedge htail ih =>
      have hc := hreturn next state.history old new (by
        simpa [hphase] using hedge.2.2.2.2)
      rcases hc with hloop | hboundary
      · rcases hloop with ⟨rfl, hsame, hne⟩
        rcases hsame with ⟨rfl, holdInactive⟩
        cases old with
        | none =>
            exact (htail.false_of_returnBeta_oldEnded hreturn rfl (by
              simp [advanceWorkState]) hdone).elim
        | some slot =>
            cases slot with
            | mk activeFlag symbol =>
                simp [InactiveOpt] at holdInactive
                subst activeFlag
                rcases ih rfl hdone with
                  ⟨beta, carry₀, rest, stage2, hfree, hcarryInactive,
                    holdRows, hnewRows, hstage2, hcarry, hended, hrest⟩
                refine ⟨symbol :: beta, carry₀, rest, stage2, ?_, hcarryInactive,
                  ?_, ?_, hstage2, hcarry, hended, hrest⟩
                · simp only [DollarFree, List.mem_cons, not_or]
                  constructor
                  · intro hsymbol
                    subst symbol
                    exact hne rfl
                  · exact hfree
                · simpa [oldProjection, inactive, List.append_assoc] using
                    congrArg (fun xs => inactive symbol :: xs) holdRows
                · simpa [newProjection, inactive, List.append_assoc] using
                    congrArg (fun xs => inactive symbol :: xs) hnewRows
      · rcases hboundary with ⟨rfl, rfl, hcarryInactive⟩
        let stage2 := advanceWorkState state (inactive WorkSym.dollar) new .stage2
        have hended : stage2.newEnded = new.isNone := by
          cases new with
          | none => simp [stage2, advanceWorkState]
          | some slot =>
              have hstateEnded : state.newEnded = false := by
                rcases hedge.2.2.2.1 with hfalse | hnone
                · exact hfalse
                · simp at hnone
              simp [stage2, advanceWorkState, hstateEnded]
        refine ⟨[], new, rows, stage2, ?_, hcarryInactive, ?_, ?_, rfl, ?_,
          hended, htail⟩
        · simp [DollarFree]
        · simp [oldProjection]
        · simp [newProjection]
        · simp [stage2, advanceWorkState, updateHistory]

private theorem WorkTrace.decodeReturnAfterStage1
    {g : IndexedGrammar T} [Fintype g.nt] {cert : CompositeCert g}
    (hstage1Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage1 next hist old new →
        next = .returnBeta ∧ ∃ z, z ≠ .dollar ∧
          old = inactive z ∧ new = active z)
    (hreturn : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .returnBeta next hist old new →
        (next = .returnBeta ∧ sameSuffix old new ∧ old ≠ inactive .dollar) ∨
        (next = .stage2 ∧ old = inactive .dollar ∧ InactiveOpt new))
    (hstage2Edge : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .stage2 next hist old new →
        next = .suffixMinus2 ∧ old = active .close ∧ InactiveOpt new)
    (hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (old new : Option (WorkSlot g)),
      WorkEdge g cert .suffixMinus2 next hist old new →
        next = .suffixMinus2 ∧ minus2Suffix hist old new)
    {stage result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (hstage : stage.phase = .stage1)
    (h : WorkTrace g cert stage rows result)
    (hdone : workScanDone result = true) :
    ∃ (Z : WorkSym g) (beta gamma : List (WorkSym g)) (k : ℕ),
      Z ≠ .dollar ∧ DollarFree beta ∧
      oldProjection rows = inactive Z :: beta.map inactive ++
        [inactive .dollar, active .close] ++ gamma.map inactive ++
          List.replicate k none ∧
      newProjection rows = active Z :: beta.map inactive ++ gamma.map inactive ++
        List.replicate (k + 2) none := by
  cases h with
  | nil => simp [workScanDone, hstage] at hdone
  | @cons _stage old₀ new₀ next₀ rows₀ result hedge₀ htail₀ =>
      have he₀ := hstage1Edge next₀ stage.history old₀ new₀ (by
        simpa [hstage] using hedge₀.2.2.2.2)
      rcases he₀ with ⟨rfl, Z, hZ, rfl, rfl⟩
      rcases htail₀.decodeReturnBeta hreturn rfl hdone with
        ⟨beta, carry₀, rest, stage2, hfree, hcarryInactive, holdBeta, hnewBeta,
          hstage2, hcarry, hended, hrest⟩
      rcases hrest.decodeDeleteTwoAfterStage2 carry₀ hstage2Edge hsuffix hstage2
          hcarry hcarryInactive hended hdone with ⟨gamma, k, holdGamma, hnewGamma⟩
      refine ⟨Z, beta, gamma, k, hZ, hfree, ?_, ?_⟩
      · calc
          oldProjection ((inactive Z, active Z, .returnBeta) :: rows₀) =
              inactive Z :: oldProjection rows₀ := rfl
          _ = inactive Z :: (beta.map inactive ++ [inactive .dollar] ++
              oldProjection rest) := by rw [holdBeta]
          _ = inactive Z :: beta.map inactive ++ [inactive .dollar, active .close] ++
              gamma.map inactive ++ List.replicate k none := by
            rw [holdGamma]
            simp [List.append_assoc]
      · calc
          newProjection ((inactive Z, active Z, .returnBeta) :: rows₀) =
              active Z :: newProjection rows₀ := rfl
          _ = active Z :: (beta.map inactive ++ carry₀ :: newProjection rest) := by
            rw [hnewBeta]
          _ = active Z :: beta.map inactive ++ gamma.map inactive ++
              List.replicate (k + 2) none := by
            rw [hnewGamma]
            simp [List.append_assoc]

private theorem return_stage1_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g .returnFrame .stage1 next hist old new ↔
      next = .returnBeta ∧ ∃ z, z ≠ .dollar ∧
        old = inactive z ∧ new = active z := by
  cases next <;> simp [WorkEdge, prefixEdge, and_assoc]

private theorem return_returnBeta_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g .returnFrame .returnBeta next hist old new ↔
      (next = .returnBeta ∧ sameSuffix old new ∧ old ≠ inactive .dollar) ∨
      (next = .stage2 ∧ old = inactive .dollar ∧ InactiveOpt new) := by
  cases next <;> simp [WorkEdge, prefixEdge, and_assoc]

private theorem return_stage2_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g .returnFrame .stage2 next hist old new ↔
      next = .suffixMinus2 ∧ old = active .close ∧ InactiveOpt new := by
  cases next <;> simp [WorkEdge, prefixEdge, and_assoc]

private theorem return_suffixMinus2_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g .returnFrame .suffixMinus2 next hist old new ↔
      next = .suffixMinus2 ∧ minus2Suffix hist old new := by
  cases next <;> simp [WorkEdge, prefixEdge, and_assoc]

public theorem workTraceAccepts_returnFrame_sound
    {g : IndexedGrammar T} [Fintype g.nt]
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g .returnFrame old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g .returnFrame oldCursor newCursor := by
  have hstage1 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g .returnFrame .stage1 next hist x y →
        next = .returnBeta ∧ ∃ z, z ≠ .dollar ∧
          x = inactive z ∧ y = active z := by
    intro next hist x y hedge
    exact (return_stage1_iff g next hist x y).mp hedge
  have hreturn : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g .returnFrame .returnBeta next hist x y →
        (next = .returnBeta ∧ sameSuffix x y ∧ x ≠ inactive .dollar) ∨
        (next = .stage2 ∧ x = inactive .dollar ∧ InactiveOpt y) := by
    intro next hist x y hedge
    exact (return_returnBeta_iff g next hist x y).mp hedge
  have hstage2 : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g .returnFrame .stage2 next hist x y →
        next = .suffixMinus2 ∧ x = active .close ∧ InactiveOpt y := by
    intro next hist x y hedge
    exact (return_stage2_iff g next hist x y).mp hedge
  have hsuffix : ∀ (next : WorkPhase) (hist : WorkHistory g)
      (x y : Option (WorkSlot g)),
      WorkEdge g .returnFrame .suffixMinus2 next hist x y →
        next = .suffixMinus2 ∧ minus2Suffix hist x y := by
    intro next hist x y hedge
    exact (return_suffixMinus2_iff g next hist x y).mp hedge
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  rcases htrace.splitNonproductivePrefix rfl rfl hdone with
    ⟨alpha, rest, stage, _henabled, holdPrefix, hnewPrefix, hstage, hrest⟩
  rcases hrest.decodeReturnAfterStage1 hstage1 hreturn hstage2 hsuffix hstage hdone with
    ⟨Z, beta, gamma, k, hZ, hfree, holdRest, hnewRest⟩
  let oldCursor : WorkCursor g :=
    ⟨alpha ++ [.dollar, Z] ++ beta ++ [.dollar], .close, gamma⟩
  let newCursor : WorkCursor g :=
    ⟨alpha ++ [.dollar], Z, beta ++ gamma⟩
  refine ⟨oldCursor, newCursor, k, k + 2, ?_, ?_, ?_⟩
  · rw [← hold]
    calc
      oldProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          oldProjection rest := holdPrefix
      _ = oldCursor.slots.map some ++ List.replicate k none := by
        rw [holdRest]
        simp [oldCursor, WorkCursor.slots, inactive, active, List.map_append,
          List.map_map, Function.comp_def, List.append_assoc]
        rfl
  · rw [← hnew]
    calc
      newProjection rows = alpha.map inactive ++ [inactive .dollar] ++
          newProjection rest := hnewPrefix
      _ = newCursor.slots.map some ++ List.replicate (k + 2) none := by
        rw [hnewRest]
        simp [newCursor, WorkCursor.slots, inactive, active, List.map_append,
          List.map_map, Function.comp_def, List.append_assoc]
        rfl
  · exact ⟨alpha, Z, beta, gamma, hZ, hfree, rfl, rfl⟩

/-- An accepting logical-slot trace reconstructs the exact work-cursor step named by its
certificate, for every one of Aho's fourteen composite transition forms. -/
public theorem workTraceAccepts_sound
    {g : IndexedGrammar T} [Fintype g.nt] (cert : CompositeCert g)
    {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ (oldCursor newCursor : WorkCursor g) (kOld kNew : ℕ),
      old = oldCursor.slots.map some ++ List.replicate kOld none ∧
      new = newCursor.slots.map some ++ List.replicate kNew none ∧
      CertWorkStep g cert oldCursor newCursor := by
  cases cert with
  | plainBinary A B C => exact workTraceAccepts_plainBinary_sound h
  | plainTerminal A a => exact workTraceAccepts_plainTerminal_sound h
  | plainPushSkip A B f => exact workTraceAccepts_plainPushSkip_sound h
  | plainPushUse A B f => exact workTraceAccepts_plainPushUse_sound h
  | liveBinaryBoth A B C => exact workTraceAccepts_liveBinaryBoth_sound h
  | liveBinaryLeft A B C => exact workTraceAccepts_liveBinaryLeft_sound h
  | liveBinaryRight A B C => exact workTraceAccepts_liveBinaryRight_sound h
  | livePushFresh A B f => exact workTraceAccepts_livePushFresh_sound h
  | livePushCompress A B f R d => exact workTraceAccepts_livePushCompress_sound h
  | popPlain R d A B => exact workTraceAccepts_popPlain_sound h
  | popLive R d A B => exact workTraceAccepts_popLive_sound h
  | matchTerminal a => exact workTraceAccepts_matchTerminal_sound h
  | eraseIndex R d => exact workTraceAccepts_eraseIndex_sound h
  | returnFrame => exact workTraceAccepts_returnFrame_sound h

/-- A semantic certificate step is exactly the conjunction of the independently checked input
head action and work-cursor action. -/
public theorem certStep_iff_inputAction_and_certWorkStep
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (cert : CompositeCert g) (oldPos newPos : ℕ)
    (oldCursor newCursor : WorkCursor g) :
    CertStep g input cert ⟨oldPos, oldCursor⟩ ⟨newPos, newCursor⟩ ↔
      cert.InputAction input oldPos newPos ∧
        CertWorkStep g cert oldCursor newCursor := by
  cases cert <;>
    simp [CertStep, CompositeCert.InputAction, CertWorkStep] <;> aesop

end Aho
end IndexedGrammar
