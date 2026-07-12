module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowWork.Replacement

@[expose]
public section

/-!
# Right-shift soundness for Aho's row checker

One-slot insertions and the binary and push certificates implemented by them.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## One-slot right shifts -/

private theorem insertOne_suffixPlus1_iff
    (productive : Bool) (oldFocus newFocus inserted : WorkSym g)
    (needOldSome : Bool) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    insertOneEdge productive oldFocus newFocus inserted needOldSome
        .suffixPlus1 next hist old new ↔
      next = .suffixPlus1 ∧ plus1Suffix hist old new := by
  cases next <;> simp [insertOneEdge, prefixEdge]

/-- Decode the exhausted-input case of a one-slot right-shift suffix. -/
public theorem WorkTrace.decodePlus1None
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

/-- Decode the carried-symbol case of a one-slot right-shift suffix. -/
public theorem WorkTrace.decodePlus1Some
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
          · simp only [oldProjection, List.map_cons, List.map_nil, List.nil_append]
            rw [holdTail']
            exact List.replicate_succ.symm
          · simp only [newProjection, List.map_cons, List.map_nil]
            rw [hnewTail']
            rfl
      | some slot =>
          cases slot with
          | mk activeFlag symbol =>
              simp [InactiveOpt] at holdInactive
              subst activeFlag
              rcases ih symbol rfl (by simp [advanceWorkState, updateHistory, inactive])
                  (by simp [advanceWorkState, inactive, holdEnded]) hdone with
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
                simp [advanceWorkState, updateHistory])
                (by simp [advanceWorkState]) hsuffix
              rcases hnone with ⟨holdTail, hnewTail⟩
              have holdTail' : suffixRows.map (fun r => r.1) =
                  List.replicate suffixRows.length none := by
                simpa [oldProjection] using holdTail
              have hnewTail' : suffixRows.map (fun r => r.2.1) =
                  List.replicate suffixRows.length none := by
                simpa [newProjection] using hnewTail
              refine ⟨[], suffixRows.length + 1, suffixRows.length, ?_, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_nil]
                rw [holdTail']
                rw [List.replicate_succ]
                rfl
              · simp only [newProjection, List.map_cons, List.map_nil]
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
                    simp [advanceWorkState, updateHistory, inactive])
                    (by simp [advanceWorkState, inactive, active, hstageOldEnded])
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
                    simp [inactive]
                  · simp only [newProjection, List.map_cons, List.map_cons]
                    rw [hnewTail']
                    simp [inactive]
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

end Aho
end IndexedGrammar
