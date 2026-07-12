module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowWork.RightShift

@[expose]
public section

/-!
# Left-shift soundness for Aho's row checker

One-slot deletion and the terminal-match and erasable-index certificates implemented by it.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## One-slot left shifts -/

private theorem deleteOne_suffixMinus1_iff
    (focusOK : Option (WorkSlot g) → Prop)
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    deleteOneEdge focusOK .suffixMinus1 next hist old new ↔
      next = .suffixMinus1 ∧ minus1Suffix hist old new := by
  cases next <;> simp [deleteOneEdge, prefixEdge]

/-- Decode the exhausted-output case of a one-slot left-shift suffix. -/
public theorem WorkTrace.decodeMinus1None
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

/-- Decode the carried-symbol case of a one-slot left-shift suffix. -/
public theorem WorkTrace.decodeMinus1Some
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
          · simp only [oldProjection, List.map_cons, List.map_nil]
            rw [holdTail']
            rfl
          · simp only [newProjection, List.map_cons, List.map_nil, List.nil_append]
            rw [hnewTail']
            exact List.replicate_succ.symm
      | some slot =>
          cases slot with
          | mk activeFlag symbol =>
              simp [InactiveOpt] at hnewInactive
              subst activeFlag
              rcases ih symbol rfl (by simp [advanceWorkState, updateHistory, inactive])
                  (by simp [advanceWorkState, inactive, hnewEnded]) hdone with
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
                simp [advanceWorkState, updateHistory])
                (by simp [advanceWorkState]) hsuffix
              rcases hnone with ⟨holdTail, hnewTail⟩
              have holdTail' : suffixRows.map (fun r => r.1) =
                  List.replicate suffixRows.length none := by
                simpa [oldProjection] using holdTail
              have hnewTail' : suffixRows.map (fun r => r.2.1) =
                  List.replicate suffixRows.length none := by
                simpa [newProjection] using hnewTail
              refine ⟨Z, [], suffixRows.length, suffixRows.length + 1, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_nil]
                rw [holdTail']
                rfl
              · simp only [newProjection, List.map_cons, List.map_nil]
                rw [hnewTail', List.replicate_succ]
                rfl
          | some slot =>
              cases slot with
              | mk activeFlag symbol =>
                  simp [InactiveOpt] at hnewInactive
                  subst activeFlag
                  have hminus := htail.decodeMinus1Some symbol rfl (by
                    simp [advanceWorkState, updateHistory, inactive])
                    (by simp [advanceWorkState, inactive, active,
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

end Aho
end IndexedGrammar
