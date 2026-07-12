module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowWork.Pop

@[expose]
public section

/-!
# Frame-return soundness for Aho's row checker

Two-slot left shifts, frame-return inversion, and the aggregate work-certificate soundness theorem.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

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
                  (by simp [advanceWorkState, inactive, hnewEnded]) hdone with
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
                        (by simp [advanceWorkState, hnewEnded]) hsuffix hdone
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
  | nil => simp [workScanDone, hphase] at hdone
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
      have : False := by simp [workScanDone, hphase] at hdone
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
  cases next <;> simp [WorkEdge, prefixEdge]

private theorem return_returnBeta_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g .returnFrame .returnBeta next hist old new ↔
      (next = .returnBeta ∧ sameSuffix old new ∧ old ≠ inactive .dollar) ∨
      (next = .stage2 ∧ old = inactive .dollar ∧ InactiveOpt new) := by
  cases next <;> simp [WorkEdge, prefixEdge]

private theorem return_stage2_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g .returnFrame .stage2 next hist old new ↔
      next = .suffixMinus2 ∧ old = active .close ∧ InactiveOpt new := by
  cases next <;> simp [WorkEdge, prefixEdge]

private theorem return_suffixMinus2_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g .returnFrame .suffixMinus2 next hist old new ↔
      next = .suffixMinus2 ∧ minus2Suffix hist old new := by
  cases next <;> simp [WorkEdge, prefixEdge]

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
