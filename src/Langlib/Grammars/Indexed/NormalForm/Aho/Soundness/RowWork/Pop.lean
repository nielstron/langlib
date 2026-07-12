module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowWork.LeftShift

@[expose]
public section

/-!
# Pop soundness for Aho's row checker

Two-slot right shifts and inversion of framed and unframed pop certificates.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

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
                  (by simp [advanceWorkState, inactive, holdEnded]) hdone with
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
                · simp [advanceWorkState] at hfalse
                · exact hnone
              subst carry₁
              have hnone := htail.decodePlus2None rfl (by
                simp [advanceWorkState, updateHistory]) (by
                simp [advanceWorkState, updateHistory])
                (by simp [advanceWorkState]) hsuffix
              rcases hnone with ⟨holdTail, hnewTail⟩
              refine ⟨[], suffixRows.length, ?_, ?_⟩
              · simp only [oldProjection, List.map_cons, List.map_nil, List.nil_append]
                have holdTail' : suffixRows.map (fun r => r.1) =
                    List.replicate suffixRows.length none := by
                  simpa [oldProjection] using holdTail
                rw [holdTail', show suffixRows.length + 2 =
                  (suffixRows.length + 1) + 1 by omega, List.replicate_succ,
                  List.replicate_succ]
              · simp only [newProjection, List.map_cons, List.map_nil]
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
                    · simp at hnone
                  cases carry₁ with
                  | none =>
                      have hmixed := htail.decodePlus2Mixed z₀ rfl (by
                        simp [advanceWorkState, updateHistory]) (by
                        simp [advanceWorkState, updateHistory, inactive])
                        (by simp [advanceWorkState]) hsuffix hdone
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
                            simp [advanceWorkState, updateHistory, inactive]) (by
                            simp [advanceWorkState, updateHistory, inactive])
                            (by simp [advanceWorkState, inactive, hstageOldEnded])
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
  | nil => simp [workScanDone, hphase] at hdone
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
      have : False := by simp [workScanDone, hphase] at hdone
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
                      simp [WorkSym.isIndex] at hzNonIndex
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
          simp [advanceWorkState, updateHistory]) hdone with
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

/-! The unframed implementation of a pop replaces the focus and erases the immediately
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
            simp [advanceWorkState, updateHistory]) hdone with
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
        | nil => simp [workScanDone, advanceWorkState] at hdone
        | @cons _minus old₁ new₁ next₁ suffixRows result hedge₁ htail =>
            have he₁ := hminusFirst next₁ minusState.history old₁ new₁ (by
              simpa [minusState, advanceWorkState] using hedge₁.2.2.2.2)
            rcases he₁ with ⟨rfl, rfl, hnewInactive⟩
            cases new₁ with
            | none =>
                have hnone := htail.decodeMinus1None rfl (by
                  simp [advanceWorkState, updateHistory])
                  (by simp [advanceWorkState]) hminus
                rcases hnone with ⟨holdTail, hnewTail⟩
                have holdTail' : suffixRows.map (fun r => r.1) =
                    List.replicate suffixRows.length none := by
                  simpa [oldProjection] using holdTail
                have hnewTail' : suffixRows.map (fun r => r.2.1) =
                    List.replicate suffixRows.length none := by
                  simpa [newProjection] using hnewTail
                refine Or.inr ⟨[], suffixRows.length, ?_, ?_⟩
                · simp only [oldProjection, List.map_cons, List.map_nil]
                  rw [holdTail']
                  simp
                · simp only [newProjection, List.map_cons, List.map_nil]
                  rw [hnewTail', List.replicate_succ]
                  simp
            | some slot =>
                cases slot with
                | mk activeFlag symbol =>
                    simp [InactiveOpt] at hnewInactive
                    subst activeFlag
                    have hdecoded := htail.decodeMinus1Some symbol rfl (by
                      simp [advanceWorkState, updateHistory, inactive])
                      (by simp [advanceWorkState, inactive, active,
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
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge]

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
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge]

private theorem popPlain_stage2_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .stage2 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        next = .stage3 ∧ InactiveOpt old ∧ new = active (.plain B) := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge]

private theorem popPlain_stage3_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .stage3 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        next = .suffixPlus2 ∧ InactiveOpt old ∧ new = inactive .close := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge]

private theorem popPlain_suffixPlus2_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .suffixPlus2 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧
        next = .suffixPlus2 ∧ plus2Suffix hist old new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge]

private theorem popPlain_minus1First_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .minus1First next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧ next = .suffixMinus1 ∧
        old = inactive (.index R d) ∧ InactiveOpt new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge]

private theorem popPlain_suffixMinus1_iff
    (g : IndexedGrammar T) [Fintype g.nt] (R : CFlag g) (d : IndexMark)
    (A B : g.nt) (next : WorkPhase) (hist : WorkHistory g)
    (old new : Option (WorkSlot g)) :
    WorkEdge g (.popPlain R d A B) .suffixMinus1 next hist old new ↔
      CertEnabled g (.popPlain R d A B) ∧ next = .suffixMinus1 ∧
        minus1Suffix hist old new := by
  cases next <;> simp [WorkEdge, CertEnabled, prefixEdge]

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

end Aho
end IndexedGrammar
