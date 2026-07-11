module

public import Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.Completeness
public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowWork.FrameReturn

@[expose]
public section

/-!
# Soundness and exactness of Aho's certified row system

This is the physical-to-semantic direction. Successful finite-control evaluations are decoded
into input and work traces, then into semantic padded machine steps. Together with row-system
completeness, this yields exact language equality and the positive-input LBA recognizer.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

private theorem evalStep_dead_result (g : IndexedGrammar T) [Fintype g.nt]
    (old new : List (RowCell g)) (certs : List (RowCert g)) {result : RowState g}
    (h : (ahoRowSystem g).evalStep .dead old new certs = some result) :
    result = .dead := by
  induction old generalizing new certs with
  | nil =>
      cases new <;> cases certs <;>
        simp [CertifiedRowSystem.evalStep] at h
      exact h.symm
  | cons old olds ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at h
      | cons new news =>
          cases certs with
          | nil => simp [CertifiedRowSystem.evalStep] at h
          | cons cert certs =>
              simp only [CertifiedRowSystem.evalStep, ahoRowSystem_stepCell] at h
              have hcell : rowStepCell g (.dead : RowState g) old new cert = .dead := by
                cases cert <;> simp [rowStepCell]
              rw [hcell] at h
              exact ih _ _ h

private theorem composite_ne_dead {g : IndexedGrammar T} {cert : CompositeCert g}
    {input : InputPhase} {work : WorkScanState g} :
    (RowState.composite cert input work : RowState g) ≠ .dead := by
  intro h
  cases h

private def RowState.InitClosed : RowState g → Prop
  | .init _ => True
  | .dead => True
  | _ => False

private theorem rowStepCell_initClosed (g : IndexedGrammar T) [Fintype g.nt]
    {state : RowState g} (hstate : state.InitClosed)
    (old new : RowCell g) (cert : RowCert g) :
    (rowStepCell g state old new cert).InitClosed := by
  cases state with
  | start => simp [RowState.InitClosed] at hstate
  | composite chosen input work => simp [RowState.InitClosed] at hstate
  | dead => cases cert <;> simp [rowStepCell, RowState.InitClosed]
  | init q =>
      cases cert <;> simp [rowStepCell, RowState.InitClosed]

private theorem evalStep_initClosed (g : IndexedGrammar T) [Fintype g.nt]
    {state : RowState g} (hstate : state.InitClosed)
    (old new : List (RowCell g)) (certs : List (RowCert g)) {result : RowState g}
    (h : (ahoRowSystem g).evalStep state old new certs = some result) :
    result.InitClosed := by
  induction old generalizing state new certs with
  | nil =>
      cases new <;> cases certs <;>
        simp [CertifiedRowSystem.evalStep] at h
      simpa [h] using hstate
  | cons old olds ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at h
      | cons new news =>
          cases certs with
          | nil => simp [CertifiedRowSystem.evalStep] at h
          | cons cert certs =>
              simp only [CertifiedRowSystem.evalStep, ahoRowSystem_stepCell] at h
              exact ih (rowStepCell_initClosed g hstate old new cert) _ _ h

private theorem evalStep_composite_structure
    (g : IndexedGrammar T) [Fintype g.nt] (chosen : CompositeCert g)
    (inputState : InputPhase) (workState : WorkScanState g)
    (old new : List (RowCell g)) (certs : List (RowCert g))
    (finalCert : CompositeCert g) (finalInput : InputPhase)
    (finalWork : WorkScanState g)
    (h : (ahoRowSystem g).evalStep (.composite chosen inputState workState)
      old new certs = some (.composite finalCert finalInput finalWork)) :
    finalCert = chosen ∧
      ∃ (oldRuns newRuns : List (RunCell g))
        (choices : List (Fin workWidth → WorkPhase)),
        old = oldRuns.map RowCell.run ∧ new = newRuns.map RowCell.run ∧
          certs = choices.map (RowCert.composite chosen) := by
  induction old generalizing inputState workState new certs with
  | nil =>
      cases new <;> cases certs <;>
        simp [CertifiedRowSystem.evalStep] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, [], [], [], rfl, rfl, rfl⟩
  | cons old olds ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at h
      | cons new news =>
          cases certs with
          | nil => simp [CertifiedRowSystem.evalStep] at h
          | cons cert certs =>
              cases cert with
              | init =>
                  have hdead : (ahoRowSystem g).evalStep (.dead : RowState g)
                      olds news certs = some (.composite finalCert finalInput finalWork) := by
                    simpa [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell] using h
                  have := evalStep_dead_result g olds news certs hdead
                  exact (composite_ne_dead this).elim
              | composite next phases =>
                  by_cases hchosen : chosen = next
                  · subst next
                    cases old with
                    | input a =>
                        have hdead : (ahoRowSystem g).evalStep (.dead : RowState g)
                            olds news certs = some (.composite finalCert finalInput finalWork) := by
                          simpa [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell,
                            compositeCell] using h
                        have := evalStep_dead_result g olds news certs hdead
                        exact (composite_ne_dead this).elim
                    | run oldRun =>
                        cases new with
                        | input a =>
                            have hdead : (ahoRowSystem g).evalStep (.dead : RowState g)
                                olds news certs = some (.composite finalCert finalInput finalWork) := by
                              simpa [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell,
                                compositeCell] using h
                            have := evalStep_dead_result g olds news certs hdead
                            exact (composite_ne_dead this).elim
                        | run newRun =>
                            have htail : (ahoRowSystem g).evalStep
                                (.composite chosen
                                  (inputStep chosen inputState oldRun newRun)
                                  (evalWorkBlock g chosen workState oldRun.block
                                    newRun.block phases))
                                olds news certs =
                              some (.composite finalCert finalInput finalWork) := by
                                simpa only [CertifiedRowSystem.evalStep,
                                  ahoRowSystem_stepCell,
                                  rowStepCell_composite_same] using h
                            rcases ih _ _ _ _ htail with
                              ⟨hfinal, oldRuns, newRuns, choices,
                                hold, hnew, hcerts⟩
                            refine ⟨hfinal, oldRun :: oldRuns, newRun :: newRuns,
                              phases :: choices, ?_, ?_, ?_⟩
                            · simp [hold]
                            · simp [hnew]
                            · simp [hcerts]
                  · have hdead : (ahoRowSystem g).evalStep (.dead : RowState g)
                        olds news certs = some (.composite finalCert finalInput finalWork) := by
                      simpa [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell,
                        hchosen] using h
                    have := evalStep_dead_result g olds news certs hdead
                    exact (composite_ne_dead this).elim

private theorem evalStep_start_composite_structure
    (g : IndexedGrammar T) [Fintype g.nt]
    (old new : List (RowCell g)) (certs : List (RowCert g))
    (cert : CompositeCert g) (inputState : InputPhase) (workState : WorkScanState g)
    (h : (ahoRowSystem g).evalStep .start old new certs =
      some (.composite cert inputState workState)) :
    ∃ (oldRuns newRuns : List (RunCell g))
      (choices : List (Fin workWidth → WorkPhase)),
      oldRuns ≠ [] ∧ old = oldRuns.map RowCell.run ∧
        new = newRuns.map RowCell.run ∧
        certs = choices.map (RowCert.composite cert) := by
  cases old with
  | nil => cases new <;> cases certs <;> simp [CertifiedRowSystem.evalStep] at h
  | cons old olds =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at h
      | cons new news =>
          cases certs with
          | nil => simp [CertifiedRowSystem.evalStep] at h
          | cons rowCert certs =>
              cases rowCert with
              | init =>
                  have htail : (ahoRowSystem g).evalStep
                      (.init (initScanCell g .first old new)) olds news certs =
                    some (.composite cert inputState workState) := by
                      simpa [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell] using h
                  have hclosed := evalStep_initClosed g
                    (by simp [RowState.InitClosed]) olds news certs htail
                  simp [RowState.InitClosed] at hclosed
              | composite chosen phases =>
                  cases old with
                  | input a =>
                      have hdead : (ahoRowSystem g).evalStep (.dead : RowState g)
                          olds news certs = some (.composite cert inputState workState) := by
                        simpa [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell,
                          compositeCell] using h
                      have := evalStep_dead_result g olds news certs hdead
                      exact (composite_ne_dead this).elim
                  | run oldRun =>
                      cases new with
                      | input a =>
                          have hdead : (ahoRowSystem g).evalStep (.dead : RowState g)
                              olds news certs = some (.composite cert inputState workState) := by
                            simpa [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell,
                              compositeCell] using h
                          have := evalStep_dead_result g olds news certs hdead
                          exact (composite_ne_dead this).elim
                      | run newRun =>
                          have htail : (ahoRowSystem g).evalStep
                              (.composite chosen
                                (inputStep chosen .prefix oldRun newRun)
                                (evalWorkBlock g chosen (initialWorkScan g) oldRun.block
                                  newRun.block phases))
                              olds news certs = some (.composite cert inputState workState) := by
                            simpa only [CertifiedRowSystem.evalStep, ahoRowSystem_stepCell,
                              rowStepCell_composite_start] using h
                          rcases evalStep_composite_structure g chosen
                              (inputStep chosen .prefix oldRun newRun)
                              (evalWorkBlock g chosen (initialWorkScan g) oldRun.block
                                newRun.block phases)
                              olds news certs cert inputState workState htail with
                            ⟨hcert, oldRuns, newRuns, choices, hold, hnew, hcerts⟩
                          subst cert
                          refine ⟨oldRun :: oldRuns, newRun :: newRuns,
                            phases :: choices, by simp, ?_, ?_, ?_⟩
                          · simp [hold]
                          · simp [hnew]
                          · simp [hcerts]

private theorem exists_slotTriples (g : IndexedGrammar T)
    (old new : List (Option (WorkSlot g))) (phases : List WorkPhase)
    (hnew : new.length = old.length) (hphases : phases.length = old.length) :
    ∃ rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase),
      rows.map (fun r => r.1) = old ∧ rows.map (fun r => r.2.1) = new ∧
        rows.map (fun r => r.2.2) = phases := by
  induction old generalizing new phases with
  | nil =>
      have hn : new = [] := List.length_eq_zero_iff.mp (by simpa using hnew)
      have hp : phases = [] := List.length_eq_zero_iff.mp (by simpa using hphases)
      subst new
      subst phases
      exact ⟨[], rfl, rfl, rfl⟩
  | cons old olds ih =>
      cases new with
      | nil => simp at hnew
      | cons new news =>
          cases phases with
          | nil => simp at hphases
          | cons phase phases =>
              simp only [List.length_cons, Nat.succ.injEq] at hnew hphases
              rcases ih _ _ hnew hphases with ⟨rows, hold, hnew, hphases⟩
              exact ⟨(old, new, phase) :: rows, by simp [hold], by simp [hnew],
                by simp [hphases]⟩

private theorem workTraceAccepts_of_evalWorkBlocks_done
    (g : IndexedGrammar T) [Fintype g.nt] (cert : CompositeCert g)
    (old new : List (WorkBlock g)) (choices : List (Fin workWidth → WorkPhase))
    (hnew : new.length = old.length) (hchoices : choices.length = old.length)
    (hdone : workScanDone
      (evalWorkBlocks g cert (initialWorkScan g) old new choices) = true) :
    WorkTraceAccepts g cert (old.flatMap List.ofFn) (new.flatMap List.ofFn) := by
  let oldSlots := old.flatMap List.ofFn
  let newSlots := new.flatMap List.ofFn
  let phases := choices.flatMap List.ofFn
  have hnewSlots : newSlots.length = oldSlots.length := by
    simp [oldSlots, newSlots, hnew]
  have hphaseSlots : phases.length = oldSlots.length := by
    simp [oldSlots, phases, hchoices]
  rcases exists_slotTriples g oldSlots newSlots phases hnewSlots hphaseSlots with
    ⟨rows, hold, hnewRows, hphases⟩
  let result := evalWorkBlocks g cert (initialWorkScan g) old new choices
  have heval : evalWorkSlots g cert (initialWorkScan g) oldSlots newSlots phases = result := by
    exact (evalWorkBlocks_eq_evalWorkSlots g cert (initialWorkScan g)
      old new choices hnew hchoices).symm
  have hphase : result.phase ≠ .dead := by
    intro hdead
    have := hdone
    simp [result, workScanDone, hdead] at this
  have htrace : WorkTrace g cert (initialWorkScan g) rows result := by
    have htrace' := trace_of_evalWorkSlots_phase_ne_dead g cert
      (initialWorkScan g) rows (by
        rw [hold, hnewRows, hphases, heval]
        exact hphase)
    simpa [hold, hnewRows, hphases, heval] using htrace'
  exact ⟨rows, result, htrace, by simpa [oldSlots] using hold,
    by simpa [newSlots] using hnewRows, by simpa [result] using hdone⟩

private theorem workBlocks_eq_of_flatten_eq (g : IndexedGrammar T)
    {xs ys : List (WorkBlock g)} (hlen : xs.length = ys.length)
    (hflat : xs.flatMap List.ofFn = ys.flatMap List.ofFn) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      have : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.flatMap_cons] at hflat
          have hhead := congrArg (List.take workWidth) hflat
          have htail := congrArg (List.drop workWidth) hflat
          have hxy : List.ofFn x = List.ofFn y := by
            simpa [workWidth] using hhead
          have hrest : xs.flatMap List.ofFn = ys.flatMap List.ofFn := by
            simpa using htail
          have hfun : x = y := List.ofFn_injective hxy
          subst y
          exact congrArg (x :: ·) (ih hlen hrest)

private theorem decode_work_blocks
    (g : IndexedGrammar T) (row : List (RunCell g))
    (cursor : WorkCursor g) (k : ℕ)
    (hflat : (row.map RunCell.block).flatMap List.ofFn =
      cursor.slots.map some ++ List.replicate k none) :
    row.map RunCell.block = packedBlockList g cursor.slots 0 row.length ∧
      cursor.word.length ≤ row.length * workWidth := by
  have hcount : row.length * workWidth = cursor.slots.length + k := by
    calc
      row.length * workWidth =
          ((row.map RunCell.block).flatMap List.ofFn).length := by
            simp [List.length_flatMap, Function.comp_def]
      _ = (cursor.slots.map some ++ List.replicate k none).length :=
        congrArg List.length hflat
      _ = cursor.slots.length + k := by simp
  have hboundSlots : cursor.slots.length ≤ row.length * workWidth := by omega
  have hbound : cursor.word.length ≤ row.length * workWidth := by
    simpa using hboundSlots
  have hpad : paddedWork row.length cursor.slots =
      cursor.slots.map some ++ List.replicate k none := by
    rw [paddedWork_eq_append row.length cursor.slots hboundSlots]
    congr 2
    omega
  refine ⟨?_, hbound⟩
  apply workBlocks_eq_of_flatten_eq g
  · simp [packedBlockList]
  · rw [packedBlockList_flatten, hpad]
    exact hflat

/-- A successful physical composite scan decodes to one bounded semantic Aho step. -/
public theorem paddedCompositeStep_of_evalStep_composite
    (g : IndexedGrammar T) [Fintype g.nt]
    (old new : List (RowCell g)) (certs : List (RowCert g))
    (cert : CompositeCert g) (inputState : InputPhase) (workState : WorkScanState g)
    (heval : (ahoRowSystem g).evalStep .start old new certs =
      some (.composite cert inputState workState))
    (hdone : rowStepDone (.composite cert inputState workState : RowState g) = true) :
    PaddedCompositeStep g old new := by
  rcases evalStep_start_composite_structure g old new certs cert inputState workState heval with
    ⟨oldRuns, newRuns, choices, holdNe, hold, hnew, hcerts⟩
  have hlens := (ahoRowSystem g).evalStep_nil_iff heval
  have hnewLen : newRuns.length = oldRuns.length := by
    simpa [hold, hnew] using hlens.1.symm
  have hchoicesLen : choices.length = oldRuns.length := by
    simpa [hold, hcerts] using hlens.2.symm
  have hcomputed := evalStep_composite_start g cert oldRuns newRuns choices
    holdNe hnewLen hchoicesLen
  rw [← hold, ← hnew, ← hcerts] at hcomputed
  have hresult : (RowState.composite cert inputState workState : RowState g) =
      .composite cert
        (evalInputBlocks cert .prefix oldRuns newRuns)
        (evalWorkBlocks g cert (initialWorkScan g)
          (oldRuns.map RunCell.block) (newRuns.map RunCell.block) choices) :=
    Option.some.inj (heval.symm.trans hcomputed)
  have hinputEq : inputState = evalInputBlocks cert .prefix oldRuns newRuns := by
    injection hresult
  have hworkEq : workState = evalWorkBlocks g cert (initialWorkScan g)
      (oldRuns.map RunCell.block) (newRuns.map RunCell.block) choices := by
    injection hresult
  have hdoneParts : inputDone cert inputState = true ∧ workScanDone workState = true := by
    simpa [rowStepDone] using hdone
  have hinputDone : inputDone cert
      (evalInputBlocks cert .prefix oldRuns newRuns) = true := by
    simpa [← hinputEq] using hdoneParts.1
  have hworkDone : workScanDone
      (evalWorkBlocks g cert (initialWorkScan g)
        (oldRuns.map RunCell.block) (newRuns.map RunCell.block) choices) = true := by
    simpa [← hworkEq] using hdoneParts.2
  have hworkAccept := workTraceAccepts_of_evalWorkBlocks_done g cert
    (oldRuns.map RunCell.block) (newRuns.map RunCell.block) choices
    (by simpa using hnewLen) (by simpa using hchoicesLen) hworkDone
  rcases workTraceAccepts_sound cert hworkAccept with
    ⟨oldCursor, newCursor, kOld, kNew, holdFlat, hnewFlat, hworkStep⟩
  rcases evalInputBlocks_decode g cert oldRuns newRuns hinputDone with
    ⟨input, oldPos, newPos, holdPos, hnewPos, holdClear, hnewClear, haction⟩
  rcases decode_work_blocks g oldRuns oldCursor kOld holdFlat with
    ⟨holdBlocks, holdBound⟩
  rcases decode_work_blocks g newRuns newCursor kNew hnewFlat with
    ⟨hnewBlocks, hnewBound⟩
  have holdLen : oldRuns.length = input.length := by
    simpa using congrArg List.length holdClear
  have hnewLenInput : newRuns.length = input.length := by
    simpa using congrArg List.length hnewClear
  have holdBlocks' : oldRuns.map RunCell.block =
      packedBlockList g oldCursor.slots 0 input.length := by
    simpa [holdLen] using holdBlocks
  have hnewBlocks' : newRuns.map RunCell.block =
      packedBlockList g newCursor.slots 0 input.length := by
    simpa [hnewLenInput] using hnewBlocks
  have holdRuns : oldRuns = encodeRunCellsFrom g oldCursor.slots oldPos 0 input :=
    eq_encodeRunCellsFrom_of_clear_of_blocks g oldRuns oldCursor.slots oldPos 0 input
      (by simpa using holdClear) holdBlocks'
  have hnewRuns : newRuns = encodeRunCellsFrom g newCursor.slots newPos 0 input :=
    eq_encodeRunCellsFrom_of_clear_of_blocks g newRuns newCursor.slots newPos 0 input
      (by simpa using hnewClear) hnewBlocks'
  let oldConfig : Config g := ⟨oldPos, oldCursor⟩
  let newConfig : Config g := ⟨newPos, newCursor⟩
  have holdEncoded : oldRuns = encodeRunCells g input oldConfig := by
    simpa [encodeRunCells, oldConfig] using holdRuns
  have hnewEncoded : newRuns = encodeRunCells g input newConfig := by
    simpa [encodeRunCells, newConfig] using hnewRuns
  have hinputNe : input ≠ [] := by
    intro hnil
    subst input
    apply holdNe
    simpa [encodeRunCells] using holdEncoded
  refine ⟨input, oldConfig, newConfig, hinputNe, holdPos, hnewPos, ?_, ?_,
    ⟨cert, ?_⟩, ?_, ?_⟩
  · simpa [oldConfig, holdLen] using holdBound
  · simpa [newConfig, hnewLenInput] using hnewBound
  · exact (certStep_iff_inputAction_and_certWorkStep g input cert
      oldPos newPos oldCursor newCursor).2 ⟨haction, hworkStep⟩
  · rw [hold, holdEncoded]
    exact (encodeRunRow_eq_map_run g input oldConfig).symm
  · rw [hnew, hnewEncoded]
    exact (encodeRunRow_eq_map_run g input newConfig).symm

/-- Every accepted finite certificate row is one of the intended semantic padded-row edges. -/
public theorem paddedRowStep_of_rowStep (g : IndexedGrammar T) [Fintype g.nt]
    {old new : List (RowCell g)} (h : (ahoRowSystem g).RowStep old new) :
    PaddedRowStep g old new := by
  rcases h with ⟨certs, result, heval, hdone⟩
  cases result with
  | start => simp [ahoRowSystem, rowStepDone] at hdone
  | dead => simp [ahoRowSystem, rowStepDone] at hdone
  | init q =>
      exact Or.inl (paddedInitStep_of_evalStep_init g heval hdone)
  | composite cert inputState workState =>
      exact Or.inr
        (paddedCompositeStep_of_evalStep_composite g old new certs cert
          inputState workState heval hdone)

/-- Exactness of the physical synchronized checker on a single row transition. -/
public theorem ahoRowSystem_rowStep_iff_paddedRowStep
    (g : IndexedGrammar T) [Fintype g.nt] (old new : List (RowCell g)) :
    (ahoRowSystem g).RowStep old new ↔ PaddedRowStep g old new :=
  ⟨paddedRowStep_of_rowStep g, rowStep_of_paddedRowStep g⟩

/-- Soundness converse of `rowReachLanguage_of_paddedReachLanguage`: every accepting physical
row-system run decodes to semantic bounded reachability. -/
public theorem paddedReachLanguage_of_rowReachLanguage
    (g : IndexedGrammar T) [Fintype g.nt] :
    ∀ input : List T, input ∈ (ahoRowSystem g).rowReachLanguage →
      input ∈ paddedReachLanguage g := by
  intro input hmem
  rcases hmem with ⟨hne, row, hreach, hfinal⟩
  refine ⟨hne, row, ?_, (final_ahoRowSystem_iff g row).1 hfinal⟩
  simpa [inputRow, ahoRowSystem] using
    hreach.mono (fun _ _ hstep => paddedRowStep_of_rowStep g hstep)

/-- The executable finite row system recognizes exactly semantic bounded Aho reachability. -/
public theorem paddedReachLanguage_eq_rowReachLanguage
    (g : IndexedGrammar T) [Fintype g.nt] :
    paddedReachLanguage g = (ahoRowSystem g).rowReachLanguage := by
  funext input
  apply propext
  exact ⟨rowReachLanguage_of_paddedReachLanguage g input,
    paddedReachLanguage_of_rowReachLanguage g input⟩

/-- Semantic bounded Aho reachability is recognized on exactly the input-sized LBA tape. -/
public theorem is_LBA_pos_paddedReachLanguage
    {T : Type} [Fintype T] [DecidableEq T]
    (g : IndexedGrammar T) [Fintype g.nt] [Fintype g.flag] :
    is_LBA_pos (paddedReachLanguage g) := by
  classical
  rw [paddedReachLanguage_eq_rowReachLanguage g]
  exact CertifiedRowSystem.is_LBA_pos_rowReachLanguage (ahoRowSystem g)

end Aho
end IndexedGrammar
