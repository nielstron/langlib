module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.PaddedRows

@[expose]
public section

/-!
# Boundary row scans

Exact finite scans recognizing the initialized and accepting padded-row formats.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Exact finite scans for initialization and final rows -/

/-- Three states suffice for the fixed first-block / blank-tail row formats. -/
public inductive BoundaryScanState where
  | first
  | tail
  | dead
deriving DecidableEq, Fintype

/-- The canonical initialized cell at the first input position. -/
public def initialFirstCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := false, block := initialBlock g }

/-- A canonical blank-tail initialized cell. -/
public def initialTailCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := false, block := blankBlock g }

/-- The canonical final cell at the first input position. -/
public def finalFirstCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := true, block := finalBlock g }

/-- A canonical blank-tail final cell. -/
public def finalTailCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := true, block := blankBlock g }

/-- Cell transition for the exact synchronized initialization scan. -/
public noncomputable def initScanCell (g : IndexedGrammar T) :
    BoundaryScanState → RowCell g → RowCell g → BoundaryScanState := by
  classical
  exact fun state old new =>
    match state, old with
    | .first, .input a => if new = initialFirstCell g a then .tail else .dead
    | .tail, .input a => if new = initialTailCell g a then .tail else .dead
    | _, _ => .dead

/-- Run the synchronized initialization scan; unequal row lengths reject. -/
public noncomputable def evalInitScan (g : IndexedGrammar T) :
    BoundaryScanState → List (RowCell g) → List (RowCell g) → BoundaryScanState
  | state, [], [] => state
  | state, old :: olds, new :: news =>
      evalInitScan g (initScanCell g state old new) olds news
  | _, _, _ => .dead

@[simp] private theorem evalInitScan_dead (g : IndexedGrammar T)
    (old new : List (RowCell g)) :
    evalInitScan g .dead old new = .dead := by
  induction old generalizing new with
  | nil => cases new <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => rfl
      | cons new news => simp [evalInitScan, initScanCell, ih]

/-- Cell transition for the exact regular final-row scan. -/
public noncomputable def finalScanCell (g : IndexedGrammar T) :
    BoundaryScanState → RowCell g → BoundaryScanState := by
  classical
  exact fun state cell =>
    match state, cell with
    | .first, .run c => if cell = finalFirstCell g c.input then .tail else .dead
    | .tail, .run c => if cell = finalTailCell g c.input then .tail else .dead
    | _, _ => .dead

/-- Run the final-row scan. -/
public noncomputable def evalFinalScan (g : IndexedGrammar T) :
    BoundaryScanState → List (RowCell g) → BoundaryScanState
  | state, [] => state
  | state, cell :: row => evalFinalScan g (finalScanCell g state cell) row

@[simp] private theorem evalFinalScan_dead (g : IndexedGrammar T)
    (row : List (RowCell g)) :
    evalFinalScan g .dead row = .dead := by
  induction row with
  | nil => rfl
  | cons cell row ih => simp [evalFinalScan, finalScanCell, ih]

private theorem evalInitScan_tail_iff (g : IndexedGrammar T)
    (old new : List (RowCell g)) :
    evalInitScan g .tail old new = .tail ↔
      ∃ w : List T,
        old = inputRow g w ∧ new = w.map (initialTailCell g) := by
  induction old generalizing new with
  | nil =>
      cases new <;> simp [evalInitScan, inputRow]
  | cons old olds ih =>
      cases new with
      | nil =>
          constructor
          · intro h
            simp [evalInitScan] at h
          · rintro ⟨w, hold, hnew⟩
            cases w with
            | nil => simp [inputRow] at hold
            | cons a w => simp at hnew
      | cons new news =>
          cases old with
          | run c =>
              constructor
              · intro h
                simp [evalInitScan, initScanCell] at h
              · rintro ⟨w, hold, _⟩
                cases w <;> simp [inputRow] at hold
          | input a =>
              classical
              by_cases hnew : new = initialTailCell g a
              · subst new
                simp only [evalInitScan, initScanCell]
                change evalInitScan g .tail olds news = .tail ↔
                  ∃ w, RowCell.input a :: olds = inputRow g w ∧
                    initialTailCell g a :: news = w.map (initialTailCell g)
                rw [ih]
                constructor
                · rintro ⟨w, hold, hnew⟩
                  exact ⟨a :: w, by simp [inputRow, hold], by simp [hnew]⟩
                · rintro ⟨w, hold, hnew⟩
                  cases w with
                  | nil => simp [inputRow] at hold
                  | cons b w =>
                      simp only [inputRow, List.map_cons, List.cons.injEq] at hold hnew
                      have hab : a = b := RowCell.input.inj hold.1
                      subst b
                      exact ⟨w, hold.2, hnew.2⟩
              · constructor
                · intro h
                  simp [evalInitScan, initScanCell, hnew] at h
                · rintro ⟨w, hold, hmap⟩
                  cases w with
                  | nil => simp [inputRow] at hold
                  | cons b w =>
                      simp only [inputRow, List.map_cons, List.cons.injEq] at hold hmap
                      have hab : a = b := RowCell.input.inj hold.1
                      subst b
                      exact (hnew hmap.1).elim

/-- The initialization scanner recognizes exactly `PaddedInitStep`. -/
public theorem evalInitScan_iff_paddedInitStep (g : IndexedGrammar T)
    (old new : List (RowCell g)) :
    evalInitScan g .first old new = .tail ↔ PaddedInitStep g old new := by
  constructor
  · intro h
    cases old with
    | nil => cases new <;> simp [evalInitScan] at h
    | cons old olds =>
        cases new with
        | nil => simp [evalInitScan] at h
        | cons new news =>
            cases old with
            | run c => simp [evalInitScan, initScanCell] at h
            | input a =>
                classical
                by_cases hnew : new = initialFirstCell g a
                · subst new
                  simp only [evalInitScan, initScanCell] at h
                  change evalInitScan g .tail olds news = .tail at h
                  rw [evalInitScan_tail_iff] at h
                  rcases h with ⟨w, hold, hnew⟩
                  refine ⟨a :: w, by simp, ?_, ?_⟩
                  · simp [inputRow, hold]
                  · rw [encodeRunRow_initial_cons]
                    simp [initialFirstCell, initialTailCell, hnew]
                · simp [evalInitScan, initScanCell, hnew] at h
  · rintro ⟨w, hw, rfl, rfl⟩
    cases w with
    | nil => exact (hw rfl).elim
    | cons a w =>
        rw [encodeRunRow_initial_cons]
        have htail : evalInitScan g .tail (w.map RowCell.input)
            (w.map (initialTailCell g)) = .tail :=
          (evalInitScan_tail_iff g _ _).2 ⟨w, by simp [inputRow], rfl⟩
        simpa [inputRow, evalInitScan, initScanCell, initialFirstCell,
          initialTailCell] using htail

private theorem evalFinalScan_tail_iff (g : IndexedGrammar T) (row : List (RowCell g)) :
    evalFinalScan g .tail row = .tail ↔
      ∃ w : List T, row = w.map (finalTailCell g) := by
  induction row with
  | nil => simp [evalFinalScan]
  | cons cell row ih =>
      cases cell with
      | input a =>
          constructor
          · intro h
            simp [evalFinalScan, finalScanCell] at h
          · rintro ⟨w, hrow⟩
            cases w <;> simp [finalTailCell] at hrow
      | run c =>
          classical
          by_cases hcell : RowCell.run c = finalTailCell g c.input
          · simp only [evalFinalScan, finalScanCell, hcell, if_pos, ih]
            constructor
            · rintro ⟨w, hw⟩
              exact ⟨c.input :: w, by simp [hw]⟩
            · rintro ⟨w, hw⟩
              cases w with
              | nil => simp at hw
              | cons a w =>
                  simp only [List.map_cons, List.cons.injEq] at hw
                  exact ⟨w, hw.2⟩
          · constructor
            · intro h
              simp [evalFinalScan, finalScanCell, hcell] at h
            · rintro ⟨w, hrow⟩
              cases w with
              | nil => simp at hrow
              | cons a w =>
                  simp only [List.map_cons, List.cons.injEq] at hrow
                  have heq : RowCell.run c = finalTailCell g c.input := by
                    cases c
                    simp_all [finalTailCell]
                  exact (hcell heq).elim

/-- The final scanner recognizes exactly `FinalRow`. -/
public theorem evalFinalScan_iff_finalRow (g : IndexedGrammar T) (row : List (RowCell g)) :
    evalFinalScan g .first row = .tail ↔ FinalRow g row := by
  constructor
  · intro h
    cases row with
    | nil => simp [evalFinalScan] at h
    | cons cell row =>
        cases cell with
        | input a => simp [evalFinalScan, finalScanCell] at h
        | run c =>
            classical
            by_cases hcell : RowCell.run c = finalFirstCell g c.input
            · simp only [evalFinalScan, finalScanCell, hcell, if_pos] at h
              rw [evalFinalScan_tail_iff] at h
              rcases h with ⟨w, hrow⟩
              refine ⟨c.input :: w, by simp, ?_⟩
              rw [encodeRunRow_final_cons]
              simp [finalFirstCell, finalTailCell, hcell, hrow]
            · simp [evalFinalScan, finalScanCell, hcell] at h
  · rintro ⟨w, hw, rfl⟩
    cases w with
    | nil => exact (hw rfl).elim
    | cons a w =>
        rw [encodeRunRow_final_cons]
        have htail : evalFinalScan g .tail (w.map (finalTailCell g)) = .tail :=
          (evalFinalScan_tail_iff g _).2 ⟨w, rfl⟩
        simpa [evalFinalScan, finalScanCell, finalFirstCell, finalTailCell] using htail


end Aho
end IndexedGrammar

