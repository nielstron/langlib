module

public import Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.Evaluation
public import Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.WorkCompleteness
public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowInput

@[expose]
public section

/-!
# Completeness of Aho's certified row system

This is the semantic-to-physical direction. It combines the input-track and work-track trace
constructors, packs them into physical cells, and proves that every semantic `PaddedRowStep` is
accepted as a `CertifiedRowSystem.RowStep`.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

@[simp] public theorem encodeRunCellsFrom_map_block (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (inputPos cell : ℕ) (input : List T) :
    (encodeRunCellsFrom g work inputPos cell input).map RunCell.block =
      packedBlockList g work cell input.length := by
  induction input generalizing cell with
  | nil => simp [encodeRunCellsFrom, packedBlockList]
  | cons a input ih =>
      simp only [encodeRunCellsFrom, List.map_cons, List.length_cons]
      rw [show packedBlockList g work cell (input.length + 1) =
          packedCell workWidth work cell ::
            packedBlockList g work (cell + 1) input.length by
        simp [packedBlockList, List.ofFn_succ, Nat.add_comm,
          Nat.add_left_comm]]
      exact congrArg (packedCell workWidth work cell :: ·) (ih (cell + 1))

@[simp] public theorem encodeRunCellsFrom_length (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (inputPos cell : ℕ) (input : List T) :
    (encodeRunCellsFrom g work inputPos cell input).length = input.length := by
  induction input generalizing cell with
  | nil => rfl
  | cons a input => simp [encodeRunCellsFrom, *]

@[simp] public theorem encodeRunCells_length (g : IndexedGrammar T)
    (input : List T) (c : Config g) :
    (encodeRunCells g input c).length = input.length := by
  simp [encodeRunCells]

@[simp] public theorem encodeRunCells_map_block (g : IndexedGrammar T)
    (input : List T) (c : Config g) :
    (encodeRunCells g input c).map RunCell.block =
      packedBlockList g c.work.slots 0 input.length := by
  exact encodeRunCellsFrom_map_block g c.work.slots c.inputPos 0 input

private theorem exists_runRowTriples (g : IndexedGrammar T)
    (old new : List (RunCell g)) (choices : List (Fin workWidth → WorkPhase))
    (hnew : new.length = old.length) (hchoices : choices.length = old.length) :
    ∃ rows : List (RunCell g × RunCell g × (Fin workWidth → WorkPhase)),
      rows.map (fun r => r.1) = old ∧ rows.map (fun r => r.2.1) = new ∧
        rows.map (fun r => r.2.2) = choices := by
  induction old generalizing new choices with
  | nil =>
      have hn : new = [] := List.length_eq_zero_iff.mp (by simpa using hnew)
      have hc : choices = [] := List.length_eq_zero_iff.mp (by simpa using hchoices)
      subst new
      subst choices
      exact ⟨[], rfl, rfl, rfl⟩
  | cons old olds ih =>
      cases new with
      | nil => simp at hnew
      | cons new news =>
          cases choices with
          | nil => simp at hchoices
          | cons choice choices =>
              simp only [List.length_cons, Nat.succ.injEq] at hnew hchoices
              rcases ih _ _ hnew hchoices with ⟨rows, hold, hnew, hchoices⟩
              exact ⟨(old, new, choice) :: rows, by simp [hold], by simp [hnew],
                by simp [hchoices]⟩

private theorem foldList_product
    {L R X A B C D E : Type}
    (big : (L × R) → List X → L × R)
    (left : L → List A → List B → L)
    (right : R → List C → List D → List E → R)
    (fa : X → A) (fb : X → B) (fc : X → C) (fd : X → D) (fe : X → E)
    (leftStep : L → X → L) (rightStep : R → X → R)
    (hbigNil : ∀ q, big q [] = q)
    (hleftNil : ∀ q, left q [] [] = q)
    (hrightNil : ∀ q, right q [] [] [] = q)
    (hbigCons : ∀ q x xs,
      big q (x :: xs) = big (leftStep q.1 x, rightStep q.2 x) xs)
    (hleftCons : ∀ q x xs ys,
      left q (fa x :: xs) (fb x :: ys) = left (leftStep q x) xs ys)
    (hrightCons : ∀ q x xs ys zs,
      right q (fc x :: xs) (fd x :: ys) (fe x :: zs) =
        right (rightStep q x) xs ys zs)
    (q : L × R) (xs : List X) :
    big q xs =
      (left q.1 (xs.map fa) (xs.map fb),
        right q.2 (xs.map fc) (xs.map fd) (xs.map fe)) := by
  induction xs generalizing q with
  | nil => simp only [List.map_nil, hbigNil, hleftNil, hrightNil]
  | cons x xs ih =>
      rw [hbigCons, ih]
      simp only [List.map_cons]
      rw [hleftCons, hrightCons]

private theorem foldList_hom
    {S Q X : Type} (big : S → List X → S) (small : Q → List X → Q)
    (embed : Q → S) (bigStep : S → X → S) (smallStep : Q → X → Q)
    (hbigNil : ∀ s, big s [] = s) (hsmallNil : ∀ q, small q [] = q)
    (hbigCons : ∀ s x xs, big s (x :: xs) = big (bigStep s x) xs)
    (hsmallCons : ∀ q x xs, small q (x :: xs) = small (smallStep q x) xs)
    (hstep : ∀ q x, bigStep (embed q) x = embed (smallStep q x))
    (q : Q) (xs : List X) : big (embed q) xs = embed (small q xs) := by
  induction xs generalizing q with
  | nil => rw [hbigNil, hsmallNil]
  | cons x xs ih => rw [hbigCons, hstep, ih, hsmallCons]

private theorem foldList_eq_of_firstStep
    {S X : Type} (big : S → List X → S) (step : S → X → S)
    (hcons : ∀ s x xs, big s (x :: xs) = big (step s x) xs)
    (s t : S) (xs : List X) (hne : xs ≠ [])
    (hstep : ∀ x, step s x = step t x) : big s xs = big t xs := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs => rw [hcons, hcons, hstep]

private noncomputable def evalCompositeTriples (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) :
    (InputPhase × WorkScanState g) →
      List (RunCell g × RunCell g × (Fin workWidth → WorkPhase)) →
        InputPhase × WorkScanState g
  | state, [] => state
  | state, (old, new, choice) :: rows =>
      evalCompositeTriples g cert
        (inputStep cert state.1 old new,
          evalWorkBlock g cert state.2 old.block new.block choice) rows

private theorem evalCompositeTriples_cons (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : InputPhase × WorkScanState g)
    (old new : RunCell g) (choice : Fin workWidth → WorkPhase)
    (rows : List (RunCell g × RunCell g × (Fin workWidth → WorkPhase))) :
    evalCompositeTriples g cert state ((old, new, choice) :: rows) =
      evalCompositeTriples g cert
        (inputStep cert state.1 old new,
          evalWorkBlock g cert state.2 old.block new.block choice) rows := rfl

private theorem evalCompositeTriples_eq (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g)
    (rows : List (RunCell g × RunCell g × (Fin workWidth → WorkPhase)))
    (inputState : InputPhase) (workState : WorkScanState g) :
    evalCompositeTriples g cert (inputState, workState) rows =
      (evalInputBlocks cert inputState (rows.map fun r => r.1)
          (rows.map fun r => r.2.1),
        evalWorkBlocks g cert workState
          (rows.map fun r => r.1.block) (rows.map fun r => r.2.1.block)
          (rows.map fun r => r.2.2)) := by
  have hflat : evalCompositeTriples g cert (inputState, workState) rows =
      (evalInputBlocks cert inputState (rows.map fun r => r.1)
          (rows.map fun r => r.2.1),
        evalWorkSlots g cert workState
          ((rows.map fun r => r.1.block).flatMap List.ofFn)
          ((rows.map fun r => r.2.1.block).flatMap List.ofFn)
          ((rows.map fun r => r.2.2).flatMap List.ofFn)) := by
    apply foldList_product (evalCompositeTriples g cert) (evalInputBlocks cert)
      (fun q olds news choices => evalWorkSlots g cert q
        (olds.flatMap List.ofFn) (news.flatMap List.ofFn)
        (choices.flatMap List.ofFn)) (fun r => r.1) (fun r => r.2.1)
      (fun r => r.1.block) (fun r => r.2.1.block) (fun r => r.2.2)
      (fun q r => inputStep cert q r.1 r.2.1)
      (fun q r => evalWorkBlock g cert q r.1.block r.2.1.block r.2.2)
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q r rs
      rcases r with ⟨old, new, choice⟩
      exact evalCompositeTriples_cons g cert q old new choice rs
    · intros; rfl
    · intro q r olds news choices
      simp only [List.flatMap_cons]
      rw [evalWorkSlots_append g cert q (List.ofFn r.1.block)
        (olds.flatMap List.ofFn) (List.ofFn r.2.1.block)
        (news.flatMap List.ofFn) (List.ofFn r.2.2)
        (choices.flatMap List.ofFn) (by simp) (by simp)]
      rfl
  rw [evalWorkBlocks_eq_evalWorkSlots g cert workState
    (rows.map fun r => r.1.block) (rows.map fun r => r.2.1.block)
    (rows.map fun r => r.2.2) (by simp) (by simp)]
  exact hflat

private theorem evalRowTriples_composite_from
    (g : IndexedGrammar T) [Fintype g.nt] (cert : CompositeCert g)
    (rows : List (RunCell g × RunCell g × (Fin workWidth → WorkPhase)))
    (inputState : InputPhase) (workState : WorkScanState g) :
    evalRowTriples g (.composite cert inputState workState)
        (rows.map fun r => (RowCell.run r.1, RowCell.run r.2.1,
          RowCert.composite cert r.2.2)) =
      .composite cert
        (evalInputBlocks cert inputState (rows.map fun r => r.1)
          (rows.map fun r => r.2.1))
        (evalWorkBlocks g cert workState
          ((rows.map fun r => r.1).map RunCell.block)
          ((rows.map fun r => r.2.1).map RunCell.block)
          (rows.map fun r => r.2.2)) := by
  let physical := fun r : RunCell g × RunCell g × (Fin workWidth → WorkPhase) =>
    (RowCell.run r.1, RowCell.run r.2.1, RowCert.composite cert r.2.2)
  have hfold := foldList_hom
    (fun state rs => evalRowTriples g state (rs.map physical))
    (evalCompositeTriples g cert)
    (fun q => RowState.composite cert q.1 q.2)
    (fun state r => rowStepCell g state (RowCell.run r.1) (RowCell.run r.2.1)
      (RowCert.composite cert r.2.2))
    (fun q r => (inputStep cert q.1 r.1 r.2.1,
      evalWorkBlock g cert q.2 r.1.block r.2.1.block r.2.2))
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro q r; simp)
    (inputState, workState) rows
  rw [evalCompositeTriples_eq g cert rows inputState workState] at hfold
  simpa [physical, List.map_map, Function.comp_def] using hfold

private theorem evalStep_composite_triples_from
    (g : IndexedGrammar T) [Fintype g.nt] (cert : CompositeCert g)
    (rows : List (RunCell g × RunCell g × (Fin workWidth → WorkPhase)))
    (inputState : InputPhase) (workState : WorkScanState g) :
    (ahoRowSystem g).evalStep (.composite cert inputState workState)
        (rows.map fun r => RowCell.run r.1) (rows.map fun r => RowCell.run r.2.1)
        (rows.map fun r => RowCert.composite cert r.2.2) =
      some (.composite cert
        (evalInputBlocks cert inputState (rows.map fun r => r.1)
          (rows.map fun r => r.2.1))
        (evalWorkBlocks g cert workState
          ((rows.map fun r => r.1).map RunCell.block)
          ((rows.map fun r => r.2.1).map RunCell.block)
          (rows.map fun r => r.2.2))) := by
  let triples := rows.map fun r =>
    (RowCell.run r.1, RowCell.run r.2.1, RowCert.composite cert r.2.2)
  have heval := evalStep_rowTriples g (.composite cert inputState workState) triples
  rw [evalRowTriples_composite_from g cert rows inputState workState] at heval
  simpa [triples, List.map_map, Function.comp_def] using heval

public theorem evalStep_composite_from (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (inputState : InputPhase) (workState : WorkScanState g)
    (old new : List (RunCell g)) (choices : List (Fin workWidth → WorkPhase))
    (hnew : new.length = old.length) (hchoices : choices.length = old.length) :
    (ahoRowSystem g).evalStep (.composite cert inputState workState)
        (old.map RowCell.run) (new.map RowCell.run)
        (choices.map (RowCert.composite cert)) =
      some (.composite cert
        (evalInputBlocks cert inputState old new)
        (evalWorkBlocks g cert workState (old.map RunCell.block)
          (new.map RunCell.block) choices)) :=
  by
    rcases exists_runRowTriples g old new choices hnew hchoices with
      ⟨rows, hold, hnew, hchoices⟩
    subst old
    subst new
    subst choices
    simpa [List.map_map, Function.comp_def] using
      evalStep_composite_triples_from g cert rows inputState workState

private theorem evalRowTriples_composite_start
    (g : IndexedGrammar T) [Fintype g.nt] (cert : CompositeCert g)
    (rows : List (RunCell g × RunCell g × (Fin workWidth → WorkPhase)))
    (hne : rows ≠ []) :
    evalRowTriples g .start
        (rows.map fun r => (RowCell.run r.1, RowCell.run r.2.1,
          RowCert.composite cert r.2.2)) =
      .composite cert
        (evalInputBlocks cert .prefix (rows.map fun r => r.1)
          (rows.map fun r => r.2.1))
        (evalWorkBlocks g cert (initialWorkScan g)
          ((rows.map fun r => r.1).map RunCell.block)
          ((rows.map fun r => r.2.1).map RunCell.block)
          (rows.map fun r => r.2.2)) := by
  let physical := fun r : RunCell g × RunCell g × (Fin workWidth → WorkPhase) =>
    (RowCell.run r.1, RowCell.run r.2.1, RowCert.composite cert r.2.2)
  have hstart := foldList_eq_of_firstStep
    (fun state rs => evalRowTriples g state (rs.map physical))
    (fun state r => rowStepCell g state (RowCell.run r.1) (RowCell.run r.2.1)
      (RowCert.composite cert r.2.2))
    (by intros; rfl) .start
    (.composite cert .prefix (initialWorkScan g)) rows hne (by
      intro r
      dsimp
      rw [rowStepCell_composite_start, rowStepCell_composite_same])
  calc
    evalRowTriples g .start
        (rows.map fun r => (RowCell.run r.1, RowCell.run r.2.1,
          RowCert.composite cert r.2.2)) =
        evalRowTriples g (.composite cert .prefix (initialWorkScan g))
          (rows.map fun r => (RowCell.run r.1, RowCell.run r.2.1,
            RowCert.composite cert r.2.2)) := by simpa [physical] using hstart
    _ = _ := evalRowTriples_composite_from g cert rows .prefix (initialWorkScan g)

private theorem evalStep_composite_triples_start
    (g : IndexedGrammar T) [Fintype g.nt] (cert : CompositeCert g)
    (rows : List (RunCell g × RunCell g × (Fin workWidth → WorkPhase)))
    (hne : rows ≠ []) :
    (ahoRowSystem g).evalStep .start
        (rows.map fun r => RowCell.run r.1) (rows.map fun r => RowCell.run r.2.1)
        (rows.map fun r => RowCert.composite cert r.2.2) =
      some (.composite cert
        (evalInputBlocks cert .prefix (rows.map fun r => r.1)
          (rows.map fun r => r.2.1))
        (evalWorkBlocks g cert (initialWorkScan g)
          ((rows.map fun r => r.1).map RunCell.block)
          ((rows.map fun r => r.2.1).map RunCell.block)
          (rows.map fun r => r.2.2))) := by
  let triples := rows.map fun r =>
    (RowCell.run r.1, RowCell.run r.2.1, RowCert.composite cert r.2.2)
  have heval := evalStep_rowTriples g .start triples
  rw [evalRowTriples_composite_start g cert rows hne] at heval
  simpa [triples, List.map_map, Function.comp_def] using heval

public theorem evalStep_composite_start (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (old new : List (RunCell g))
    (choices : List (Fin workWidth → WorkPhase))
    (hne : old ≠ []) (hnew : new.length = old.length)
    (hchoices : choices.length = old.length) :
    (ahoRowSystem g).evalStep .start
        (old.map RowCell.run) (new.map RowCell.run)
        (choices.map (RowCert.composite cert)) =
      some (.composite cert
        (evalInputBlocks cert .prefix old new)
        (evalWorkBlocks g cert (initialWorkScan g) (old.map RunCell.block)
          (new.map RunCell.block) choices)) :=
  by
    rcases exists_runRowTriples g old new choices hnew hchoices with
      ⟨rows, hold, hnew, hchoices⟩
    have hrows : rows ≠ [] := by
      intro hr
      apply hne
      simpa [hr] using hold.symm
    subst old
    subst new
    subst choices
    simpa [List.map_map, Function.comp_def] using
      evalStep_composite_triples_start g cert rows hrows

private theorem exists_phaseFn_of_length {n : ℕ} {phases : List WorkPhase}
    (h : phases.length = n) :
    ∃ choices : Fin n → WorkPhase, List.ofFn choices = phases := by
  let choices : Fin n → WorkPhase := fun i =>
    phases.get ⟨i.val, by simp [h]⟩
  refine ⟨choices, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi₁ hi₂
    simp [choices]

public theorem exists_phaseBlocks_of_workTraceAccepts
    (g : IndexedGrammar T) [Fintype g.nt] (cert : CompositeCert g)
    (n : ℕ) (old new : List (WorkSlot g))
    (h : WorkTraceAccepts g cert (paddedWork n old) (paddedWork n new)) :
    ∃ (choices : List (Fin workWidth → WorkPhase)) (result : WorkScanState g),
      choices.length = n ∧
      evalWorkBlocks g cert (initialWorkScan g)
          (packedBlockList g old 0 n) (packedBlockList g new 0 n) choices = result ∧
      workScanDone result = true := by
  rcases evalWorkSlots_of_accepts g cert h with
    ⟨phases, result, hphaseLen, _, heval, hdone⟩
  have hlen : phases.length = n * workWidth := by
    simpa using hphaseLen
  rcases exists_phaseFn_of_length hlen with ⟨phaseFn, hphaseFn⟩
  let choices := phaseBlockList n phaseFn
  refine ⟨choices, result, by simp [choices], ?_, hdone⟩
  rw [evalWorkBlocks_eq_evalWorkSlots g cert (initialWorkScan g)
    (packedBlockList g old 0 n) (packedBlockList g new 0 n) choices
    (by simp [packedBlockList]) (by simp [choices, packedBlockList])]
  rw [packedBlockList_flatten, packedBlockList_flatten,
    phaseBlockList_flatten, hphaseFn]
  exact heval

/-- One bounded semantic Aho certificate is accepted by the physical certified-row checker. -/
public theorem rowStep_of_certStep (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) (cert : CompositeCert g) (old new : Config g)
    (hne : input ≠ []) (holdPos : old.InputWithin input)
    (hnewPos : new.InputWithin input)
    (holdWork : old.Within (input.length * workWidth))
    (hnewWork : new.Within (input.length * workWidth))
    (hstep : CertStep g input cert old new) :
    (ahoRowSystem g).RowStep
      (encodeRunRow g input old) (encodeRunRow g input new) := by
  have hwork := workTraceAccepts_of_certStep g input cert input.length hstep
    holdWork hnewWork
  rcases exists_phaseBlocks_of_workTraceAccepts g cert input.length
      old.work.slots new.work.slots hwork with
    ⟨choices, workResult, hchoices, hworkEval, hworkDone⟩
  have hinputDone := evalInputBlocks_encodeRunCells_complete g cert input old new
    holdPos hnewPos (certStep_inputAction input cert hstep)
  let oldCells := encodeRunCells g input old
  let newCells := encodeRunCells g input new
  have holdCells : oldCells.length = input.length := by
    simp [oldCells]
  have hnewCells : newCells.length = oldCells.length := by
    simp [oldCells, newCells]
  have holdNe : oldCells ≠ [] := by
    intro hnil
    apply hne
    have := holdCells
    simp [hnil] at this
    exact List.length_eq_zero_iff.mp this.symm
  let inputResult := evalInputBlocks cert .prefix oldCells newCells
  refine ⟨choices.map (RowCert.composite cert),
    .composite cert inputResult workResult, ?_, ?_⟩
  · rw [encodeRunRow_eq_map_run, encodeRunRow_eq_map_run]
    have heval := evalStep_composite_start g cert oldCells newCells choices holdNe
      hnewCells (by simpa [holdCells] using hchoices)
    simp only [oldCells, newCells, encodeRunCells_map_block] at heval
    rw [hworkEval] at heval
    exact heval
  · simp only [ahoRowSystem, rowStepDone, Bool.and_eq_true]
    exact ⟨by simpa [inputResult, oldCells, newCells] using hinputDone, hworkDone⟩

/-- Every semantic composite padded-row edge is accepted by the certified row system;
initialization is handled separately by `rowStep_of_paddedRowStep`. -/
public theorem rowStep_of_paddedCompositeStep (g : IndexedGrammar T) [Fintype g.nt]
    {old new : List (RowCell g)} (h : PaddedCompositeStep g old new) :
    (ahoRowSystem g).RowStep old new := by
  rcases h with ⟨input, c, c', hne, hcpos, hc'pos, hcwork, hc'work,
    ⟨cert, hcert⟩, rfl, rfl⟩
  exact rowStep_of_certStep g input cert c c' hne hcpos hc'pos hcwork hc'work hcert

/-- Every semantic padded-row edge has a finite certificate row. -/
public theorem rowStep_of_paddedRowStep (g : IndexedGrammar T) [Fintype g.nt]
    {old new : List (RowCell g)} (h : PaddedRowStep g old new) :
    (ahoRowSystem g).RowStep old new := by
  rcases h with hinit | hcomposite
  · exact rowStep_of_paddedInitStep g hinit
  · exact rowStep_of_paddedCompositeStep g hcomposite

/-- Semantic padded reachability embeds into the executable finite row system. -/
public theorem rowReachLanguage_of_paddedReachLanguage
    (g : IndexedGrammar T) [Fintype g.nt] :
    ∀ input : List T, input ∈ paddedReachLanguage g →
      input ∈ (ahoRowSystem g).rowReachLanguage := by
  intro input hmem
  rcases hmem with ⟨hne, row, hreach, hfinal⟩
  refine ⟨hne, row, ?_, (final_ahoRowSystem_iff g row).2 hfinal⟩
  simpa [inputRow, ahoRowSystem] using
    hreach.mono (fun _ _ hstep => rowStep_of_paddedRowStep g hstep)

end Aho
end IndexedGrammar
