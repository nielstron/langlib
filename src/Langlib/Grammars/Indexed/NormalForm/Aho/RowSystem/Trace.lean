module

public import Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.Checker

@[expose]
public section

/-!
# Logical-slot traces for Aho's row checker

This module gives the proof-relevant trace relation behind the finite checker. A trace records
every aligned old/new logical slot and scan phase, enforces canonical `some* none*` padding on
both tracks, and connects accepting traces to the executable slot evaluator.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Logical-slot traces -/

public def advanceWorkState (state : WorkScanState g)
    (old new : Option (WorkSlot g)) (next : WorkPhase) : WorkScanState g :=
  ⟨next, updateHistory state.history old new,
    state.oldEnded || old.isNone, state.newEnded || new.isNone⟩

public def ValidWorkEdge (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old new : Option (WorkSlot g)) (next : WorkPhase) : Prop :=
  state.phase ≠ .dead ∧ next ≠ .dead ∧
    paddingOK state.oldEnded old ∧ paddingOK state.newEnded new ∧
    WorkEdge g cert state.phase next state.history old new

@[simp] public theorem workSlotStep_of_valid (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old new : Option (WorkSlot g)) (next : WorkPhase)
    (h : ValidWorkEdge g cert state old new next) :
    workSlotStep g cert state old new next = advanceWorkState state old new next := by
  classical
  simp only [workSlotStep, advanceWorkState]
  rw [if_pos ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩]

public theorem valid_of_workSlotStep_phase_ne_dead
    (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old new : Option (WorkSlot g)) (next : WorkPhase)
    (h : (workSlotStep g cert state old new next).phase ≠ .dead) :
    ValidWorkEdge g cert state old new next := by
  classical
  unfold workSlotStep at h
  split at h
  · rename_i hedge
    exact ⟨hedge.1, h, hedge.2.1, hedge.2.2.1, hedge.2.2.2⟩
  · simp at h

@[simp] public theorem workSlotStep_phase_dead
    (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old new : Option (WorkSlot g)) (next : WorkPhase)
    (h : state.phase = .dead) :
    (workSlotStep g cert state old new next).phase = .dead := by
  classical
  unfold workSlotStep
  rw [if_neg (by simp [h])]

public theorem evalWorkSlots_phase_dead
    (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
    (h : state.phase = .dead) :
    (evalWorkSlots g cert state (rows.map fun r => r.1)
      (rows.map fun r => r.2.1) (rows.map fun r => r.2.2)).phase = .dead := by
  induction rows generalizing state with
  | nil => exact h
  | cons row rows ih =>
      rcases row with ⟨old, new, next⟩
      simp only [List.map_cons, evalWorkSlots]
      exact ih _ (workSlotStep_phase_dead g cert state old new next h)

/-- The exact `some* none*` discipline enforced independently on each padded work track. -/
public inductive PaddingStream (g : IndexedGrammar T) :
    Bool → List (Option (WorkSlot g)) → Prop
  | nil (ended) : PaddingStream g ended []
  | cons {ended x xs}
      (hhead : paddingOK ended x)
      (htail : PaddingStream g (ended || x.isNone) xs) :
      PaddingStream g ended (x :: xs)

public theorem paddingStream_replicate_none (g : IndexedGrammar T)
    (ended : Bool) (k : ℕ) :
    PaddingStream g ended (List.replicate k none) := by
  induction k generalizing ended with
  | zero => exact .nil _
  | succ k ih =>
      simp only [List.replicate_succ]
      exact .cons (by simp [paddingOK]) (by simpa using ih true)

public theorem paddingStream_inactive_append_none (g : IndexedGrammar T)
    (xs : List (WorkSym g)) (k : ℕ) :
    PaddingStream g false (xs.map inactive ++ List.replicate k none) := by
  induction xs with
  | nil => simpa using paddingStream_replicate_none g false k
  | cons x xs ih =>
      simp only [List.map_cons, List.cons_append]
      exact .cons (by simp [paddingOK]) (by simpa [inactive] using ih)

public theorem PaddingStream.tail {g : IndexedGrammar T} {ended : Bool}
    {x : Option (WorkSlot g)} {xs : List (Option (WorkSlot g))}
    (h : PaddingStream g ended (x :: xs)) :
    PaddingStream g (ended || x.isNone) xs := by
  cases h
  assumption

public theorem PaddingStream.head {g : IndexedGrammar T} {ended : Bool}
    {x : Option (WorkSlot g)} {xs : List (Option (WorkSlot g))}
    (h : PaddingStream g ended (x :: xs)) : paddingOK ended x := by
  cases h
  assumption

public theorem PaddingStream.append_none {g : IndexedGrammar T} {ended : Bool}
    {xs : List (Option (WorkSlot g))} (h : PaddingStream g ended xs) :
    PaddingStream g ended (xs ++ [none]) := by
  induction h with
  | nil ended => exact .cons (by simp [paddingOK]) (.nil _)
  | cons hhead htail ih => exact .cons hhead ih

/-- A successful aligned slot trace, retaining every local edge fact needed for inversion. -/
public inductive WorkTrace (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) : WorkScanState g →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase) →
      WorkScanState g → Prop
  | nil (state) : WorkTrace g cert state [] state
  | cons {state old new next rows result}
      (hedge : ValidWorkEdge g cert state old new next)
      (htail : WorkTrace g cert (advanceWorkState state old new next) rows result) :
      WorkTrace g cert state ((old, new, next) :: rows) result

public theorem evalWorkSlots_of_trace (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) {state result : WorkScanState g}
    {rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (h : WorkTrace g cert state rows result) :
    evalWorkSlots g cert state (rows.map fun r => r.1)
        (rows.map fun r => r.2.1) (rows.map fun r => r.2.2) = result := by
  induction h with
  | nil => rfl
  | cons hedge htail ih =>
      simp only [List.map_cons, evalWorkSlots, workSlotStep_of_valid _ _ _ _ _ _ hedge]
      exact ih

public theorem trace_of_evalWorkSlots_phase_ne_dead
    (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
    (hne : (evalWorkSlots g cert state (rows.map fun r => r.1)
      (rows.map fun r => r.2.1) (rows.map fun r => r.2.2)).phase ≠ .dead) :
    WorkTrace g cert state rows
      (evalWorkSlots g cert state (rows.map fun r => r.1)
        (rows.map fun r => r.2.1) (rows.map fun r => r.2.2)) := by
  induction rows generalizing state with
  | nil => exact .nil state
  | cons row rows ih =>
      rcases row with ⟨old, new, next⟩
      simp only [List.map_cons, evalWorkSlots] at hne ⊢
      have hstep : (workSlotStep g cert state old new next).phase ≠ .dead := by
        intro hdead
        exact hne (evalWorkSlots_phase_dead g cert _ rows hdead)
      have hedge := valid_of_workSlotStep_phase_ne_dead g cert state old new next hstep
      rw [workSlotStep_of_valid g cert state old new next hedge] at hne ⊢
      exact .cons hedge (ih _ hne)

/-- Acceptance of two already-aligned logical-slot streams. -/
public def WorkTraceAccepts (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g)
    (old new : List (Option (WorkSlot g))) : Prop :=
  ∃ rows result,
    WorkTrace g cert (initialWorkScan g) rows result ∧
      rows.map (fun r => r.1) = old ∧
      rows.map (fun r => r.2.1) = new ∧
      workScanDone result = true

public theorem evalWorkSlots_of_accepts (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) {old new : List (Option (WorkSlot g))}
    (h : WorkTraceAccepts g cert old new) :
    ∃ phases result,
      phases.length = old.length ∧ new.length = old.length ∧
      evalWorkSlots g cert (initialWorkScan g) old new phases = result ∧
      workScanDone result = true := by
  rcases h with ⟨rows, result, htrace, hold, hnew, hdone⟩
  refine ⟨rows.map (fun r => r.2.2), result, ?_, ?_, ?_, hdone⟩
  · simp [← hold]
  · simp [← hold, ← hnew]
  · rw [← hold, ← hnew]
    exact evalWorkSlots_of_trace g cert htrace

end Aho
end IndexedGrammar
