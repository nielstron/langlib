module

public import Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.Trace
public import Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowInput

@[expose]
public section

/-!
# Trace foundations for Aho's logical-slot checker

The work-cursor semantics, canonical-padding inversion, and shared suffix decoder used by the
certificate-specific soundness proofs.
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

/-- Old-track cells projected from synchronized trace rows. -/
public def oldProjection
    (rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)) :
    List (Option (WorkSlot g)) :=
  rows.map fun r => r.1

/-- New-track cells projected from synchronized trace rows. -/
public def newProjection
    (rows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)) :
    List (Option (WorkSlot g)) :=
  rows.map fun r => r.2.1

/-- In the equal-suffix phase, the remaining non-padding symbols are the same inactive word on
both tracks. -/
public theorem WorkTrace.decodeSuffixSame
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

end Aho
end IndexedGrammar
