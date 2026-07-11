module

public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayStructural
public import Langlib.Grammars.Indexed.NormalForm.AhoPlainRunner
public import Langlib.Grammars.Indexed.NormalForm.AhoProtectedStructural

@[expose]
public section

/-!
# Root invocation of Aho's invariant-carrying scheduler

This file discharges the bookkeeping which is specific to the initial parse task.  Initially no
productive-event owner is in use, so the complete finite carrier is the free-owner pool.  Once the
mutual compressed runner is supplied, its plain projection is therefore an accepting bounded run.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Initially every productive-event owner is free. -/
public def initialIndexOwnerPool
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    IndexOwnerPool (initialScheduleCursor parse) where
  free := genericOwnerRange g input
  all_nodup := by
    simpa [initialScheduleCursor, initialScheduleTask,
      ScheduleCursor.indexOwners, ScheduleCursor.word,
      ScheduleAtom.indexOwner?] using
      (genericOwnerRange_nodup g input)
  all_perm := by
    simp [initialScheduleCursor, initialScheduleTask,
      ScheduleCursor.indexOwners, ScheduleCursor.word,
      ScheduleAtom.indexOwner?]

@[simp] public theorem initialIndexOwnerPool_free
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    (initialIndexOwnerPool parse).free =
      genericOwnerRange g input := rfl

/-- The root cursor has no persistent owners, so its logical ticket ledger is the unique
empty live assignment. -/
public def initialIndexTicketLedger
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    IndexTicketLedger (initialScheduleCursor parse) :=
  IndexTicketLedger.ofEmpty parse.yield_length_pos (by
    simp [initialScheduleCursor, initialScheduleTask,
      ScheduleCursor.indexOwners, ScheduleCursor.word,
      ScheduleAtom.indexOwner?])

/-- The empty root ledger satisfies the strict window-addressed parking invariant. -/
public theorem initialParkingBelow
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    (initialIndexTicketLedger parse).ParkingBelow
      (ProductiveOwnerWindow.root parse) := by
  unfold initialIndexTicketLedger
  apply IndexTicketLedger.parkingBelow_ofEmpty

/-- Productive-owner provenance on the root's empty logical projection. -/
public def initialTicketOwnerLedger
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    (initialIndexTicketLedger parse).SemanticScheduleOwnerLedger parse
      (ProductiveOwnerWindow.root parse) := by
  simpa [initialIndexTicketLedger, IndexTicketLedger.semanticCursor,
    ScheduleCursor.relabelTicketOwners, initialScheduleCursor,
    initialScheduleTask] using ScheduleOwnerLedger.root parse

/-- Shadow-owner provenance on the same empty root projection. -/
public def initialTicketShadowLedger
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    (initialIndexTicketLedger parse).SemanticShadowOwnerLedger parse
      (ProductiveOwnerWindow.root parse) := by
  simpa [initialIndexTicketLedger, IndexTicketLedger.semanticCursor,
    ScheduleCursor.relabelTicketOwners, initialScheduleCursor,
    initialScheduleTask] using ShadowOwnerLedger.root parse

/-- The root task begins with the exact full productive-event credit and owns the whole input
interval. -/
public def initialScheduleRunResources
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
  ScheduleRunResources parse [] (initialScheduleCursor parse) where
  pool := initialIndexOwnerPool parse
  tickets := initialIndexTicketLedger parse
  window := ProductiveOwnerWindow.root parse
  parkingAtOrBelow := (initialParkingBelow parse).toAtOrBelow
  ownerLedger := ScheduleOwnerLedger.root parse
  ticketOwnerLedger := initialTicketOwnerLedger parse
  ticket_active_eq := by
    simp [initialTicketOwnerLedger, ScheduleOwnerLedger.root,
      IndexTicketLedger.semanticOwners]
  ticketShadowBlocks := []
  ticketShadowOwners := []
  ticketShadowOwners_subset := by simp
  ticketShadowOwners_nodup := by simp
  ticketShadowLedger := initialTicketShadowLedger parse
  ticket_shadow_active_eq := by
    change ([] : List (Fin (10 * input.length))) = []
    rfl
  ticketShadowLayout := ShadowStartLayout.nil
  shadowLedger := ShadowOwnerLedger.root parse
  shadow_active_eq := rfl
  charged := 0
  charged_eq_indices := by
    simp [initialScheduleCursor, initialScheduleTask,
      ScheduleCursor.indexOwners, ScheduleCursor.word,
      ScheduleAtom.indexOwner?]
  charged_le_indices := Nat.zero_le _
  productive_le_credit := by
    rw [parse.productiveCount_eq_twice_yield_length_sub_one]
    simp
    omega
  task_locality := by
    intro owner howner
    simp [initialScheduleCursor, initialScheduleTask,
      ScheduleCursor.taskOwners, ScheduleCursor.word,
      ScheduleAtom.taskOwner?, ScheduleTask.owner] at howner
    exact Or.inl (by simpa using congrArg Fin.val howner)

/-- Ordinary protected/plain execution and copy-on-write overlay execution are constructed
simultaneously by strong recursion on parse node count. -/
public theorem completeScheduleRuns
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : CompleteScheduleRuns parse := by
  refine ⟨⟨plainScheduleRun_of_smaller parse ?_ ?_,
    protectedScheduleRun_of_smaller parse ?_ ?_⟩,
    overlayScheduleRun_of_smaller parse ?_ ?_⟩
  · intro B residualStack yield q hq
    exact (completeScheduleRuns q).1
  · intro B residualStack yield q hq
    exact (completeScheduleRuns q).2
  · intro B residualStack yield q hq
    exact (completeScheduleRuns q).1
  · intro B residualStack yield q hq
    exact (completeScheduleRuns q).2
  · intro B residualStack yield q hq
    exact (completeScheduleRuns q).1
  · intro B residualStack yield q hq
    exact (completeScheduleRuns q).2
termination_by parse.nodeCount

/-- A completed mutual compressed-runner proof supplies the ownership-preserving root schedule. -/
public theorem parseScheduled_of_completeScheduleRuns
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input)
    (runs : CompleteScheduleRuns parse) : ParseScheduled parse := by
  have run := runs.1.1
    (input := input)
    (parse.not_consumesAt_of_stack_nil 0)
    ([] : List T) [] (by simp) [] (.hash : ScheduleAtom g input) []
    (stablePrefix_nil g)
    (initialScheduleCursor_invariant parse)
    (by simpa [scheduleWordCursor] using
      finalScheduleCursor_invariant (g := g) input)
    (initialScheduleRunResources parse)
    (by
      intro hnil
      have hlength := congrArg List.length hnil
      simp [initialScheduleRunResources, initialIndexOwnerPool] at hlength
      have hpositive := parse.yield_length_pos
      omega)
    (initialParkingBelow parse)
    (by simp [initialScheduleRunResources, ScheduleOwnerLedger.root])
    (ShadowStartLayout.nil)
    (by
      intro _hinput hmem
      simp [plainScheduleCursor, ScheduleCursor.indexTickets,
        ScheduleCursor.indexOwners, ScheduleCursor.word,
        ScheduleAtom.indexOwner?] at hmem)
    (by
      intro _hinput hmem
      simp [plainScheduleCursor,
        ScheduleCursor.indexOwners, ScheduleCursor.word,
        ScheduleAtom.indexOwner?] at hmem)
    (by
      intro _hinput hmem
      simp [plainScheduleCursor,
        ScheduleCursor.indexOwners, ScheduleCursor.word,
        ScheduleAtom.indexOwner?] at hmem)
  simpa [ParseScheduled, initialScheduleState, finalScheduleState,
    initialScheduleCursor, plainScheduleCursor, scheduleWordCursor,
    scheduleStateOfCursor] using run

/-- The invariant-carrying mutual runner implies the concrete `21|w|` completeness theorem. -/
public theorem complete_bounded_of_completeScheduleRuns
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input)
    (runs : CompleteScheduleRuns parse) :
    BoundedReaches g input (21 * input.length)
      (initialConfig g) (finalConfig g input.length) :=
  complete_bounded_of_parseScheduled parse
    (parseScheduled_of_completeScheduleRuns parse runs)

/-- Every normal-form parse has a uniform `21|w|` bounded accepting run. -/
public theorem complete_bounded
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    BoundedReaches g input (21 * input.length)
      (initialConfig g) (finalConfig g input.length) :=
  complete_bounded_of_completeScheduleRuns parse (completeScheduleRuns parse)

end Aho
end IndexedGrammar
