module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.CompressedState
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Resources.Moves
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Resources.RunResources
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.EventCompatibility
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Ownership.PushFreshness
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Runners.Overlay.Interface

@[expose]
public section

/-!
# Plain-mode compressed scheduler

Plain tasks consume no inherited stack occurrence.  Their binary, irrelevant-push, and terminal
moves only rearrange terminal-owned payloads; a relevant push temporarily allocates one
productive-event owner and delegates to copy-on-write overlay execution.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

@[simp] public theorem scheduleTaskOfParse_owner_val
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) (pre post : List T)
    (input_eq : input = pre ++ w ++ post) (mode : TaskMode parse) :
    (scheduleTaskOfParse parse pre post input_eq mode).owner.val = pre.length := rfl

namespace IndexOwnerPool

/-- Transport a free-owner pool across a cursor change which preserves persistent indices. -/
public def transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (hindices : new.indexOwners = old.indexOwners) : IndexOwnerPool new where
  free := pool.free
  all_nodup := by simpa [hindices] using pool.all_nodup
  all_perm := by simpa [hindices] using pool.all_perm

@[simp] public theorem transport_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (hindices : new.indexOwners = old.indexOwners) :
    (pool.transport hindices).free = pool.free := rfl

end IndexOwnerPool

/-- Run a terminal constructor in ordinary plain mode. -/
public theorem plainScheduleRun_terminal
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    PlainScheduleRun (NFParse.terminal (σ := stack) hr hlhs hc hrhs) := by
  intro input unused pre post input_eq alpha next tail hstable hstart hend
    resources hfree _parkingBelow _hactive _shadowLayout _ticketTransientFree
    _htransientFree _hScratchFree
  let parse : NFParse g A stack [a] := .terminal hr hlhs hc hrhs
  let task : ScheduleTask g input :=
    scheduleTaskOfParse parse pre post input_eq (.plain unused)
  let emitted : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .terminal task.owner a, next :: tail⟩
  have hemitted : ScheduleInvariant emitted := by
    dsimp [emitted]
    apply ScheduleInvariant.plainTerminal
      (alpha ++ [ScheduleAtom.dollar]) (next :: tail) task a
    simpa [parse, task, plainScheduleCursor] using hstart
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos _ hstart
  let emittedState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos emitted hemitted
  have hterminal : ScheduleReaches g input startState emittedState := by
    apply ScheduleReaches.single
    have hstep := composite_plainTerminal_stable input
      (terminalRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
      pre.length (alpha.map ScheduleAtom.workSym)
      ((next :: tail).map ScheduleAtom.workSym) hstable
    simpa [startState, emittedState, scheduleStateOfCursor, ScheduleState.config,
      plainScheduleCursor, parse, task, emitted, scheduleTaskOfParse,
      ScheduleCursor.erase, ScheduleAtom.workSym, ScheduleTask.workSym,
      List.map_append] using hstep
  have hinput : input[pre.length]? = some a := by
    rw [input_eq]
    simp
  let endState : ScheduleState g input :=
    scheduleStateOfCursor (pre ++ [a]).length (by
      rw [input_eq]
      simp) (scheduleWordCursor alpha (next :: tail)) hend
  have hmatch : ScheduleReaches g input emittedState endState := by
    apply ScheduleReaches.single
    have hstep := composite_matchTerminal_at input a pre.length
      (alpha.map ScheduleAtom.workSym) next.workSym
      (tail.map ScheduleAtom.workSym) hinput
    simpa [emittedState, endState, scheduleStateOfCursor, ScheduleState.config,
      emitted, scheduleWordCursor, ScheduleCursor.erase, ScheduleAtom.workSym,
      List.map_append] using hstep
  exact hterminal.trans hmatch

/-- Split a plain binary task into its two ordered plain children and run them sequentially. -/
public theorem plainScheduleRun_binary
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (leftParse : NFParse g B stack u) (rightParse : NFParse g C stack v)
    (leftRuns : OrdinaryScheduleRuns leftParse)
    (rightRuns : OrdinaryScheduleRuns rightParse) :
    PlainScheduleRun
      (NFParse.binary hr hlhs hc hrhs leftParse rightParse) := by
  intro input unused pre post input_eq alpha next tail hstable hstart hend
    resources hfree parkingBelow hactive shadowLayout ticketTransientFree htransientFree
    hScratchFree
  have parkingAtOrBelow : resources.tickets.ParkingAtOrBelow resources.window :=
    parkingBelow.toAtOrBelow
  let parent : NFParse g A stack (u ++ v) :=
    .binary hr hlhs hc hrhs leftParse rightParse
  have leftUnused : ¬ leftParse.ConsumesAt 0 := fun h => unused (Or.inl h)
  have rightUnused : ¬ rightParse.ConsumesAt 0 := fun h => unused (Or.inr h)
  have leftInputEq : input = pre ++ u ++ (v ++ post) := by
    simpa [List.append_assoc] using input_eq
  have rightInputEq : input = (pre ++ u) ++ v ++ post := by
    simpa [List.append_assoc] using input_eq
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.plain unused)
  let leftTask : ScheduleTask g input :=
    scheduleTaskOfParse leftParse pre (v ++ post) leftInputEq (.plain leftUnused)
  let rightTask : ScheduleTask g input :=
    scheduleTaskOfParse rightParse (pre ++ u) post rightInputEq (.plain rightUnused)
  let startCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task parentTask, next :: tail⟩
  let forkCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task leftTask, .task rightTask :: next :: tail⟩
  let rightCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task rightTask, next :: tail⟩
  have hstart' : ScheduleInvariant startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstart
  /- Push-owner selection belongs to the unary branch below.
  have hboundary : ¬ rest.ConsumesAt 1 := by
    simpa [parent, NFParse.ConsumesAt] using unused
  have hone : 1 ∈ rest.eventDepths := by
    rcases (rest.consumesAt_iff_exists_mem_eventDepths_lt 0).1 restUsed with
      ⟨d, hd, hdpos⟩
    have hdle : d ≤ 1 := by
      by_contra hnot
      apply hboundary
      exact (rest.consumesAt_iff_exists_mem_eventDepths_lt 1).2
        ⟨d, hd, by omega⟩
    have heq : d = 1 := by omega
    simpa [heq] using hd
  have parentCompatible : EventCompatible parent [] := by
    constructor
    intro d hd
    have hd0 : d = 0 := by
      by_contra hne
      exact unused ((parent.consumesAt_iff_exists_mem_eventDepths_lt 0).2
        ⟨d, hd, Nat.pos_of_ne_zero hne⟩)
    subst d
    exact BlockLayout.Boundary.start []
  have childCompatible : EventCompatible rest [[f]] :=
    EventCompatible.pushFresh parentCompatible
  have hinputPos : 0 < input.length := by
    have hw := rest.yield_length_pos
    have hlen := congrArg List.length input_eq
    simp only [List.length_append] at hlen
    omega
  let startLedger : ScheduleOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ownerLedger
  let startShadowLedger : ShadowOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.shadowLedger
  have startActive : startLedger.active = [] := by
    simpa [startLedger, startCursor, parentTask, parent, plainScheduleCursor] using
      hactive
  have startShadowActiveEq : startShadowLedger.active = startLedger.active := by
    simpa [startShadowLedger, startLedger, startCursor, parentTask, parent,
      plainScheduleCursor] using resources.shadow_active_eq
  let canonical : Fin (10 * input.length) :=
    resources.window.pushChild.eventOwner 1 hone
  let transient : Fin (10 * input.length) :=
    ProductiveOwnerWindow.transientOwner (g := g) hinputPos
  have hcanonicalInside :
      ¬ OutsideProductiveWindow resources.window canonical := by
    intro hout
    have hlt := rest.eventOwnerNat_lt_productiveCount hone
    have hcount : parent.productiveCount = rest.productiveCount := by
      simp [parent, NFParse.productiveCount, NFParse.binaryCount,
        NFParse.terminalCount]
    simp only [canonical, OutsideProductiveWindow,
      ProductiveOwnerWindow.eventOwner_val,
      ProductiveOwnerWindow.pushChild_base] at hout
    rw [hcount] at hout
    rcases hout with hout | hout <;> omega
  have htransientFresh : transient ∉ startCursor.indexOwners := by
    simpa [transient, startCursor, parentTask, parent, plainScheduleCursor] using
      htransientFree hinputPos
  obtain ⟨owner, hownerFresh, hownerFree, hownerProvenance,
      hownerTransient, hownerKind⟩ :
      ∃ owner : Fin (10 * input.length),
        owner ∉ startCursor.indexOwners ∧ owner ∈ resources.pool.free ∧
        ((∃ hd : 1 ∈ rest.eventDepths,
            owner = resources.window.pushChild.eventOwner 1 hd) ∨
          OutsideProductiveWindow resources.window.pushChild owner) ∧
        (owner = transient → 0 ∉ rest.eventDepths) ∧
        (owner = canonical ∨ owner = transient) := by
    by_cases hshadow : canonical ∈ startCursor.frameOwners
    · have hzeroAbsent : 0 ∉ rest.eventDepths := by
        intro hzero
        rcases startLedger.frames.owner_at canonical hshadow with
          hout | ⟨event, heq⟩
        · exact hcanonicalInside hout
        · rcases event with ⟨d, hd⟩
          have hd0 : d = 0 := by
            by_contra hne
            exact unused ((parent.consumesAt_iff_exists_mem_eventDepths_lt 0).2
              ⟨d, hd, Nat.pos_of_ne_zero hne⟩)
          subst d
          have htransport := resources.window.eventOwner_push hd
          have hcollision : resources.window.pushChild.eventOwner 1 hone =
              resources.window.pushChild.eventOwner 0 hzero := by
            simpa [canonical, NFParse.pushEventPreimage, hzero] using
              heq.trans htransport
          have hdepth := resources.window.pushChild.eventOwner_injective
            hone hzero hcollision
          omega
      refine ⟨transient, htransientFresh,
        resources.pool.mem_free_of_not_mem_indices htransientFresh,
        Or.inr (by
          simpa [transient] using
            resources.window.pushChild.transientOwner_outside hinputPos), ?_, Or.inr rfl⟩
      intro _
      exact hzeroAbsent
    · have hcanonicalFresh : canonical ∉ startCursor.indexOwners := by
        intro hmem
        simp only [startCursor, ScheduleCursor.indexOwners_mk,
          ScheduleAtom.indexOwner?, List.filterMap_cons, List.filterMap_nil,
          List.append_nil] at hmem
        rcases List.mem_append.mp hmem with hleft | hright
        · exact hshadow (startLedger.prefixLedger.owners_perm.mem_iff.mp hleft)
        · have hright' : canonical ∈
              startCursor.right.filterMap ScheduleAtom.indexOwner? := by
            simpa [startCursor] using hright
          have hrightEq := startLedger.right_eq
          rw [startActive] at hrightEq
          simp only [List.nil_append] at hrightEq
          rw [hrightEq] at hright'
          exact hcanonicalInside (startLedger.outside_at canonical hright')
      refine ⟨canonical, hcanonicalFresh,
        resources.pool.mem_free_of_not_mem_indices hcanonicalFresh,
        Or.inl ⟨hone, rfl⟩, ?_, Or.inl rfl⟩
      intro heq
      have hout : OutsideProductiveWindow resources.window canonical := by
        rw [heq]
        simpa [transient] using
          resources.window.transientOwner_outside hinputPos
      exact False.elim (hcanonicalInside hout)
  let owned : ScheduleIndex g input := {
    flags := [f]
    relation := cflagBase g f
    mark := .firstPending
    denotes := .base f
    owner := owner
  }
  have hownerShadowOutside : OutsideShadowWindow resources.window.pushChild owner := by
    rcases hownerKind with hcanonical | htransient
    · subst owner
      exact OutsideShadowWindow.eventOwner resources.window.pushChild hone
    · subst owner
      simpa [transient] using
        OutsideShadowWindow.transientOwner resources.window.pushChild hinputPos
  let childShadowLayout : ShadowStartLayout rest resources.window.pushChild
      [[f]] [owner] :=
    shadowLayout.cons (by simp) (Or.inr hownerShadowOutside)
      (fun candidate hout => by
        simpa [ProductiveOwnerWindow.pushChild] using
          OutsideShadowWindow.transport resources.window (by rfl) hout)
      (fun i => Fin.elim0 i)
  let childCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task childTask, .index owned :: next :: tail⟩
  -/
  have hleftOwner : leftTask.owner = parentTask.owner := by
    apply Fin.ext
    rfl
  have hrightFresh : rightTask.owner ∉ startCursor.taskOwners := by
    intro hmem
    have hloc := resources.task_locality rightTask.owner (by
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hmem)
    have hu := leftParse.yield_length_pos
    have hv := rightParse.yield_length_pos
    rcases hloc with heq | hlt | hafter
    · change (pre ++ u).length = pre.length at heq
      simp only [List.length_append] at heq
      omega
    · change (pre ++ u).length < pre.length at hlt
      simp only [List.length_append] at hlt
      omega
    · change pre.length + (u ++ v).length ≤ (pre ++ u).length at hafter
      simp only [List.length_append] at hafter
      omega
  have hfork : ScheduleInvariant forkCursor := by
    dsimp [forkCursor, startCursor] at hrightFresh ⊢
    exact ScheduleInvariant.plainBinary (alpha ++ [ScheduleAtom.dollar])
      (next :: tail) parentTask leftTask rightTask hleftOwner hrightFresh hstart'
  have hright : ScheduleInvariant rightCursor := by
    dsimp [forkCursor, rightCursor] at hfork ⊢
    exact ScheduleInvariant.finishTask (alpha ++ [ScheduleAtom.dollar]) leftTask
      (.task rightTask) (next :: tail) hfork
  have hindicesFork : forkCursor.indexOwners = startCursor.indexOwners := by
    simp [forkCursor, startCursor, ScheduleCursor.indexOwners,
      ScheduleCursor.word, ScheduleAtom.indexOwner?, List.filterMap_append]
  have hindicesRight : rightCursor.indexOwners = startCursor.indexOwners := by
    simp [rightCursor, startCursor, ScheduleCursor.indexOwners,
      ScheduleCursor.word, ScheduleAtom.indexOwner?, List.filterMap_append]
  let startLedger : ScheduleOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ownerLedger
  let startShadowLedger : ShadowOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.shadowLedger
  have startActive : startLedger.active = [] := by
    simpa [startLedger, startCursor, parentTask, parent, plainScheduleCursor] using
      hactive
  have startShadowActiveEq : startShadowLedger.active = startLedger.active := by
    simpa [startShadowLedger, startLedger, startCursor, parentTask, parent,
      plainScheduleCursor] using resources.shadow_active_eq
  let startTickets : IndexTicketLedger startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.tickets
  have startParkingAtOrBelow : startTickets.ParkingAtOrBelow resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      parkingAtOrBelow
  let startTicketOwnerLedger : startTickets.SemanticScheduleOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ticketOwnerLedger
  let startTicketShadowLedger : startTickets.SemanticShadowOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ticketShadowLedger
  have startTicketActiveEq : startTicketOwnerLedger.active =
      startTickets.semanticOwners startLedger.active := by
    simpa [startTicketOwnerLedger, startTickets, startLedger, startCursor,
      parentTask, parent, plainScheduleCursor] using resources.ticket_active_eq
  have startTicketShadowActiveEq : startTicketShadowLedger.active =
      startTickets.semanticOwners resources.ticketShadowOwners := by
    simpa [startTicketShadowLedger, startTickets, startCursor,
      parentTask, parent, plainScheduleCursor] using
        resources.ticket_shadow_active_eq
  have hframesFork : forkCursor.frameOwners = startCursor.frameOwners := by
    simp [forkCursor, startCursor, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append]
  have hframesRight : rightCursor.frameOwners = startCursor.frameOwners := by
    simp [rightCursor, startCursor, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append]
  let leftTickets : IndexTicketLedger forkCursor :=
    startTickets.transport (by rw [hindicesFork])
  let rightTickets : IndexTicketLedger rightCursor :=
    startTickets.transport (by rw [hindicesRight])
  have leftParkingBelow :
      leftTickets.ParkingBelow resources.window.binaryLeft := by
    exact startParkingAtOrBelow.transport_toBelow_of_base_lt
      (hindicesFork ▸ List.Perm.refl _) (by
        simp only [ProductiveOwnerWindow.binaryLeft_base]
        omega)
  have rightParkingBelow :
      rightTickets.ParkingBelow resources.window.binaryRight := by
    exact startParkingAtOrBelow.transport_toBelow_of_base_lt
      (hindicesRight ▸ List.Perm.refl _) (by
        simp only [ProductiveOwnerWindow.binaryRight_base]
        omega)
  have leftSemanticOwnerOf : leftTickets.semanticOwnerOf =
      startTickets.semanticOwnerOf := by
    funext owner
    rfl
  have rightSemanticOwnerOf : rightTickets.semanticOwnerOf =
      startTickets.semanticOwnerOf := by
    funext owner
    rfl
  have leftPrefixLedger : PrefixFrameLedger forkCursor :=
    startLedger.prefixLedger.transport
      (by simp [forkCursor, startCursor])
      (by rw [hframesFork])
  have rightPrefixLedger : PrefixFrameLedger rightCursor :=
    startLedger.prefixLedger.transport
      (by simp [rightCursor, startCursor])
      (by rw [hframesRight])
  have leftTicketPrefixLedger : PrefixFrameLedger leftTickets.semanticCursor :=
    startTicketOwnerLedger.prefixLedger.transport
      (by
        simp only [IndexTicketLedger.semanticCursor]
        rw [leftSemanticOwnerOf]
        simp [startTickets, forkCursor, startCursor,
        ScheduleCursor.relabelTicketOwners])
      (by
        simp only [IndexTicketLedger.semanticCursor]
        rw [leftSemanticOwnerOf]
        simp [startTickets, hframesFork])
  have rightTicketPrefixLedger : PrefixFrameLedger rightTickets.semanticCursor :=
    startTicketOwnerLedger.prefixLedger.transport
      (by
        simp only [IndexTicketLedger.semanticCursor]
        rw [rightSemanticOwnerOf]
        simp [startTickets, rightCursor, startCursor,
        ScheduleCursor.relabelTicketOwners])
      (by
        simp only [IndexTicketLedger.semanticCursor]
        rw [rightSemanticOwnerOf]
        simp [startTickets, hframesRight])
  let leftOwnerLedger : ScheduleOwnerLedger leftParse
      resources.window.binaryLeft forkCursor :=
    startLedger.transport resources.window.binaryLeft
      (by
        simpa [forkCursor, startCursor, ScheduleAtom.indexOwner?] using
          startLedger.right_eq)
      (fun owner howner =>
        EventOwnedLayout.outside_binaryLeft resources.window
          (startLedger.outside_at owner howner))
      (by
        rw [hframesFork]
        exact startLedger.frames.binaryLeft)
      leftPrefixLedger
  let rightOwnerLedger : ScheduleOwnerLedger rightParse
      resources.window.binaryRight rightCursor :=
    startLedger.transport resources.window.binaryRight
      (by
        simpa [rightCursor, startCursor, ScheduleAtom.indexOwner?] using
          startLedger.right_eq)
      (fun owner howner =>
        EventOwnedLayout.outside_binaryRight resources.window
          (startLedger.outside_at owner howner))
      (by
        rw [hframesRight]
        exact startLedger.frames.binaryRight)
      rightPrefixLedger
  let leftShadowLedger : ShadowOwnerLedger leftParse
      resources.window.binaryLeft forkCursor :=
    startShadowLedger.transport resources.window.binaryLeft
      (by
        simpa [forkCursor, startCursor, ScheduleAtom.indexOwner?] using
          startShadowLedger.right_eq)
      (fun owner howner =>
        OutsideShadowWindow.binaryLeft resources.window
          (startShadowLedger.outside_at owner howner))
      (by
        rw [hframesFork]
        exact startShadowLedger.frames.binaryLeft)
      leftPrefixLedger
  let rightShadowLedger : ShadowOwnerLedger rightParse
      resources.window.binaryRight rightCursor :=
    startShadowLedger.transport resources.window.binaryRight
      (by
        simpa [rightCursor, startCursor, ScheduleAtom.indexOwner?] using
          startShadowLedger.right_eq)
      (fun owner howner =>
        OutsideShadowWindow.binaryRight resources.window
          (startShadowLedger.outside_at owner howner))
      (by
        rw [hframesRight]
        exact startShadowLedger.frames.binaryRight)
      rightPrefixLedger
  let leftTicketOwnerLedger : leftTickets.SemanticScheduleOwnerLedger leftParse
      resources.window.binaryLeft :=
    startTicketOwnerLedger.transport resources.window.binaryLeft
      (by
        simpa [leftTickets, startTickets, forkCursor, startCursor,
          IndexTicketLedger.transport, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf,
          ScheduleCursor.relabelTicketOwners] using
            startTicketOwnerLedger.right_eq)
      (fun owner howner =>
        EventOwnedLayout.outside_binaryLeft resources.window
          (startTicketOwnerLedger.outside_at owner howner))
      (by
        simpa [leftTickets, startTickets, hframesFork,
          IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketOwnerLedger.frames.binaryLeft)
      leftTicketPrefixLedger
  let rightTicketOwnerLedger : rightTickets.SemanticScheduleOwnerLedger rightParse
      resources.window.binaryRight :=
    startTicketOwnerLedger.transport resources.window.binaryRight
      (by
        simpa [rightTickets, startTickets, rightCursor, startCursor,
          IndexTicketLedger.transport, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf,
          ScheduleCursor.relabelTicketOwners] using
            startTicketOwnerLedger.right_eq)
      (fun owner howner =>
        EventOwnedLayout.outside_binaryRight resources.window
          (startTicketOwnerLedger.outside_at owner howner))
      (by
        simpa [rightTickets, startTickets, hframesRight,
          IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketOwnerLedger.frames.binaryRight)
      rightTicketPrefixLedger
  let leftTicketShadowLedger : leftTickets.SemanticShadowOwnerLedger leftParse
      resources.window.binaryLeft :=
    startTicketShadowLedger.transport resources.window.binaryLeft
      (by
        simpa [leftTickets, startTickets, forkCursor, startCursor,
          IndexTicketLedger.transport, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf,
          ScheduleCursor.relabelTicketOwners] using
            startTicketShadowLedger.right_eq)
      (fun owner howner =>
        OutsideShadowWindow.binaryLeft resources.window
          (startTicketShadowLedger.outside_at owner howner))
      (by
        simpa [leftTickets, startTickets, hframesFork,
          IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketShadowLedger.frames.binaryLeft)
      leftTicketPrefixLedger
  let rightTicketShadowLedger : rightTickets.SemanticShadowOwnerLedger rightParse
      resources.window.binaryRight :=
    startTicketShadowLedger.transport resources.window.binaryRight
      (by
        simpa [rightTickets, startTickets, rightCursor, startCursor,
          IndexTicketLedger.transport, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf,
          ScheduleCursor.relabelTicketOwners] using
            startTicketShadowLedger.right_eq)
      (fun owner howner =>
        OutsideShadowWindow.binaryRight resources.window
          (startTicketShadowLedger.outside_at owner howner))
      (by
        simpa [rightTickets, startTickets, hframesRight,
          IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketShadowLedger.frames.binaryRight)
      rightTicketPrefixLedger
  have htaskPerm : forkCursor.taskOwners.Perm
      (rightTask.owner :: startCursor.taskOwners) := by
    simp only [forkCursor, startCursor, ScheduleCursor.taskOwners_mk,
      ScheduleAtom.taskOwner?, List.filterMap_cons, List.filterMap_nil]
    rw [hleftOwner]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.taskOwner? ++ [parentTask.owner])
        (l₂ := (next :: tail).filterMap ScheduleAtom.taskOwner?)
        (a := rightTask.owner))
  have hfinishPerm : forkCursor.taskOwners.Perm
      (leftTask.owner :: rightCursor.taskOwners) := by
    simp only [forkCursor, rightCursor, ScheduleCursor.taskOwners_mk,
      ScheduleAtom.taskOwner?, List.filterMap_cons, List.filterMap_nil]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.taskOwner?)
        (l₂ := rightTask.owner ::
          (next :: tail).filterMap ScheduleAtom.taskOwner?)
        (a := leftTask.owner))
  let leftPool : IndexOwnerPool forkCursor :=
    resources.pool.transport hindicesFork
  let leftResources : ScheduleRunResources leftParse pre forkCursor := {
    pool := leftPool
    tickets := leftTickets
    window := resources.window.binaryLeft
    parkingAtOrBelow := by
      have hbound : startTickets.ParkingAtOrBelow resources.window := by
        simpa [startTickets, startCursor, parentTask, parent,
          plainScheduleCursor] using resources.parkingAtOrBelow
      simpa [leftTickets] using hbound.transport_mono
        (by rw [hindicesFork]) (by simp)
    ownerLedger := leftOwnerLedger
    ticketOwnerLedger := leftTicketOwnerLedger
    ticket_active_eq := by
      simpa [leftTicketOwnerLedger, leftTickets, leftOwnerLedger,
        IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketActiveEq
    ticketShadowBlocks := resources.ticketShadowBlocks
    ticketShadowOwners := resources.ticketShadowOwners
    ticketShadowOwners_subset := by
      intro owner howner
      rw [hindicesFork]
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using
        resources.ticketShadowOwners_subset howner
    ticketShadowOwners_nodup := resources.ticketShadowOwners_nodup
    ticketShadowLedger := leftTicketShadowLedger
    ticket_shadow_active_eq := by
      simpa [leftTicketShadowLedger, leftTickets,
        IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketShadowActiveEq
    ticketShadowLayout := by
      simpa [leftTickets, startTickets, startCursor, parentTask, parent,
        plainScheduleCursor, IndexTicketLedger.transport,
        IndexTicketLedger.semanticOwnerOf] using
          resources.ticketShadowLayout.binaryLeft
    shadowLedger := leftShadowLedger
    shadow_active_eq := by
      simpa [leftShadowLedger, leftOwnerLedger] using startShadowActiveEq
    charged := resources.charged
    charged_eq_indices := by
      rw [hindicesFork]
      exact resources.charged_eq_indices
    charged_le_indices := by
      rw [hindicesFork]
      exact resources.charged_le_indices
    productive_le_credit := by
      have hp := resources.productive_le_credit
      simp only [NFParse.productiveCount, NFParse.binaryCount,
        NFParse.terminalCount] at hp
      dsimp [leftPool]
      simp only [NFParse.productiveCount]
      omega
    task_locality := by
      intro owner howner
      have hclass := htaskPerm.mem_iff.mp howner
      simp only [List.mem_cons] at hclass
      rcases hclass with hrightOwner | hold
      · subst owner
        right
        right
        simp [rightTask]
      · have hloc := resources.task_locality owner (by
          simpa [startCursor, parentTask, parent, plainScheduleCursor] using hold)
        rcases hloc with heq | hbefore | hafter
        · exact Or.inl heq
        · exact Or.inr (Or.inl hbefore)
        · exact Or.inr (Or.inr (by
            simp only [List.length_append] at hafter ⊢
            omega))
    }
  let rightPool : IndexOwnerPool rightCursor :=
    resources.pool.transport hindicesRight
  have hleftNotRight : leftTask.owner ∉ rightCursor.taskOwners := by
    have hconsNodup : (leftTask.owner :: rightCursor.taskOwners).Nodup :=
      hfinishPerm.nodup_iff.mp hfork.taskOwners_nodup
    exact (List.nodup_cons.mp hconsNodup).1
  let rightResources : ScheduleRunResources rightParse (pre ++ u) rightCursor := {
    pool := rightPool
    tickets := rightTickets
    window := resources.window.binaryRight
    parkingAtOrBelow := by
      have hbound : startTickets.ParkingAtOrBelow resources.window := by
        simpa [startTickets, startCursor, parentTask, parent,
          plainScheduleCursor] using resources.parkingAtOrBelow
      simpa [rightTickets] using hbound.transport_mono
        (by rw [hindicesRight]) (by
          rw [ProductiveOwnerWindow.binaryRight_base]
          omega)
    ownerLedger := rightOwnerLedger
    ticketOwnerLedger := rightTicketOwnerLedger
    ticket_active_eq := by
      simpa [rightTicketOwnerLedger, rightTickets, rightOwnerLedger,
        IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketActiveEq
    ticketShadowBlocks := resources.ticketShadowBlocks
    ticketShadowOwners := resources.ticketShadowOwners
    ticketShadowOwners_subset := by
      intro owner howner
      rw [hindicesRight]
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using
        resources.ticketShadowOwners_subset howner
    ticketShadowOwners_nodup := resources.ticketShadowOwners_nodup
    ticketShadowLedger := rightTicketShadowLedger
    ticket_shadow_active_eq := by
      simpa [rightTicketShadowLedger, rightTickets,
        IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketShadowActiveEq
    ticketShadowLayout := by
      simpa [rightTickets, startTickets, startCursor, parentTask, parent,
        plainScheduleCursor, IndexTicketLedger.transport,
        IndexTicketLedger.semanticOwnerOf] using
          resources.ticketShadowLayout.binaryRight
    shadowLedger := rightShadowLedger
    shadow_active_eq := by
      simpa [rightShadowLedger, rightOwnerLedger] using startShadowActiveEq
    charged := resources.charged
    charged_eq_indices := by
      rw [hindicesRight]
      exact resources.charged_eq_indices
    charged_le_indices := by
      rw [hindicesRight]
      exact resources.charged_le_indices
    productive_le_credit := by
      have hp := resources.productive_le_credit
      simp only [NFParse.productiveCount, NFParse.binaryCount,
        NFParse.terminalCount] at hp
      dsimp [rightPool]
      simp only [NFParse.productiveCount]
      omega
    task_locality := by
      intro owner howner
      have hownerFork : owner ∈ forkCursor.taskOwners :=
        hfinishPerm.mem_iff.mpr (List.mem_cons_of_mem leftTask.owner howner)
      have hclass := htaskPerm.mem_iff.mp hownerFork
      simp only [List.mem_cons] at hclass
      rcases hclass with hrightOwner | hold
      · left
        subst owner
        simp [rightTask]
      · have hloc := resources.task_locality owner (by
          simpa [startCursor, parentTask, parent, plainScheduleCursor] using hold)
        rcases hloc with heq | hbefore | hafter
        · have hownerEq : owner = leftTask.owner := by
            apply Fin.ext
            simpa [leftTask] using heq
          exact False.elim (hleftNotRight (hownerEq ▸ howner))
        · right
          left
          simp [List.length_append]
          omega
        · right
          right
          simp only [List.length_append] at hafter ⊢
          omega
    }
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos startCursor hstart'
  let forkState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos forkCursor hfork
  have hforkStep : ScheduleReaches g input startState forkState := by
    apply ScheduleReaches.single
    have hstep := composite_plainBinary_stable input
      (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
      pre.length (alpha.map ScheduleAtom.workSym)
      ((next :: tail).map ScheduleAtom.workSym) hstable
    simpa [startState, forkState, scheduleStateOfCursor, ScheduleState.config,
      startCursor, forkCursor, parentTask, leftTask, rightTask, parent,
      scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
      ScheduleTask.workSym, List.map_append] using hstep
  have hleftRun := leftRuns.1 (input := input) leftUnused pre (v ++ post)
    leftInputEq alpha (.task rightTask) (next :: tail) hstable
    (by simpa [forkCursor, leftTask, plainScheduleCursor])
    (by simpa [rightCursor, scheduleWordCursor]) leftResources
    (by simpa [leftResources, leftPool] using hfree)
    (by simpa [leftResources] using leftParkingBelow)
    (by simpa [leftResources, leftOwnerLedger] using startActive)
    ShadowStartLayout.nil
    (by
      intro hinput hmem
      apply ticketTransientFree hinput
      have hforkMem : IndexTicket.transient hinput ∈
          forkCursor.indexTickets startTickets.ticketOf := by
        simpa [leftResources, leftTickets, startTickets,
          IndexTicketLedger.transport, forkCursor, leftTask,
          plainScheduleCursor] using hmem
      have hstartMem : IndexTicket.transient hinput ∈
          startCursor.indexTickets startTickets.ticketOf := by
        simpa [ScheduleCursor.indexTickets, hindicesFork] using hforkMem
      simpa [startTickets, startCursor, parentTask, parent,
        plainScheduleCursor] using hstartMem)
    (by
      intro hinput hmem
      apply htransientFree hinput
      have hforkMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          forkCursor.indexOwners := by
        simpa [forkCursor, leftTask, plainScheduleCursor] using hmem
      have hstartMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          startCursor.indexOwners := by rwa [hindicesFork] at hforkMem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstartMem)
    (by
      intro hinput hmem
      apply hScratchFree hinput
      have hforkMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
          forkCursor.indexOwners := by
        simpa [forkCursor, leftTask, plainScheduleCursor] using hmem
      have hstartMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
          startCursor.indexOwners := by rwa [hindicesFork] at hforkMem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstartMem)
  have hrightRun := rightRuns.1 (input := input) rightUnused (pre ++ u) post
    rightInputEq alpha next tail hstable
    (by simpa [rightCursor, rightTask, plainScheduleCursor]) hend
    rightResources (by simpa [rightResources, rightPool] using hfree)
    (by simpa [rightResources] using rightParkingBelow)
    (by simpa [rightResources, rightOwnerLedger] using startActive)
    ShadowStartLayout.nil
    (by
      intro hinput hmem
      apply ticketTransientFree hinput
      have hrightMem : IndexTicket.transient hinput ∈
          rightCursor.indexTickets startTickets.ticketOf := by
        simpa [rightResources, rightTickets, startTickets,
          IndexTicketLedger.transport, rightCursor, rightTask,
          plainScheduleCursor] using hmem
      have hstartMem : IndexTicket.transient hinput ∈
          startCursor.indexTickets startTickets.ticketOf := by
        simpa [ScheduleCursor.indexTickets, hindicesRight] using hrightMem
      simpa [startTickets, startCursor, parentTask, parent,
        plainScheduleCursor] using hstartMem)
    (by
      intro hinput hmem
      apply htransientFree hinput
      have hrightMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          rightCursor.indexOwners := by
        simpa [rightCursor, rightTask, plainScheduleCursor] using hmem
      have hstartMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          startCursor.indexOwners := by rwa [hindicesRight] at hrightMem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstartMem)
    (by
      intro hinput hmem
      apply hScratchFree hinput
      have hrightMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
          rightCursor.indexOwners := by
        simpa [rightCursor, rightTask, plainScheduleCursor] using hmem
      have hstartMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
          startCursor.indexOwners := by rwa [hindicesRight] at hrightMem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstartMem)
  simpa [startState, startCursor, parentTask, parent, plainScheduleCursor,
    List.append_assoc] using hforkStep.trans (hleftRun.trans hrightRun)

/-- An irrelevant push merely replaces the plain task by its unary child while preserving
the strict parking bound through the unchanged productive window. -/
public theorem plainScheduleRun_pushSkip
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: stack) w)
    (restUnused : ¬ rest.ConsumesAt 0)
    (restRuns : OrdinaryScheduleRuns rest) :
    PlainScheduleRun (NFParse.push hr hlhs hc hrhs rest) := by
  intro input unused pre post input_eq alpha next tail hstable hstart hend
    resources hfree parkingBelow hactive shadowLayout ticketTransientFree htransientFree
    hScratchFree
  let parent : NFParse g A stack w := .push hr hlhs hc hrhs rest
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.plain unused)
  let childTask : ScheduleTask g input :=
    scheduleTaskOfParse rest pre post input_eq (.plain restUnused)
  let startCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task parentTask, next :: tail⟩
  let childCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task childTask, next :: tail⟩
  have hstart' : ScheduleInvariant startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstart
  have howner : childTask.owner = parentTask.owner := by
    apply Fin.ext
    rfl
  have hchild : ScheduleInvariant childCursor := by
    dsimp [childCursor, startCursor]
    exact ScheduleInvariant.plainPushSkip (alpha ++ [ScheduleAtom.dollar])
      (next :: tail) parentTask childTask howner hstart'
  have htasks : childCursor.taskOwners = startCursor.taskOwners := by
    simp [childCursor, startCursor, ScheduleCursor.taskOwners,
      ScheduleCursor.word, ScheduleAtom.taskOwner?, List.filterMap_append, howner]
  have hindices : childCursor.indexOwners = startCursor.indexOwners := by
    simp [childCursor, startCursor, ScheduleCursor.indexOwners,
      ScheduleCursor.word, ScheduleAtom.indexOwner?, List.filterMap_append]
  have hframes : childCursor.frameOwners = startCursor.frameOwners := by
    simp [childCursor, startCursor, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append]
  have hdepthOne : 1 ∉ rest.eventDepths := by
    intro hone
    exact restUnused ((rest.consumesAt_iff_exists_mem_eventDepths_lt 0).2
      ⟨1, hone, by omega⟩)
  let startLedger : ScheduleOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ownerLedger
  let startShadowLedger : ShadowOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.shadowLedger
  have startActive : startLedger.active = [] := by
    simpa [startLedger, startCursor, parentTask, parent, plainScheduleCursor] using
      hactive
  have startShadowActiveEq : startShadowLedger.active = startLedger.active := by
    simpa [startShadowLedger, startLedger, startCursor, parentTask, parent,
      plainScheduleCursor] using resources.shadow_active_eq
  let startTickets : IndexTicketLedger startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.tickets
  have startParking : startTickets.ParkingBelow resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      parkingBelow
  let startTicketOwnerLedger : startTickets.SemanticScheduleOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ticketOwnerLedger
  let startTicketShadowLedger : startTickets.SemanticShadowOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ticketShadowLedger
  have startTicketActiveEq : startTicketOwnerLedger.active =
      startTickets.semanticOwners startLedger.active := by
    simpa [startTicketOwnerLedger, startTickets, startLedger, startCursor,
      parentTask, parent, plainScheduleCursor] using resources.ticket_active_eq
  have startTicketShadowActiveEq : startTicketShadowLedger.active =
      startTickets.semanticOwners resources.ticketShadowOwners := by
    simpa [startTicketShadowLedger, startTickets, startCursor,
      parentTask, parent, plainScheduleCursor] using
        resources.ticket_shadow_active_eq
  let childTickets : IndexTicketLedger childCursor :=
    startTickets.transport (by rw [hindices])
  have childParking : childTickets.ParkingBelow resources.window.pushChild := by
    exact startParking.transport_mono
      (hindices ▸ List.Perm.refl _) (by simp)
  have childSemanticOwnerOf : childTickets.semanticOwnerOf =
      startTickets.semanticOwnerOf := by
    funext owner
    rfl
  have childPrefixLedger : PrefixFrameLedger childCursor :=
    startLedger.prefixLedger.transport
      (by simp [childCursor, startCursor])
      (by rw [hframes])
  have childTicketPrefixLedger : PrefixFrameLedger childTickets.semanticCursor :=
    startTicketOwnerLedger.prefixLedger.transport
      (by
        simp only [IndexTicketLedger.semanticCursor]
        rw [childSemanticOwnerOf]
        simp [startTickets, childCursor, startCursor,
        ScheduleCursor.relabelTicketOwners])
      (by
        simp only [IndexTicketLedger.semanticCursor]
        rw [childSemanticOwnerOf]
        simp [startTickets, hframes])
  let childOwnerLedger : ScheduleOwnerLedger rest resources.window.pushChild
      childCursor :=
    startLedger.transport resources.window.pushChild
      (by
        simpa [childCursor, startCursor, ScheduleAtom.indexOwner?] using
          startLedger.right_eq)
      (fun owner howner => by
        simpa [ProductiveOwnerWindow.pushChild] using
          EventOwnedFrames.outside_transport resources.window (by rfl)
            (startLedger.outside_at owner howner))
      (by
        rw [hframes]
        simpa [ProductiveOwnerWindow.pushChild] using
          startLedger.frames.push)
      childPrefixLedger
  let childShadowLedger : ShadowOwnerLedger rest resources.window.pushChild
      childCursor :=
    startShadowLedger.transport resources.window.pushChild
      (by
        simpa [childCursor, startCursor, ScheduleAtom.indexOwner?] using
          startShadowLedger.right_eq)
      (fun owner howner => by
        simpa [ProductiveOwnerWindow.pushChild] using
          OutsideShadowWindow.transport resources.window (by rfl)
            (startShadowLedger.outside_at owner howner))
      (by
        rw [hframes]
        simpa [ProductiveOwnerWindow.pushChild] using
          startShadowLedger.frames.transportEqual (residual := rest) (by rfl))
      childPrefixLedger
  let childTicketOwnerLedger : childTickets.SemanticScheduleOwnerLedger rest
      resources.window.pushChild :=
    startTicketOwnerLedger.transport resources.window.pushChild
      (by
        simpa [childTickets, startTickets, childCursor, startCursor,
          IndexTicketLedger.transport, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf,
          ScheduleCursor.relabelTicketOwners] using
            startTicketOwnerLedger.right_eq)
      (fun owner howner => by
        simpa [ProductiveOwnerWindow.pushChild] using
          EventOwnedFrames.outside_transport resources.window (by rfl)
            (startTicketOwnerLedger.outside_at owner howner))
      (by
        simpa [childTickets, startTickets, hframes,
          IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf,
          ProductiveOwnerWindow.pushChild] using
            startTicketOwnerLedger.frames.push)
      childTicketPrefixLedger
  let childTicketShadowLedger : childTickets.SemanticShadowOwnerLedger rest
      resources.window.pushChild :=
    startTicketShadowLedger.transport resources.window.pushChild
      (by
        simpa [childTickets, startTickets, childCursor, startCursor,
          IndexTicketLedger.transport, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf,
          ScheduleCursor.relabelTicketOwners] using
            startTicketShadowLedger.right_eq)
      (fun owner howner => by
        simpa [ProductiveOwnerWindow.pushChild] using
          OutsideShadowWindow.transport resources.window (by rfl)
            (startTicketShadowLedger.outside_at owner howner))
      (by
        simpa [childTickets, startTickets, hframes,
          IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf,
          ProductiveOwnerWindow.pushChild] using
            startTicketShadowLedger.frames.transportEqual
              (residual := rest) (by rfl))
      childTicketPrefixLedger
  let childPool : IndexOwnerPool childCursor :=
    resources.pool.transport hindices
  let childResources : ScheduleRunResources rest pre childCursor := {
    pool := childPool
    tickets := childTickets
    window := resources.window.pushChild
    parkingAtOrBelow := by
      have hbound : startTickets.ParkingAtOrBelow resources.window := by
        simpa [startTickets, startCursor, parentTask, parent,
          plainScheduleCursor] using resources.parkingAtOrBelow
      simpa [childTickets] using hbound.transport_mono
        (by rw [hindices]) (by simp)
    ownerLedger := childOwnerLedger
    ticketOwnerLedger := childTicketOwnerLedger
    ticket_active_eq := by
      simpa [childTicketOwnerLedger, childTickets, childOwnerLedger,
        IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketActiveEq
    ticketShadowBlocks := resources.ticketShadowBlocks
    ticketShadowOwners := resources.ticketShadowOwners
    ticketShadowOwners_subset := by
      intro owner howner
      rw [hindices]
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using
        resources.ticketShadowOwners_subset howner
    ticketShadowOwners_nodup := resources.ticketShadowOwners_nodup
    ticketShadowLedger := childTicketShadowLedger
    ticket_shadow_active_eq := by
      simpa [childTicketShadowLedger, childTickets,
        IndexTicketLedger.transport, IndexTicketLedger.semanticOwnerOf] using
          startTicketShadowActiveEq
    ticketShadowLayout := by
      change ShadowStartLayout rest resources.window.pushChild
        resources.ticketShadowBlocks
        (childTickets.semanticOwners resources.ticketShadowOwners)
      have hparentLayout : ShadowStartLayout parent resources.window
          resources.ticketShadowBlocks
          (startTickets.semanticOwners resources.ticketShadowOwners) := by
        simpa [startTickets, startCursor, parentTask, parent,
          plainScheduleCursor] using resources.ticketShadowLayout
      have htransported := hparentLayout.transport
        (residualWindow := resources.window.pushChild)
        (fun candidate hout => by
          simpa [ProductiveOwnerWindow.pushChild] using
            OutsideShadowWindow.transport resources.window (by rfl) hout)
        (fun i hd => by
          have hpre := NFParse.pushEventPreimage_mem hd
          have hpreZero :
              NFParse.pushEventPreimage rest.eventDepths
                (blockStart resources.ticketShadowBlocks i) = 0 := by
            by_contra hne
            have hprePos : 0 < NFParse.pushEventPreimage rest.eventDepths
                (blockStart resources.ticketShadowBlocks i) :=
              Nat.pos_of_ne_zero hne
            exact restUnused
              ((rest.consumesAt_iff_exists_mem_eventDepths_lt 0).2
                ⟨_, hpre, hprePos⟩)
          have hdepthZero : blockStart resources.ticketShadowBlocks i = 0 := by
            have hpred :
                (NFParse.pushEventPreimage rest.eventDepths
                  (blockStart resources.ticketShadowBlocks i)).pred =
                    blockStart resources.ticketShadowBlocks i :=
              NFParse.pred_pushEventPreimage hd
            rw [hpreZero] at hpred
            simpa using hpred.symm
          have hchildZero : 0 ∈ rest.eventDepths := by
            rw [hpreZero] at hpre
            exact hpre
          refine ⟨by simpa [hdepthZero] using hchildZero, ?_⟩
          have hpreEq : NFParse.pushEventPreimage rest.eventDepths
              (blockStart resources.ticketShadowBlocks i) =
                blockStart resources.ticketShadowBlocks i :=
            hpreZero.trans hdepthZero.symm
          simpa only [hpreEq] using
            resources.window.shadowEventOwner_push hd)
      simpa [childTickets, startTickets, IndexTicketLedger.transport,
        IndexTicketLedger.semanticOwnerOf] using htransported
    shadowLedger := childShadowLedger
    shadow_active_eq := by
      simpa [childShadowLedger, childOwnerLedger] using startShadowActiveEq
    charged := resources.charged
    charged_eq_indices := by
      rw [hindices]
      exact resources.charged_eq_indices
    charged_le_indices := by
      rw [hindices]
      exact resources.charged_le_indices
    productive_le_credit := by
      have hp := resources.productive_le_credit
      simpa [parent, NFParse.productiveCount, NFParse.binaryCount,
        NFParse.terminalCount, childPool] using hp
    task_locality := by
      intro owner hmem
      apply resources.task_locality owner
      have hold : owner ∈ startCursor.taskOwners := by
        rw [← htasks]
        exact hmem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hold
  }
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos startCursor hstart'
  let childState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos childCursor hchild
  have hpush : ScheduleReaches g input startState childState := by
    apply ScheduleReaches.single
    have hstep := composite_plainPushSkip_stable input
      (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
      pre.length (alpha.map ScheduleAtom.workSym)
      ((next :: tail).map ScheduleAtom.workSym)
    simpa [startState, childState, scheduleStateOfCursor, ScheduleState.config,
      startCursor, childCursor, parentTask, childTask, parent,
      scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
      ScheduleTask.workSym, List.map_append] using hstep
  have hrestRun := restRuns.1 (input := input) restUnused pre post input_eq
    alpha next tail hstable
    (by simpa [childCursor, childTask, plainScheduleCursor]) hend
    childResources (by simpa [childResources, childPool] using hfree)
    (by simpa [childResources] using childParking)
    (by simpa [childResources, childOwnerLedger] using startActive)
    ShadowStartLayout.nil
    (by
      intro hinput hmem
      apply ticketTransientFree hinput
      have hchildMem : IndexTicket.transient hinput ∈
          childCursor.indexTickets startTickets.ticketOf := by
        simpa [childResources, childTickets, startTickets,
          IndexTicketLedger.transport, childCursor, childTask,
          plainScheduleCursor] using hmem
      have hstartMem : IndexTicket.transient hinput ∈
          startCursor.indexTickets startTickets.ticketOf := by
        simpa [ScheduleCursor.indexTickets, hindices] using hchildMem
      simpa [startTickets, startCursor, parentTask, parent,
        plainScheduleCursor] using hstartMem)
    (by
      intro hinput hmem
      apply htransientFree hinput
      have hchildMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          childCursor.indexOwners := by
        simpa [childCursor, childTask, plainScheduleCursor] using hmem
      have hstartMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          startCursor.indexOwners := by rwa [hindices] at hchildMem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstartMem)
    (by
      intro hinput hmem
      apply hScratchFree hinput
      have hchildMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
          childCursor.indexOwners := by
        simpa [childCursor, childTask, plainScheduleCursor] using hmem
      have hstartMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
          startCursor.indexOwners := by rwa [hindices] at hchildMem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstartMem)
  simpa [startState, startCursor, parentTask, parent, plainScheduleCursor] using
    hpush.trans hrestRun

/-- A relevant push allocates the head of the free owner pool and delegates to overlay mode,
while preserving the strict parking bound through the nonparking ticket rotation. -/
public theorem plainScheduleRun_pushUse_of_pool_nonempty
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: stack) w)
    (restUsed : rest.ConsumesAt 0) (restOverlay : OverlayScheduleRun rest) :
    PlainScheduleRun (NFParse.push hr hlhs hc hrhs rest) := by
  intro input unused pre post input_eq alpha next tail hstable hstart hend
    resources hfree parkingBelow hactive shadowLayout ticketTransientFree htransientFree
    _hScratchFree
  let parent : NFParse g A stack w := .push hr hlhs hc hrhs rest
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.plain unused)
  let childTask : ScheduleTask g input :=
    scheduleTaskOfParse rest pre post input_eq (.live restUsed)
  let startCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task parentTask, next :: tail⟩
  have hstart' : ScheduleInvariant startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using hstart
  have hboundary : ¬ rest.ConsumesAt 1 := by
    simpa [parent, NFParse.ConsumesAt] using unused
  have hone : 1 ∈ rest.eventDepths := by
    rcases (rest.consumesAt_iff_exists_mem_eventDepths_lt 0).1 restUsed with
      ⟨d, hd, hdpos⟩
    have hdle : d ≤ 1 := by
      by_contra hnot
      apply hboundary
      exact (rest.consumesAt_iff_exists_mem_eventDepths_lt 1).2
        ⟨d, hd, by omega⟩
    have heq : d = 1 := by omega
    simpa [heq] using hd
  have parentCompatible : EventCompatible parent [] := by
    constructor
    intro d hd
    have hd0 : d = 0 := by
      by_contra hne
      exact unused ((parent.consumesAt_iff_exists_mem_eventDepths_lt 0).2
        ⟨d, hd, Nat.pos_of_ne_zero hne⟩)
    subst d
    exact BlockLayout.Boundary.start []
  have childCompatible : EventCompatible rest [[f]] :=
    EventCompatible.pushFresh parentCompatible
  have hinputPos : 0 < input.length := by
    have hw := rest.yield_length_pos
    have hlen := congrArg List.length input_eq
    simp only [List.length_append] at hlen
    omega
  let startLedger : ScheduleOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ownerLedger
  have startActive : startLedger.active = [] := by
    simpa [startLedger, startCursor, parentTask, parent, plainScheduleCursor] using
      hactive
  let startShadowLedger : ShadowOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.shadowLedger
  have startShadowActiveEq : startShadowLedger.active = startLedger.active := by
    simpa [startShadowLedger, startLedger, startCursor, parentTask, parent,
      plainScheduleCursor] using resources.shadow_active_eq
  let startTickets : IndexTicketLedger startCursor := by
    simpa [startCursor, parentTask, parent, plainScheduleCursor] using
      resources.tickets
  have startParking : startTickets.ParkingBelow resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      parkingBelow
  let startTicketOwnerLedger : startTickets.SemanticScheduleOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ticketOwnerLedger
  let startTicketShadowLedger : startTickets.SemanticShadowOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      resources.ticketShadowLedger
  have startTicketActiveEq : startTicketOwnerLedger.active =
      startTickets.semanticOwners startLedger.active := by
    simpa [startTicketOwnerLedger, startTickets, startLedger, startCursor,
      parentTask, parent, plainScheduleCursor] using resources.ticket_active_eq
  have startTicketShadowActiveEq : startTicketShadowLedger.active =
      startTickets.semanticOwners resources.ticketShadowOwners := by
    simpa [startTicketShadowLedger, startTickets, startCursor,
      parentTask, parent, plainScheduleCursor] using
        resources.ticket_shadow_active_eq
  have startTicketActive : startTicketOwnerLedger.active = [] := by
    simpa [startActive, IndexTicketLedger.semanticOwners] using
      startTicketActiveEq
  have hparentZero : 0 ∈ parent.eventDepths := by
    simpa [parent, NFParse.eventDepths] using
      (Finset.mem_image.mpr ⟨1, hone, by simp⟩)
  let parentZeroTicket : IndexTicket input :=
    resources.window.shadowEventTicket 0 hparentZero
  let childOneTicket : IndexTicket input :=
    resources.window.pushChild.shadowEventTicket 1 hone
  let parentZeroOwner : Fin (10 * input.length) :=
    resources.window.shadowEventOwner 0 hparentZero
  let childOneOwner : Fin (10 * input.length) :=
    resources.window.pushChild.shadowEventOwner 1 hone
  have hparentZeroNotScratch : ∀ h : 0 < input.length,
      parentZeroTicket ≠ IndexTicket.scratch h := by
    intro h heq
    have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
    simp only [parentZeroTicket,
      ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
      IndexTicket.semanticOwner_scratch] at hsemantic
    exact resources.window.shadowEventOwner_ne_scratchOwner
      hparentZero h hsemantic
  have hchildOneNotScratch : ∀ h : 0 < input.length,
      childOneTicket ≠ IndexTicket.scratch h := by
    intro h heq
    have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
    simp only [childOneTicket,
      ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
      IndexTicket.semanticOwner_scratch] at hsemantic
    exact resources.window.pushChild.shadowEventOwner_ne_scratchOwner
      hone h hsemantic
  let ticketOwnerSwap : Fin (10 * input.length) → Fin (10 * input.length) :=
    Equiv.swap parentZeroOwner childOneOwner
  have hsemanticSwap (ticket : IndexTicket input) :
      IndexTicket.semanticOwner (g := g)
          (Equiv.swap parentZeroTicket childOneTicket ticket) =
        ticketOwnerSwap (IndexTicket.semanticOwner (g := g) ticket) := by
    by_cases hleft : ticket = parentZeroTicket
    · subst ticket
      simp [ticketOwnerSwap, parentZeroTicket, childOneTicket,
        parentZeroOwner, childOneOwner]
    · by_cases hright : ticket = childOneTicket
      · subst ticket
        simp [ticketOwnerSwap, parentZeroTicket, childOneTicket,
          parentZeroOwner, childOneOwner]
      · have hleftSemantic :
            IndexTicket.semanticOwner (g := g) ticket ≠ parentZeroOwner := by
          intro heq
          apply hleft
          apply IndexTicket.semanticOwner_injective (g := g)
          simpa [parentZeroTicket, parentZeroOwner] using heq
        have hrightSemantic :
            IndexTicket.semanticOwner (g := g) ticket ≠ childOneOwner := by
          intro heq
          apply hright
          apply IndexTicket.semanticOwner_injective (g := g)
          simpa [childOneTicket, childOneOwner] using heq
        rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
        exact (Equiv.swap_apply_of_ne_of_ne hleftSemantic
          hrightSemantic).symm
  let rotatedStartTickets : IndexTicketLedger startCursor :=
    startTickets.swapTickets parentZeroTicket childOneTicket
      hparentZeroNotScratch hchildOneNotScratch
  have rotatedParking : rotatedStartTickets.ParkingBelow resources.window := by
    apply startParking.swapTickets_nonparking parentZeroTicket childOneTicket
      hparentZeroNotScratch hchildOneNotScratch
    · exact resources.window.shadowEventTicket_nonparking 0 hparentZero
    · exact resources.window.pushChild.shadowEventTicket_nonparking 1 hone
  have hrotatedSemanticOwner (candidate : Fin (10 * input.length)) :
      rotatedStartTickets.semanticOwnerOf candidate =
        ticketOwnerSwap (startTickets.semanticOwnerOf candidate) := by
    simpa [IndexTicketLedger.semanticOwnerOf, rotatedStartTickets,
      IndexTicketLedger.swapTickets] using
        hsemanticSwap (startTickets.ticketOf candidate)
  have hparentZeroOutsidePrimaryChild :
      OutsideProductiveWindow resources.window.pushChild parentZeroOwner := by
    right
    have hend := resources.window.pushChild.end_le
    simp only [parentZeroOwner,
      ProductiveOwnerWindow.shadowEventOwner_val,
      ProductiveOwnerWindow.pushChild_base, shadowOwnerOffset] at hend ⊢
    omega
  have hchildOneOutsidePrimaryChild :
      OutsideProductiveWindow resources.window.pushChild childOneOwner := by
    right
    have hend := resources.window.pushChild.end_le
    simp only [childOneOwner,
      ProductiveOwnerWindow.shadowEventOwner_val, shadowOwnerOffset] at hend ⊢
    omega
  have hparentZeroNotOutsideShadowChild :
      ¬ OutsideShadowWindow resources.window.pushChild parentZeroOwner := by
    have hpre : NFParse.pushEventPreimage rest.eventDepths 0 ∈
        rest.eventDepths := NFParse.pushEventPreimage_mem hparentZero
    have htransport := resources.window.shadowEventOwner_push hparentZero
    intro hout
    apply OutsideShadowWindow.shadowEventOwner_not_outside
      resources.window.pushChild hpre
    have heq : parentZeroOwner =
        resources.window.pushChild.shadowEventOwner
          (NFParse.pushEventPreimage rest.eventDepths 0) hpre := by
      simpa [parentZeroOwner] using htransport
    exact heq ▸ hout
  have hchildOneNotOutsideShadowChild :
      ¬ OutsideShadowWindow resources.window.pushChild childOneOwner := by
    simpa [childOneOwner] using
      resources.window.pushChild_shadowEventOwner_one_not_outside hone
  have hswapOutsidePrimaryChild
      {candidate : Fin (10 * input.length)}
      (hout : OutsideProductiveWindow resources.window.pushChild candidate) :
      OutsideProductiveWindow resources.window.pushChild
        (ticketOwnerSwap candidate) := by
    by_cases hleft : candidate = parentZeroOwner
    · subst candidate
      simpa [ticketOwnerSwap] using hchildOneOutsidePrimaryChild
    · by_cases hright : candidate = childOneOwner
      · subst candidate
        simpa [ticketOwnerSwap] using hparentZeroOutsidePrimaryChild
      · simpa [ticketOwnerSwap,
          Equiv.swap_apply_of_ne_of_ne hleft hright] using hout
  have hswapEventFrameChild
      {candidate : Fin (10 * input.length)}
      (hframe : EventOwnedFrame rest resources.window.pushChild candidate) :
      EventOwnedFrame rest resources.window.pushChild
        (ticketOwnerSwap candidate) := by
    rcases hframe with hout | ⟨event, hevent⟩
    · exact Or.inl (hswapOutsidePrimaryChild hout)
    · subst candidate
      have hleft : resources.window.pushChild.eventOwner event.val
          event.property ≠ parentZeroOwner := by
        intro heq
        apply EventOwnedFrames.eventOwner_not_outside event.property
        rw [heq]
        exact hparentZeroOutsidePrimaryChild
      have hright : resources.window.pushChild.eventOwner event.val
          event.property ≠ childOneOwner := by
        intro heq
        apply EventOwnedFrames.eventOwner_not_outside event.property
        rw [heq]
        exact hchildOneOutsidePrimaryChild
      apply Or.inr
      refine ⟨event, ?_⟩
      simp [ticketOwnerSwap,
        Equiv.swap_apply_of_ne_of_ne hleft hright]
  have hswapOutsideShadowChild
      {candidate : Fin (10 * input.length)}
      (hout : OutsideShadowWindow resources.window.pushChild candidate) :
      OutsideShadowWindow resources.window.pushChild
        (ticketOwnerSwap candidate) := by
    have hleft : candidate ≠ parentZeroOwner := by
      intro heq
      exact hparentZeroNotOutsideShadowChild (heq ▸ hout)
    have hright : candidate ≠ childOneOwner := by
      intro heq
      exact hchildOneNotOutsideShadowChild (heq ▸ hout)
    simpa [ticketOwnerSwap,
      Equiv.swap_apply_of_ne_of_ne hleft hright] using hout
  obtain ⟨owner, freeTail, hfreeEq⟩ := List.exists_cons_of_ne_nil hfree
  have hownerFresh : owner ∉ startCursor.indexOwners :=
    resources.pool.head_fresh hfreeEq
  have hownerFree : owner ∈ resources.pool.free := by simp [hfreeEq]
  have hownerGeneric : owner ∈ genericOwnerRange g input := by
    exact resources.pool.all_perm.mem_iff.mp
      (List.mem_append_right startCursor.indexOwners hownerFree)
  have hownerProvenance :
      ((∃ hd : 1 ∈ rest.eventDepths,
          owner = resources.window.pushChild.eventOwner 1 hd) ∨
        OutsideProductiveWindow resources.window.pushChild owner) := by
    exact Or.inr (resources.window.pushChild.genericOwner_outside hownerGeneric)
  have hownerShadowOutside :
      OutsideShadowWindow resources.window.pushChild owner :=
    OutsideShadowWindow.genericOwner resources.window.pushChild hownerGeneric
  have hownerTransientNe : owner ≠
      ProductiveOwnerWindow.transientOwner (g := g) hinputPos := by
    intro heq
    have hge := genericOwnerRange_val_ge hownerGeneric
    have hval := congrArg Fin.val heq
    simp only [genericOwnerOffset, ProductiveOwnerWindow.transientOwner_val] at hge hval
    omega
  have hownerScratchNe : owner ≠
      ProductiveOwnerWindow.scratchOwner (g := g) hinputPos := by
    intro heq
    have hge := genericOwnerRange_val_ge hownerGeneric
    have hval := congrArg Fin.val heq
    simp only [genericOwnerOffset, ProductiveOwnerWindow.scratchOwner_val] at hge hval
    omega
  have hticketTransientFresh : IndexTicket.transient hinputPos ∉
      startCursor.indexTickets startTickets.ticketOf := by
    simpa [startTickets, startCursor, parentTask, parent, plainScheduleCursor] using
      ticketTransientFree hinputPos
  have hparentZeroNotTransient :
      parentZeroTicket ≠ IndexTicket.transient hinputPos := by
    intro heq
    have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
    simp only [parentZeroTicket,
      ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
      IndexTicket.semanticOwner_transient] at hsemantic
    exact resources.window.shadowEventOwner_ne_transientOwner
      hparentZero hinputPos hsemantic
  have hchildOneNotTransient :
      childOneTicket ≠ IndexTicket.transient hinputPos := by
    intro heq
    have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
    simp only [childOneTicket,
      ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
      IndexTicket.semanticOwner_transient] at hsemantic
    exact resources.window.pushChild.shadowEventOwner_ne_transientOwner
      hone hinputPos hsemantic
  have hrotatedTransientFresh : IndexTicket.transient hinputPos ∉
      startCursor.indexTickets rotatedStartTickets.ticketOf := by
    intro hmem
    rw [ScheduleCursor.indexTickets] at hmem
    rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
    change Equiv.swap parentZeroTicket childOneTicket
      (startTickets.ticketOf candidate) = IndexTicket.transient hinputPos at heq
    rw [Equiv.swap_apply_eq_iff] at heq
    have hfix : Equiv.swap parentZeroTicket childOneTicket
        (IndexTicket.transient hinputPos) = IndexTicket.transient hinputPos :=
      Equiv.swap_apply_of_ne_of_ne hparentZeroNotTransient.symm
        hchildOneNotTransient.symm
    rw [hfix] at heq
    apply hticketTransientFresh
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hcandidate, heq⟩
  have hticketTransientNotScratch : ∀ h : 0 < input.length,
      IndexTicket.transient hinputPos ≠ IndexTicket.scratch h := by
    intro h heq
    have hval := congrArg Fin.val heq
    simp only [IndexTicket.transient_val, IndexTicket.scratch_val] at hval
    omega
  let owned : ScheduleIndex g input := {
    flags := [f]
    relation := cflagBase g f
    mark := .firstPending
    denotes := .base f
    owner := owner
  }
  let childCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task childTask, .index owned :: next :: tail⟩
  let childShadowLayout : ShadowStartLayout rest resources.window.pushChild
      [[f]] [owner] :=
    shadowLayout.cons (by simp) (Or.inr hownerShadowOutside)
      (fun candidate hout => by
        simpa [ProductiveOwnerWindow.pushChild] using
          OutsideShadowWindow.transport resources.window (by rfl) hout)
      (fun i => Fin.elim0 i)
  have htaskOwner : childTask.owner = parentTask.owner := by
    apply Fin.ext
    rfl
  have hchild : ScheduleInvariant childCursor := by
    dsimp [childCursor, startCursor]
    exact ScheduleInvariant.plainPushUse (alpha ++ [ScheduleAtom.dollar])
      (next :: tail) parentTask childTask owned htaskOwner hownerFresh
      (resources.pool.index_count_lt_of_free_ne_nil hfree) hstart'
  have hindexPerm : childCursor.indexOwners.Perm
      (owner :: startCursor.indexOwners) := by
    simp only [childCursor, startCursor, owned, ScheduleCursor.indexOwners_mk,
      ScheduleAtom.indexOwner?, List.filterMap_cons, List.filterMap_nil,
      List.append_nil]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.indexOwner?)
        (l₂ := (next :: tail).filterMap ScheduleAtom.indexOwner?)
        (a := owner))
  have htasks : childCursor.taskOwners = startCursor.taskOwners := by
    simp [childCursor, startCursor, ScheduleCursor.taskOwners,
      ScheduleCursor.word, ScheduleAtom.taskOwner?, List.filterMap_append, htaskOwner]
  have hframes : childCursor.frameOwners = startCursor.frameOwners := by
    simp [childCursor, startCursor, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append]
  let childTickets : IndexTicketLedger childCursor :=
    rotatedStartTickets.allocate owner (IndexTicket.transient hinputPos)
      hownerFresh hrotatedTransientFresh hticketTransientNotScratch hindexPerm
  have childParking : childTickets.ParkingBelow resources.window.pushChild := by
    have hallocated := rotatedParking.allocate_nonparking owner
      (IndexTicket.transient hinputPos) hownerFresh hrotatedTransientFresh
      hticketTransientNotScratch hindexPerm
      (IndexTicket.transient_nonparking hinputPos)
    simpa [childTickets] using hallocated.transport_mono
      (List.Perm.refl _) (by simp)
  have childTicketOfOwner : childTickets.ticketOf owner =
      IndexTicket.transient hinputPos := by
    simp [childTickets]
  have childSemanticOwners_singleton : childTickets.semanticOwners [owner] =
      [childTickets.semanticOwnerOf owner] := by
    rfl
  have childTicketOf_eq_of_start_mem
      {candidate : Fin (10 * input.length)}
      (hcandidate : candidate ∈ startCursor.indexOwners) :
      childTickets.ticketOf candidate = rotatedStartTickets.ticketOf candidate := by
    simpa [childTickets, IndexTicketLedger.allocate] using
      rotatedStartTickets.insertTicket_eq_of_mem owner
        (IndexTicket.transient hinputPos) hcandidate hownerFresh
  have childTicketFramesEq : childTickets.semanticCursor.frameOwners =
      rotatedStartTickets.semanticCursor.frameOwners := by
    rw [childTickets.semanticCursor_frameOwners,
      rotatedStartTickets.semanticCursor_frameOwners, hframes]
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [childTicketOf_eq_of_start_mem
      (hstart'.frameOwners_subset_indexOwners hcandidate)]
  have childTicketRightTailEq :
      (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
          childTickets.semanticOwnerOf =
        (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
          rotatedStartTickets.semanticOwnerOf := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    apply childTicketOf_eq_of_start_mem
    rw [ScheduleCursor.indexOwners_mk]
    exact List.mem_append_right _ hcandidate
  have childPrefixLedger : PrefixFrameLedger childCursor :=
    startLedger.prefixLedger.transport
      (by simp [childCursor, startCursor])
      (by rw [hframes])
  have childTicketPrefixLedger : PrefixFrameLedger childTickets.semanticCursor := {
    owners_perm := by
      rw [childTickets.semanticCursor_frameOwners]
      simp only [IndexTicketLedger.semanticCursor,
        ScheduleCursor.relabelTicketOwners]
      rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
      exact childPrefixLedger.owners_perm.map childTickets.semanticOwnerOf
  }
  let childOwnerLayout : EventOwnedLayout rest resources.window.pushChild
      [[f]] [owner] := {
    compatible := childCompatible
    owners_length := by simp
    endpoint_pos := by
      intro i
      have hival : i.val = 0 := by
        have hilt := i.isLt
        simp only [List.length_cons, List.length_nil] at hilt
        omega
      have hi : i = (⟨0, by simp⟩ : Fin ([[f]] : List (List g.flag)).length) :=
        Fin.ext hival
      subst i
      simp [blockEndpoint]
    owner_at := by
      intro i
      have hival : i.val = 0 := by
        have hilt := i.isLt
        simp only [List.length_cons, List.length_nil] at hilt
        omega
      have hi : i = (⟨0, by simp⟩ : Fin ([[f]] : List (List g.flag)).length) :=
        Fin.ext hival
      subst i
      simpa [blockEndpoint, blockOwnerAt] using hownerProvenance
  }
  let childOwnerLedger : ScheduleOwnerLedger rest resources.window.pushChild
      childCursor := {
    active := [owner]
    outside := startLedger.outside
    right_eq := by
      simpa [childCursor, startCursor, owned, ScheduleAtom.indexOwner?,
        startActive] using congrArg (List.cons owner) startLedger.right_eq
    outside_at := fun candidate hcandidate =>
      EventOwnedLayout.outside_pushChild resources.window
        (startLedger.outside_at candidate hcandidate)
    frames := by
      rw [hframes]
      exact startLedger.frames.push
    prefixLedger := childPrefixLedger
  }
  let childShadowLedger : ShadowOwnerLedger rest resources.window.pushChild
      childCursor := {
    active := [owner]
    outside := startShadowLedger.outside
    right_eq := by
      have hshadowActive : startShadowLedger.active = [] :=
        startShadowActiveEq.trans startActive
      simpa [childCursor, startCursor, owned, ScheduleAtom.indexOwner?,
        hshadowActive] using congrArg (List.cons owner) startShadowLedger.right_eq
    outside_at := fun candidate hcandidate => by
      simpa [ProductiveOwnerWindow.pushChild] using
        OutsideShadowWindow.transport resources.window (by rfl)
          (startShadowLedger.outside_at candidate hcandidate)
    frames := by
      rw [hframes]
      simpa [ProductiveOwnerWindow.pushChild] using
        startShadowLedger.frames.transportEqual (residual := rest) (by rfl)
    prefixLedger := childPrefixLedger
  }
  let childTicketOwnerLayout : childTickets.EventTicketLayout rest
      resources.window.pushChild [[f]] [owner] := {
    compatible := childCompatible
    owners_length := by simp [IndexTicketLedger.semanticOwners]
    endpoint_pos := by
      intro i
      have hival : i.val = 0 := by
        have hilt := i.isLt
        simp only [List.length_cons, List.length_nil] at hilt
        omega
      have hi : i = (⟨0, by simp⟩ : Fin ([[f]] : List (List g.flag)).length) :=
        Fin.ext hival
      subst i
      simp [blockEndpoint]
    owner_at := by
      intro i
      have hival : i.val = 0 := by
        have hilt := i.isLt
        simp only [List.length_cons, List.length_nil] at hilt
        omega
      have hi : i = (⟨0, by simp⟩ : Fin ([[f]] : List (List g.flag)).length) :=
        Fin.ext hival
      subst i
      apply Or.inr
      simpa [blockOwnerAt, IndexTicketLedger.semanticOwners,
        IndexTicketLedger.semanticOwnerOf, childTicketOfOwner] using
          resources.window.pushChild.transientOwner_outside hinputPos
  }
  let childTicketShadowLayout : childTickets.ShadowTicketLayout rest
      resources.window.pushChild [[f]] [owner] :=
    ShadowStartLayout.ofOutside
      (by simp [IndexTicketLedger.semanticOwners])
      (by simp)
      (fun i => by
        have hival : i.val = 0 := by
          have hilt := i.isLt
          simp only [List.length_cons, List.length_nil] at hilt
          omega
        have hi : i =
            (⟨0, by simp⟩ : Fin ([[f]] : List (List g.flag)).length) :=
          Fin.ext hival
        subst i
        simpa [blockOwnerAt, IndexTicketLedger.semanticOwners,
          IndexTicketLedger.semanticOwnerOf, childTicketOfOwner] using
            OutsideShadowWindow.transientOwner
              resources.window.pushChild hinputPos)
  have startFullTicketShadowLayout : ShadowStartLayout parent resources.window
      resources.ticketShadowBlocks
      (startTickets.semanticOwners resources.ticketShadowOwners) := by
    simpa [startTickets, startCursor, parentTask, parent,
      plainScheduleCursor] using resources.ticketShadowLayout
  have childSemanticContextEq :
      childTickets.semanticOwners resources.ticketShadowOwners =
        (startTickets.semanticOwners resources.ticketShadowOwners).map
          ticketOwnerSwap := by
    simp only [IndexTicketLedger.semanticOwners, List.map_map]
    apply List.map_congr_left
    intro candidate hcandidate
    have hcandidateIndex : candidate ∈ startCursor.indexOwners := by
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using
        resources.ticketShadowOwners_subset hcandidate
    rw [show childTickets.semanticOwnerOf candidate =
        rotatedStartTickets.semanticOwnerOf candidate by
      simp only [IndexTicketLedger.semanticOwnerOf]
      rw [childTicketOf_eq_of_start_mem hcandidateIndex]]
    exact hrotatedSemanticOwner candidate
  have childFullOwnersLength :
      (childTickets.semanticOwners
        (owner :: resources.ticketShadowOwners)).length =
        ([f] :: resources.ticketShadowBlocks).length := by
    simpa [IndexTicketLedger.semanticOwners] using
      congrArg Nat.succ startFullTicketShadowLayout.owners_length
  let childFullTicketShadowLayout : childTickets.ShadowTicketLayout rest
      resources.window.pushChild
      ([f] :: resources.ticketShadowBlocks)
      (owner :: resources.ticketShadowOwners) := {
    owners_length := childFullOwnersLength
    block_nonempty := by
      intro block hblock
      rcases List.mem_cons.mp hblock with rfl | htail
      · simp
      · exact startFullTicketShadowLayout.block_nonempty block htail
    owner_at := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · apply Or.inr
        simpa [blockOwnerAt, IndexTicketLedger.semanticOwners,
          IndexTicketLedger.semanticOwnerOf, childTicketOfOwner] using
            OutsideShadowWindow.transientOwner
              resources.window.pushChild hinputPos
      · have htailAt :
            blockOwnerAt
                (childTickets.semanticOwners
                  (owner :: resources.ticketShadowOwners))
                childFullOwnersLength
                (Fin.succ j) =
              ticketOwnerSwap
                (blockOwnerAt
                  (startTickets.semanticOwners resources.ticketShadowOwners)
                  startFullTicketShadowLayout.owners_length j) := by
          calc
            blockOwnerAt
                (childTickets.semanticOwners
                  (owner :: resources.ticketShadowOwners))
                childFullOwnersLength (Fin.succ j) =
              blockOwnerAt
                (childTickets.semanticOwners resources.ticketShadowOwners)
                (by simpa [IndexTicketLedger.semanticOwners] using
                  childFullOwnersLength) j := by
                have hsucc : Fin.succ j =
                    (⟨j.val + 1, by simp⟩ :
                      Fin ([f] :: resources.ticketShadowBlocks).length) := by
                  apply Fin.ext
                  rfl
                rw [hsucc]
                change blockOwnerAt
                    (childTickets.semanticOwnerOf owner ::
                      childTickets.semanticOwners
                      resources.ticketShadowOwners)
                    childFullOwnersLength
                    ⟨j.val + 1, by simp⟩ = _
                exact EventOwnedLayout.blockOwnerAt_cons_succ
                  (block := [f])
                  (owner := childTickets.semanticOwnerOf owner)
                  (owners := childTickets.semanticOwners
                    resources.ticketShadowOwners)
                  childFullOwnersLength j
            _ = ticketOwnerSwap
                (blockOwnerAt
                  (startTickets.semanticOwners resources.ticketShadowOwners)
                  startFullTicketShadowLayout.owners_length j) := by
              simp only [blockOwnerAt, List.get_eq_getElem,
                IndexTicketLedger.semanticOwners, List.getElem_map]
              have hownersLength : resources.ticketShadowOwners.length =
                  resources.ticketShadowBlocks.length := by
                simpa [IndexTicketLedger.semanticOwners] using
                  startFullTicketShadowLayout.owners_length
              let k : Fin resources.ticketShadowOwners.length :=
                ⟨j.val, by rw [hownersLength]; exact j.isLt⟩
              have hcandidate :=
                List.get_mem resources.ticketShadowOwners k
              have hcandidateIndex :
                  resources.ticketShadowOwners.get k ∈
                    startCursor.indexOwners := by
                simpa [startCursor, parentTask, parent, plainScheduleCursor] using
                  resources.ticketShadowOwners_subset hcandidate
              change childTickets.semanticOwnerOf
                  (resources.ticketShadowOwners.get k) =
                ticketOwnerSwap (startTickets.semanticOwnerOf
                  (resources.ticketShadowOwners.get k))
              rw [show childTickets.semanticOwnerOf
                    (resources.ticketShadowOwners.get k) =
                  rotatedStartTickets.semanticOwnerOf
                    (resources.ticketShadowOwners.get k) by
                simp only [IndexTicketLedger.semanticOwnerOf]
                rw [childTicketOf_eq_of_start_mem hcandidateIndex]]
              simpa [List.get_eq_getElem, k] using
                hrotatedSemanticOwner
                  (resources.ticketShadowOwners.get k)
        rcases startFullTicketShadowLayout.owner_at j with hlocal | hout
        · rcases hlocal with ⟨hd, hownerEq⟩
          have hdepthZero :
              blockStart resources.ticketShadowBlocks j = 0 := by
            by_contra hne
            apply unused
            exact (parent.consumesAt_iff_exists_mem_eventDepths_lt 0).2
              ⟨_, hd, Nat.pos_of_ne_zero hne⟩
          apply Or.inl
          refine ⟨by simpa [hdepthZero] using hone, ?_⟩
          rw [htailAt, hownerEq]
          simp [ticketOwnerSwap, parentZeroOwner, childOneOwner,
            hdepthZero]
        · apply Or.inr
          rw [htailAt]
          apply hswapOutsideShadowChild
          simpa [ProductiveOwnerWindow.pushChild] using
            OutsideShadowWindow.transport resources.window (by rfl) hout
  }
  have rotatedRightEq :
      (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
          rotatedStartTickets.semanticOwnerOf =
        (startTickets.semanticCursor.right.filterMap
          ScheduleAtom.indexOwner?).map ticketOwnerSwap := by
    rw [startTickets.semanticCursor_right_indexOwners]
    simp only [List.map_map]
    apply List.map_congr_left
    intro candidate _hcandidate
    exact hrotatedSemanticOwner candidate
  have rotatedFramesEq : rotatedStartTickets.semanticCursor.frameOwners =
      startTickets.semanticCursor.frameOwners.map ticketOwnerSwap := by
    rw [rotatedStartTickets.semanticCursor_frameOwners,
      startTickets.semanticCursor_frameOwners]
    simp only [List.map_map]
    apply List.map_congr_left
    intro candidate _hcandidate
    exact hrotatedSemanticOwner candidate
  let childTicketOwnerLedger : childTickets.SemanticScheduleOwnerLedger rest
      resources.window.pushChild := {
    active := childTickets.semanticOwners [owner]
    outside := startTicketOwnerLedger.outside.map ticketOwnerSwap
    right_eq := by
      rw [childTickets.semanticCursor_right_indexOwners]
      change childTickets.semanticOwnerOf owner ::
          (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
            childTickets.semanticOwnerOf = _
      rw [childTicketRightTailEq, rotatedRightEq,
        startTicketOwnerLedger.right_eq, startTicketActive]
      rw [childSemanticOwners_singleton]
      simp
    outside_at := by
      intro candidate hcandidate
      rcases List.mem_map.mp hcandidate with ⟨old, hold, rfl⟩
      apply hswapOutsidePrimaryChild
      simpa [ProductiveOwnerWindow.pushChild] using
        EventOwnedFrames.outside_transport resources.window (by rfl)
          (startTicketOwnerLedger.outside_at old hold)
    frames := by
      rw [childTicketFramesEq, rotatedFramesEq]
      let transported := startTicketOwnerLedger.frames.push
      exact {
        owner_at := by
          intro candidate hcandidate
          rcases List.mem_map.mp hcandidate with ⟨old, hold, rfl⟩
          exact hswapEventFrameChild (transported.owner_at old hold)
      }
    prefixLedger := childTicketPrefixLedger
  }
  let childTicketShadowLedger : childTickets.SemanticShadowOwnerLedger rest
      resources.window.pushChild := {
    active := childTickets.semanticOwners
      (owner :: resources.ticketShadowOwners)
    outside := startTicketShadowLedger.outside.map ticketOwnerSwap
    right_eq := by
      rw [childTickets.semanticCursor_right_indexOwners]
      change childTickets.semanticOwnerOf owner ::
          (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
            childTickets.semanticOwnerOf = _
      rw [childTicketRightTailEq, rotatedRightEq,
        startTicketShadowLedger.right_eq, startTicketShadowActiveEq,
        List.map_append, ← childSemanticContextEq]
      simp [IndexTicketLedger.semanticOwners]
    outside_at := by
      intro candidate hcandidate
      rcases List.mem_map.mp hcandidate with ⟨old, hold, rfl⟩
      apply hswapOutsideShadowChild
      simpa [ProductiveOwnerWindow.pushChild] using
        OutsideShadowWindow.transport resources.window (by rfl)
          (startTicketShadowLedger.outside_at old hold)
    frames := by
      rw [childTicketFramesEq, rotatedFramesEq]
      let transported := startTicketShadowLedger.frames.transportEqual
        (residual := rest) (by rfl)
      exact {
        owner_at := by
          intro candidate hcandidate
          rcases List.mem_map.mp hcandidate with ⟨old, hold, rfl⟩
          exact hswapOutsideShadowChild (transported.owner_at old hold)
      }
    prefixLedger := childTicketPrefixLedger
  }
  let childPool : IndexOwnerPool childCursor :=
    resources.pool.allocateMember owner hownerFree hindexPerm
  let childResources : ScheduleRunResources rest pre childCursor := {
    pool := childPool
    tickets := childTickets
    window := resources.window.pushChild
    parkingAtOrBelow := childParking.toAtOrBelow
    ownerLedger := childOwnerLedger
    ticketOwnerLedger := childTicketOwnerLedger
    ticket_active_eq := by rfl
    ticketShadowBlocks := [f] :: resources.ticketShadowBlocks
    ticketShadowOwners := owner :: resources.ticketShadowOwners
    ticketShadowOwners_subset := by
      intro candidate hcandidate
      rcases List.mem_cons.mp hcandidate with rfl | hold
      · exact hindexPerm.mem_iff.mpr (by simp)
      · have hstartMem : candidate ∈ startCursor.indexOwners := by
          simpa [startCursor, parentTask, parent, plainScheduleCursor] using
            resources.ticketShadowOwners_subset hold
        exact hindexPerm.mem_iff.mpr (List.mem_cons_of_mem owner hstartMem)
    ticketShadowOwners_nodup := by
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        apply hownerFresh
        simpa [startCursor, parentTask, parent, plainScheduleCursor] using
          resources.ticketShadowOwners_subset hmem
      · exact resources.ticketShadowOwners_nodup
    ticketShadowLedger := childTicketShadowLedger
    ticket_shadow_active_eq := by rfl
    ticketShadowLayout := childFullTicketShadowLayout
    shadowLedger := childShadowLedger
    shadow_active_eq := by rfl
    charged := resources.charged + 1
    charged_eq_indices := by
      have hlen := hindexPerm.length_eq
      have hold : resources.charged = startCursor.indexOwners.length := by
        simpa [startCursor, parentTask, parent, plainScheduleCursor] using
          resources.charged_eq_indices
      simp only [List.length_cons] at hlen
      omega
    charged_le_indices := by
      have hlen := hindexPerm.length_eq
      have hold := resources.charged_le_indices
      have hold' : resources.charged ≤ startCursor.indexOwners.length := by
        simpa [startCursor, parentTask, parent, plainScheduleCursor] using hold
      simp at hlen
      omega
    productive_le_credit := by
      have hp := resources.productive_le_credit
      have hfreeLen := (List.perm_cons_erase hownerFree).length_eq
      change rest.productiveCount ≤ resources.charged + 1 +
        (resources.pool.free.erase owner).length
      simp only [NFParse.productiveCount, NFParse.binaryCount,
        NFParse.terminalCount] at hp
      simp only [NFParse.productiveCount] at ⊢
      simp only [List.length_cons] at hfreeLen
      omega
    task_locality := by
      intro taskOwner hmem
      apply resources.task_locality taskOwner
      have hold : taskOwner ∈ startCursor.taskOwners := by
        rw [← htasks]
        exact hmem
      simpa [startCursor, parentTask, parent, plainScheduleCursor] using hold
  }
  have hchildCredit : 0 < childResources.charged := by
    dsimp [childResources]
    omega
  have hframeDisjoint : List.Disjoint [owner] childCursor.frameOwners := by
    rw [List.disjoint_left]
    intro candidate hcandidate hframe
    simp only [List.mem_singleton] at hcandidate
    subst candidate
    have hstartFrame : owner ∈ startCursor.frameOwners := by
      simpa [hframes] using hframe
    exact hownerFresh (hstart'.frameOwners_subset_indexOwners hstartFrame)
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos startCursor hstart'
  let childState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos childCursor hchild
  have hpush : ScheduleReaches g input startState childState := by
    apply ScheduleReaches.single
    have hstep := composite_plainPushUse_at input
      (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
      pre.length (alpha.map ScheduleAtom.workSym)
      ((next :: tail).map ScheduleAtom.workSym)
    simpa [startState, childState, scheduleStateOfCursor, ScheduleState.config,
      startCursor, childCursor, parentTask, childTask, parent, owned,
      scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
      ScheduleTask.workSym, List.map_append] using hstep
  let baseLayout : ScheduleBlockLayout g input [] [] []
      (next :: tail) (next :: tail) := .nil (next :: tail)
  let overlayLayout : AdjacentOverlayLayout baseLayout [owned] :=
    AdjacentOverlayLayout.singleton baseLayout owned (by simp [owned])
      (by intro hnil; simp at hnil) (by simp)
  let childParkingContext : OverlayParkingContext childResources [owned] [] [] :=
    .strict (by simpa [childResources] using childParking)
  have childFree : childResources.pool.free ≠ [] := by
    apply childResources.free_ne_nil_of_index_count_lt
    simpa [childResources] using childTickets.index_count_lt hinputPos
  have hrestRun := restOverlay (input := input) owned [] [] stack [] []
    (next :: tail) (next :: tail)
    (by simp [owned]) baseLayout overlayLayout
    (by
      intro k hk
      have hk0 : k = 0 := by simp [owned] at hk; omega
      simpa [hk0] using restUsed)
    (by simpa [owned] using hboundary)
    (by simpa using childCompatible) (by simp)
    pre post input_eq alpha hstable
    (by simpa [childCursor, childTask, liveScheduleCursor])
    (by simpa using hframeDisjoint) hend childResources childParkingContext childFree
    hchildCredit (by simpa using childOwnerLayout)
    (by simpa [owned] using childShadowLayout)
    (by simpa [owned] using childTicketOwnerLayout)
    (by
      refine ⟨resources.ticketShadowBlocks,
        resources.ticketShadowOwners, ?_, ?_⟩
      · simp [childResources, owned]
      · simp [childResources, owned])
    (by
      intro hinput _hmem
      simpa [childResources, owned] using childTicketOfOwner)
    (by simp [childResources, childOwnerLedger, owned])
    (by
      intro hinput hmem
      have hchildMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          childCursor.indexOwners := by
        simpa [childCursor, childTask, liveScheduleCursor] using hmem
      have hclass := hindexPerm.mem_iff.mp hchildMem
      simp only [List.mem_cons] at hclass
      rcases hclass with heq | hold
      · simpa [owned] using heq.symm
      · have holdFresh : ProductiveOwnerWindow.transientOwner
            (g := g) hinput ∉ startCursor.indexOwners := by
          simpa [startCursor, parentTask, parent, plainScheduleCursor] using
            htransientFree hinput
        exact False.elim (holdFresh hold))
    (by
      intro hinput hmem
      have hchildMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
          childCursor.indexOwners := by
        simpa [childCursor, childTask, liveScheduleCursor] using hmem
      have hclass := hindexPerm.mem_iff.mp hchildMem
      simp only [List.mem_cons] at hclass
      rcases hclass with heq | hold
      · exact False.elim (hownerScratchNe (by simpa using heq.symm))
      · have holdFresh : ProductiveOwnerWindow.scratchOwner
            (g := g) hinput ∉ startCursor.indexOwners := by
          simpa [startCursor, parentTask, parent, plainScheduleCursor] using
            _hScratchFree hinput
        exact False.elim (holdFresh hold))
  simpa [startState, startCursor, parentTask, parent, plainScheduleCursor] using
    hpush.trans hrestRun

/-- A concrete pop can never occur in plain mode because it consumes the top inherited flag. -/
public theorem plainScheduleRun_pop_false
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (rest : NFParse g B stack w) :
    PlainScheduleRun (NFParse.pop hr hlhs hc hrhs rest) := by
  intro input unused
  exact False.elim (unused (by simp [NFParse.ConsumesAt]))

/-- Ordinary plain mode follows one grammar constructor and delegates every smaller parse
task to the ordinary/overlay mutual induction hypotheses. -/
public theorem plainScheduleRun_of_smaller
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (ordinaryIH : ∀ {B : g.nt} {stack' : List g.flag} {yield : List T}
      (q : NFParse g B stack' yield), q.nodeCount < parse.nodeCount →
        OrdinaryScheduleRuns q)
    (overlayIH : ∀ {B : g.nt} {stack' : List g.flag} {yield : List T}
      (q : NFParse g B stack' yield), q.nodeCount < parse.nodeCount →
        OverlayScheduleRun q) :
    PlainScheduleRun parse := by
  cases parse with
  | @binary A B C stack u v r hr hlhs hc hrhs leftParse rightParse =>
      have leftRuns : OrdinaryScheduleRuns leftParse := ordinaryIH leftParse (by
        simp only [NFParse.nodeCount]
        have := rightParse.nodeCount_pos
        omega)
      have rightRuns : OrdinaryScheduleRuns rightParse := ordinaryIH rightParse (by
        simp only [NFParse.nodeCount]
        have := leftParse.nodeCount_pos
        omega)
      exact (plainScheduleRun_binary hr hlhs hc hrhs leftParse rightParse
        leftRuns rightRuns :
          PlainScheduleRun
            (NFParse.binary hr hlhs hc hrhs leftParse rightParse))
  | @pop A B f stack w r hr hlhs hc hrhs rest =>
      exact plainScheduleRun_pop_false hr hlhs hc hrhs rest
  | @push A B f stack w r hr hlhs hc hrhs rest =>
      have restRuns : OrdinaryScheduleRuns rest := ordinaryIH rest (by
        simp [NFParse.nodeCount])
      have restOverlay : OverlayScheduleRun rest := overlayIH rest (by
        simp [NFParse.nodeCount])
      intro input unused pre post input_eq alpha next tail hstable hstart hend
        resources hfree parkingBelow hactive shadowLayout ticketTransientFree
        transientFree scratchFree
      by_cases restUsed : rest.ConsumesAt 0
      · exact plainScheduleRun_pushUse_of_pool_nonempty hr hlhs hc hrhs rest
          restUsed restOverlay unused pre post input_eq alpha next tail hstable
          hstart hend resources hfree parkingBelow hactive shadowLayout
          ticketTransientFree transientFree scratchFree
      · exact plainScheduleRun_pushSkip hr hlhs hc hrhs rest restUsed restRuns
          unused pre post input_eq alpha next tail hstable hstart hend resources
          hfree parkingBelow hactive shadowLayout ticketTransientFree transientFree
          scratchFree
  | @terminal A stack a r hr hlhs hc hrhs =>
      exact plainScheduleRun_terminal hr hlhs hc hrhs

end Aho
end IndexedGrammar
