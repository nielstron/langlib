module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Ownership.Shadow
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Resources.IndexTickets

@[expose]
public section

/-!
# Resource-pool surgery for Aho's compressed scheduler

Fresh compressed blocks move one owner from the free suffix into the cursor's persistent-index
owners.  Erasing a private overlay block performs the inverse operation.  These lemmas express
both updates as permutations, keeping the duplicate-freedom proof independent of cursor syntax.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

namespace ShadowOwnerLedger

/-- Build the shadow ledger canonically when the physical owner pool is wholly outside every
semantic shadow window. -/
public def ofGeneric
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {cursor : ScheduleCursor g input}
    (pool : IndexOwnerPool cursor)
    (ledger : ScheduleOwnerLedger parse window cursor) :
    ShadowOwnerLedger parse window cursor where
  active := ledger.active
  outside := ledger.outside
  right_eq := ledger.right_eq
  outside_at := by
    intro owner howner
    have hright : owner ∈ cursor.right.filterMap ScheduleAtom.indexOwner? := by
      rw [ledger.right_eq]
      exact List.mem_append_right _ howner
    have hindex : owner ∈ cursor.indexOwners := by
      rw [ScheduleCursor.indexOwners_mk]
      exact List.mem_append_right _ hright
    exact OutsideShadowWindow.genericOwner window
      (pool.mem_genericOwnerRange_of_mem_indices hindex)
  frames := by
    constructor
    intro owner howner
    have hleft : owner ∈ cursor.left.filterMap ScheduleAtom.indexOwner? :=
      ledger.prefixLedger.owners_perm.mem_iff.mpr howner
    have hindex : owner ∈ cursor.indexOwners := by
      rw [ScheduleCursor.indexOwners_mk]
      exact List.mem_append_left _ (List.mem_append_left _ hleft)
    exact OutsideShadowWindow.genericOwner window
      (pool.mem_genericOwnerRange_of_mem_indices hindex)
  prefixLedger := ledger.prefixLedger

end ShadowOwnerLedger

/-- Resources carried by one mutually recursive runner call.  `charged` counts productive
events of the active task already represented by persistent blocks.  The remaining events fit
in the free-owner pool.  `task_locality` reserves the interior of the active yield interval for
the child tasks introduced by its binary nodes. -/
public structure ScheduleRunResources
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
  (parse : NFParse g A stack w) (pre : List T)
  (cursor : ScheduleCursor g input) where
  pool : IndexOwnerPool cursor
  /-- An injective logical ticket assignment for the generic physical owners. -/
  tickets : IndexTicketLedger cursor
  window : ProductiveOwnerWindow (input := input) parse
  /-- Parking tickets in ordinary resources never lie above the current root-relative
  productive-window base.  Protected mode strengthens this to a strict bound, while an active
  copy-on-write overlay may occupy the base slot itself. -/
  parkingAtOrBelow : tickets.ParkingAtOrBelow window
  ownerLedger : ScheduleOwnerLedger parse window cursor
  /-- Productive-event provenance, interpreted on the logical-ticket projection of `cursor`. -/
  ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger parse window
  /-- The projected active list is aligned with the physical active-owner list. -/
  ticket_active_eq : ticketOwnerLedger.active =
    tickets.semanticOwners ownerLedger.active
  /-- The full aligned shadow context.  It may extend the primary active prefix with parked
  lower blocks which remain on the tape while a structural child runs only that prefix. -/
  ticketShadowBlocks : List (List g.flag)
  ticketShadowOwners : List (Fin (10 * input.length))
  ticketShadowOwners_subset : ticketShadowOwners ⊆ cursor.indexOwners
  ticketShadowOwners_nodup : ticketShadowOwners.Nodup
  /-- Shadow-start provenance on the same logical-ticket projection. -/
  ticketShadowLedger : tickets.SemanticShadowOwnerLedger parse window
  ticket_shadow_active_eq : ticketShadowLedger.active =
    tickets.semanticOwners ticketShadowOwners
  ticketShadowLayout : tickets.ShadowTicketLayout parse window
    ticketShadowBlocks ticketShadowOwners
  shadowLedger : ShadowOwnerLedger parse window cursor
  shadow_active_eq : shadowLedger.active = ownerLedger.active
  charged : ℕ
  charged_eq_indices : charged = cursor.indexOwners.length
  charged_le_indices : charged ≤ cursor.indexOwners.length
  productive_le_credit : parse.productiveCount ≤ charged + pool.free.length
  task_locality : ∀ owner ∈ cursor.taskOwners,
    owner.val = pre.length ∨ owner.val < pre.length ∨
      pre.length + w.length ≤ owner.val

namespace ScheduleRunResources

/-- The selected primary block context is a prefix of the full projected shadow context.
The suffix is parked on the tape and remains visible to shadow-ticket freshness. -/
public def TicketShadowContextExtends
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length))) : Prop :=
  ∃ parkedBlocks parkedOwners,
    resources.ticketShadowBlocks = blocks ++ parkedBlocks ∧
    resources.ticketShadowOwners = owners ++ parkedOwners

/-- An explicit strict index bound below the exhaustive `6|input|` owner pool supplies a free
physical owner. -/
public theorem free_ne_nil_of_index_count_lt
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (hcapacity : cursor.indexOwners.length < 6 * input.length) :
    resources.pool.free ≠ [] := by
  apply resources.tickets.pool_free_ne_nil resources.pool
  exact hcapacity

/-- Every active owner is physically present among the cursor's persistent indices. -/
public theorem active_subset_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor) :
    resources.ownerLedger.active ⊆ cursor.indexOwners := by
  intro owner howner
  have hright : owner ∈ cursor.right.filterMap ScheduleAtom.indexOwner? := by
    rw [resources.ownerLedger.right_eq]
    exact List.mem_append_left _ howner
  rw [ScheduleCursor.indexOwners_mk]
  exact List.mem_append_right _ hright

/-- Pooled owners all lie beyond the semantic shadow window, so any block partition whose
owners are active admits an all-outside shadow layout. -/
public def genericShadowStartLayout
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    {blocks : List (List g.flag)} {owners : List (Fin (10 * input.length))}
    (hactive : resources.ownerLedger.active = owners)
    (hlen : owners.length = blocks.length)
    (hne : ∀ block ∈ blocks, block ≠ []) :
    ShadowStartLayout parse resources.window blocks owners :=
  ShadowStartLayout.ofOutside hlen hne (fun i => by
    have hmemOwners : blockOwnerAt owners hlen i ∈ owners := by
      simp [blockOwnerAt]
    have hmemActive : blockOwnerAt owners hlen i ∈
        resources.ownerLedger.active := by
      rwa [hactive]
    have hmemIndices := resources.active_subset_indexOwners hmemActive
    have hgeneric := resources.pool.mem_genericOwnerRange_of_mem_indices hmemIndices
    exact OutsideShadowWindow.genericOwner resources.window hgeneric)

end ScheduleRunResources

/-- Resource-aware plain runner mode.  Both endpoints are genuine invariant-carrying scheduler
states, so every intermediate node of the result is automatically within the linear bound. -/
public def PlainScheduleRun
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  ∀ {input : List T} (unused : ¬ parse.ConsumesAt 0)
    (pre post : List T) (input_eq : input = pre ++ w ++ post)
    (alpha : List (ScheduleAtom g input)) (next : ScheduleAtom g input)
    (tail : List (ScheduleAtom g input))
    (hstable : StablePrefix (alpha.map ScheduleAtom.workSym))
    (hstart : ScheduleInvariant
      (plainScheduleCursor parse unused pre post input_eq alpha next tail))
    (hend : ScheduleInvariant (scheduleWordCursor alpha (next :: tail)))
      (resources : ScheduleRunResources parse pre
      (plainScheduleCursor parse unused pre post input_eq alpha next tail))
      (_free : resources.pool.free ≠ [])
      (_parkingBelow : resources.tickets.ParkingBelow resources.window)
      (_hactive : resources.ownerLedger.active = [])
      (_shadowLayout : ShadowStartLayout parse resources.window [] [])
      (_ticketTransientFree : ∀ hinput : 0 < input.length,
        IndexTicket.transient hinput ∉
          (plainScheduleCursor parse unused pre post input_eq alpha next tail).indexTickets
            resources.tickets.ticketOf)
      (_transientFree : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
        (plainScheduleCursor parse unused pre post input_eq alpha next tail).indexOwners)
    (_scratchFree : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
        (plainScheduleCursor parse unused pre post input_eq alpha next tail).indexOwners),
    ScheduleReaches g input
      (scheduleStateOfCursor pre.length (by
        rw [input_eq]
        simp) _ hstart)
      (scheduleStateOfCursor (pre ++ w).length (by
        rw [input_eq]
        simp) _ hend)

/-- Resource-aware protected-block runner mode. -/
public def ProtectedScheduleRun
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  ∀ {input : List T} (visible hidden : List g.flag)
    (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length)))
    (word used : List (ScheduleAtom g input))
    (hstack : stack = visible ++ hidden) (hne : visible ≠ [])
    (hall : ∀ k < visible.length, parse.ConsumesAt k)
    (hboundary : ¬ parse.ConsumesAt visible.length)
    (layout : ScheduleBlockLayout g input visible blocks owners word used)
    (compatible : EventCompatible parse blocks),
    ∀ (pre post : List T) (input_eq : input = pre ++ w ++ post)
      (alpha : List (ScheduleAtom g input))
      (hstable : StablePrefix (alpha.map ScheduleAtom.workSym))
      (hstart : ScheduleInvariant
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word))
      (_hframes : List.Disjoint owners
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word).frameOwners)
      (hend : ScheduleInvariant (scheduleWordCursor alpha used))
      (resources : ScheduleRunResources parse pre
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word))
      (_free : resources.pool.free ≠ [])
      (_parkingBelow : resources.tickets.ParkingBelow resources.window)
      (_ownerLayout : EventOwnedLayout parse resources.window blocks owners)
      (_shadowLayout : ShadowStartLayout parse resources.window blocks owners)
      (_ticketOwnerLayout : resources.tickets.EventTicketLayout
        parse resources.window blocks owners)
      (_ticketShadowContext : resources.TicketShadowContextExtends blocks owners)
      (_ticketTransientFree : ∀ hinput : 0 < input.length,
        IndexTicket.transient hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexTickets
              resources.tickets.ticketOf)
      (_hactive : resources.ownerLedger.active = owners)
      (_transientFree : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexOwners)
      (_scratchFree : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexOwners),
      ScheduleReaches g input
        (scheduleStateOfCursor pre.length (by
          rw [input_eq]
          simp) _ hstart)
        (scheduleStateOfCursor (pre ++ w).length (by
          rw [input_eq]
          simp) _ hend)

/-- The two ordinary strict-entry runners used by the window-parking recursion. -/
public def OrdinaryScheduleRuns
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  PlainScheduleRun parse ∧ ProtectedScheduleRun parse
namespace IndexOwnerPool

/-- The head of a free-owner pool cannot already own a persistent index. -/
public theorem head_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    {owner : Fin (10 * input.length)} {rest : List (Fin (10 * input.length))}
    (hfree : pool.free = owner :: rest) : owner ∉ cursor.indexOwners := by
  intro howner
  exact pool.free_disjoint howner (by simp [hfree])

/-- Allocate the head free owner after a cursor change which inserts exactly that owner. -/
public def allocate
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length))
    (rest : List (Fin (10 * input.length)))
    (hfree : pool.free = owner :: rest)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    IndexOwnerPool new where
  free := rest
  all_nodup := by
    have hmove : (new.indexOwners ++ rest).Perm
        (old.indexOwners ++ owner :: rest) := by
      apply (hindices.append_right rest).trans
      simpa only [List.cons_append] using
        (List.perm_middle (l₁ := old.indexOwners) (l₂ := rest)
          (a := owner)).symm
    apply hmove.nodup_iff.mpr
    simpa only [hfree] using pool.all_nodup
  all_perm := by
    have hmove : (new.indexOwners ++ rest).Perm
        (old.indexOwners ++ owner :: rest) := by
      apply (hindices.append_right rest).trans
      simpa only [List.cons_append] using
        (List.perm_middle (l₁ := old.indexOwners) (l₂ := rest)
          (a := owner)).symm
    exact hmove.trans (by simpa only [hfree] using pool.all_perm)

@[simp] public theorem allocate_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length))
    (rest : List (Fin (10 * input.length)))
    (hfree : pool.free = owner :: rest)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    (pool.allocate owner rest hfree hindices).free = rest := rfl

/-- Allocate an explicitly selected free owner.  Unlike `allocate`, the owner need not be the
head of the current free list; the remaining pool is supplied up to permutation. -/
public def allocatePerm
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length))
    (rest : List (Fin (10 * input.length)))
    (hfree : pool.free.Perm (owner :: rest))
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    IndexOwnerPool new where
  free := rest
  all_nodup := by
    have hmove : (new.indexOwners ++ rest).Perm
        (old.indexOwners ++ pool.free) := by
      apply (hindices.append_right rest).trans
      apply (List.perm_middle (l₁ := old.indexOwners) (l₂ := rest)
        (a := owner)).symm.trans
      exact List.Perm.append_left old.indexOwners hfree.symm
    exact hmove.nodup_iff.mpr pool.all_nodup
  all_perm := by
    have hmove : (new.indexOwners ++ rest).Perm
        (old.indexOwners ++ pool.free) := by
      apply (hindices.append_right rest).trans
      apply (List.perm_middle (l₁ := old.indexOwners) (l₂ := rest)
        (a := owner)).symm.trans
      exact List.Perm.append_left old.indexOwners hfree.symm
    exact hmove.trans pool.all_perm

@[simp] public theorem allocatePerm_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length))
    (rest : List (Fin (10 * input.length)))
    (hfree : pool.free.Perm (owner :: rest))
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    (pool.allocatePerm owner rest hfree hindices).free = rest := rfl

/-- Allocate an arbitrary known member of the exhaustive free pool. -/
public def allocateMember
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length)) (hfree : owner ∈ pool.free)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    IndexOwnerPool new :=
  pool.allocatePerm owner (pool.free.erase owner)
    (List.perm_cons_erase hfree) hindices

@[simp] public theorem allocateMember_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length)) (hfree : owner ∈ pool.free)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    (pool.allocateMember owner hfree hindices).free = pool.free.erase owner := rfl

/-- Return an erased owner to the free pool after the cursor removes exactly that index. -/
public def release
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    IndexOwnerPool new where
  free := owner :: pool.free
  all_nodup := by
    have hmove : (new.indexOwners ++ owner :: pool.free).Perm
        (old.indexOwners ++ pool.free) := by
      apply (List.perm_middle (l₁ := new.indexOwners) (l₂ := pool.free)
        (a := owner)).trans
      simpa only [List.cons_append] using hindices.symm.append_right pool.free
    exact hmove.nodup_iff.mpr pool.all_nodup
  all_perm := by
    have hmove : (new.indexOwners ++ owner :: pool.free).Perm
        (old.indexOwners ++ pool.free) := by
      apply (List.perm_middle (l₁ := new.indexOwners) (l₂ := pool.free)
        (a := owner)).trans
      simpa only [List.cons_append] using hindices.symm.append_right pool.free
    exact hmove.trans pool.all_perm

@[simp] public theorem release_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    (pool.release owner hindices).free = owner :: pool.free := rfl

end IndexOwnerPool

namespace ScheduleRunResources

/-- Release a private overlay owner before running a same-yield residual parse. One charged
owner becomes one free owner, so the productive-event credit is preserved exactly. -/
public def releaseOwned
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack residualStack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B residualStack w}
    {pre : List T} {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners))
    (htasks : new.taskOwners = old.taskOwners)
    (hproductive : residual.productiveCount = parse.productiveCount)
    (ownerLedger : ScheduleOwnerLedger residual
      (resources.window.transport hproductive) new)
    (ticketOwnerLedger :
      (resources.tickets.release owner hindices).SemanticScheduleOwnerLedger
        residual (resources.window.transport hproductive))
    (ticket_active_eq : ticketOwnerLedger.active =
      (resources.tickets.release owner hindices).semanticOwners
        ownerLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ new.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger : ShadowOwnerLedger residual
      (resources.window.transport hproductive)
      (resources.tickets.release owner hindices).semanticCursor)
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      (resources.tickets.release owner hindices).semanticOwners
        ticketShadowOwners)
    (ticketShadowLayout :
      (resources.tickets.release owner hindices).ShadowTicketLayout residual
        (resources.window.transport hproductive) ticketShadowBlocks
        ticketShadowOwners)
    (shadowLedger : ShadowOwnerLedger residual
      (resources.window.transport hproductive) new)
    (shadow_active_eq : shadowLedger.active = ownerLedger.active)
    (hcharged : 0 < resources.charged) :
    ScheduleRunResources residual pre new where
  pool := resources.pool.release owner hindices
  tickets := resources.tickets.release owner hindices
  window := resources.window.transport hproductive
  parkingAtOrBelow := by
    intro slot hslot
    apply resources.parkingAtOrBelow slot
    rw [ScheduleCursor.indexTickets] at hslot ⊢
    rcases List.mem_map.mp hslot with ⟨candidate, hcandidate, heq⟩
    exact List.mem_map.mpr ⟨candidate,
      hindices.mem_iff.mpr (List.mem_cons_of_mem owner hcandidate), heq⟩
  ownerLedger := ownerLedger
  ticketOwnerLedger := ticketOwnerLedger
  ticket_active_eq := ticket_active_eq
  ticketShadowBlocks := ticketShadowBlocks
  ticketShadowOwners := ticketShadowOwners
  ticketShadowOwners_subset := ticketShadowOwners_subset
  ticketShadowOwners_nodup := ticketShadowOwners_nodup
  ticketShadowLedger := ticketShadowLedger
  ticket_shadow_active_eq := ticket_shadow_active_eq
  ticketShadowLayout := ticketShadowLayout
  shadowLedger := shadowLedger
  shadow_active_eq := shadow_active_eq
  charged := resources.charged - 1
  charged_eq_indices := by
    have hold := resources.charged_eq_indices
    have hlength := hindices.length_eq
    simp only [List.length_cons] at hlength
    omega
  charged_le_indices := by
    have hold := resources.charged_le_indices
    have hlength := hindices.length_eq
    simp only [List.length_cons] at hlength
    omega
  productive_le_credit := by
    have hold := resources.productive_le_credit
    rw [hproductive]
    simp only [IndexOwnerPool.release_free, List.length_cons]
    omega
  task_locality := by
    intro taskOwner hmem
    apply resources.task_locality taskOwner
    rwa [← htasks]

@[simp] public theorem releaseOwned_charged
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack residualStack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B residualStack w}
    {pre : List T} {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners))
    (htasks : new.taskOwners = old.taskOwners)
    (hproductive : residual.productiveCount = parse.productiveCount)
    (ownerLedger : ScheduleOwnerLedger residual
      (resources.window.transport hproductive) new)
    (ticketOwnerLedger :
      (resources.tickets.release owner hindices).SemanticScheduleOwnerLedger
        residual (resources.window.transport hproductive))
    (ticket_active_eq : ticketOwnerLedger.active =
      (resources.tickets.release owner hindices).semanticOwners
        ownerLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ new.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger :
      (resources.tickets.release owner hindices).SemanticShadowOwnerLedger
        residual (resources.window.transport hproductive))
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      (resources.tickets.release owner hindices).semanticOwners
        ticketShadowOwners)
    (ticketShadowLayout :
      (resources.tickets.release owner hindices).ShadowTicketLayout residual
        (resources.window.transport hproductive) ticketShadowBlocks
        ticketShadowOwners)
    (shadowLedger : ShadowOwnerLedger residual
      (resources.window.transport hproductive) new)
    (shadow_active_eq : shadowLedger.active = ownerLedger.active)
    (hcharged : 0 < resources.charged) :
    (resources.releaseOwned owner hindices htasks hproductive ownerLedger
      ticketOwnerLedger ticket_active_eq ticketShadowBlocks ticketShadowOwners
      ticketShadowOwners_subset ticketShadowOwners_nodup ticketShadowLedger
      ticket_shadow_active_eq ticketShadowLayout shadowLedger
      shadow_active_eq hcharged).charged =
      resources.charged - 1 := rfl

@[simp] public theorem releaseOwned_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack residualStack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B residualStack w}
    {pre : List T} {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners))
    (htasks : new.taskOwners = old.taskOwners)
    (hproductive : residual.productiveCount = parse.productiveCount)
    (ownerLedger : ScheduleOwnerLedger residual
      (resources.window.transport hproductive) new)
    (ticketOwnerLedger :
      (resources.tickets.release owner hindices).SemanticScheduleOwnerLedger
        residual (resources.window.transport hproductive))
    (ticket_active_eq : ticketOwnerLedger.active =
      (resources.tickets.release owner hindices).semanticOwners
        ownerLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ new.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger :
      (resources.tickets.release owner hindices).SemanticShadowOwnerLedger
        residual (resources.window.transport hproductive))
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      (resources.tickets.release owner hindices).semanticOwners
        ticketShadowOwners)
    (ticketShadowLayout :
      (resources.tickets.release owner hindices).ShadowTicketLayout residual
        (resources.window.transport hproductive) ticketShadowBlocks
        ticketShadowOwners)
    (shadowLedger : ShadowOwnerLedger residual
      (resources.window.transport hproductive) new)
    (shadow_active_eq : shadowLedger.active = ownerLedger.active)
    (hcharged : 0 < resources.charged) :
    (resources.releaseOwned owner hindices htasks hproductive ownerLedger
      ticketOwnerLedger ticket_active_eq ticketShadowBlocks ticketShadowOwners
      ticketShadowOwners_subset ticketShadowOwners_nodup ticketShadowLedger
      ticket_shadow_active_eq ticketShadowLayout shadowLedger
      shadow_active_eq hcharged).pool.free =
      owner :: resources.pool.free := rfl

end ScheduleRunResources
end Aho
end IndexedGrammar
