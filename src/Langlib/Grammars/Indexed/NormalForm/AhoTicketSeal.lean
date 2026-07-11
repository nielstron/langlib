module

public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleResources
public import Langlib.Grammars.Indexed.NormalForm.AhoPushOwnerFreshness
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayParking

@[expose]
public section

/-!
# Ghost sealing of a transient logical ticket

An unaligned live head may temporarily use the distinguished transient ticket.  At a
depth-zero productive event the head can be reticketed, without a machine move, to the
canonical shadow ticket at block start zero.  The physical cursor, owner pool, and erased work
configuration are unchanged.

This module packages the reusable lower-level part of that operation.  Runner-specific code
still rebuilds the two projected cursor ledgers, because its exact right-side decomposition and
frame transport depend on the surrounding zipper shape.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

namespace EventOwnedLayout

/-- Replace the first owner by one outside the primary productive window.  Every lower block
classification is unchanged. -/
public def reownerHeadOutside
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {block : List g.flag} {blocks : List (List g.flag)}
    {oldOwner newOwner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (layout : EventOwnedLayout parse window
      (block :: blocks) (oldOwner :: owners))
    (houtside : OutsideProductiveWindow window newOwner) :
    EventOwnedLayout parse window (block :: blocks) (newOwner :: owners) where
  compatible := layout.compatible
  owners_length := by simpa using layout.owners_length
  endpoint_pos := layout.endpoint_pos
  owner_at i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr (by simpa [blockOwnerAt] using houtside)
    · simpa [blockOwnerAt] using layout.owner_at (Fin.succ j)

end EventOwnedLayout

namespace ShadowStartLayout

/-- Restrict a full shadow context to a known aligned prefix. -/
public def appendLeft
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {blocks parkedBlocks : List (List g.flag)}
    {owners parkedOwners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window
      (blocks ++ parkedBlocks) (owners ++ parkedOwners))
    (hlen : owners.length = blocks.length) :
    ShadowStartLayout parse window blocks owners where
  owners_length := hlen
  block_nonempty block hblock :=
    layout.block_nonempty block (List.mem_append_left parkedBlocks hblock)
  owner_at i := by
    let j : Fin (blocks ++ parkedBlocks).length :=
      ⟨i.val, by simp only [List.length_append]; omega⟩
    have hstart : blockStart (blocks ++ parkedBlocks) j =
        blockStart blocks i := by
      simp [blockStart, j,
        List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
    have howner :
        blockOwnerAt (owners ++ parkedOwners) layout.owners_length j =
          blockOwnerAt owners hlen i := by
      simp only [blockOwnerAt, j]
      exact List.getElem_append_left (by rw [hlen]; exact i.isLt)
    have hj := layout.owner_at j
    rcases hj with ⟨hd, hj⟩ | hj
    · left
      refine ⟨hstart ▸ hd, ?_⟩
      simpa only [howner, hstart] using hj
    · right
      simpa only [howner] using hj

/-- Prepend a fresh singleton block after rotating the old first owner to child shadow depth
one.  All lower positive parent starts transport canonically one position deeper. -/
public def pushFreshRotateHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {block : List g.flag} {blocks : List (List g.flag)}
    {oldHead newHead : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout (NFParse.push hr hlhs hc hrhs rest) window
      (block :: blocks) (oldHead :: owners))
    (hone : 1 ∈ rest.eventDepths)
    (hnew : OutsideShadowWindow window.pushChild newHead) :
    ShadowStartLayout rest window.pushChild ([f] :: block :: blocks)
      (newHead :: window.pushChild.shadowEventOwner 1 hone :: owners) where
  owners_length := by simpa using layout.owners_length
  block_nonempty candidate hmem := by
    rcases List.mem_cons.mp hmem with rfl | htail
    · simp
    · exact layout.block_nonempty candidate htail
  owner_at i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr (by simpa [blockOwnerAt] using hnew)
    · refine Fin.cases ?_ (fun k => ?_) j
      · apply Or.inl
        have hstart : blockStart ([f] :: block :: blocks)
            (Fin.succ (0 : Fin (block :: blocks).length)) = 1 := by
          simp [blockStart]
        have hdepth : blockStart ([f] :: block :: blocks)
            (Fin.succ (0 : Fin (block :: blocks).length)) ∈
              rest.eventDepths := by
          simpa [hstart] using hone
        refine ⟨hdepth, ?_⟩
        have hget : blockOwnerAt (blocks := [f] :: block :: blocks)
            (newHead :: window.pushChild.shadowEventOwner 1 hone :: owners)
              (by simpa using layout.owners_length)
              (Fin.succ (0 : Fin (block :: blocks).length)) =
            window.pushChild.shadowEventOwner 1 hone := by
          simp [blockOwnerAt]
        rw [hget]
        apply window.pushChild.shadowEventOwner_congr window.pushChild hone hdepth
        apply Fin.ext
        simp only [ProductiveOwnerWindow.eventOwner_val]
        have hnat := congrArg rest.eventOwnerNat hstart.symm
        omega
      · let oldIndex : Fin (block :: blocks).length := Fin.succ k
        rcases layout.owner_at oldIndex with hlocal | hout
        · rcases hlocal with ⟨hd, howner⟩
          have hdpos : 0 < blockStart (block :: blocks) oldIndex := by
            simp only [oldIndex, blockStart_cons_succ]
            have hblock := layout.block_nonempty block (by simp)
            exact Nat.add_pos_left (List.length_pos_of_ne_nil hblock) _
          have hchild := window.exists_child_eventDepth_of_push_parent_pos hdpos hd
          apply Or.inl
          refine ⟨by
            simpa [oldIndex, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hchild, ?_⟩
          have hshift := window.shadowEventOwner_push_pos hdpos hchild
          simpa [oldIndex, blockOwnerAt, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using howner.trans hshift
        · apply Or.inr
          simpa [oldIndex, blockOwnerAt, ProductiveOwnerWindow.pushChild] using
            OutsideShadowWindow.transport window (by rfl) hout

end ShadowStartLayout

/-- Result of sealing one transient active head. -/
public structure TicketHeadSeal
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (head : Fin (10 * input.length))
    (block : List g.flag) (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length)))
    (hzero : 0 ∈ parse.eventDepths) where
  sealed : IndexTicketLedger cursor
  head_ticket : sealed.ticketOf head = resources.window.shadowEventTicket 0 hzero
  transient_fresh : ∀ hinput : 0 < input.length,
    IndexTicket.transient hinput ∉ cursor.indexTickets sealed.ticketOf
  unchanged : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
    sealed.ticketOf owner = resources.tickets.ticketOf owner
  tail_tickets : ∀ owner ∈ owners,
    sealed.ticketOf owner = resources.tickets.ticketOf owner
  context_tail_tickets : ∀ owner ∈ resources.ticketShadowOwners,
    owner ≠ head → sealed.ticketOf owner = resources.tickets.ticketOf owner
  eventLayout : sealed.EventTicketLayout parse resources.window
    (block :: blocks) (head :: owners)
  shadowLayout : sealed.ShadowTicketLayout parse resources.window
    (block :: blocks) (head :: owners)
  fullShadowLayout : sealed.ShadowTicketLayout parse resources.window
    resources.ticketShadowBlocks resources.ticketShadowOwners

/-- A transient-normalized ticket view of the same physical cursor.  The physical pool,
window, owner ledgers, and accounting data remain in the surrounding `resources`; this
package contains exactly the projected fields which may change when the head is sealed. -/
public structure TicketHeadNormalization
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (head : Fin (10 * input.length))
  (block : List g.flag) (blocks : List (List g.flag))
  (owners : List (Fin (10 * input.length))) where
  tickets : IndexTicketLedger cursor
  parkingAtOrBelow : tickets.ParkingAtOrBelow resources.window
  ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger
    parse resources.window
  ticket_active_eq : ticketOwnerLedger.active =
    tickets.semanticOwners resources.ownerLedger.active
  ticketShadowLedger : tickets.SemanticShadowOwnerLedger
    parse resources.window
  ticket_shadow_active_eq : ticketShadowLedger.active =
    tickets.semanticOwners resources.ticketShadowOwners
  eventLayout : tickets.EventTicketLayout parse resources.window
    (block :: blocks) (head :: owners)
  shadowLayout : tickets.ShadowTicketLayout parse resources.window
    (block :: blocks) (head :: owners)
  fullShadowLayout : tickets.ShadowTicketLayout parse resources.window
    resources.ticketShadowBlocks resources.ticketShadowOwners
  head_shadow : ∀ hzero : 0 ∈ parse.eventDepths,
    tickets.ticketOf head = resources.window.shadowEventTicket 0 hzero
  transient_fresh : ∀ hinput : 0 < input.length,
    IndexTicket.transient hinput ∉ cursor.indexTickets tickets.ticketOf
  unchanged : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
    tickets.ticketOf owner = resources.tickets.ticketOf owner

/-- The complete ghost update obtained by restoring a parked active head to a fresh
nonparking ticket.  Unlike `TicketHeadNormalization`, the restore ticket need not be the
canonical shadow at depth zero: its semantic owner may instead lie outside the residual
shadow window. -/
public structure ActiveHeadTicketRestoration
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (old : ScheduleRunResources parse pre cursor)
    (head : Fin (10 * input.length))
    (block : List g.flag) (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length)))
    (target : IndexTicket input) where
  tickets : IndexTicketLedger cursor
  head_ticket : tickets.ticketOf head = target
  parkingBelow : tickets.ParkingBelow old.window
  ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger parse old.window
  ticket_active_eq : ticketOwnerLedger.active =
    tickets.semanticOwners old.ownerLedger.active
  ticketShadowLedger : tickets.SemanticShadowOwnerLedger parse old.window
  ticket_shadow_active_eq : ticketShadowLedger.active =
    tickets.semanticOwners old.ticketShadowOwners
  eventLayout : tickets.EventTicketLayout parse old.window
    (block :: blocks) (head :: owners)
  shadowLayout : tickets.ShadowTicketLayout parse old.window
    (block :: blocks) (head :: owners)
  fullShadowLayout : tickets.ShadowTicketLayout parse old.window
    old.ticketShadowBlocks old.ticketShadowOwners
  transient_fresh : ∀ hinput : 0 < input.length,
    IndexTicket.transient hinput ∉ cursor.indexTickets tickets.ticketOf
  unchanged : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
    tickets.ticketOf owner = old.tickets.ticketOf owner

namespace ActiveHeadTicketRestoration

/-- Reassemble the unchanged physical resource package around a restored ticket view. -/
public def resources
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    {old : ScheduleRunResources parse pre cursor}
    {head : Fin (10 * input.length)} {block : List g.flag}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {target : IndexTicket input}
    (restored : ActiveHeadTicketRestoration old head block blocks owners target) :
    ScheduleRunResources parse pre cursor := {
  pool := old.pool
  tickets := restored.tickets
  window := old.window
  parkingAtOrBelow := restored.parkingBelow.toAtOrBelow
  ownerLedger := old.ownerLedger
  ticketOwnerLedger := restored.ticketOwnerLedger
  ticket_active_eq := restored.ticket_active_eq
  ticketShadowBlocks := old.ticketShadowBlocks
  ticketShadowOwners := old.ticketShadowOwners
  ticketShadowOwners_subset := old.ticketShadowOwners_subset
  ticketShadowOwners_nodup := old.ticketShadowOwners_nodup
  ticketShadowLedger := restored.ticketShadowLedger
  ticket_shadow_active_eq := restored.ticket_shadow_active_eq
  ticketShadowLayout := restored.fullShadowLayout
  shadowLedger := old.shadowLedger
  shadow_active_eq := old.shadow_active_eq
  charged := old.charged
  charged_eq_indices := old.charged_eq_indices
  charged_le_indices := old.charged_le_indices
  productive_le_credit := old.productive_le_credit
  task_locality := old.task_locality
}

end ActiveHeadTicketRestoration

namespace TicketHeadNormalization

/-- Normalizing a live head to its canonical shadow-zero ticket preserves the ordinary
strict parking invariant.  The normalized head is nonparking and every other live ticket is
unchanged. -/
public theorem parkingBelow
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    {old : ScheduleRunResources parse pre cursor}
    {head : Fin (10 * input.length)} {block : List g.flag}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (normal : TicketHeadNormalization old head block blocks owners)
    (hzero : 0 ∈ parse.eventDepths)
    (hbound : old.tickets.ParkingBelow old.window) :
    normal.tickets.ParkingBelow old.window := by
  intro slot hmem
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  by_cases hhead : candidate = head
  · subst candidate
    rw [normal.head_shadow hzero] at heq
    exact False.elim
      ((old.window.shadowEventTicket_nonparking 0 hzero) slot heq)
  · rw [normal.unchanged candidate hcandidate hhead] at heq
    apply hbound slot
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hcandidate, heq⟩

/-- Reassemble a complete resource package after ghost-only head normalization. -/
public def resources
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    {old : ScheduleRunResources parse pre cursor}
    {head : Fin (10 * input.length)} {block : List g.flag}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (normal : TicketHeadNormalization old head block blocks owners) :
    ScheduleRunResources parse pre cursor := {
  pool := old.pool
  tickets := normal.tickets
  window := old.window
  parkingAtOrBelow := normal.parkingAtOrBelow
  ownerLedger := old.ownerLedger
  ticketOwnerLedger := normal.ticketOwnerLedger
  ticket_active_eq := normal.ticket_active_eq
  ticketShadowBlocks := old.ticketShadowBlocks
  ticketShadowOwners := old.ticketShadowOwners
  ticketShadowOwners_subset := old.ticketShadowOwners_subset
  ticketShadowOwners_nodup := old.ticketShadowOwners_nodup
  ticketShadowLedger := normal.ticketShadowLedger
  ticket_shadow_active_eq := normal.ticket_shadow_active_eq
  ticketShadowLayout := normal.fullShadowLayout
  shadowLedger := old.shadowLedger
  shadow_active_eq := old.shadow_active_eq
  charged := old.charged
  charged_eq_indices := old.charged_eq_indices
  charged_le_indices := old.charged_le_indices
  productive_le_credit := old.productive_le_credit
  task_locality := old.task_locality
}

end TicketHeadNormalization

/-- Logical head alignment used immediately before a fresh unary push.  The old first block
will start at child depth one, while the newly allocated singleton receives the transient
ticket. -/
public structure FreshPushHeadRotation
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources
      (NFParse.push hr hlhs hc hrhs rest) pre cursor)
    {head : Fin (10 * input.length)} {block : List g.flag}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
  (normal : TicketHeadNormalization resources head block blocks owners)
  (hone : 1 ∈ rest.eventDepths) where
  tickets : IndexTicketLedger cursor
  head_ticket : tickets.ticketOf head =
    resources.window.pushChild.shadowEventTicket 1 hone
  transient_fresh : ∀ hinput : 0 < input.length,
    IndexTicket.transient hinput ∉ cursor.indexTickets tickets.ticketOf
  unchanged_normal : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
    tickets.ticketOf owner = normal.tickets.ticketOf owner
  unchanged : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
    tickets.ticketOf owner = resources.tickets.ticketOf owner

namespace ScheduleRunResources

/-- Reticket a parked first active block to a fresh nonparking ticket and rebuild every
ticket-projected resource invariant over the unchanged physical cursor.

The restore ticket may denote either the residual depth-zero shadow owner or an owner outside
the residual shadow window.  Its primary interpretation must be outside the productive window;
these are exactly the two layout facts needed at a singleton-overlay exit. -/
public def restoreParkedActiveHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    {head : Fin (10 * input.length)}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (hactive : resources.ownerLedger.active = head :: owners)
    (hownersNodup : (head :: owners).Nodup)
    (hcontext : resources.TicketShadowContextExtends
      (block :: blocks) (head :: owners))
    (eventLayout : resources.tickets.EventTicketLayout parse resources.window
      (block :: blocks) (head :: owners))
    (shadowLayout : resources.tickets.ShadowTicketLayout parse resources.window
      (block :: blocks) (head :: owners))
    (hheadMem : head ∈ cursor.indexOwners)
    (hheadFrameFresh : head ∉ cursor.frameOwners)
    (hframeSubset : cursor.frameOwners ⊆ cursor.indexOwners)
    (parking : resources.tickets.OverlayParking resources.window head)
    (target : IndexTicket input)
    (htargetFresh : target ∉ cursor.indexTickets resources.tickets.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (htargetNotTransient : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.transient hinput)
    (htargetNonparking : target.Nonparking)
    (htargetOutside : OutsideProductiveWindow resources.window
      (IndexTicket.semanticOwner (g := g) target))
    (htargetShadow :
      (∃ hzero : 0 ∈ parse.eventDepths,
        IndexTicket.semanticOwner (g := g) target =
          resources.window.shadowEventOwner 0 hzero) ∨
      OutsideShadowWindow resources.window
        (IndexTicket.semanticOwner (g := g) target))
    (htransientFree : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∉
        cursor.indexTickets resources.tickets.ticketOf) :
    ActiveHeadTicketRestoration resources head block blocks owners target := by
  let restored : IndexTicketLedger cursor :=
    resources.tickets.reticket head target hheadMem htargetFresh htargetNotScratch
  have hheadTicket : restored.ticketOf head = target := by
    exact resources.tickets.reticket_ticketOf_owner head target hheadMem
      htargetFresh htargetNotScratch
  have hunchanged : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
      restored.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner hne
    exact resources.tickets.reticket_ticketOf_eq_of_mem_ne head target hheadMem
      htargetFresh htargetNotScratch howner hne
  have hrestoredParking : restored.ParkingBelow resources.window := by
    exact parking.reticket_base_nonparking_restores hheadMem target htargetFresh
      htargetNotScratch htargetNonparking
  have htransientRestored : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∉ cursor.indexTickets restored.ticketOf := by
    intro hinput hmem
    rw [ScheduleCursor.indexTickets] at hmem
    rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
    by_cases hownerHead : owner = head
    · subst owner
      rw [hheadTicket] at heq
      exact htargetNotTransient hinput heq
    · rw [hunchanged owner howner hownerHead] at heq
      apply htransientFree hinput
      rw [ScheduleCursor.indexTickets]
      exact List.mem_map.mpr ⟨owner, howner, heq⟩
  have hindexNodup : cursor.indexOwners.Nodup :=
    (List.nodup_append.mp resources.pool.all_nodup).1
  have hrightSublist :
      (cursor.right.filterMap ScheduleAtom.indexOwner?).Sublist
        cursor.indexOwners := by
    change (cursor.right.filterMap ScheduleAtom.indexOwner?).Sublist
      (cursor.word.filterMap ScheduleAtom.indexOwner?)
    apply List.Sublist.filterMap
    rw [ScheduleCursor.word]
    exact ((List.Sublist.refl cursor.right).cons cursor.focus).trans
      (List.sublist_append_right cursor.left (cursor.focus :: cursor.right))
  have hrightNodup :
      (cursor.right.filterMap ScheduleAtom.indexOwner?).Nodup :=
    hindexNodup.sublist hrightSublist
  have hright : cursor.right.filterMap ScheduleAtom.indexOwner? =
      head :: (owners ++ resources.ownerLedger.outside) := by
    rw [resources.ownerLedger.right_eq, hactive]
    simp only [List.cons_append]
  have hheadRightTail : head ∉ owners ++ resources.ownerLedger.outside := by
    rw [hright] at hrightNodup
    exact (List.nodup_cons.mp hrightNodup).1
  have hrightTailTickets : ∀ owner ∈ owners ++ resources.ownerLedger.outside,
      restored.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner
    apply hunchanged owner
    · exact hrightSublist.mem (by
        rw [hright]
        exact List.mem_cons_of_mem head howner)
    · intro heq
      subst owner
      exact hheadRightTail howner
  have hrightTailSemantic :
      (owners ++ resources.ownerLedger.outside).map restored.semanticOwnerOf =
        (owners ++ resources.ownerLedger.outside).map
          resources.tickets.semanticOwnerOf := by
    apply List.map_congr_left
    intro owner howner
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [hrightTailTickets owner howner]
  have hframeTickets : ∀ owner ∈ cursor.frameOwners,
      restored.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner
    apply hunchanged owner (hframeSubset howner)
    intro heq
    subst owner
    exact hheadFrameFresh howner
  have hframeSemantic : cursor.frameOwners.map restored.semanticOwnerOf =
      cursor.frameOwners.map resources.tickets.semanticOwnerOf := by
    apply List.map_congr_left
    intro owner howner
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [hframeTickets owner howner]
  let restoredPrefixLedger : PrefixFrameLedger restored.semanticCursor := {
    owners_perm := by
      rw [restored.semanticCursor_frameOwners]
      simp only [IndexTicketLedger.semanticCursor,
        ScheduleCursor.relabelTicketOwners]
      rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
      exact resources.ownerLedger.prefixLedger.owners_perm.map
        restored.semanticOwnerOf
  }
  have holdOwnerOutside : resources.ticketOwnerLedger.outside =
      resources.tickets.semanticOwners resources.ownerLedger.outside := by
    have heq := resources.ticketOwnerLedger.right_eq
    rw [resources.tickets.semanticCursor_right_indexOwners,
      resources.ownerLedger.right_eq, List.map_append,
      resources.ticket_active_eq] at heq
    have heq' :
        resources.tickets.semanticOwners resources.ownerLedger.active ++
            resources.tickets.semanticOwners resources.ownerLedger.outside =
          resources.tickets.semanticOwners resources.ownerLedger.active ++
            resources.ticketOwnerLedger.outside := by
      simpa only [IndexTicketLedger.semanticOwners] using heq
    exact (List.append_cancel_left heq').symm
  let restoredTicketOwnerLedger : restored.SemanticScheduleOwnerLedger
      parse resources.window := {
    active := restored.semanticOwners resources.ownerLedger.active
    outside := restored.semanticOwners resources.ownerLedger.outside
    right_eq := by
      rw [restored.semanticCursor_right_indexOwners,
        resources.ownerLedger.right_eq, List.map_append]
      rfl
    outside_at := by
      intro semanticOwner hsemantic
      rcases List.mem_map.mp hsemantic with ⟨owner, howner, rfl⟩
      have hownerIndex : owner ∈ cursor.indexOwners := by
        apply hrightSublist.mem
        rw [resources.ownerLedger.right_eq]
        exact List.mem_append_right resources.ownerLedger.active howner
      have hownerNe : owner ≠ head := by
        intro heq
        subst owner
        exact hheadRightTail (List.mem_append_right owners howner)
      have holdMem : resources.tickets.semanticOwnerOf owner ∈
          resources.ticketOwnerLedger.outside := by
        rw [holdOwnerOutside]
        exact List.mem_map.mpr ⟨owner, howner, rfl⟩
      have hold := resources.ticketOwnerLedger.outside_at _ holdMem
      have hticket := hunchanged owner hownerIndex hownerNe
      simpa [IndexTicketLedger.semanticOwnerOf, hticket] using hold
    frames := by
      rw [restored.semanticCursor_frameOwners, hframeSemantic,
        ← resources.tickets.semanticCursor_frameOwners]
      exact resources.ticketOwnerLedger.frames
    prefixLedger := restoredPrefixLedger
  }
  have hcontextTailTickets : ∀ owner ∈ resources.ticketShadowOwners,
      owner ≠ head → restored.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner hne
    exact hunchanged owner (resources.ticketShadowOwners_subset howner) hne
  let restoredTicketShadowLedger : restored.SemanticShadowOwnerLedger
      parse resources.window := {
    active := restored.semanticOwners resources.ticketShadowOwners
    outside := resources.ticketShadowLedger.outside
    right_eq := by
      rcases hcontext with
        ⟨parkedBlocks, parkedOwners, _hcontextBlocks, hcontextOwners⟩
      have hfullOwners : resources.ticketShadowOwners =
          head :: (owners ++ parkedOwners) := by
        simpa only [List.cons_append] using hcontextOwners
      have hcontextTailSemantic :
          (owners ++ parkedOwners).map restored.semanticOwnerOf =
            (owners ++ parkedOwners).map resources.tickets.semanticOwnerOf := by
        apply List.map_congr_left
        intro owner howner
        simp only [IndexTicketLedger.semanticOwnerOf]
        apply congrArg (IndexTicket.semanticOwner (g := g))
        apply hcontextTailTickets owner
        · rw [hfullOwners]
          exact List.mem_cons_of_mem head howner
        · intro heq
          subst owner
          have hfullNodup := resources.ticketShadowOwners_nodup
          rw [hfullOwners] at hfullNodup
          exact (List.nodup_cons.mp hfullNodup).1 howner
      have holdShadowTail :
          resources.tickets.semanticOwners
              (owners ++ resources.ownerLedger.outside) =
            resources.tickets.semanticOwners (owners ++ parkedOwners) ++
              resources.ticketShadowLedger.outside := by
        have heq := resources.ticketShadowLedger.right_eq
        rw [resources.tickets.semanticCursor_right_indexOwners, hright,
          resources.ticket_shadow_active_eq, hfullOwners] at heq
        have htail := congrArg List.tail heq
        simpa [IndexTicketLedger.semanticOwners] using htail
      rw [restored.semanticCursor_right_indexOwners, hright, hfullOwners]
      simp only [IndexTicketLedger.semanticOwners, List.map_cons,
        List.cons_append, List.cons.injEq, true_and]
      rw [hrightTailSemantic, hcontextTailSemantic]
      simpa [IndexTicketLedger.semanticOwners] using holdShadowTail
    outside_at := resources.ticketShadowLedger.outside_at
    frames := by
      rw [restored.semanticCursor_frameOwners, hframeSemantic,
        ← resources.tickets.semanticCursor_frameOwners]
      exact resources.ticketShadowLedger.frames
    prefixLedger := restoredPrefixLedger
  }
  have htailTickets : ∀ owner ∈ owners,
      restored.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner
    apply hunchanged owner
    · apply resources.active_subset_indexOwners
      rw [hactive]
      exact List.mem_cons_of_mem head howner
    · intro heq
      subst owner
      exact (List.nodup_cons.mp hownersNodup).1 howner
  have hnewOwners : restored.semanticOwners (head :: owners) =
      IndexTicket.semanticOwner (g := g) target ::
        resources.tickets.semanticOwners owners := by
    simp only [IndexTicketLedger.semanticOwners, List.map_cons]
    change IndexTicket.semanticOwner (g := g) (restored.ticketOf head) ::
        List.map restored.semanticOwnerOf owners = _
    rw [hheadTicket]
    congr 1
    apply List.map_congr_left
    intro owner howner
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [htailTickets owner howner]
  have restoredEventLayout : restored.EventTicketLayout parse resources.window
      (block :: blocks) (head :: owners) := by
    change EventOwnedLayout parse resources.window (block :: blocks)
      (restored.semanticOwners (head :: owners))
    rw [hnewOwners]
    exact eventLayout.reownerHeadOutside htargetOutside
  have restoredShadowLayout : restored.ShadowTicketLayout parse resources.window
      (block :: blocks) (head :: owners) := by
    change ShadowStartLayout parse resources.window (block :: blocks)
      (restored.semanticOwners (head :: owners))
    rw [hnewOwners]
    exact shadowLayout.reownerHead htargetShadow
  have restoredFullShadowLayout : restored.ShadowTicketLayout parse
      resources.window resources.ticketShadowBlocks
        resources.ticketShadowOwners := by
    rcases hcontext with
      ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
    have hfullOwners : resources.ticketShadowOwners =
        head :: (owners ++ parkedOwners) := by
      simpa only [List.cons_append] using hcontextOwners
    have htailFull : ∀ owner ∈ owners ++ parkedOwners,
        restored.ticketOf owner = resources.tickets.ticketOf owner := by
      intro owner howner
      apply hcontextTailTickets owner
      · rw [hfullOwners]
        exact List.mem_cons_of_mem head howner
      · intro heq
        subst owner
        have hfullNodup := resources.ticketShadowOwners_nodup
        rw [hfullOwners] at hfullNodup
        exact (List.nodup_cons.mp hfullNodup).1 howner
    have hnewFullOwners :
        restored.semanticOwners (head :: (owners ++ parkedOwners)) =
          IndexTicket.semanticOwner (g := g) target ::
            resources.tickets.semanticOwners (owners ++ parkedOwners) := by
      simp only [IndexTicketLedger.semanticOwners, List.map_cons]
      change IndexTicket.semanticOwner (g := g) (restored.ticketOf head) ::
          List.map restored.semanticOwnerOf (owners ++ parkedOwners) = _
      rw [hheadTicket]
      congr 1
      apply List.map_congr_left
      intro owner howner
      simp only [IndexTicketLedger.semanticOwnerOf]
      rw [htailFull owner howner]
    have holdFullLayout : resources.tickets.ShadowTicketLayout parse
        resources.window (block :: (blocks ++ parkedBlocks))
          (head :: (owners ++ parkedOwners)) := by
      rw [← List.cons_append, ← List.cons_append]
      rw [← hcontextBlocks, ← hcontextOwners]
      exact resources.ticketShadowLayout
    rw [hcontextBlocks, hcontextOwners]
    simp only [List.cons_append]
    change ShadowStartLayout parse resources.window
      (block :: (blocks ++ parkedBlocks))
      (restored.semanticOwners (head :: (owners ++ parkedOwners)))
    rw [hnewFullOwners]
    exact holdFullLayout.reownerHead htargetShadow
  exact {
    tickets := restored
    head_ticket := hheadTicket
    parkingBelow := hrestoredParking
    ticketOwnerLedger := restoredTicketOwnerLedger
    ticket_active_eq := rfl
    ticketShadowLedger := restoredTicketShadowLedger
    ticket_shadow_active_eq := rfl
    eventLayout := restoredEventLayout
    shadowLayout := restoredShadowLayout
    fullShadowLayout := restoredFullShadowLayout
    transient_fresh := htransientRestored
    unchanged := hunchanged
  }

/-- Seal a transient logical head into the canonical shadow ticket at depth zero.

The active-list and focus hypotheses are precisely what lets the projected shadow ledger prove
whole-cursor freshness.  `hownersNodup` is normally obtained from the surrounding
`ScheduleBlockLayout`; it is used only to show that reticketing the head leaves all lower owner
associations unchanged. -/
public def sealTransientHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (hinput : 0 < input.length)
    {head : Fin (10 * input.length)}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (hactive : resources.ownerLedger.active = head :: owners)
    (hownersNodup : (head :: owners).Nodup)
    (hcontext : resources.TicketShadowContextExtends
      (block :: blocks) (head :: owners))
    (eventLayout : resources.tickets.EventTicketLayout parse resources.window
      (block :: blocks) (head :: owners))
    (shadowLayout : resources.tickets.ShadowTicketLayout parse resources.window
      (block :: blocks) (head :: owners))
    (hzero : 0 ∈ parse.eventDepths)
    (hheadMem : head ∈ cursor.indexOwners)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hheadTarget : resources.tickets.ticketOf head ≠
      resources.window.shadowEventTicket 0 hzero)
    (htransientHead : IndexTicket.transient hinput ∈
        cursor.indexTickets resources.tickets.ticketOf →
      resources.tickets.ticketOf head = IndexTicket.transient hinput) :
    TicketHeadSeal resources head block blocks owners hzero := by
  let target : IndexTicket input := resources.window.shadowEventTicket 0 hzero
  have hheadNe : resources.window.shadowEventOwner 0 hzero ≠
      resources.tickets.semanticOwnerOf head := by
    intro heq
    apply hheadTarget
    apply IndexTicket.semanticOwner_injective
    simpa [target, IndexTicketLedger.semanticOwnerOf] using heq.symm
  have hactiveFresh : resources.window.shadowEventOwner 0 hzero ∉
      resources.ticketShadowLedger.active := by
    rcases hcontext with
      ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
    have hfullShadowLayout : resources.tickets.ShadowTicketLayout parse
        resources.window (block :: (blocks ++ parkedBlocks))
          (head :: (owners ++ parkedOwners)) := by
      rw [← List.cons_append, ← List.cons_append]
      rw [← hcontextBlocks, ← hcontextOwners]
      exact resources.ticketShadowLayout
    have hactiveFreshRaw : resources.window.shadowEventOwner 0 hzero ∉
        resources.tickets.semanticOwners
          (head :: (owners ++ parkedOwners)) :=
      hfullShadowLayout.shadowEventOwner_zero_fresh_of_head_ne hzero hheadNe
    rw [resources.ticket_shadow_active_eq, hcontextOwners]
    simpa only [List.cons_append] using hactiveFreshRaw
  have hfocusSemantic :
      [resources.tickets.semanticCursor.focus].filterMap
        ScheduleAtom.indexOwner? = [] := by
    rw [resources.tickets.semanticCursor_focus_indexOwners, hfocus]
    rfl
  have htargetSemanticFresh : resources.window.shadowEventOwner 0 hzero ∉
      resources.tickets.semanticCursor.indexOwners :=
    resources.ticketShadowLedger.shadowEventOwner_not_mem_indexOwners_of_active
      hfocusSemantic hzero hactiveFresh
  have htargetFresh : target ∉
      cursor.indexTickets resources.tickets.ticketOf := by
    apply resources.tickets.ticket_not_mem_of_semanticOwner_not_mem
    simpa [target] using htargetSemanticFresh
  have htargetNotScratch : ∀ h : 0 < input.length,
      target ≠ IndexTicket.scratch h := by
    intro h heq
    have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
    simp only [target, ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
      IndexTicket.semanticOwner_scratch] at hsemantic
    exact resources.window.shadowEventOwner_ne_scratchOwner hzero h hsemantic
  let sealed : IndexTicketLedger cursor :=
    resources.tickets.reticket head target hheadMem htargetFresh htargetNotScratch
  have hheadTicket : sealed.ticketOf head = target := by
    exact resources.tickets.reticket_ticketOf_owner head target hheadMem
      htargetFresh htargetNotScratch
  have hunchanged : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
      sealed.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner hne
    exact resources.tickets.reticket_ticketOf_eq_of_mem_ne head target hheadMem
      htargetFresh htargetNotScratch howner hne
  have htransientFresh : ∀ h : 0 < input.length,
      IndexTicket.transient h ∉ cursor.indexTickets sealed.ticketOf := by
    intro h hmem
    have hsame : IndexTicket.transient h = IndexTicket.transient hinput := by
      apply Fin.ext
      rfl
    rw [hsame] at hmem
    by_cases holdTransient : IndexTicket.transient hinput ∈
        cursor.indexTickets resources.tickets.ticketOf
    · have holdFresh := resources.tickets.reticket_old_fresh head target
        hheadMem htargetFresh htargetNotScratch
      rw [← htransientHead holdTransient] at hmem
      exact holdFresh hmem
    · rw [ScheduleCursor.indexTickets] at hmem
      rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
      by_cases heqHead : owner = head
      · subst owner
        rw [hheadTicket] at heq
        have hne : target ≠ IndexTicket.transient hinput := by
          intro htargetTransient
          have hsemantic := congrArg (IndexTicket.semanticOwner (g := g))
            htargetTransient
          simp only [target,
            ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
            IndexTicket.semanticOwner_transient] at hsemantic
          exact resources.window.shadowEventOwner_ne_transientOwner
            hzero hinput hsemantic
        exact hne heq
      · rw [hunchanged owner howner heqHead] at heq
        apply holdTransient
        rw [ScheduleCursor.indexTickets]
        exact List.mem_map.mpr ⟨owner, howner, heq⟩
  have hcontextTailTickets : ∀ owner ∈ resources.ticketShadowOwners,
      owner ≠ head → sealed.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner hne
    apply resources.tickets.reticket_ticketOf_eq_of_mem_ne head target hheadMem
      htargetFresh htargetNotScratch
    · exact resources.ticketShadowOwners_subset howner
    · exact hne
  have htailTickets : ∀ owner ∈ owners,
      sealed.ticketOf owner = resources.tickets.ticketOf owner := by
    intro owner howner
    apply resources.tickets.reticket_ticketOf_eq_of_mem_ne head target hheadMem
      htargetFresh htargetNotScratch
    · apply resources.active_subset_indexOwners
      rw [hactive]
      exact List.mem_cons_of_mem head howner
    · intro heq
      subst owner
      exact (List.nodup_cons.mp hownersNodup).1 howner
  have hnewOwners : sealed.semanticOwners (head :: owners) =
      resources.window.shadowEventOwner 0 hzero ::
        resources.tickets.semanticOwners owners := by
    simp only [IndexTicketLedger.semanticOwners, List.map_cons]
    change IndexTicket.semanticOwner (g := g) (sealed.ticketOf head) ::
        List.map sealed.semanticOwnerOf owners = _
    rw [hheadTicket]
    simp only [target,
      ProductiveOwnerWindow.semanticOwner_shadowEventTicket]
    congr 1
    apply List.map_congr_left
    intro owner howner
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [htailTickets owner howner]
  have htargetOutside : OutsideProductiveWindow resources.window
      (resources.window.shadowEventOwner 0 hzero) := by
    right
    have hend := resources.window.end_le
    simp only [ProductiveOwnerWindow.shadowEventOwner_val, shadowOwnerOffset]
    omega
  have sealedEventLayout : sealed.EventTicketLayout parse resources.window
      (block :: blocks) (head :: owners) := by
    change EventOwnedLayout parse resources.window (block :: blocks)
      (sealed.semanticOwners (head :: owners))
    rw [hnewOwners]
    exact eventLayout.reownerHeadOutside htargetOutside
  have sealedShadowLayout : sealed.ShadowTicketLayout parse resources.window
      (block :: blocks) (head :: owners) := by
    change ShadowStartLayout parse resources.window (block :: blocks)
      (sealed.semanticOwners (head :: owners))
    rw [hnewOwners]
    exact shadowLayout.reownerHead (Or.inl ⟨hzero, rfl⟩)
  have sealedFullShadowLayout : sealed.ShadowTicketLayout parse resources.window
      resources.ticketShadowBlocks resources.ticketShadowOwners := by
    rcases hcontext with
      ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
    have holdLayout : resources.tickets.ShadowTicketLayout parse resources.window
        (block :: (blocks ++ parkedBlocks))
          (head :: (owners ++ parkedOwners)) := by
      rw [← List.cons_append, ← List.cons_append]
      rw [← hcontextBlocks, ← hcontextOwners]
      exact resources.ticketShadowLayout
    have htailFull : ∀ owner ∈ owners ++ parkedOwners,
        sealed.ticketOf owner = resources.tickets.ticketOf owner := by
      intro owner howner
      apply hcontextTailTickets owner
      · rw [hcontextOwners]
        simpa only [List.cons_append] using List.mem_cons_of_mem head howner
      · intro heq
        subst owner
        have hcontextNodup := resources.ticketShadowOwners_nodup
        rw [hcontextOwners] at hcontextNodup
        exact (List.nodup_cons.mp (by simpa only [List.cons_append] using
          hcontextNodup)).1 howner
    have hnewFullOwners :
        sealed.semanticOwners (head :: (owners ++ parkedOwners)) =
          resources.window.shadowEventOwner 0 hzero ::
            resources.tickets.semanticOwners (owners ++ parkedOwners) := by
      simp only [IndexTicketLedger.semanticOwners, List.map_cons]
      change IndexTicket.semanticOwner (g := g) (sealed.ticketOf head) ::
          List.map sealed.semanticOwnerOf (owners ++ parkedOwners) = _
      rw [hheadTicket]
      simp only [target,
        ProductiveOwnerWindow.semanticOwner_shadowEventTicket]
      congr 1
      apply List.map_congr_left
      intro owner howner
      simp only [IndexTicketLedger.semanticOwnerOf]
      rw [htailFull owner howner]
    rw [hcontextBlocks, hcontextOwners]
    simp only [List.cons_append]
    change ShadowStartLayout parse resources.window
      (block :: (blocks ++ parkedBlocks))
      (sealed.semanticOwners (head :: (owners ++ parkedOwners)))
    rw [hnewFullOwners]
    exact holdLayout.reownerHead (Or.inl ⟨hzero, rfl⟩)
  exact {
    sealed := sealed
    head_ticket := hheadTicket
    transient_fresh := htransientFresh
    unchanged := hunchanged
    tail_tickets := htailTickets
    context_tail_tickets := hcontextTailTickets
    eventLayout := sealedEventLayout
    shadowLayout := sealedShadowLayout
    fullShadowLayout := sealedFullShadowLayout
  }

/-- Normalize the logical transient ticket at a compressed head. If the transient ticket is
already absent this is the identity package; otherwise the head is sealed to shadow start zero
and both projected cursor ledgers are rebuilt over the unchanged physical cursor. -/
public def normalizeTransientHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (hinput : 0 < input.length)
    {head : Fin (10 * input.length)}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (hactive : resources.ownerLedger.active = head :: owners)
    (hownersNodup : (head :: owners).Nodup)
    (hcontext : resources.TicketShadowContextExtends
      (block :: blocks) (head :: owners))
    (eventLayout : resources.tickets.EventTicketLayout parse resources.window
      (block :: blocks) (head :: owners))
    (hzero : 0 ∈ parse.eventDepths)
    (hheadMem : head ∈ cursor.indexOwners)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hheadFrameFresh : head ∉ cursor.frameOwners)
    (hframeSubset : cursor.frameOwners ⊆ cursor.indexOwners)
    (htransientHead : IndexTicket.transient hinput ∈
        cursor.indexTickets resources.tickets.ticketOf →
      resources.tickets.ticketOf head = IndexTicket.transient hinput) :
    TicketHeadNormalization resources head block blocks owners := by
  have hselectedShadow : resources.tickets.ShadowTicketLayout parse
      resources.window (block :: blocks) (head :: owners) := by
    rcases hcontext with
      ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
    have hfull : resources.tickets.ShadowTicketLayout parse resources.window
        ((block :: blocks) ++ parkedBlocks)
        ((head :: owners) ++ parkedOwners) := by
      rw [← hcontextBlocks, ← hcontextOwners]
      exact resources.ticketShadowLayout
    change ShadowStartLayout parse resources.window
      ((block :: blocks) ++ parkedBlocks)
      (resources.tickets.semanticOwners
        ((head :: owners) ++ parkedOwners)) at hfull
    have hfull' : ShadowStartLayout parse resources.window
        ((block :: blocks) ++ parkedBlocks)
        (resources.tickets.semanticOwners (head :: owners) ++
          resources.tickets.semanticOwners parkedOwners) := by
      change ShadowStartLayout parse resources.window
        ((block :: blocks) ++ parkedBlocks)
        ((head :: owners).map resources.tickets.semanticOwnerOf ++
          parkedOwners.map resources.tickets.semanticOwnerOf)
      rw [← List.map_append]
      exact hfull
    exact hfull'.appendLeft (by
      simpa [IndexTicketLedger.semanticOwners] using eventLayout.owners_length)
  by_cases hheadTarget : resources.tickets.ticketOf head ≠
      resources.window.shadowEventTicket 0 hzero
  · let headSeal := resources.sealTransientHead hinput hactive hownersNodup
      hcontext
      eventLayout hselectedShadow hzero hheadMem hfocus
      hheadTarget htransientHead
    have hindexNodup : cursor.indexOwners.Nodup :=
      (List.nodup_append.mp resources.pool.all_nodup).1
    have hrightSublist :
        (cursor.right.filterMap ScheduleAtom.indexOwner?).Sublist
          cursor.indexOwners := by
      change (cursor.right.filterMap ScheduleAtom.indexOwner?).Sublist
        (cursor.word.filterMap ScheduleAtom.indexOwner?)
      apply List.Sublist.filterMap
      rw [ScheduleCursor.word]
      exact ((List.Sublist.refl cursor.right).cons cursor.focus).trans
        (List.sublist_append_right cursor.left (cursor.focus :: cursor.right))
    have hrightNodup :
        (cursor.right.filterMap ScheduleAtom.indexOwner?).Nodup :=
      hindexNodup.sublist hrightSublist
    have hright : cursor.right.filterMap ScheduleAtom.indexOwner? =
        head :: (owners ++ resources.ownerLedger.outside) := by
      rw [resources.ownerLedger.right_eq, hactive]
      simp only [List.cons_append]
    have hrightTailNodup : (owners ++ resources.ownerLedger.outside).Nodup := by
      rw [hright] at hrightNodup
      exact (List.nodup_cons.mp hrightNodup).2
    have hheadRightTail : head ∉ owners ++ resources.ownerLedger.outside := by
      rw [hright] at hrightNodup
      exact (List.nodup_cons.mp hrightNodup).1
    have hrightTailTickets : ∀ owner ∈
        owners ++ resources.ownerLedger.outside,
        headSeal.sealed.ticketOf owner = resources.tickets.ticketOf owner := by
      intro owner howner
      apply headSeal.unchanged owner
      · exact hrightSublist.mem (by rw [hright]; exact List.mem_cons_of_mem head howner)
      · intro heq
        subst owner
        exact hheadRightTail howner
    have hrightTailSemantic :
        (owners ++ resources.ownerLedger.outside).map
            headSeal.sealed.semanticOwnerOf =
          (owners ++ resources.ownerLedger.outside).map
            resources.tickets.semanticOwnerOf := by
      apply List.map_congr_left
      intro owner howner
      simp only [IndexTicketLedger.semanticOwnerOf]
      rw [hrightTailTickets owner howner]
    have hframeTickets : ∀ owner ∈ cursor.frameOwners,
        headSeal.sealed.ticketOf owner = resources.tickets.ticketOf owner := by
      intro owner howner
      apply headSeal.unchanged owner (hframeSubset howner)
      intro heq
      subst owner
      exact hheadFrameFresh howner
    have hframeSemantic : cursor.frameOwners.map headSeal.sealed.semanticOwnerOf =
        cursor.frameOwners.map resources.tickets.semanticOwnerOf := by
      apply List.map_congr_left
      intro owner howner
      simp only [IndexTicketLedger.semanticOwnerOf]
      rw [hframeTickets owner howner]
    let sealedPrefixLedger : PrefixFrameLedger headSeal.sealed.semanticCursor := {
      owners_perm := by
        rw [headSeal.sealed.semanticCursor_frameOwners]
        simp only [IndexTicketLedger.semanticCursor,
          ScheduleCursor.relabelTicketOwners]
        rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
        exact resources.ownerLedger.prefixLedger.owners_perm.map
          headSeal.sealed.semanticOwnerOf
    }
    have holdOwnerOutside : resources.ticketOwnerLedger.outside =
        resources.tickets.semanticOwners resources.ownerLedger.outside := by
      have heq := resources.ticketOwnerLedger.right_eq
      rw [resources.tickets.semanticCursor_right_indexOwners,
        resources.ownerLedger.right_eq, List.map_append,
        resources.ticket_active_eq] at heq
      have heq' :
          resources.tickets.semanticOwners resources.ownerLedger.active ++
              resources.tickets.semanticOwners resources.ownerLedger.outside =
            resources.tickets.semanticOwners resources.ownerLedger.active ++
              resources.ticketOwnerLedger.outside := by
        simpa only [IndexTicketLedger.semanticOwners] using heq
      exact (List.append_cancel_left heq').symm
    let sealedTicketOwnerLedger : headSeal.sealed.SemanticScheduleOwnerLedger
        parse resources.window := {
      active := headSeal.sealed.semanticOwners resources.ownerLedger.active
      outside := headSeal.sealed.semanticOwners resources.ownerLedger.outside
      right_eq := by
        rw [headSeal.sealed.semanticCursor_right_indexOwners,
          resources.ownerLedger.right_eq, List.map_append]
        rfl
      outside_at := by
        intro semanticOwner hsemantic
        rcases List.mem_map.mp hsemantic with
          ⟨owner, howner, rfl⟩
        have hownerIndex : owner ∈ cursor.indexOwners := by
          apply hrightSublist.mem
          rw [resources.ownerLedger.right_eq]
          exact List.mem_append_right resources.ownerLedger.active howner
        have hownerNe : owner ≠ head := by
          intro heq
          subst owner
          exact hheadRightTail
            (List.mem_append_right owners howner)
        have holdMem : resources.tickets.semanticOwnerOf owner ∈
            resources.ticketOwnerLedger.outside := by
          rw [holdOwnerOutside]
          exact List.mem_map.mpr ⟨owner, howner, rfl⟩
        have hold := resources.ticketOwnerLedger.outside_at _ holdMem
        have hticket := headSeal.unchanged owner hownerIndex hownerNe
        simpa [IndexTicketLedger.semanticOwnerOf, hticket] using hold
      frames := by
        rw [headSeal.sealed.semanticCursor_frameOwners, hframeSemantic,
          ← resources.tickets.semanticCursor_frameOwners]
        exact resources.ticketOwnerLedger.frames
      prefixLedger := sealedPrefixLedger
    }
    let sealedTicketShadowLedger : headSeal.sealed.SemanticShadowOwnerLedger
        parse resources.window := {
      active := headSeal.sealed.semanticOwners resources.ticketShadowOwners
      outside := resources.ticketShadowLedger.outside
      right_eq := by
        rcases hcontext with
          ⟨parkedBlocks, parkedOwners, _hcontextBlocks, hcontextOwners⟩
        have hfullOwners : resources.ticketShadowOwners =
            head :: (owners ++ parkedOwners) := by
          simpa only [List.cons_append] using hcontextOwners
        have hcontextTailSemantic :
            (owners ++ parkedOwners).map headSeal.sealed.semanticOwnerOf =
              (owners ++ parkedOwners).map
                resources.tickets.semanticOwnerOf := by
          apply List.map_congr_left
          intro owner howner
          simp only [IndexTicketLedger.semanticOwnerOf]
          apply congrArg (IndexTicket.semanticOwner (g := g))
          apply headSeal.context_tail_tickets owner
          · rw [hfullOwners]
            exact List.mem_cons_of_mem head howner
          · intro heq
            subst owner
            have hfullNodup := resources.ticketShadowOwners_nodup
            rw [hfullOwners] at hfullNodup
            exact (List.nodup_cons.mp hfullNodup).1 howner
        have holdShadowTail :
            resources.tickets.semanticOwners
                (owners ++ resources.ownerLedger.outside) =
              resources.tickets.semanticOwners (owners ++ parkedOwners) ++
                resources.ticketShadowLedger.outside := by
          have heq := resources.ticketShadowLedger.right_eq
          rw [resources.tickets.semanticCursor_right_indexOwners, hright,
            resources.ticket_shadow_active_eq, hfullOwners] at heq
          have htail := congrArg List.tail heq
          simpa [IndexTicketLedger.semanticOwners] using htail
        rw [headSeal.sealed.semanticCursor_right_indexOwners, hright, hfullOwners]
        simp only [IndexTicketLedger.semanticOwners, List.map_cons,
          List.cons_append, List.cons.injEq, true_and]
        rw [hrightTailSemantic, hcontextTailSemantic]
        simpa [IndexTicketLedger.semanticOwners] using holdShadowTail
      outside_at := resources.ticketShadowLedger.outside_at
      frames := by
        rw [headSeal.sealed.semanticCursor_frameOwners, hframeSemantic,
          ← resources.tickets.semanticCursor_frameOwners]
        exact resources.ticketShadowLedger.frames
      prefixLedger := sealedPrefixLedger
    }
    exact {
      tickets := headSeal.sealed
      parkingAtOrBelow := by
        intro slot hslot
        rw [ScheduleCursor.indexTickets] at hslot
        rcases List.mem_map.mp hslot with ⟨owner, howner, heq⟩
        by_cases hownerHead : owner = head
        · subst owner
          rw [headSeal.head_ticket] at heq
          have hval := congrArg Fin.val heq
          simp only [ProductiveOwnerWindow.shadowEventTicket,
            IndexTicket.ofSemanticOwner, IndexTicket.parking_val] at hval
          have hlocal := parse.eventOwnerNat_lt_productiveCount hzero
          have hend := resources.window.end_le
          simp only [ProductiveOwnerWindow.shadowEventOwner_val,
            shadowOwnerOffset] at hval
          omega
        · apply resources.parkingAtOrBelow slot
          rw [ScheduleCursor.indexTickets]
          exact List.mem_map.mpr ⟨owner, howner,
            (headSeal.unchanged owner howner hownerHead).symm.trans heq⟩
      ticketOwnerLedger := sealedTicketOwnerLedger
      ticket_active_eq := rfl
      ticketShadowLedger := sealedTicketShadowLedger
      ticket_shadow_active_eq := rfl
      eventLayout := headSeal.eventLayout
      shadowLayout := headSeal.shadowLayout
      fullShadowLayout := headSeal.fullShadowLayout
      head_shadow := by
        intro hzero'
        simpa using headSeal.head_ticket
      transient_fresh := headSeal.transient_fresh
      unchanged := headSeal.unchanged
    }
  · exact {
      tickets := resources.tickets
      parkingAtOrBelow := resources.parkingAtOrBelow
      ticketOwnerLedger := resources.ticketOwnerLedger
      ticket_active_eq := resources.ticket_active_eq
      ticketShadowLedger := resources.ticketShadowLedger
      ticket_shadow_active_eq := resources.ticket_shadow_active_eq
      eventLayout := eventLayout
      shadowLayout := hselectedShadow
      fullShadowLayout := resources.ticketShadowLayout
      head_shadow := by
        intro hzero'
        have hheadTargetEq : resources.tickets.ticketOf head =
            resources.window.shadowEventTicket 0 hzero :=
          Decidable.not_not.mp hheadTarget
        simpa using hheadTargetEq
      transient_fresh := by
        intro h hmem
        have heq : IndexTicket.transient h = IndexTicket.transient hinput := by
          apply Fin.ext
          rfl
        rw [heq] at hmem
        have hheadTransient := htransientHead hmem
        have hheadTargetEq : resources.tickets.ticketOf head =
            resources.window.shadowEventTicket 0 hzero :=
          Decidable.not_not.mp hheadTarget
        have htargetTransient : resources.window.shadowEventTicket 0 hzero =
            IndexTicket.transient hinput :=
          hheadTargetEq.symm.trans hheadTransient
        have hsemantic := congrArg (IndexTicket.semanticOwner (g := g))
          htargetTransient
        simp only [ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
          IndexTicket.semanticOwner_transient] at hsemantic
        exact resources.window.shadowEventOwner_ne_transientOwner
          hzero hinput hsemantic
      unchanged := by intros; rfl
    }

/-- Move an already normalized parent head to the child depth-one shadow ticket.  When the
child has no depth-zero event this is the identity, because parent shadow zero transports to
child shadow one.  When depth zero is present, the child-one ticket is absent from the fully
accounted parent shadow cursor and one ghost reticketing step performs the alignment. -/
public def rotateHeadForFreshPush
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources
      (NFParse.push hr hlhs hc hrhs rest) pre cursor)
    {head : Fin (10 * input.length)} {block : List g.flag}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (normal : TicketHeadNormalization resources head block blocks owners)
    (hinput : 0 < input.length) (hone : 1 ∈ rest.eventDepths)
    (hheadMem : head ∈ cursor.indexOwners)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = []) :
    FreshPushHeadRotation resources normal hone := by
  have _ := hinput
  let target : IndexTicket input :=
    resources.window.pushChild.shadowEventTicket 1 hone
  by_cases hzero : 0 ∈ rest.eventDepths
  · have hfocusSemantic :
        [normal.tickets.semanticCursor.focus].filterMap
          ScheduleAtom.indexOwner? = [] := by
      rw [normal.tickets.semanticCursor_focus_indexOwners, hfocus]
      rfl
    have hactiveLayout : ShadowStartLayout
        (NFParse.push hr hlhs hc hrhs rest) resources.window
        resources.ticketShadowBlocks normal.ticketShadowLedger.active := by
      rw [normal.ticket_shadow_active_eq]
      exact normal.fullShadowLayout
    have htargetSemanticFresh :
        resources.window.pushChild.shadowEventOwner 1 hone ∉
          normal.tickets.semanticCursor.indexOwners :=
      normal.ticketShadowLedger
        |>.pushChild_shadowEventOwner_one_not_mem_indexOwners_of_child_zero
          hactiveLayout hfocusSemantic hzero hone
    have htargetFresh : target ∉
        cursor.indexTickets normal.tickets.ticketOf := by
      apply normal.tickets.ticket_not_mem_of_semanticOwner_not_mem
      simpa [target] using htargetSemanticFresh
    have htargetNotScratch : ∀ h : 0 < input.length,
        target ≠ IndexTicket.scratch h := by
      intro h heq
      have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
      simp only [target,
        ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
        IndexTicket.semanticOwner_scratch] at hsemantic
      exact resources.window.pushChild.shadowEventOwner_ne_scratchOwner
        hone h hsemantic
    let rotated : IndexTicketLedger cursor :=
      normal.tickets.reticket head target hheadMem htargetFresh
        htargetNotScratch
    have hheadTicket : rotated.ticketOf head = target := by
      exact normal.tickets.reticket_ticketOf_owner head target hheadMem
        htargetFresh htargetNotScratch
    have hunchangedNormal : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
        rotated.ticketOf owner = normal.tickets.ticketOf owner := by
      intro owner howner hne
      exact normal.tickets.reticket_ticketOf_eq_of_mem_ne head target hheadMem
        htargetFresh htargetNotScratch howner hne
    have htransientFresh : ∀ h : 0 < input.length,
        IndexTicket.transient h ∉ cursor.indexTickets rotated.ticketOf := by
      intro h hmem
      rw [ScheduleCursor.indexTickets] at hmem
      rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
      by_cases heqHead : owner = head
      · subst owner
        rw [hheadTicket] at heq
        have hne : target ≠ IndexTicket.transient h := by
          intro htargetTransient
          have hsemantic := congrArg (IndexTicket.semanticOwner (g := g))
            htargetTransient
          simp only [target,
            ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
            IndexTicket.semanticOwner_transient] at hsemantic
          exact resources.window.pushChild.shadowEventOwner_ne_transientOwner
            hone h hsemantic
        exact hne heq
      · rw [hunchangedNormal owner howner heqHead] at heq
        apply normal.transient_fresh h
        rw [ScheduleCursor.indexTickets]
        exact List.mem_map.mpr ⟨owner, howner, heq⟩
    exact {
      tickets := rotated
      head_ticket := hheadTicket
      transient_fresh := htransientFresh
      unchanged_normal := hunchangedNormal
      unchanged := by
        intro owner howner hne
        exact (hunchangedNormal owner howner hne).trans
          (normal.unchanged owner howner hne)
    }
  · have hparentZero : 0 ∈
        (NFParse.push hr hlhs hc hrhs rest).eventDepths :=
      Finset.mem_image.mpr ⟨1, hone, by simp⟩
    have hpreimage : NFParse.pushEventPreimage rest.eventDepths 0 = 1 := by
      simp [NFParse.pushEventPreimage, hzero]
    have hshadowTransport := resources.window.shadowEventOwner_push hparentZero
    have htargetEq : resources.window.shadowEventTicket 0 hparentZero =
        target := by
      apply IndexTicket.semanticOwner_injective (g := g)
      simp only [target,
        ProductiveOwnerWindow.semanticOwner_shadowEventTicket]
      simpa [hpreimage] using hshadowTransport
    exact {
      tickets := normal.tickets
      head_ticket := (normal.head_shadow hparentZero).trans htargetEq
      transient_fresh := normal.transient_fresh
      unchanged_normal := by intros; rfl
      unchanged := normal.unchanged
    }

end ScheduleRunResources

end Aho
end IndexedGrammar
