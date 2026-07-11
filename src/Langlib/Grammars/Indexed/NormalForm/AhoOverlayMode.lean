module

public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayLayout
public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleResources

@[expose]
public section

/-!
# Restorable parking for copy-on-write overlay execution

This module states the runner interface used to preserve branch-local compressed accumulators.
It intentionally contains no constructor dispatch.

The nonempty adjacent list `head :: overlayTail` is private to the active branch.  `word` begins
the sibling-shared protected suffix.  A successful run erases every private overlay token and
leaves the protected suffix in its existing `used` form.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Restoration data carried only while a copy-on-write overlay is active.

`restore` is the nonparking ticket displaced when the protected base head was parked.  It is
reserved either by remaining absent from the live ticket image or by being carried by a private
overlay index.  Its semantic owner is tracked at a depth inside (or exactly at the lower boundary
of) the private overlay prefix.  This is the information needed to make it a valid residual
depth-zero base ticket when the last private block is erased. -/
public structure OverlayRestoreData
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (overlay : List (ScheduleIndex g input))
    (baseBlocks : List (List g.flag))
    (baseOwners : List (Fin (10 * input.length))) : Type where
  marker : Fin (10 * input.length)
  base_head : ∃ block tailBlocks tailOwners,
    baseBlocks = block :: tailBlocks ∧ baseOwners = marker :: tailOwners
  parkingAtOrBelow : resources.tickets.ParkingAtOrBelow resources.window
  marker_live : marker ∈ cursor.indexOwners
  marker_ticket : resources.tickets.ticketOf marker = resources.window.parkingTicket
  restore : IndexTicket input
  restore_nonparking : restore.Nonparking
  restore_not_scratch : ∀ hinput : 0 < input.length,
    restore ≠ IndexTicket.scratch hinput
  restore_not_transient : ∀ hinput : 0 < input.length,
    restore ≠ IndexTicket.transient hinput
  restore_outside_primary : OutsideProductiveWindow resources.window
    (IndexTicket.semanticOwner (g := g) restore)
  available :
    restore ∉ cursor.indexTickets resources.tickets.ticketOf ∨
      ∃ idx ∈ overlay, resources.tickets.ticketOf idx.owner = restore
  depth : ℕ
  depth_le : depth ≤ (ScheduleOverlay.flags overlay []).length
  aligned :
    (∃ hd : depth ∈ parse.eventDepths,
      IndexTicket.semanticOwner (g := g) restore =
        resources.window.shadowEventOwner depth hd) ∨
      OutsideShadowWindow resources.window
        (IndexTicket.semanticOwner (g := g) restore)

/-- Parking state for an active overlay.  Strict mode needs no restoration metadata.  Attached
mode records exactly how to restore the parked protected base before leaving overlay mode. -/
public inductive OverlayParkingContext
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor)
    (overlay : List (ScheduleIndex g input))
    (baseBlocks : List (List g.flag))
    (baseOwners : List (Fin (10 * input.length))) : Type where
  | strict (below : resources.tickets.ParkingBelow resources.window) :
      OverlayParkingContext resources overlay baseBlocks baseOwners
  | attached (restore : OverlayRestoreData resources overlay baseBlocks baseOwners) :
      OverlayParkingContext resources overlay baseBlocks baseOwners

/-- Resource-aware copy-on-write overlay execution.

The structural recursion intended for this interface is:

* `livePushCompress` replaces `head` through `AdjacentOverlayLayout.replaceHead`;
* `livePushFresh` conses a new private head through `AdjacentOverlayLayout.push`;
* adjacent atomic pop erases `head` and resumes at `overlayTail` via
  `AdjacentOverlayLayout.tail`;
* a binary fork seals the whole overlay with `AdjacentOverlayLayout.toProtected`, after which
  the already-certified protected runner may share it between both children.
-/
public def OverlayScheduleRun
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  ∀ {input : List T} (head : ScheduleIndex g input)
    (overlayTail : List (ScheduleIndex g input))
    (protectedFlags hidden : List g.flag) (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length)))
    (word used : List (ScheduleAtom g input))
    (hstack : stack =
      ScheduleOverlay.flags (head :: overlayTail) protectedFlags ++ hidden)
    (baseLayout :
      ScheduleBlockLayout g input protectedFlags blocks owners word used)
    (overlayLayout : AdjacentOverlayLayout baseLayout (head :: overlayTail))
    (hall : ∀ k <
      (ScheduleOverlay.flags (head :: overlayTail) protectedFlags).length,
      parse.ConsumesAt k)
    (hboundary : ¬ parse.ConsumesAt
      (ScheduleOverlay.flags (head :: overlayTail) protectedFlags).length)
    (compatible : EventCompatible parse
      (ScheduleOverlay.blocks (head :: overlayTail) ++ blocks))
    (hused : used ≠ []),
    ∀ (pre post : List T) (input_eq : input = pre ++ w ++ post)
      (alpha : List (ScheduleAtom g input))
      (hstable : StablePrefix (alpha.map ScheduleAtom.workSym))
      (hstart : ScheduleInvariant
        (liveScheduleCursor parse (by
          exact hall 0 overlayLayout.flags_length_pos)
          pre post input_eq alpha
            (ScheduleOverlay.word (head :: overlayTail) word)))
      (_hframes : List.Disjoint
        (ScheduleOverlay.owners (head :: overlayTail) owners)
        (liveScheduleCursor parse (by
          exact hall 0 overlayLayout.flags_length_pos)
          pre post input_eq alpha
            (ScheduleOverlay.word (head :: overlayTail) word)).frameOwners)
      (hend : ScheduleInvariant (scheduleWordCursor alpha used))
      (resources : ScheduleRunResources parse pre
        (liveScheduleCursor parse (by
          exact hall 0 overlayLayout.flags_length_pos)
          pre post input_eq alpha
            (ScheduleOverlay.word (head :: overlayTail) word)))
      (parkingContext : OverlayParkingContext resources
        (head :: overlayTail) blocks owners)
      (_free : resources.pool.free ≠ [])
      (_credit : 0 < resources.charged)
      (_ownerLayout : EventOwnedLayout parse resources.window
        (ScheduleOverlay.blocks (head :: overlayTail) ++ blocks)
        (ScheduleOverlay.owners (head :: overlayTail) owners))
      (_shadowLayout : ShadowStartLayout parse resources.window
        (ScheduleOverlay.blocks (head :: overlayTail) ++ blocks)
        (ScheduleOverlay.owners (head :: overlayTail) owners))
      (_ticketOwnerLayout : resources.tickets.EventTicketLayout
        parse resources.window
        (ScheduleOverlay.blocks (head :: overlayTail) ++ blocks)
        (ScheduleOverlay.owners (head :: overlayTail) owners))
      (_ticketShadowContext : resources.TicketShadowContextExtends
        (ScheduleOverlay.blocks (head :: overlayTail) ++ blocks)
        (ScheduleOverlay.owners (head :: overlayTail) owners))
      (_ticketTransientHead : ∀ hinput : 0 < input.length,
        IndexTicket.transient hinput ∈
            (liveScheduleCursor parse (by
              exact hall 0 overlayLayout.flags_length_pos)
              pre post input_eq alpha
                (ScheduleOverlay.word (head :: overlayTail) word)).indexTickets
                  resources.tickets.ticketOf →
          resources.tickets.ticketOf head.owner = IndexTicket.transient hinput)
      (_hactive : resources.ownerLedger.active =
        ScheduleOverlay.owners (head :: overlayTail) owners)
      (_transientHead : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
            (liveScheduleCursor parse (by
              exact hall 0 overlayLayout.flags_length_pos)
              pre post input_eq alpha
                (ScheduleOverlay.word (head :: overlayTail) word)).indexOwners →
          head.owner = ProductiveOwnerWindow.transientOwner (g := g) hinput)
      (_scratchHead : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
            (liveScheduleCursor parse (by
              exact hall 0 overlayLayout.flags_length_pos)
              pre post input_eq alpha
                (ScheduleOverlay.word (head :: overlayTail) word)).indexOwners →
          head.owner = ProductiveOwnerWindow.scratchOwner (g := g) hinput),
      ScheduleReaches g input
        (scheduleStateOfCursor pre.length (by
          rw [input_eq]
          simp) _ hstart)
        (scheduleStateOfCursor (pre ++ w).length (by
          rw [input_eq]
          simp) _ hend)

/-- The sound mutual scheduler target. Ordinary and copy-on-write overlay execution are proved
together by strong recursion on parse size. -/
public def CompleteScheduleRuns
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  OrdinaryScheduleRuns parse ∧ OverlayScheduleRun parse

end Aho
end IndexedGrammar

end
