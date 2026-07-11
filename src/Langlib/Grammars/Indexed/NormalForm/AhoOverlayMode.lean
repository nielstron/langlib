module

public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayLayout
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayParking
public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleResources

@[expose]
public section

/-!
# Restorable parking and copy-on-write overlay runner modes

This module states the exact runner interface needed to preserve branch-local compressed
accumulators.  It intentionally contains no constructor dispatch: the existing plain,
protected, and ephemeral proofs can be migrated one case at a time while this checked type fixes
the ownership and endpoint conventions.

The nonempty adjacent list `head :: overlayTail` is private to the active branch.  `word` begins
the sibling-shared protected suffix.  A successful run erases every private overlay token and
leaves the protected suffix in its existing `used` form.  The parking marker is deliberately
independent of the active block list: an atomic protected pop may move that owner into a frame
while its current-base parking ticket remains live.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- A restorable current-base parking marker.

The marker need not be an active block owner.  In particular, an event-free protected pop can
open the marked owner into a frame and recurse in plain mode while preserving this context.
The parked branch of `OverlayParking` itself proves that the marker is live; in the strict
branch the stored value is only a stable name that can continue through the mutual recursion. -/
public structure ParkingContext
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre cursor) : Type where
  marker : Fin (10 * input.length)
  parking : resources.tickets.OverlayParking resources.window marker

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

namespace OverlayParkingContext

/-- Every overlay parking mode supplies the non-strict resource bound. -/
public def atOrBelow
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {cursor : ScheduleCursor g input}
    {resources : ScheduleRunResources parse pre cursor}
    {overlay : List (ScheduleIndex g input)}
    {baseBlocks : List (List g.flag)}
    {baseOwners : List (Fin (10 * input.length))}
    (context : OverlayParkingContext resources overlay baseBlocks baseOwners) :
    resources.tickets.ParkingAtOrBelow resources.window := by
  cases context with
  | strict below => exact below.toAtOrBelow
  | attached restore => exact restore.parkingAtOrBelow

end OverlayParkingContext

/-- Plain execution under the non-strict current-window parking bound.  Binary children have
strictly larger productive-window bases, so this is the common interface needed before their
parking bound becomes strict again. -/
public def PlainScheduleRunAtOrBelow
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
    (_parkingAtOrBelow : resources.tickets.ParkingAtOrBelow resources.window)
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

/-- A non-strict plain runner specializes to the ordinary strict contract. -/
public theorem PlainScheduleRunAtOrBelow.toPlain
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (run : PlainScheduleRunAtOrBelow parse) : PlainScheduleRun parse := by
  intro input unused pre post input_eq alpha next tail hstable hstart hend resources
    hfree parkingBelow hactive shadowLayout ticketTransientFree transientFree scratchFree
  exact run unused pre post input_eq alpha next tail hstable hstart hend resources hfree
    parkingBelow.toAtOrBelow hactive shadowLayout ticketTransientFree transientFree
    scratchFree

/-- Plain execution which carries a restorable parking marker.  This is the mode reached when
an event-free protected pop has moved the marked block into a frame and exposed no active
protected suffix. -/
public def ParkedPlainScheduleRun
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
    (parkingContext : ParkingContext resources)
    (_free : resources.pool.free ≠ [])
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

/-- A marker-aware plain runner supplies the ordinary strict contract by seeding an arbitrary
stable marker name from the caller's strict parking bound. -/
public theorem ParkedPlainScheduleRun.toPlain
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (run : ParkedPlainScheduleRun parse) : PlainScheduleRun parse := by
  intro input unused pre post input_eq alpha next tail hstable hstart hend resources
    hfree parkingBelow hactive shadowLayout ticketTransientFree transientFree scratchFree
  have hinput : 0 < input.length := by
    have hw := parse.yield_length_pos
    have hlen := congrArg List.length input_eq
    simp only [List.length_append] at hlen
    omega
  let marker := ProductiveOwnerWindow.transientOwner (g := g) hinput
  let parkingContext : ParkingContext resources := {
    marker := marker
    parking := IndexTicketLedger.OverlayParking.ofBelow marker parkingBelow
  }
  exact run unused pre post input_eq alpha next tail hstable hstart hend resources
    parkingContext hfree hactive shadowLayout ticketTransientFree transientFree scratchFree

/-- A non-strict plain runner also handles a detached restorable marker by forgetting the
marker identity and retaining its global `ParkingAtOrBelow` bound. -/
public theorem PlainScheduleRunAtOrBelow.toParkedPlain
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (run : PlainScheduleRunAtOrBelow parse) : ParkedPlainScheduleRun parse := by
  intro input unused pre post input_eq alpha next tail hstable hstart hend resources
    parkingContext hfree hactive shadowLayout ticketTransientFree transientFree scratchFree
  exact run unused pre post input_eq alpha next tail hstable hstart hend resources hfree
    parkingContext.parking.atOrBelow hactive shadowLayout ticketTransientFree transientFree
    scratchFree

/-- Protected execution which may inherit a base block already parked at the current window.

This is the boundary mode reached after the last private overlay block is erased.  It differs
from `ProtectedScheduleRun` only in its parking premise: a detached restorable marker replaces
the ordinary strict bound.  The marker may be active, framed, or merely a stable name for an
already-strict invariant. -/
public def ParkedProtectedScheduleRun
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
      (hframes : List.Disjoint owners
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word).frameOwners)
      (hend : ScheduleInvariant (scheduleWordCursor alpha used))
      (resources : ScheduleRunResources parse pre
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word))
      (parkingContext : ParkingContext resources)
      (hfree : resources.pool.free ≠ [])
      (ownerLayout : EventOwnedLayout parse resources.window blocks owners)
      (shadowLayout : ShadowStartLayout parse resources.window blocks owners)
      (ticketOwnerLayout : resources.tickets.EventTicketLayout
        parse resources.window blocks owners)
      (ticketShadowContext : resources.TicketShadowContextExtends blocks owners)
      (ticketTransientFree : ∀ hinput : 0 < input.length,
        IndexTicket.transient hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexTickets
              resources.tickets.ticketOf)
      (hactive : resources.ownerLedger.active = owners)
      (transientFree : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexOwners)
      (scratchFree : ∀ hinput : 0 < input.length,
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

/-- A parked-protected runner supplies the ordinary protected contract by seeding its boundary
companion from the caller's strict parking bound. -/
public theorem ParkedProtectedScheduleRun.toProtected
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (run : ParkedProtectedScheduleRun parse) : ProtectedScheduleRun parse := by
  intro input visible hidden blocks owners word used hstack hne hall hboundary
    layout compatible pre post input_eq alpha hstable hstart hframes hend resources
    hfree parkingBelow ownerLayout shadowLayout ticketOwnerLayout ticketShadowContext
    ticketTransientFree hactive transientFree scratchFree
  have howners : owners ≠ [] := by
    intro hnil
    have hlen := layout.owners_length
    rw [hnil] at hlen
    simp only [List.length_nil, Nat.zero_eq] at hlen
    apply hne
    have hblocks : blocks = [] := List.length_eq_zero_iff.mp hlen.symm
    have hflags := layout.flags_eq_flatten
    simpa [hblocks] using hflags
  obtain ⟨owner, tail, rfl⟩ := List.exists_cons_of_ne_nil howners
  let parkingContext : ParkingContext resources := {
    marker := owner
    parking := IndexTicketLedger.OverlayParking.ofBelow owner parkingBelow
  }
  exact run visible hidden blocks (owner :: tail) word used hstack hne hall hboundary
    layout compatible pre post input_eq alpha hstable hstart hframes hend resources
    parkingContext hfree ownerLayout shadowLayout ticketOwnerLayout ticketShadowContext
    ticketTransientFree hactive transientFree scratchFree

/-- The two marker-aware ordinary modes used after a parked owner can move between the active
block list and the scheduler's frame stack. -/
public def ParkedOrdinaryScheduleRuns
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  ParkedPlainScheduleRun parse ∧ ParkedProtectedScheduleRun parse

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

/-- The sound mutual scheduler target.  Strict ordinary execution, marker-aware ordinary
execution, and copy-on-write overlay execution are proved together by strong recursion on
parse size. -/
public def CompleteScheduleRuns
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  OrdinaryScheduleRuns parse ∧ OverlayScheduleRun parse

/-! ## Specialization identities used by constructor proofs -/

@[simp] public theorem singletonOverlay_flags
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (head : ScheduleIndex g input) (protectedFlags : List g.flag) :
    ScheduleOverlay.flags [head] protectedFlags = head.flags ++ protectedFlags := by
  simp

@[simp] public theorem singletonOverlay_blocks
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (head : ScheduleIndex g input) :
    ScheduleOverlay.blocks [head] = [head.flags] := by
  simp

@[simp] public theorem singletonOverlay_owners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (head : ScheduleIndex g input)
    (owners : List (Fin (10 * input.length))) :
    ScheduleOverlay.owners [head] owners = head.owner :: owners := by
  simp

@[simp] public theorem singletonOverlay_word
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (head : ScheduleIndex g input) (word : List (ScheduleAtom g input)) :
    ScheduleOverlay.word [head] word = .index head :: word := by
  simp

@[simp] public theorem singletonOverlay_used
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (head : ScheduleIndex g input) (used : List (ScheduleAtom g input)) :
    ScheduleOverlay.used [head] used = .index head.markUsed :: used := by
  simp

/-- After an adjacent head pop, every computed overlay component is exactly the tail component. -/
public theorem OverlayTailData.of_cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    {baseLayout : ScheduleBlockLayout g input protectedFlags blocks owners word used}
    {head : ScheduleIndex g input} {overlayTail : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout baseLayout (head :: overlayTail)) :
    AdjacentOverlayLayout baseLayout overlayTail ∧
      ScheduleOverlay.flags (head :: overlayTail) protectedFlags =
        head.flags ++ ScheduleOverlay.flags overlayTail protectedFlags ∧
      ScheduleOverlay.blocks (head :: overlayTail) =
        head.flags :: ScheduleOverlay.blocks overlayTail ∧
      ScheduleOverlay.owners (head :: overlayTail) owners =
        head.owner :: ScheduleOverlay.owners overlayTail owners ∧
      ScheduleOverlay.word (head :: overlayTail) word =
        .index head :: ScheduleOverlay.word overlayTail word ∧
      ScheduleOverlay.used (head :: overlayTail) used =
        .index head.markUsed :: ScheduleOverlay.used overlayTail used := by
  exact ⟨layout.tail, by simp, by simp, by simp, by simp, by simp⟩

end Aho
end IndexedGrammar

end
