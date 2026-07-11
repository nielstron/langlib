module

public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayMode
public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleMoves

@[expose]
public section

/-!
# Push compression for copy-on-write overlays

A live push which stays inside the current compressed block replaces only the private adjacent
overlay head.  Its physical owner, ticket, and charge are unchanged, and the child continues in
overlay mode with the shared protected base untouched.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Preserve the owner pool across a push-compress cursor change with identical index owners. -/
private def IndexOwnerPool.transportStructuralOverlay
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (hindices : new.indexOwners = old.indexOwners) : IndexOwnerPool new where
  free := pool.free
  all_nodup := by simpa [hindices] using pool.all_nodup
  all_perm := by simpa [hindices] using pool.all_perm

namespace NFParse
namespace ConsumeRoute

private theorem compressedSlice_nonemptyOverlay
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {k : ℕ}
    (route : NFParse.ConsumeRoute g parse k) (offset : ℕ)
    (hoffset : offset ≤ k)
    (hinterior : ∀ d ∈ parse.eventDepths, offset < d → d ≤ k → False) :
    ∃ f flags,
      (stack.drop offset).take (k + 1 - offset) = f :: flags ∧
        (compressedFlags g f flags).Nonempty := by
  induction route generalizing offset with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      apply ih offset hoffset
      intro d hd hleft hright
      apply hinterior d
      · simp only [NFParse.eventDepths, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hd)
      · exact hleft
      · exact hright
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      apply ih offset hoffset
      intro d hd hleft hright
      apply hinterior d
      · simp only [NFParse.eventDepths, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inr hd)
      · exact hleft
      · exact hright
  | @popHere A B f stack w r hr hlhs hc hrhs rest =>
      have hoffsetZero : offset = 0 := by omega
      subst offset
      refine ⟨f, [], by simp, A, B, ?_⟩
      simpa [compressedFlags] using
        (cflagBase_apply f A B).2 (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
  | @popTail A B f stack w r hr hlhs hc hrhs rest k route ih =>
      cases offset with
      | zero =>
          have hevents : ∀ d ∈ rest.eventDepths, k < d := by
            intro d hd
            by_contra hnot
            have hdle : d ≤ k := Nat.le_of_not_gt hnot
            have hparent : d + 1 ∈
                (NFParse.pop hr hlhs hc hrhs rest).eventDepths :=
              Finset.mem_image.mpr ⟨d, hd, by omega⟩
            exact hinterior (d + 1) hparent (by omega) (by omega)
          have hnoBinary : route.NoBinary :=
            IndexedGrammar.Aho.NFParse.ConsumeRoute.noBinary_of_eventDepths_gt
              route hevents
          rcases consumeRoute_factor_noBinary route hnoBinary with
            ⟨X, Y, hneutral, path⟩
          let fullPath : PopPath g A (f :: stack.take (k + 1)) Y :=
            .cons (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
              (path.preNeutral hneutral)
          rcases fullPath.compressedFlags_nonempty with
            ⟨f', flags, hflags, hnonempty⟩
          exact ⟨f', flags, by simpa using hflags, hnonempty⟩
      | succ offset =>
          have hoffset' : offset ≤ k := by omega
          rcases ih offset hoffset' (by
            intro d hd hleft hright
            have hparent : d + 1 ∈
                (NFParse.pop hr hlhs hc hrhs rest).eventDepths :=
              Finset.mem_image.mpr ⟨d, hd, by omega⟩
            exact hinterior (d + 1) hparent (by omega) (by omega)) with
            ⟨f', flags, hflags, hnonempty⟩
          exact ⟨f', flags, by simpa using hflags, hnonempty⟩
  | @push A B f stack w r hr hlhs hc hrhs rest k route ih =>
      rcases ih (offset + 1) (by omega) (by
        intro d hd hleft hright
        have hdpos : 0 < d := by omega
        have hdpred : d.pred + 1 = d := Nat.succ_pred_eq_of_pos hdpos
        have hparent : d.pred ∈
            (NFParse.push hr hlhs hc hrhs rest).eventDepths :=
          Finset.mem_image.mpr ⟨d, hd, rfl⟩
        apply hinterior d.pred hparent
        · omega
        · omega) with ⟨f', flags, hflags, hnonempty⟩
      exact ⟨f', flags, by simpa using hflags, hnonempty⟩

end ConsumeRoute
end NFParse

namespace ShadowStartLayout

/-- Overlay-local copy of the positive-start shadow transport used by push compression. -/
private def pushExtendHeadOverlay
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout (NFParse.push hr hlhs hc hrhs rest) window
      (block :: blocks) owners)
    (hdepthOne : 1 ∉ rest.eventDepths) :
    ShadowStartLayout rest window.pushChild ((f :: block) :: blocks) owners where
  owners_length := by simpa using layout.owners_length
  block_nonempty candidate hmem := by
    rcases List.mem_cons.mp hmem with rfl | htail
    · simp
    · exact layout.block_nonempty candidate (List.mem_cons_of_mem block htail)
  owner_at i := by
    have outsidePush : ∀ candidate,
        OutsideShadowWindow window candidate →
          OutsideShadowWindow window.pushChild candidate := by
      intro candidate hout
      simpa [ProductiveOwnerWindow.pushChild] using
        OutsideShadowWindow.transport window (residual := rest) (by rfl) hout
    refine Fin.cases ?_ (fun j => ?_) i
    · let oldHead : Fin (block :: blocks).length := ⟨0, by simp⟩
      rcases layout.owner_at oldHead with hlocal | hout
      · rcases hlocal with ⟨hd, howner⟩
        have hd0 : 0 ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths := by
          simpa [oldHead] using hd
        let childDepth := NFParse.pushEventPreimage rest.eventDepths 0
        have hchild : childDepth ∈ rest.eventDepths :=
          NFParse.pushEventPreimage_mem hd0
        have hpred : childDepth.pred = 0 :=
          NFParse.pred_pushEventPreimage hd0
        have hchildNeOne : childDepth ≠ 1 := by
          intro heq
          exact hdepthOne (heq ▸ hchild)
        have hchildZero : childDepth = 0 := by
          cases hcd : childDepth with
          | zero => rfl
          | succ d =>
              cases d with
              | zero => exact False.elim (hchildNeOne (by simpa using hcd))
              | succ d => simp [hcd] at hpred
        apply Or.inl
        refine ⟨by simpa [childDepth, hchildZero] using hchild, ?_⟩
        have hshift := window.shadowEventOwner_push hd0
        simpa [oldHead, blockOwnerAt, childDepth, hchildZero] using
          howner.trans hshift
      · exact Or.inr (outsidePush _ (by simpa [oldHead, blockOwnerAt] using hout))
    · let oldIndex : Fin (block :: blocks).length := Fin.succ j
      rcases layout.owner_at oldIndex with hlocal | hout
      · rcases hlocal with ⟨hd, howner⟩
        have hdpos : 0 < blockStart (block :: blocks) oldIndex := by
          simp only [oldIndex, blockStart_cons_succ]
          have hblock := layout.block_nonempty block (by simp)
          have := List.length_pos_of_ne_nil hblock
          omega
        have hchild := window.exists_child_eventDepth_of_push_parent_pos hdpos hd
        apply Or.inl
        refine ⟨by
          simpa [oldIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchild, ?_⟩
        have hshift := window.shadowEventOwner_push_pos hdpos hchild
        simpa [oldIndex, blockOwnerAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using howner.trans hshift
      · apply Or.inr
        exact outsidePush _ (by simpa [oldIndex, blockOwnerAt] using hout)

end ShadowStartLayout


/-- Compress a pushed flag into the branch-local overlay head and recurse in overlay mode. -/
public theorem overlayScheduleRun_pushCompress
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: stack) w)
    (hdepthOne : 1 ∉ rest.eventDepths)
    (restOverlay : OverlayScheduleRun rest) :
    OverlayScheduleRun (NFParse.push hr hlhs hc hrhs rest) := by
  intro input head overlayTail protectedFlags hidden blocks owners word used hstack
    baseLayout overlayLayout hall hboundary compatible hused pre post input_eq alpha
    hstable hstart hframes hend resources parkingContext hfree hcredit ownerLayout shadowLayout
    ticketOwnerLayout ticketShadowContext ticketTransientHead hactive transientHead
    scratchHead
  let tailFlags : List g.flag :=
    ScheduleOverlay.flags overlayTail protectedFlags
  let tailBlocks : List (List g.flag) :=
    ScheduleOverlay.blocks overlayTail ++ blocks
  let tailOwners : List (Fin (10 * input.length)) :=
    ScheduleOverlay.owners overlayTail owners
  let tailWord : List (ScheduleAtom g input) :=
    ScheduleOverlay.word overlayTail word
  let tailUsed : List (ScheduleAtom g input) :=
    ScheduleOverlay.used overlayTail used
  have tailOverlayLayout : AdjacentOverlayLayout baseLayout overlayTail :=
    overlayLayout.tail
  let tailLayout : ScheduleBlockLayout g input tailFlags tailBlocks tailOwners
      tailWord tailUsed := by
    simpa [tailFlags, tailBlocks, tailOwners, tailWord, tailUsed] using
      tailOverlayLayout.toProtected
  have hstackHead : stack = head.flags ++ tailFlags ++ hidden := by
    simpa [tailFlags] using hstack
  have hhead : head.flags ≠ [] := overlayLayout.head_block_ne
  have hallHead : ∀ k < head.flags.length + tailFlags.length,
      (NFParse.push hr hlhs hc hrhs rest).ConsumesAt k := by
    intro k hk
    apply hall
    simpa [tailFlags] using hk
  have hboundaryHead : ¬ (NFParse.push hr hlhs hc hrhs rest).ConsumesAt
      (head.flags.length + tailFlags.length) := by
    simpa [tailFlags] using hboundary
  have compatibleHead : EventCompatible (NFParse.push hr hlhs hc hrhs rest)
      (head.flags :: tailBlocks) := by
    simpa [tailBlocks] using compatible
  have headLater : tailFlags ≠ [] → head.mark.later = true := by
    intro hne
    apply overlayLayout.head_later
    simpa [tailFlags] using hne
  have hstartHead : ScheduleInvariant
      (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
        (hallHead 0 (by
          have := List.length_pos_of_ne_nil hhead
          omega))
        pre post input_eq alpha (.index head :: tailWord)) := by
    simpa [tailWord] using hstart
  have hframesHead : List.Disjoint (head.owner :: tailOwners)
      (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
        (hallHead 0 (by
          have := List.length_pos_of_ne_nil hhead
          omega))
        pre post input_eq alpha (.index head :: tailWord)).frameOwners := by
    simpa [tailOwners, tailWord] using hframes
  let startResources : ScheduleRunResources (NFParse.push hr hlhs hc hrhs rest) pre
      (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
        (hallHead 0 (by
          have := List.length_pos_of_ne_nil hhead
          omega))
        pre post input_eq alpha (.index head :: tailWord)) := by
    simpa [tailWord] using resources
  let startParkingContext : OverlayParkingContext startResources
      (head :: overlayTail) blocks owners := by
    simpa [startResources, tailWord] using parkingContext
  have ownerLayoutHead : EventOwnedLayout (NFParse.push hr hlhs hc hrhs rest)
      startResources.window (head.flags :: tailBlocks) (head.owner :: tailOwners) := by
    simpa [startResources, tailBlocks, tailOwners] using ownerLayout
  have shadowLayoutHead : ShadowStartLayout (NFParse.push hr hlhs hc hrhs rest)
      startResources.window (head.flags :: tailBlocks) (head.owner :: tailOwners) := by
    simpa [startResources, tailBlocks, tailOwners] using shadowLayout
  have ticketOwnerLayoutHead : startResources.tickets.EventTicketLayout
      (NFParse.push hr hlhs hc hrhs rest) startResources.window
      (head.flags :: tailBlocks) (head.owner :: tailOwners) := by
    simpa [startResources, tailBlocks, tailOwners] using ticketOwnerLayout
  have ticketShadowContextHead : startResources.TicketShadowContextExtends
      (head.flags :: tailBlocks) (head.owner :: tailOwners) := by
    simpa [startResources, tailBlocks, tailOwners] using ticketShadowContext
  have ticketTransientHeadHead : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∈
          (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
            (hallHead 0 (by
              have := List.length_pos_of_ne_nil hhead
              omega))
            pre post input_eq alpha (.index head :: tailWord)).indexTickets
              startResources.tickets.ticketOf →
        startResources.tickets.ticketOf head.owner = IndexTicket.transient hinput := by
    simpa [startResources, tailWord] using ticketTransientHead
  have hactiveHead : startResources.ownerLedger.active = head.owner :: tailOwners := by
    simpa [startResources, tailOwners] using hactive
  let parent : NFParse g A stack w := .push hr hlhs hc hrhs rest
  obtain ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩ :=
    ticketShadowContextHead
  let parentUsed : parent.ConsumesAt 0 := hallHead 0 (by
    have := List.length_pos_of_ne_nil hhead
    omega)
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.live parentUsed)
  let newOwned : ScheduleIndex g input := {
    flags := f :: head.flags
    relation := cflagComp g (cflagBase g f) head.relation
    mark := head.mark
    denotes := .comp (.base f) head.denotes
    owner := head.owner
  }
  have hallRest : ∀ k < newOwned.flags.length + tailFlags.length,
      rest.ConsumesAt k := by
    intro k hk
    cases k with
    | zero =>
        have hp : rest.ConsumesAt 1 := by
          simpa [parent, NFParse.ConsumesAt] using parentUsed
        exact rest.consumesAt_of_consumesAt_succ 0 hp
    | succ k =>
        have hk' : k < head.flags.length + tailFlags.length := by
          simp only [newOwned, List.length_cons] at hk
          omega
        simpa [parent, NFParse.ConsumesAt] using hallHead k hk'
  have hboundaryRest :
      ¬ rest.ConsumesAt (newOwned.flags.length + tailFlags.length) := by
    simpa [parent, newOwned, NFParse.ConsumesAt, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hboundaryHead
  have compatibleRest : EventCompatible rest (newOwned.flags :: tailBlocks) := by
    simpa [newOwned] using EventCompatible.pushExtendHead hdepthOne compatibleHead
  have hcomp :
      (cflagComp g (cflagBase g f) head.relation).Nonempty := by
    have hlast : rest.ConsumesAt head.flags.length := by
      apply hallRest
      simp only [newOwned, List.length_cons]
      omega
    let route : NFParse.ConsumeRoute g rest head.flags.length :=
      NFParse.ConsumeRoute.ofConsumesAt rest head.flags.length hlast
    rcases IndexedGrammar.Aho.NFParse.ConsumeRoute.compressedSlice_nonemptyOverlay
      route 0 (Nat.zero_le _) (by
      intro d hd hdpos hdle
      have hfirst := BlockLayout.Boundary.first_length_le_of_pos
        (by simp [newOwned]) (compatibleRest.boundary d hd) hdpos
      simp only [newOwned, List.length_cons] at hfirst
      omega) with ⟨f', flags, hslice, hnonempty⟩
    have htake : (f :: stack).take (head.flags.length + 1) =
        f :: head.flags := by
      rw [hstackHead]
      simp
    have hflags : f :: head.flags = f' :: flags := by
      simpa using htake.symm.trans hslice
    have hcanonical : (compressedFlags g f head.flags).Nonempty := by
      simp only [List.cons.injEq] at hflags
      rcases hflags with ⟨rfl, rfl⟩
      exact hnonempty
    have hrelation : cflagComp g (cflagBase g f) head.relation =
        compressedFlags g f head.flags := by
      rcases head.denotes.exists_eq_compressedFlags with
        ⟨f₀, flags₀, hownedFlags, hownedRelation⟩
      rw [hownedFlags, hownedRelation]
      rfl
    rwa [hrelation]
  let childUsed : rest.ConsumesAt 0 := hallRest 0 (by
    have hnew : 0 < newOwned.flags.length := by simp [newOwned]
    omega)
  let childTask : ScheduleTask g input :=
    scheduleTaskOfParse rest pre post input_eq (.live childUsed)
  have htaskOwner : childTask.owner = parentTask.owner := by
    apply Fin.ext
    rfl
  have hindexOwner : newOwned.owner = head.owner := rfl
  have hchildInv : ScheduleInvariant
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)) := by
    apply ScheduleInvariant.livePushCompress (alpha ++ [ScheduleAtom.dollar]) tailWord
      parentTask childTask head newOwned htaskOwner hindexOwner
    simpa [liveScheduleCursor, parentTask, parent] using hstartHead
  have hindices :
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)).indexOwners =
      (liveScheduleCursor parent parentUsed pre post input_eq alpha
        (.index head :: tailWord)).indexOwners := by
    simp [liveScheduleCursor, newOwned, ScheduleCursor.indexOwners,
      ScheduleCursor.word, ScheduleAtom.indexOwner?, List.filterMap_append]
  have htasks :
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)).taskOwners =
      (liveScheduleCursor parent parentUsed pre post input_eq alpha
        (.index head :: tailWord)).taskOwners := by
    simp [liveScheduleCursor, childTask, parentTask, ScheduleCursor.taskOwners,
      ScheduleCursor.word, ScheduleAtom.taskOwner?, List.filterMap_append, htaskOwner]
  have hframesEq :
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)).frameOwners =
      (liveScheduleCursor parent parentUsed pre post input_eq alpha
        (.index head :: tailWord)).frameOwners := by
    simp [liveScheduleCursor, newOwned, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append]
  let childPrefixLedger : PrefixFrameLedger
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)) :=
    startResources.ownerLedger.prefixLedger.transport (by rfl) (by rw [hframesEq])
  let childOwnerLedger : ScheduleOwnerLedger rest startResources.window.pushChild
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)) := {
    active := startResources.ownerLedger.active
    outside := startResources.ownerLedger.outside
    right_eq := by
      simpa [liveScheduleCursor, newOwned, ScheduleAtom.indexOwner?] using
        startResources.ownerLedger.right_eq
    outside_at := fun candidate hcandidate =>
      EventOwnedLayout.outside_pushChild startResources.window
        (startResources.ownerLedger.outside_at candidate hcandidate)
    frames := by
      rw [hframesEq]
      exact startResources.ownerLedger.frames.pushCompress hdepthOne
    prefixLedger := childPrefixLedger
  }
  let childTickets : IndexTicketLedger
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)) :=
    startResources.tickets.transport (by rw [hindices])
  have hticketFramesEq : childTickets.semanticCursor.frameOwners =
      startResources.tickets.semanticCursor.frameOwners := by
    rw [IndexTicketLedger.semanticCursor_frameOwners,
      IndexTicketLedger.semanticCursor_frameOwners, hframesEq]
    rfl
  let childTicketPrefix : PrefixFrameLedger childTickets.semanticCursor :=
    startResources.ticketOwnerLedger.prefixLedger.transport (by
      rfl)
      (by rw [hticketFramesEq])
  let childTicketOwnerLedger : childTickets.SemanticScheduleOwnerLedger
      rest startResources.window.pushChild := {
    active := startResources.ticketOwnerLedger.active
    outside := startResources.ticketOwnerLedger.outside
    right_eq := by
      simpa [childTickets, IndexTicketLedger.semanticCursor,
        IndexTicketLedger.semanticOwnerOf, liveScheduleCursor, newOwned,
        ScheduleCursor.relabelTicketOwners, ScheduleAtom.relabelTicketOwner,
        ScheduleAtom.indexOwner?] using startResources.ticketOwnerLedger.right_eq
    outside_at := fun candidate hcandidate =>
      EventOwnedLayout.outside_pushChild startResources.window
        (startResources.ticketOwnerLedger.outside_at candidate hcandidate)
    frames := by
      rw [hticketFramesEq]
      exact startResources.ticketOwnerLedger.frames.pushCompress hdepthOne
    prefixLedger := childTicketPrefix
  }
  let childTicketShadowLedger : childTickets.SemanticShadowOwnerLedger
      rest startResources.window.pushChild := {
    active := startResources.ticketShadowLedger.active
    outside := startResources.ticketShadowLedger.outside
    right_eq := by
      simpa [childTickets, IndexTicketLedger.semanticCursor,
        IndexTicketLedger.semanticOwnerOf, liveScheduleCursor, newOwned,
        ScheduleCursor.relabelTicketOwners, ScheduleAtom.relabelTicketOwner,
        ScheduleAtom.indexOwner?] using startResources.ticketShadowLedger.right_eq
    outside_at := fun candidate hcandidate => by
      simpa [ProductiveOwnerWindow.pushChild] using
        OutsideShadowWindow.transport startResources.window (residual := rest) (by rfl)
          (startResources.ticketShadowLedger.outside_at candidate hcandidate)
    frames := by
      rw [hticketFramesEq]
      simpa [ProductiveOwnerWindow.pushChild] using
        startResources.ticketShadowLedger.frames.transportEqual (residual := rest) (by rfl)
    prefixLedger := childTicketPrefix
  }
  let childTicketShadowLayout : childTickets.ShadowTicketLayout rest
      startResources.window.pushChild
      ((f :: head.flags) :: (tailBlocks ++ parkedBlocks))
      (head.owner :: (tailOwners ++ parkedOwners)) := by
    have parentFull : startResources.tickets.ShadowTicketLayout parent startResources.window
        (head.flags :: (tailBlocks ++ parkedBlocks))
        (head.owner :: (tailOwners ++ parkedOwners)) := by
      simpa [parent, hcontextBlocks, hcontextOwners, List.cons_append] using
        startResources.ticketShadowLayout
    simpa [childTickets, IndexTicketLedger.transport] using
      parentFull.pushExtendHeadOverlay hdepthOne
  let childPool : IndexOwnerPool
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)) :=
    startResources.pool.transportStructuralOverlay hindices
  let childResources : ScheduleRunResources rest pre
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)) := {
    pool := childPool
    tickets := childTickets
    window := startResources.window.pushChild
    parkingAtOrBelow := startResources.parkingAtOrBelow.transport_mono
      (by rw [hindices]) (by rfl)
    ownerLedger := childOwnerLedger
    ticketOwnerLedger := childTicketOwnerLedger
    ticket_active_eq := by
      simpa [childTicketOwnerLedger, childTickets, childOwnerLedger,
        IndexTicketLedger.semanticOwners] using startResources.ticket_active_eq
    ticketShadowBlocks := (f :: head.flags) :: (tailBlocks ++ parkedBlocks)
    ticketShadowOwners := head.owner :: (tailOwners ++ parkedOwners)
    ticketShadowOwners_subset := by
      intro owner hmem
      have hold : owner ∈ startResources.ticketShadowOwners := by
        simpa [hcontextOwners, List.cons_append] using hmem
      have hold' := startResources.ticketShadowOwners_subset hold
      rw [hindices]
      exact hold'
    ticketShadowOwners_nodup := by
      simpa [hcontextOwners, List.cons_append] using
        startResources.ticketShadowOwners_nodup
    ticketShadowLedger := childTicketShadowLedger
    ticket_shadow_active_eq := by
      simpa [childTicketShadowLedger, childTickets, hcontextOwners,
        IndexTicketLedger.transport, IndexTicketLedger.semanticOwners,
        List.cons_append] using startResources.ticket_shadow_active_eq
    ticketShadowLayout := childTicketShadowLayout
    shadowLedger := ShadowOwnerLedger.ofGeneric childPool childOwnerLedger
    shadow_active_eq := rfl
    charged := startResources.charged
    charged_eq_indices := by simpa [hindices] using startResources.charged_eq_indices
    charged_le_indices := by
      rw [hindices]
      exact startResources.charged_le_indices
    productive_le_credit := by
      have hp := startResources.productive_le_credit
      simpa [parent, NFParse.productiveCount, NFParse.binaryCount,
        NFParse.terminalCount, childPool] using hp
    task_locality := by
      intro owner howner
      apply startResources.task_locality owner
      rw [← htasks]
      exact howner
  }
  have hchildCredit : 0 < childResources.charged := by
    simpa [childResources] using hcredit
  have hframesRest : List.Disjoint (newOwned.owner :: tailOwners)
      (liveScheduleCursor rest childUsed pre post input_eq alpha
        (.index newOwned :: tailWord)).frameOwners := by
    simpa [newOwned, liveScheduleCursor, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append] using hframesHead
  have hstackRest : f :: stack = newOwned.flags ++ tailFlags ++ hidden := by
    simp [newOwned, hstackHead, List.append_assoc]
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos _ hstartHead
  let childState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos _ hchildInv
  have hpush : ScheduleReaches g input startState childState := by
    apply ScheduleReaches.single
    have hstep := composite_livePushCompress_at input head.relation head.mark
      (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
      hcomp
      pre.length (alpha.map ScheduleAtom.workSym) (tailWord.map ScheduleAtom.workSym)
    simpa [startState, childState, scheduleStateOfCursor, ScheduleState.config,
      liveScheduleCursor, parentTask, childTask, parent, newOwned,
      scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
      ScheduleTask.workSym, List.map_append] using hstep
  let childShadowLayout : ShadowStartLayout rest childResources.window
      (newOwned.flags :: tailBlocks) (newOwned.owner :: tailOwners) :=
    childResources.genericShadowStartLayout
      (by simpa [childResources, childOwnerLedger, newOwned] using hactiveHead)
      (by simpa [newOwned] using ownerLayoutHead.owners_length)
      (by
        intro block hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · simp [newOwned]
        · exact shadowLayoutHead.block_nonempty block
            (List.mem_cons_of_mem head.flags htail))
  let childTicketOwnerLayout : childResources.tickets.EventTicketLayout rest
      childResources.window (newOwned.flags :: tailBlocks) (newOwned.owner :: tailOwners) := by
    change EventOwnedLayout rest startResources.window.pushChild
      (newOwned.flags :: tailBlocks)
        (childTickets.semanticOwners (newOwned.owner :: tailOwners))
    simpa [childResources, childTickets, newOwned,
      IndexTicketLedger.semanticOwners] using
        ticketOwnerLayoutHead.pushCompress hdepthOne
  have childTicketTransientHead : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∈
          (liveScheduleCursor rest childUsed pre post input_eq alpha
            (.index newOwned :: tailWord)).indexTickets childResources.tickets.ticketOf →
        childResources.tickets.ticketOf newOwned.owner = IndexTicket.transient hinput := by
    intro hinput hmem
    have hold : IndexTicket.transient hinput ∈
        (liveScheduleCursor parent parentUsed pre post input_eq alpha
          (.index head :: tailWord)).indexTickets startResources.tickets.ticketOf := by
      simpa [childResources, childTickets, IndexTicketLedger.transport,
        ScheduleCursor.indexTickets, hindices] using hmem
    simpa [childResources, childTickets, newOwned] using
      ticketTransientHeadHead hinput hold
  have childTicketShadowContext : childResources.TicketShadowContextExtends
      (newOwned.flags :: tailBlocks) (newOwned.owner :: tailOwners) := by
    refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
    · simp [childResources, newOwned]
    · simp [childResources, newOwned]

  have childOverlayLayout : AdjacentOverlayLayout baseLayout
      (newOwned :: overlayTail) := by
    apply overlayLayout.replaceHead
    · simp [newOwned]
    · rfl
    · rfl
  have hallRestOverlay : ∀ k <
      (ScheduleOverlay.flags (newOwned :: overlayTail) protectedFlags).length,
      rest.ConsumesAt k := by
    simpa [newOwned, tailFlags, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hallRest
  have hboundaryRestOverlay : ¬ rest.ConsumesAt
      (ScheduleOverlay.flags (newOwned :: overlayTail) protectedFlags).length := by
    simpa [newOwned, tailFlags, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hboundaryRest
  have hstackRestOverlay : f :: stack =
      ScheduleOverlay.flags (newOwned :: overlayTail) protectedFlags ++ hidden := by
    simpa [newOwned, tailFlags] using hstackRest
  have hframesRestOverlay : List.Disjoint
      (ScheduleOverlay.owners (newOwned :: overlayTail) owners)
      (liveScheduleCursor rest
        (hallRestOverlay 0 childOverlayLayout.flags_length_pos)
        pre post input_eq alpha
          (ScheduleOverlay.word (newOwned :: overlayTail) word)).frameOwners := by
    simpa [newOwned, tailOwners, tailWord] using hframesRest
  have hchildFree : childResources.pool.free ≠ [] := by
    simpa [childResources, childPool, IndexOwnerPool.transportStructuralOverlay] using hfree
  let childParkingContext : OverlayParkingContext childResources
      (newOwned :: overlayTail) blocks owners := by
    cases startParkingContext with
    | strict below =>
        exact .strict (by
          simpa [childResources, childTickets] using
            below.transport_mono (by rw [hindices]) (by rfl))
    | attached restore =>
        have houtsidePrimary : OutsideProductiveWindow childResources.window
            (IndexTicket.semanticOwner (g := g) restore.restore) := by
          simpa [childResources] using
            EventOwnedLayout.outside_pushChild startResources.window
              restore.restore_outside_primary
        have havailable :
            restore.restore ∉
                (liveScheduleCursor rest childUsed pre post input_eq alpha
                  (.index newOwned :: tailWord)).indexTickets
                    childResources.tickets.ticketOf ∨
              ∃ idx ∈ newOwned :: overlayTail,
                childResources.tickets.ticketOf idx.owner = restore.restore := by
          rcases restore.available with hfresh | ⟨idx, hidx, hticket⟩
          · exact Or.inl (by
              simpa [childResources, childTickets, IndexTicketLedger.transport,
                ScheduleCursor.indexTickets, hindices] using hfresh)
          · rcases List.mem_cons.mp hidx with rfl | htail
            · exact Or.inr ⟨newOwned, by simp, by
                simpa [childResources, childTickets, newOwned] using hticket⟩
            · exact Or.inr ⟨idx, by simp [htail], by
                simpa [childResources, childTickets] using hticket⟩
        let childDepth := NFParse.pushEventPreimage rest.eventDepths restore.depth
        have hdepthStep : childDepth ≤ restore.depth + 1 := by
          simp [childDepth, NFParse.pushEventPreimage]
          split <;> omega
        have hlengthStep :
            (ScheduleOverlay.flags (newOwned :: overlayTail) []).length =
              (ScheduleOverlay.flags (head :: overlayTail) []).length + 1 := by
          simp [newOwned, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        exact .attached {
          marker := restore.marker
          base_head := restore.base_head
          parkingAtOrBelow := by
            simpa [childResources, childTickets] using
              restore.parkingAtOrBelow.transport_mono
                (by rw [hindices]) (by rfl)
          marker_live := by
            rw [hindices]
            exact restore.marker_live
          marker_ticket := by
            simpa [childResources, childTickets] using restore.marker_ticket
          restore := restore.restore
          restore_nonparking := restore.restore_nonparking
          restore_not_scratch := restore.restore_not_scratch
          restore_not_transient := restore.restore_not_transient
          restore_outside_primary := houtsidePrimary
          available := havailable
          depth := childDepth
          depth_le := by
            calc
              childDepth ≤ restore.depth + 1 := hdepthStep
              _ ≤ (ScheduleOverlay.flags (head :: overlayTail) []).length + 1 :=
                Nat.add_le_add_right restore.depth_le 1
              _ = (ScheduleOverlay.flags (newOwned :: overlayTail) []).length :=
                hlengthStep.symm
          aligned := by
            rcases restore.aligned with ⟨hd, halign⟩ | houtside
            · have hparentDepth : restore.depth ∈ parent.eventDepths := by
                simpa [parent] using hd
              have hchildDepth : childDepth ∈ rest.eventDepths :=
                NFParse.pushEventPreimage_mem hparentDepth
              exact Or.inl ⟨hchildDepth, by
                have hshift := startResources.window.shadowEventOwner_push hparentDepth
                simpa [childDepth, childResources] using halign.trans hshift⟩
            · exact Or.inr (by
                simpa [childResources, ProductiveOwnerWindow.pushChild] using
                  OutsideShadowWindow.transport startResources.window
                    (residual := rest) (by rfl) houtside)
        }
  have hrestRun := restOverlay newOwned overlayTail protectedFlags hidden blocks owners
    word used hstackRestOverlay baseLayout childOverlayLayout hallRestOverlay
    hboundaryRestOverlay (by
      simpa [newOwned, tailBlocks] using compatibleRest) hused pre post input_eq alpha
    hstable (by
      simpa [newOwned, tailWord] using hchildInv) hframesRestOverlay hend
    (by simpa [newOwned, tailWord] using childResources)
    (by simpa [newOwned, tailWord] using childParkingContext) hchildFree hchildCredit
    (by simpa [newOwned, tailBlocks, tailOwners] using
      ownerLayoutHead.pushCompress hdepthOne)
    (by simpa [newOwned, tailBlocks, tailOwners] using childShadowLayout)
    (by simpa [newOwned, tailBlocks, tailOwners] using childTicketOwnerLayout)
    (by simpa [newOwned, tailBlocks, tailOwners] using childTicketShadowContext)
    (by simpa [newOwned, tailWord] using childTicketTransientHead)
    (by simpa [childResources, childOwnerLedger, newOwned, tailOwners] using hactiveHead)
    (by
      intro hinput hmem
      exact False.elim
        (childResources.pool.transientOwner_not_mem_indices hinput hmem))
    (by
      intro hinput hmem
      exact False.elim
        (childResources.pool.scratchOwner_not_mem_indices hinput hmem))
  simpa [startState, childState, parent, parentTask, liveScheduleCursor,
    scheduleStateOfCursor, tailWord] using hpush.trans hrestRun

end Aho
end IndexedGrammar

end
