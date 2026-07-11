module

public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayMode
public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleMoves
public import Langlib.Grammars.Indexed.NormalForm.AhoTicketSeal

@[expose]
public section

/-!
# Fresh pushes for copy-on-write overlays

A productive unary push allocates a singleton private block above the existing
adjacent overlay.  The protected base remains shared, and its exact parking
witness is transported through head normalization, head rotation, and fresh
owner allocation.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Start a fresh private singleton above a nonempty adjacent overlay. -/
public theorem overlayScheduleRun_pushFresh
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: stack) w)
    (hone : 1 ∈ rest.eventDepths)
    (restOverlay : OverlayScheduleRun rest) :
    OverlayScheduleRun (NFParse.push hr hlhs hc hrhs rest) := by
  intro input owned overlayTail baseFlags hidden baseBlocks baseOwners baseWord
    baseUsed hstackOverlay baseLayout overlayLayout hallOverlay hboundaryOverlay
    compatibleOverlay hbaseUsed pre post input_eq alpha hstable hstartOverlay
    hframesOverlay hend rawResources rawParkingContext hfree hcredit
    ownerLayoutOverlay shadowLayoutOverlay ticketOwnerLayoutOverlay
    ticketShadowContextOverlay ticketTransientHeadOverlay hactiveOverlay
    _transientHead _scratchHead
  let protectedFlags : List g.flag :=
    ScheduleOverlay.flags overlayTail baseFlags
  let blocks : List (List g.flag) :=
    ScheduleOverlay.blocks overlayTail ++ baseBlocks
  let owners : List (Fin (10 * input.length)) :=
    ScheduleOverlay.owners overlayTail baseOwners
  let word : List (ScheduleAtom g input) :=
    ScheduleOverlay.word overlayTail baseWord
  let used : List (ScheduleAtom g input) :=
    ScheduleOverlay.used overlayTail baseUsed
  have tailOverlayLayout : AdjacentOverlayLayout baseLayout overlayTail :=
    overlayLayout.tail
  let layout : ScheduleBlockLayout g input protectedFlags blocks owners word used := by
    simpa [protectedFlags, blocks, owners, word, used] using
      tailOverlayLayout.toProtected
  have hstack : stack = owned.flags ++ protectedFlags ++ hidden := by
    simpa [protectedFlags] using hstackOverlay
  have howned : owned.flags ≠ [] := overlayLayout.head_block_ne
  have hall : ∀ k < owned.flags.length + protectedFlags.length,
      (NFParse.push hr hlhs hc hrhs rest).ConsumesAt k := by
    intro k hk
    apply hallOverlay
    simpa [protectedFlags] using hk
  have hboundary :
      ¬ (NFParse.push hr hlhs hc hrhs rest).ConsumesAt
        (owned.flags.length + protectedFlags.length) := by
    simpa [protectedFlags] using hboundaryOverlay
  have compatible : EventCompatible (NFParse.push hr hlhs hc hrhs rest)
      (owned.flags :: blocks) := by
    simpa [blocks] using compatibleOverlay
  have hlater : protectedFlags ≠ [] → owned.mark.later = true := by
    intro hne
    apply overlayLayout.head_later
    simpa [protectedFlags] using hne
  have hused : used ≠ [] := by
    dsimp [used, ScheduleOverlay.used]
    exact List.append_ne_nil_of_right_ne_nil _ hbaseUsed
  have hstart : ScheduleInvariant
      (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
        (hall 0 (by
          have := List.length_pos_of_ne_nil howned
          omega))
        pre post input_eq alpha (.index owned :: word)) := by
    simpa [word] using hstartOverlay
  have hframes : List.Disjoint (owned.owner :: owners)
      (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
        (hall 0 (by
          have := List.length_pos_of_ne_nil howned
          omega))
        pre post input_eq alpha (.index owned :: word)).frameOwners := by
    simpa [owners, word] using hframesOverlay
  let resources : ScheduleRunResources
      (NFParse.push hr hlhs hc hrhs rest) pre
      (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
        (hall 0 (by
          have := List.length_pos_of_ne_nil howned
          omega))
        pre post input_eq alpha (.index owned :: word)) := by
    simpa [word] using rawResources
  let startParkingContext : OverlayParkingContext resources
      (owned :: overlayTail) baseBlocks baseOwners := by
    simpa [resources, word] using rawParkingContext
  have ownerLayout : EventOwnedLayout (NFParse.push hr hlhs hc hrhs rest)
      resources.window (owned.flags :: blocks) (owned.owner :: owners) := by
    simpa [resources, blocks, owners] using ownerLayoutOverlay
  have shadowLayout : ShadowStartLayout (NFParse.push hr hlhs hc hrhs rest)
      resources.window (owned.flags :: blocks) (owned.owner :: owners) := by
    simpa [resources, blocks, owners] using shadowLayoutOverlay
  have ticketOwnerLayout : resources.tickets.EventTicketLayout
      (NFParse.push hr hlhs hc hrhs rest) resources.window
      (owned.flags :: blocks) (owned.owner :: owners) := by
    simpa [resources, blocks, owners] using ticketOwnerLayoutOverlay
  have ticketShadowContext : resources.TicketShadowContextExtends
      (owned.flags :: blocks) (owned.owner :: owners) := by
    simpa [resources, blocks, owners] using ticketShadowContextOverlay
  have ticketTransientHead : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∈
          (liveScheduleCursor (NFParse.push hr hlhs hc hrhs rest)
            (hall 0 (by
              have := List.length_pos_of_ne_nil howned
              omega))
            pre post input_eq alpha (.index owned :: word)).indexTickets
              resources.tickets.ticketOf →
        resources.tickets.ticketOf owned.owner = IndexTicket.transient hinput := by
    simpa [resources, word] using ticketTransientHeadOverlay
  have hactive : resources.ownerLedger.active = owned.owner :: owners := by
    simpa [resources, owners] using hactiveOverlay
  let parent : NFParse g A stack w := .push hr hlhs hc hrhs rest
  let parentUsed : parent.ConsumesAt 0 := hall 0 (by
    have := List.length_pos_of_ne_nil howned
    omega)
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.live parentUsed)
  let startCursor : ScheduleCursor g input :=
    liveScheduleCursor parent parentUsed pre post input_eq alpha (.index owned :: word)
  have hstart' : ScheduleInvariant startCursor := by
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using hstart
  let startLedger : ScheduleOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      resources.ownerLedger
  have startActive : startLedger.active = owned.owner :: owners := by
    simpa [startLedger, startCursor, parent, parentTask, liveScheduleCursor] using hactive
  have hinputPos : 0 < input.length := by
    have hw := rest.yield_length_pos
    have hlen := congrArg List.length input_eq
    simp only [List.length_append] at hlen
    omega
  have hparentZero : 0 ∈ parent.eventDepths := by
    simpa [parent, NFParse.eventDepths] using
      (Finset.mem_image.mpr ⟨1, hone, by simp⟩)
  have hrightSublist :
      (startCursor.right.filterMap ScheduleAtom.indexOwner?).Sublist
        startCursor.indexOwners := by
    change (startCursor.right.filterMap ScheduleAtom.indexOwner?).Sublist
      (startCursor.word.filterMap ScheduleAtom.indexOwner?)
    apply List.Sublist.filterMap
    rw [ScheduleCursor.word]
    exact ((List.Sublist.refl startCursor.right).cons startCursor.focus).trans
      (List.sublist_append_right startCursor.left
        (startCursor.focus :: startCursor.right))
  have hrightNodup :
      (startCursor.right.filterMap ScheduleAtom.indexOwner?).Nodup :=
    hstart'.indexOwners_nodup.sublist hrightSublist
  have hownersNodup : (owned.owner :: owners).Nodup := by
    rw [startLedger.right_eq, startActive] at hrightNodup
    exact (List.nodup_append.mp hrightNodup).1
  have hheadMem : owned.owner ∈ startCursor.indexOwners := by
    apply resources.active_subset_indexOwners
    rw [hactive]
    simp
  have hfocusNoIndex :
      [startCursor.focus].filterMap ScheduleAtom.indexOwner? = [] := by
    simp [startCursor, liveScheduleCursor, ScheduleAtom.indexOwner?]
  have hheadFrameFresh : owned.owner ∉ startCursor.frameOwners := by
    have hframes' : List.Disjoint (owned.owner :: owners)
        startCursor.frameOwners := by
      simpa [startCursor, parent, parentTask, liveScheduleCursor] using hframes
    intro hmem
    exact (List.disjoint_left.mp hframes') (by simp) hmem
  let normal := resources.normalizeTransientHead hinputPos hactive hownersNodup
    ticketShadowContext ticketOwnerLayout hparentZero
    (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using hheadMem)
    (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      hfocusNoIndex)
    (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      hheadFrameFresh)
    (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      hstart'.frameOwners_subset_indexOwners)
    (ticketTransientHead hinputPos)
  let rotation := resources.rotateHeadForFreshPush normal hinputPos hone
    (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using hheadMem)
    (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      hfocusNoIndex)
  obtain ⟨newOwner, hnewFree, hnewGeneric⟩ :=
    resources.pool.exists_free_generic hfree
  have hnewFresh : newOwner ∉ startCursor.indexOwners := by
    intro hmem
    exact resources.pool.free_disjoint
      (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using hmem)
      hnewFree
  have hheadOwner :
      ((∃ h₁ : 1 ∈ rest.eventDepths,
          newOwner = resources.window.pushChild.eventOwner 1 h₁) ∨
        OutsideProductiveWindow resources.window.pushChild newOwner) :=
    Or.inr (resources.window.pushChild.genericOwner_outside hnewGeneric)
  let childProtected : List g.flag := owned.flags ++ protectedFlags
  let freshOwned : ScheduleIndex g input := {
    flags := [f]
    relation := cflagBase g f
    mark := .laterPending
    denotes := .base f
    owner := newOwner
  }
  have hallRest : ∀ k < freshOwned.flags.length + childProtected.length,
      rest.ConsumesAt k := by
    intro k hk
    cases k with
    | zero =>
        have hp : rest.ConsumesAt 1 := by
          simpa [parent, NFParse.ConsumesAt] using parentUsed
        exact rest.consumesAt_of_consumesAt_succ 0 hp
    | succ k =>
        have hk' : k < owned.flags.length + protectedFlags.length := by
          simp only [freshOwned, childProtected, List.length_singleton,
            List.length_append] at hk
          omega
        simpa [parent, NFParse.ConsumesAt] using hall k hk'
  have hboundaryRest :
      ¬ rest.ConsumesAt (freshOwned.flags.length + childProtected.length) := by
    simpa [parent, freshOwned, childProtected, NFParse.ConsumesAt,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hboundary
  let childUsed : rest.ConsumesAt 0 := hallRest 0 (by
    have : 0 < freshOwned.flags.length := by simp [freshOwned]
    omega)
  let childTask : ScheduleTask g input :=
    scheduleTaskOfParse rest pre post input_eq (.live childUsed)
  have htaskOwner : childTask.owner = parentTask.owner := by
    apply Fin.ext
    rfl
  let childCursor : ScheduleCursor g input :=
    liveScheduleCursor rest childUsed pre post input_eq alpha
      (.index freshOwned :: .index owned :: word)
  have hchildInv : ScheduleInvariant childCursor := by
    dsimp [childCursor, startCursor]
    exact ScheduleInvariant.plainPushUse (alpha ++ [ScheduleAtom.dollar])
      (.index owned :: word) parentTask childTask freshOwned htaskOwner hnewFresh
      (resources.pool.index_count_lt_of_free_ne_nil hfree) hstart'
  have hindexPerm : childCursor.indexOwners.Perm
      (newOwner :: startCursor.indexOwners) := by
    simp only [childCursor, startCursor, liveScheduleCursor, freshOwned,
      ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.indexOwner?)
        (l₂ := owned.owner :: word.filterMap ScheduleAtom.indexOwner?)
        (a := newOwner))
  have hticketTransientNotScratch : ∀ h : 0 < input.length,
      IndexTicket.transient hinputPos ≠ IndexTicket.scratch h := by
    intro h heq
    have hval := congrArg Fin.val heq
    simp only [IndexTicket.transient_val, IndexTicket.scratch_val] at hval
    omega
  let childTickets : IndexTicketLedger childCursor :=
    rotation.tickets.allocate newOwner (IndexTicket.transient hinputPos)
      (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using hnewFresh)
      (rotation.transient_fresh hinputPos) hticketTransientNotScratch hindexPerm
  have childTicketNew : childTickets.ticketOf newOwner =
      IndexTicket.transient hinputPos := by
    simp [childTickets]
  have childTicketOld {candidate : Fin (10 * input.length)}
      (hcandidate : candidate ∈ startCursor.indexOwners) :
      childTickets.ticketOf candidate = rotation.tickets.ticketOf candidate := by
    simpa [childTickets, IndexTicketLedger.allocate] using
      rotation.tickets.insertTicket_eq_of_mem newOwner
        (IndexTicket.transient hinputPos) hcandidate hnewFresh
  have htasks : childCursor.taskOwners = startCursor.taskOwners := by
    simp only [childCursor, startCursor, liveScheduleCursor,
      ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?,
      List.filterMap_cons, List.filterMap_nil]
    rw [htaskOwner]
  have hframesEq : childCursor.frameOwners = startCursor.frameOwners := by
    simp [childCursor, startCursor, liveScheduleCursor,
      ScheduleCursor.frameOwners, ScheduleCursor.word,
      ScheduleAtom.closeOwner?, List.filterMap_append]
  let childPrefixLedger : PrefixFrameLedger childCursor :=
    startLedger.prefixLedger.transport (by rfl) (by rw [hframesEq])
  let childOwnerLedger : ScheduleOwnerLedger rest resources.window.pushChild
      childCursor := {
    active := newOwner :: owned.owner :: owners
    outside := startLedger.outside
    right_eq := by
      have hright := startLedger.right_eq
      rw [startActive] at hright
      simpa [childCursor, startCursor, freshOwned, liveScheduleCursor,
        ScheduleAtom.indexOwner?] using congrArg (List.cons newOwner) hright
    outside_at := fun candidate hcandidate =>
      EventOwnedLayout.outside_pushChild resources.window
        (startLedger.outside_at candidate hcandidate)
    frames := by
      rw [hframesEq]
      exact startLedger.frames.push
    prefixLedger := childPrefixLedger
  }
  have hrightPhysical : startCursor.right.filterMap ScheduleAtom.indexOwner? =
      (owned.owner :: owners) ++ startLedger.outside := by
    rw [startLedger.right_eq, startActive]
  have hrightPhysicalNodup :
      ((owned.owner :: owners) ++ startLedger.outside).Nodup := by
    rw [← hrightPhysical]
    exact hrightNodup
  have hheadOutsideFresh : owned.owner ∉ startLedger.outside := by
    have hdisjoint := (List.nodup_append.mp hrightPhysicalNodup).2.2
    intro hmem
    exact hdisjoint owned.owner (by simp) owned.owner hmem rfl
  have childTicketOriginal {candidate : Fin (10 * input.length)}
      (hcandidate : candidate ∈ startCursor.indexOwners)
      (hne : candidate ≠ owned.owner) :
      childTickets.ticketOf candidate = resources.tickets.ticketOf candidate :=
    (childTicketOld hcandidate).trans
      (rotation.unchanged candidate (by
        simpa [startCursor, parent, parentTask, liveScheduleCursor] using
          hcandidate) hne)
  have childTicketFramesEq : childTickets.semanticCursor.frameOwners =
      resources.tickets.semanticCursor.frameOwners := by
    rw [childTickets.semanticCursor_frameOwners,
      resources.tickets.semanticCursor_frameOwners, hframesEq]
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [childTicketOriginal
      (hstart'.frameOwners_subset_indexOwners hcandidate) (by
        intro heq
        subst candidate
        exact hheadFrameFresh hcandidate)]
  let childTicketPrefixLedger : PrefixFrameLedger childTickets.semanticCursor := {
    owners_perm := by
      rw [childTickets.semanticCursor_frameOwners]
      change
        ((childCursor.left.map
          (ScheduleAtom.relabelTicketOwner childTickets.semanticOwnerOf)).filterMap
            ScheduleAtom.indexOwner?).Perm
          (childCursor.frameOwners.map childTickets.semanticOwnerOf)
      rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
      exact childPrefixLedger.owners_perm.map childTickets.semanticOwnerOf
  }
  have htargetOutsidePrimary : OutsideProductiveWindow resources.window
      (resources.window.pushChild.shadowEventOwner 1 hone) := by
    right
    have hend := resources.window.end_le
    have hlocal := rest.eventOwnerNat_lt_productiveCount hone
    simp only [ProductiveOwnerWindow.shadowEventOwner_val,
      ProductiveOwnerWindow.pushChild_base, shadowOwnerOffset]
    omega
  have hrotationSelected : rotation.tickets.semanticOwners
      (owned.owner :: owners) =
        resources.window.pushChild.shadowEventOwner 1 hone ::
          normal.tickets.semanticOwners owners := by
    simp only [IndexTicketLedger.semanticOwners, List.map_cons]
    change IndexTicket.semanticOwner (g := g)
        (rotation.tickets.ticketOf owned.owner) ::
          List.map rotation.tickets.semanticOwnerOf owners = _
    rw [rotation.head_ticket]
    simp only [ProductiveOwnerWindow.semanticOwner_shadowEventTicket]
    congr 1
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    apply rotation.unchanged_normal candidate
    · apply resources.active_subset_indexOwners
      rw [hactive]
      exact List.mem_cons_of_mem owned.owner hcandidate
    · intro heq
      subst candidate
      exact (List.nodup_cons.mp hownersNodup).1 hcandidate
  let rotatedParentEventLayout : rotation.tickets.EventTicketLayout parent
      resources.window (owned.flags :: blocks) (owned.owner :: owners) := by
    change EventOwnedLayout parent resources.window (owned.flags :: blocks)
      (rotation.tickets.semanticOwners (owned.owner :: owners))
    rw [hrotationSelected]
    exact normal.eventLayout.reownerHeadOutside htargetOutsidePrimary
  have childSelectedTail : childTickets.semanticOwners
      (owned.owner :: owners) =
        rotation.tickets.semanticOwners (owned.owner :: owners) := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    apply childTicketOld
    apply resources.active_subset_indexOwners
    rw [hactive]
    exact hcandidate
  have childNewSemantic : childTickets.semanticOwnerOf newOwner =
      ProductiveOwnerWindow.transientOwner (g := g) hinputPos := by
    simp [IndexTicketLedger.semanticOwnerOf, childTicketNew]
  let childTicketOwnerLayout : childTickets.EventTicketLayout rest
      resources.window.pushChild (freshOwned.flags :: owned.flags :: blocks)
      (freshOwned.owner :: owned.owner :: owners) := by
    change EventOwnedLayout rest resources.window.pushChild
      ([f] :: owned.flags :: blocks)
      (childTickets.semanticOwnerOf newOwner ::
        childTickets.semanticOwners (owned.owner :: owners))
    rw [childNewSemantic, childSelectedTail]
    exact rotatedParentEventLayout.pushFresh
      (Or.inr (resources.window.pushChild.transientOwner_outside hinputPos))
  have holdOwnerOutside : resources.ticketOwnerLedger.outside =
      resources.tickets.semanticOwners startLedger.outside := by
    have heq := resources.ticketOwnerLedger.right_eq
    rw [resources.tickets.semanticCursor_right_indexOwners,
      startLedger.right_eq, List.map_append, resources.ticket_active_eq,
      hactive, startActive] at heq
    have heq' :
        resources.tickets.semanticOwners (owned.owner :: owners) ++
            resources.tickets.semanticOwners startLedger.outside =
          resources.tickets.semanticOwners (owned.owner :: owners) ++
            resources.ticketOwnerLedger.outside := by
      simpa only [IndexTicketLedger.semanticOwners] using heq
    exact (List.append_cancel_left heq').symm
  let childTicketOwnerLedger : childTickets.SemanticScheduleOwnerLedger rest
      resources.window.pushChild := {
    active := childTickets.semanticOwners (newOwner :: owned.owner :: owners)
    outside := childTickets.semanticOwners startLedger.outside
    right_eq := by
      rw [childTickets.semanticCursor_right_indexOwners,
        childOwnerLedger.right_eq, List.map_append]
      rfl
    outside_at := by
      intro semanticOwner hsemantic
      rcases List.mem_map.mp hsemantic with ⟨candidate, hcandidate, rfl⟩
      have hcandidateRight : candidate ∈
          startCursor.right.filterMap ScheduleAtom.indexOwner? := by
        rw [hrightPhysical]
        exact List.mem_append_right (owned.owner :: owners) hcandidate
      have hcandidateIndex := hrightSublist.mem hcandidateRight
      have hcandidateNe : candidate ≠ owned.owner := by
        intro heq
        subst candidate
        exact hheadOutsideFresh hcandidate
      have holdMem : resources.tickets.semanticOwnerOf candidate ∈
          resources.ticketOwnerLedger.outside := by
        rw [holdOwnerOutside]
        exact List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩
      have hold := resources.ticketOwnerLedger.outside_at _ holdMem
      have htickets := childTicketOriginal hcandidateIndex hcandidateNe
      simpa [IndexTicketLedger.semanticOwnerOf, htickets,
        ProductiveOwnerWindow.pushChild] using
          EventOwnedLayout.outside_pushChild resources.window hold
    frames := by
      rw [childTicketFramesEq]
      exact resources.ticketOwnerLedger.frames.push
    prefixLedger := childTicketPrefixLedger
  }
  have childOldSemantic : childTickets.semanticOwnerOf owned.owner =
      resources.window.pushChild.shadowEventOwner 1 hone := by
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [childTicketOld hheadMem, rotation.head_ticket]
    exact ProductiveOwnerWindow.semanticOwner_shadowEventTicket
      resources.window.pushChild 1 hone
  have childFullShadowLayout : childTickets.ShadowTicketLayout rest
      resources.window.pushChild ([f] :: resources.ticketShadowBlocks)
      (newOwner :: resources.ticketShadowOwners) := by
    rcases ticketShadowContext with
      ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
    have hnormalFull : ShadowStartLayout parent resources.window
        (owned.flags :: (blocks ++ parkedBlocks))
        (normal.tickets.semanticOwnerOf owned.owner ::
          normal.tickets.semanticOwners (owners ++ parkedOwners)) := by
      have hold := normal.fullShadowLayout
      rw [hcontextBlocks, hcontextOwners] at hold
      simpa only [IndexTicketLedger.semanticOwners] using hold
    have htailSemantic : childTickets.semanticOwners (owners ++ parkedOwners) =
        normal.tickets.semanticOwners (owners ++ parkedOwners) := by
      apply List.map_congr_left
      intro candidate hcandidate
      simp only [IndexTicketLedger.semanticOwnerOf]
      apply congrArg (IndexTicket.semanticOwner (g := g))
      have hcontextMem : candidate ∈ resources.ticketShadowOwners := by
        rw [hcontextOwners]
        exact List.mem_cons_of_mem owned.owner hcandidate
      have hcandidateIndex : candidate ∈ startCursor.indexOwners := by
        simpa [startCursor, parent, parentTask, liveScheduleCursor] using
          resources.ticketShadowOwners_subset hcontextMem
      rw [childTicketOld hcandidateIndex]
      apply rotation.unchanged_normal candidate
      · exact resources.ticketShadowOwners_subset hcontextMem
      · intro heq
        subst candidate
        have hfullNodup := resources.ticketShadowOwners_nodup
        rw [hcontextOwners] at hfullNodup
        exact (List.nodup_cons.mp hfullNodup).1 hcandidate
    rw [hcontextBlocks, hcontextOwners]
    change ShadowStartLayout rest resources.window.pushChild
      ([f] :: owned.flags :: (blocks ++ parkedBlocks))
      (childTickets.semanticOwnerOf newOwner ::
        childTickets.semanticOwnerOf owned.owner ::
          childTickets.semanticOwners (owners ++ parkedOwners))
    rw [childNewSemantic, childOldSemantic, htailSemantic]
    exact hnormalFull.pushFreshRotateHead hone
      (OutsideShadowWindow.transientOwner
        resources.window.pushChild hinputPos)
  let childTicketShadowLedger : childTickets.SemanticShadowOwnerLedger rest
      resources.window.pushChild := {
    active := childTickets.semanticOwners
      (newOwner :: resources.ticketShadowOwners)
    outside := resources.ticketShadowLedger.outside
    right_eq := by
      rcases ticketShadowContext with
        ⟨parkedBlocks, parkedOwners, _hcontextBlocks, hcontextOwners⟩
      have hfullOwners : resources.ticketShadowOwners =
          owned.owner :: (owners ++ parkedOwners) := by
        simpa only [List.cons_append] using hcontextOwners
      have hrightTailSemantic : childTickets.semanticOwners
          (owners ++ startLedger.outside) =
            resources.tickets.semanticOwners (owners ++ startLedger.outside) := by
        apply List.map_congr_left
        intro candidate hcandidate
        simp only [IndexTicketLedger.semanticOwnerOf]
        apply congrArg (IndexTicket.semanticOwner (g := g))
        have hcandidateRight : candidate ∈
            startCursor.right.filterMap ScheduleAtom.indexOwner? := by
          rw [hrightPhysical]
          exact List.mem_cons_of_mem owned.owner hcandidate
        apply childTicketOriginal (hrightSublist.mem hcandidateRight)
        intro heq
        subst candidate
        exact (List.nodup_cons.mp (by
          simpa only [List.cons_append] using hrightPhysicalNodup)).1 hcandidate
      have hcontextTailSemantic : childTickets.semanticOwners
          (owners ++ parkedOwners) =
            resources.tickets.semanticOwners (owners ++ parkedOwners) := by
        apply List.map_congr_left
        intro candidate hcandidate
        simp only [IndexTicketLedger.semanticOwnerOf]
        apply congrArg (IndexTicket.semanticOwner (g := g))
        have hcontextMem : candidate ∈ resources.ticketShadowOwners := by
          rw [hfullOwners]
          exact List.mem_cons_of_mem owned.owner hcandidate
        have hcandidateIndex : candidate ∈ startCursor.indexOwners := by
          simpa [startCursor, parent, parentTask, liveScheduleCursor] using
            resources.ticketShadowOwners_subset hcontextMem
        apply childTicketOriginal hcandidateIndex
        intro heq
        subst candidate
        have hfullNodup := resources.ticketShadowOwners_nodup
        rw [hfullOwners] at hfullNodup
        exact (List.nodup_cons.mp hfullNodup).1 hcandidate
      have holdTail : resources.tickets.semanticOwners
          (owners ++ startLedger.outside) =
            resources.tickets.semanticOwners (owners ++ parkedOwners) ++
              resources.ticketShadowLedger.outside := by
        have heq := resources.ticketShadowLedger.right_eq
        rw [resources.tickets.semanticCursor_right_indexOwners,
          hrightPhysical, resources.ticket_shadow_active_eq, hfullOwners] at heq
        have htail := congrArg List.tail heq
        simpa [IndexTicketLedger.semanticOwners] using htail
      rw [childTickets.semanticCursor_right_indexOwners,
        childOwnerLedger.right_eq, hfullOwners]
      simp only [childOwnerLedger]
      simp only [IndexTicketLedger.semanticOwners, List.map_cons,
        List.cons_append, List.cons.injEq, true_and]
      change childTickets.semanticOwners (owners ++ startLedger.outside) =
        childTickets.semanticOwners (owners ++ parkedOwners) ++
          resources.ticketShadowLedger.outside
      rw [hrightTailSemantic, hcontextTailSemantic]
      exact holdTail
    outside_at := by
      intro candidate hcandidate
      simpa [ProductiveOwnerWindow.pushChild] using
        OutsideShadowWindow.transport resources.window (by rfl)
          (resources.ticketShadowLedger.outside_at candidate hcandidate)
    frames := by
      rw [childTicketFramesEq]
      simpa [ProductiveOwnerWindow.pushChild] using
        resources.ticketShadowLedger.frames.transportEqual
          (residual := rest) (by rfl)
    prefixLedger := childTicketPrefixLedger
  }
  have normalHeadNonparking :
      (normal.tickets.ticketOf owned.owner).Nonparking := by
    rw [normal.head_shadow hparentZero]
    exact resources.window.shadowEventTicket_nonparking 0 hparentZero
  have rotationHeadNonparking :
      (rotation.tickets.ticketOf owned.owner).Nonparking := by
    rw [rotation.head_ticket]
    exact resources.window.pushChild.shadowEventTicket_nonparking 1 hone
  have rotationParkingAtOrBelow :
      rotation.tickets.ParkingAtOrBelow resources.window :=
    normal.parkingAtOrBelow.change_nonparking owned.owner rotationHeadNonparking
      rotation.unchanged_normal
  have childParkingParent : childTickets.ParkingAtOrBelow resources.window := by
    simpa [childTickets] using
      rotationParkingAtOrBelow.allocate_nonparking newOwner
        (IndexTicket.transient hinputPos)
        (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using
          hnewFresh)
        (rotation.transient_fresh hinputPos) hticketTransientNotScratch
        hindexPerm (IndexTicket.transient_nonparking hinputPos)
  have childParking : childTickets.ParkingAtOrBelow resources.window.pushChild := by
    simpa [IndexTicketLedger.transport] using
      childParkingParent.transport_mono
        (List.Perm.refl childCursor.indexOwners) (by rfl)
  let childPool : IndexOwnerPool childCursor :=
    resources.pool.allocateMember newOwner hnewFree hindexPerm
  let childResources : ScheduleRunResources rest pre childCursor := {
    pool := childPool
    tickets := childTickets
    window := resources.window.pushChild
    parkingAtOrBelow := childParking
    ownerLedger := childOwnerLedger
    ticketOwnerLedger := childTicketOwnerLedger
    ticket_active_eq := by rfl
    ticketShadowBlocks := [f] :: resources.ticketShadowBlocks
    ticketShadowOwners := newOwner :: resources.ticketShadowOwners
    ticketShadowOwners_subset := by
      intro candidate hcandidate
      rcases List.mem_cons.mp hcandidate with hnew | hold
      · subst candidate
        exact hindexPerm.mem_iff.mpr (by simp)
      · have holdStart : candidate ∈ startCursor.indexOwners := by
          simpa [startCursor, parent, parentTask, liveScheduleCursor] using
            resources.ticketShadowOwners_subset hold
        exact hindexPerm.mem_iff.mpr (List.mem_cons_of_mem newOwner holdStart)
    ticketShadowOwners_nodup := by
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        apply hnewFresh
        have holdStart : newOwner ∈ startCursor.indexOwners := by
          simpa [startCursor, parent, parentTask, liveScheduleCursor] using
            resources.ticketShadowOwners_subset hmem
        exact holdStart
      · exact resources.ticketShadowOwners_nodup
    ticketShadowLedger := childTicketShadowLedger
    ticket_shadow_active_eq := by rfl
    ticketShadowLayout := childFullShadowLayout
    shadowLedger := ShadowOwnerLedger.ofGeneric childPool childOwnerLedger
    shadow_active_eq := rfl
    charged := resources.charged + 1
    charged_eq_indices := by
      have hlen := hindexPerm.length_eq
      have hold : resources.charged = startCursor.indexOwners.length := by
        simpa [startCursor, parent, parentTask, liveScheduleCursor] using
          resources.charged_eq_indices
      simp only [List.length_cons] at hlen
      omega
    charged_le_indices := by
      have hlen := hindexPerm.length_eq
      have hold := resources.charged_le_indices
      have hold' : resources.charged ≤ startCursor.indexOwners.length := by
        simpa [startCursor, parent, parentTask, liveScheduleCursor] using hold
      simp only [List.length_cons] at hlen
      omega
    productive_le_credit := by
      have hp := resources.productive_le_credit
      change rest.productiveCount ≤ resources.charged + 1 +
        (resources.pool.free.erase newOwner).length
      have hfreeLen := (List.perm_cons_erase hnewFree).length_eq
      simp only [NFParse.productiveCount, NFParse.binaryCount,
        NFParse.terminalCount] at hp ⊢
      simp only [List.length_cons] at hfreeLen
      omega
    task_locality := by
      intro owner howner
      apply resources.task_locality owner
      have hold : owner ∈ startCursor.taskOwners := by
        rw [← htasks]
        exact howner
      simpa [startCursor, parent, parentTask, liveScheduleCursor] using hold
  }
  have hchildCredit : 0 < childResources.charged := by
    dsimp [childResources]
    omega
  have compatibleRest :
      EventCompatible rest (freshOwned.flags :: owned.flags :: blocks) := by
    simpa [freshOwned] using EventCompatible.pushFresh compatible
  let childOwnerLayout : EventOwnedLayout rest childResources.window
      (freshOwned.flags :: owned.flags :: blocks)
      (freshOwned.owner :: owned.owner :: owners) := by
    simpa [childResources, freshOwned] using ownerLayout.pushFresh hheadOwner
  let childShadowLayout : ShadowStartLayout rest childResources.window
      (freshOwned.flags :: owned.flags :: blocks)
      (freshOwned.owner :: owned.owner :: owners) :=
    childResources.genericShadowStartLayout (by
      simp [childResources, childOwnerLedger, freshOwned])
      childOwnerLayout.owners_length
      (by
        intro block hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · simp [freshOwned]
        · rcases List.mem_cons.mp htail with rfl | hblocks
          · exact howned
          · exact shadowLayout.block_nonempty block
              (List.mem_cons_of_mem owned.flags hblocks))
  have hstackRest : f :: stack =
      freshOwned.flags ++ childProtected ++ hidden := by
    simp [freshOwned, childProtected, hstack, List.append_assoc]
  have hframesRest : List.Disjoint
      (freshOwned.owner :: owned.owner :: owners) childCursor.frameOwners := by
    rw [List.disjoint_left]
    intro candidate hcandidate hframe
    rcases List.mem_cons.mp hcandidate with hnew | hold
    · subst candidate
      apply hnewFresh
      apply hstart'.frameOwners_subset_indexOwners
      simpa [childCursor, startCursor, liveScheduleCursor,
        ScheduleCursor.frameOwners, ScheduleCursor.word,
        ScheduleAtom.closeOwner?, List.filterMap_append] using hframe
    · apply (List.disjoint_left.mp hframes) hold
      simpa [childCursor, startCursor, parent, liveScheduleCursor,
        ScheduleCursor.frameOwners, ScheduleCursor.word,
        ScheduleAtom.closeOwner?, List.filterMap_append] using hframe
  have childTicketShadowContext : childResources.TicketShadowContextExtends
      (freshOwned.flags :: owned.flags :: blocks)
      (freshOwned.owner :: owned.owner :: owners) := by
    rcases ticketShadowContext with
      ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
    refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
    · simp [childResources, freshOwned, hcontextBlocks, List.cons_append]
    · simp [childResources, freshOwned, hcontextOwners, List.cons_append]
  have childTicketTransientHead : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∈
          childCursor.indexTickets childResources.tickets.ticketOf →
        childResources.tickets.ticketOf freshOwned.owner =
          IndexTicket.transient hinput := by
    intro hinput _hmem
    change childTickets.ticketOf newOwner = IndexTicket.transient hinput
    rw [childTicketNew]
  let childParkingContext : OverlayParkingContext childResources
      (freshOwned :: owned :: overlayTail) baseBlocks baseOwners := by
    cases startParkingContext with
    | strict below =>
        have normalStrict : normal.tickets.ParkingBelow resources.window :=
          below.change_nonparking owned.owner normalHeadNonparking normal.unchanged
        have rotationStrict : rotation.tickets.ParkingBelow resources.window :=
          normalStrict.change_nonparking owned.owner rotationHeadNonparking
            rotation.unchanged_normal
        have childStrictParent : childTickets.ParkingBelow resources.window := by
          simpa [childTickets] using
            rotationStrict.allocate_nonparking newOwner
              (IndexTicket.transient hinputPos)
              (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using
                hnewFresh)
              (rotation.transient_fresh hinputPos) hticketTransientNotScratch
              hindexPerm (IndexTicket.transient_nonparking hinputPos)
        exact .strict (by
          simpa [IndexTicketLedger.transport] using
            childStrictParent.transport_mono
              (List.Perm.refl childCursor.indexOwners) (by rfl))
    | attached restore =>
        have hmarkerLower : restore.marker ∈
            ScheduleOverlay.owners overlayTail baseOwners := by
          rcases restore.base_head with
            ⟨block, tailBlocks, tailOwners, _hblocks, howners⟩
          have hmemBase : restore.marker ∈ baseOwners := by
            simp [howners]
          exact List.mem_append_right _ hmemBase
        have hmarkerNe : restore.marker ≠ owned.owner := by
          intro heq
          apply overlayLayout.head_fresh
          simpa [heq] using hmarkerLower
        have hmarkerStart : restore.marker ∈ startCursor.indexOwners := by
          simpa [startCursor, parent, parentTask, liveScheduleCursor] using
            restore.marker_live
        have hmarkerChild : restore.marker ∈ childCursor.indexOwners :=
          hindexPerm.mem_iff.mpr (List.mem_cons_of_mem newOwner hmarkerStart)
        have hmarkerTicket : childTickets.ticketOf restore.marker =
            resources.window.pushChild.parkingTicket := by
          calc
            childTickets.ticketOf restore.marker =
                resources.tickets.ticketOf restore.marker :=
              childTicketOriginal hmarkerStart hmarkerNe
            _ = resources.window.parkingTicket := restore.marker_ticket
            _ = resources.window.pushChild.parkingTicket := by rfl
        have hrestoreAvailable :
            restore.restore ∉ childCursor.indexTickets childTickets.ticketOf ∨
              ∃ idx ∈ freshOwned :: owned :: overlayTail,
                childTickets.ticketOf idx.owner = restore.restore := by
          by_cases hfresh :
              restore.restore ∉ childCursor.indexTickets childTickets.ticketOf
          · exact Or.inl hfresh
          · apply Or.inr
            have hmem : restore.restore ∈
                childCursor.indexTickets childTickets.ticketOf := by
              simpa using hfresh
            rw [ScheduleCursor.indexTickets] at hmem
            rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, hticket⟩
            have hclass := hindexPerm.mem_iff.mp hcandidate
            rcases List.mem_cons.mp hclass with hnew | hold
            · subst candidate
              rw [childTicketNew] at hticket
              exact False.elim
                (restore.restore_not_transient hinputPos hticket.symm)
            · by_cases hhead : candidate = owned.owner
              · refine ⟨owned, by simp, ?_⟩
                simpa [hhead] using hticket
              · have holdTicket : resources.tickets.ticketOf candidate =
                    restore.restore := by
                  rw [← childTicketOriginal hold hhead]
                  exact hticket
                rcases restore.available with holdFresh |
                    ⟨idx, hidx, hidxTicket⟩
                · exact False.elim (holdFresh (by
                    rw [ScheduleCursor.indexTickets]
                    exact List.mem_map.mpr ⟨candidate, hold, holdTicket⟩))
                · have hidxActive : idx.owner ∈
                      resources.ownerLedger.active := by
                    rw [hactive]
                    rcases List.mem_cons.mp hidx with rfl | htail
                    · simp
                    · exact List.mem_cons_of_mem owned.owner (by
                        dsimp [owners, ScheduleOverlay.owners]
                        exact List.mem_append_left baseOwners
                          (List.mem_map.mpr ⟨idx, htail, rfl⟩))
                  have hidxLive := resources.active_subset_indexOwners hidxActive
                  have hcandidateEq : candidate = idx.owner := by
                    apply resources.tickets.ticketOf_injectiveOn
                      (by simpa [startCursor, parent, parentTask,
                        liveScheduleCursor] using hold)
                      hidxLive
                    exact holdTicket.trans hidxTicket.symm
                  refine ⟨idx, by simp [hidx], ?_⟩
                  simpa [hcandidateEq] using hticket
        let childDepth := NFParse.pushEventPreimage rest.eventDepths restore.depth
        have hdepthStep : childDepth ≤ restore.depth + 1 := by
          simp [childDepth, NFParse.pushEventPreimage]
          split <;> omega
        have hlengthStep :
            (ScheduleOverlay.flags (freshOwned :: owned :: overlayTail) []).length =
              (ScheduleOverlay.flags (owned :: overlayTail) []).length + 1 := by
          simp [freshOwned, Nat.add_comm, Nat.add_left_comm]
        exact .attached {
          marker := restore.marker
          base_head := restore.base_head
          parkingAtOrBelow := by simpa [childResources] using childParking
          marker_live := by simpa [childResources] using hmarkerChild
          marker_ticket := by
            simpa [childResources] using hmarkerTicket
          restore := restore.restore
          restore_nonparking := restore.restore_nonparking
          restore_not_scratch := restore.restore_not_scratch
          restore_not_transient := restore.restore_not_transient
          restore_outside_primary := by
            simpa [childResources] using
              EventOwnedLayout.outside_pushChild resources.window
                restore.restore_outside_primary
          available := by
            simpa [childResources] using hrestoreAvailable
          depth := childDepth
          depth_le := by
            calc
              childDepth ≤ restore.depth + 1 := hdepthStep
              _ ≤ (ScheduleOverlay.flags (owned :: overlayTail) []).length + 1 :=
                Nat.add_le_add_right restore.depth_le 1
              _ = (ScheduleOverlay.flags
                    (freshOwned :: owned :: overlayTail) []).length :=
                hlengthStep.symm
          aligned := by
            rcases restore.aligned with ⟨hd, halign⟩ | houtside
            · have hparentDepth : restore.depth ∈ parent.eventDepths := by
                simpa [parent] using hd
              have hchildDepth : childDepth ∈ rest.eventDepths :=
                NFParse.pushEventPreimage_mem hparentDepth
              exact Or.inl ⟨hchildDepth, by
                have hshift := resources.window.shadowEventOwner_push hparentDepth
                simpa [childResources, childDepth] using halign.trans hshift⟩
            · exact Or.inr (by
                simpa [childResources, ProductiveOwnerWindow.pushChild] using
                  OutsideShadowWindow.transport resources.window
                    (residual := rest) (by rfl) houtside)
        }
  have childFree : childResources.pool.free ≠ [] := by
    apply childResources.free_ne_nil_of_index_count_lt
    simpa [childResources] using childTickets.index_count_lt hinputPos
  have childOverlayLayout : AdjacentOverlayLayout baseLayout
      (freshOwned :: owned :: overlayTail) := by
    apply overlayLayout.push freshOwned
    · simp [freshOwned]
    · intro _
      rfl
    · intro hmem
      apply hnewFresh
      apply resources.active_subset_indexOwners
      rw [hactive]
      simpa [freshOwned, owners] using hmem
  have hallRestOverlay : ∀ k <
      (ScheduleOverlay.flags (freshOwned :: owned :: overlayTail) baseFlags).length,
      rest.ConsumesAt k := by
    simpa [freshOwned, childProtected, protectedFlags, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hallRest
  have hboundaryRestOverlay : ¬ rest.ConsumesAt
      (ScheduleOverlay.flags (freshOwned :: owned :: overlayTail) baseFlags).length := by
    simpa [freshOwned, childProtected, protectedFlags, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hboundaryRest
  have hstackRestOverlay : f :: stack =
      ScheduleOverlay.flags (freshOwned :: owned :: overlayTail) baseFlags ++ hidden := by
    simpa [freshOwned, childProtected, protectedFlags] using hstackRest
  have hframesRestOverlay : List.Disjoint
      (ScheduleOverlay.owners (freshOwned :: owned :: overlayTail) baseOwners)
      (liveScheduleCursor rest
        (hallRestOverlay 0 childOverlayLayout.flags_length_pos)
        pre post input_eq alpha
          (ScheduleOverlay.word (freshOwned :: owned :: overlayTail) baseWord)).frameOwners := by
    simpa [freshOwned, owners, word] using hframesRest
  have hrestRun := restOverlay freshOwned (owned :: overlayTail) baseFlags hidden
    baseBlocks baseOwners baseWord baseUsed hstackRestOverlay baseLayout
    childOverlayLayout hallRestOverlay hboundaryRestOverlay (by
      simpa [freshOwned, blocks] using compatibleRest) hbaseUsed pre post input_eq
    alpha hstable (by
      simpa [freshOwned, word] using hchildInv) hframesRestOverlay hend
    (by simpa [freshOwned, word] using childResources)
    (by simpa [freshOwned, word] using childParkingContext) childFree hchildCredit
    (by simpa [freshOwned, blocks, owners] using childOwnerLayout)
    (by simpa [freshOwned, blocks, owners] using childShadowLayout)
    (by simpa [freshOwned, blocks, owners] using childTicketOwnerLayout)
    (by simpa [freshOwned, blocks, owners] using childTicketShadowContext)
    (by simpa [freshOwned, word] using childTicketTransientHead)
    (by simp [childResources, childOwnerLedger, freshOwned, owners])
    (by
      intro hinput hmem
      exact False.elim
        (childResources.pool.transientOwner_not_mem_indices hinput hmem))
    (by
      intro hinput hmem
      exact False.elim
        (childResources.pool.scratchOwner_not_mem_indices hinput hmem))
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos startCursor hstart'
  let childState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos childCursor hchildInv
  have hpush : ScheduleReaches g input startState childState := by
    apply ScheduleReaches.single
    have hstep := composite_livePushFresh_at input
      (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) pre.length
      (alpha.map ScheduleAtom.workSym) (ScheduleAtom.index owned).workSym
      (word.map ScheduleAtom.workSym)
    simpa [startState, childState, scheduleStateOfCursor, ScheduleState.config,
      startCursor, childCursor, liveScheduleCursor, parentTask, childTask, parent,
      freshOwned, scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
      ScheduleTask.workSym, List.map_append] using hstep
  simpa [startState, childState, parent, parentTask, liveScheduleCursor,
    scheduleStateOfCursor, word] using hpush.trans hrestRun

end Aho
end IndexedGrammar

end
