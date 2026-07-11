module

public import Langlib.Grammars.Indexed.NormalForm.AhoEventCompatibility
public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleMoves
public import Langlib.Grammars.Indexed.NormalForm.AhoTicketSeal
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayMode

@[expose]
public section

/-!
# Atomic pop for copy-on-write overlays

An event-free private head is erased by the existing adjacent pop certificate.  If another
private block is exposed, execution stays in overlay mode; only an empty private tail returns to
the marker-aware protected/plain modes.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Reassemble the complete owner ledger after an ephemeral head is erased without opening a
frame. -/
private def ScheduleOwnerLedger.eraseHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {old new : ScheduleCursor g input}
    {head : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (ledger : ScheduleOwnerLedger parse window old)
    (residualWindow : ProductiveOwnerWindow (input := input) residual)
    (_hactive : ledger.active = head :: owners)
    (hright : new.right.filterMap ScheduleAtom.indexOwner? = owners ++ ledger.outside)
    (houtside : ∀ owner ∈ ledger.outside,
      OutsideProductiveWindow residualWindow owner)
    (hframes : EventOwnedFrames residual residualWindow new.frameOwners)
    (hprefix : PrefixFrameLedger new) :
    ScheduleOwnerLedger residual residualWindow new where
  active := owners
  outside := ledger.outside
  right_eq := hright
  outside_at := houtside
  frames := hframes
  prefixLedger := hprefix

/-- Reassemble the shadow-owner ledger after the ephemeral head is erased. -/
private def ShadowOwnerLedger.eraseHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {old new : ScheduleCursor g input}
    {head : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (ledger : ShadowOwnerLedger parse window old)
    (residualWindow : ProductiveOwnerWindow (input := input) residual)
    (_hactive : ledger.active = head :: owners)
    (hright : new.right.filterMap ScheduleAtom.indexOwner? = owners ++ ledger.outside)
    (houtside : ∀ owner ∈ ledger.outside,
      OutsideShadowWindow residualWindow owner)
    (hframes : ShadowOwnedFrames residual residualWindow new.frameOwners)
    (hprefix : PrefixFrameLedger new) :
    ShadowOwnerLedger residual residualWindow new where
  active := owners
  outside := ledger.outside
  right_eq := hright
  outside_at := houtside
  frames := hframes
  prefixLedger := hprefix

/-- Releasing one owner cannot make a previously absent ticket appear in the residual
cursor. -/
private theorem IndexTicketLedger.release_preserves_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input}
    (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners))
    {target : IndexTicket input}
    (hfresh : target ∉ old.indexTickets ledger.ticketOf) :
    target ∉ new.indexTickets (ledger.release owner hindices).ticketOf := by
  intro hmem
  apply hfresh
  rw [ScheduleCursor.indexTickets] at hmem ⊢
  have htail : target ∈ new.indexOwners.map ledger.ticketOf := by
    simpa using hmem
  have hcons : target ∈ (owner :: new.indexOwners).map ledger.ticketOf :=
    List.mem_cons_of_mem _ htail
  exact (hindices.map ledger.ticketOf).mem_iff.mpr hcons

/-- The ticket carried by the released owner is absent from the residual cursor. -/
private theorem IndexTicketLedger.release_owner_ticket_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input}
    (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    ledger.ticketOf owner ∉
      new.indexTickets (ledger.release owner hindices).ticketOf := by
  have hperm := hindices.map ledger.ticketOf
  have holdNodup : (old.indexOwners.map ledger.ticketOf).Nodup := by
    simpa [ScheduleCursor.indexTickets] using ledger.tickets_nodup
  have hnewNodup :
      (ledger.ticketOf owner :: new.indexOwners.map ledger.ticketOf).Nodup :=
    hperm.nodup_iff.mp holdNodup
  have hfresh := (List.nodup_cons.mp hnewNodup).1
  intro hmem
  apply hfresh
  simpa [ScheduleCursor.indexTickets] using hmem

/-- Execute and erase the first private overlay block when it contains no productive event.

The marker-aware ordinary mutual hypothesis handles the singleton/base case.  The overlay
hypothesis is used only after a pop exposes another branch-local block.
-/
public theorem overlayScheduleRun_atomicPop
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (hpositive : ∀ d ∈ parse.eventDepths, 0 < d)
    (ordinaryIH : ∀ {B : g.nt} {residualStack : List g.flag}
      (residual : NFParse g B residualStack w),
      residual.nodeCount < parse.nodeCount → OrdinaryScheduleRuns residual)
    (overlayIH : ∀ {B : g.nt} {residualStack : List g.flag}
      (residual : NFParse g B residualStack w),
      residual.nodeCount < parse.nodeCount → OverlayScheduleRun residual) :
    OverlayScheduleRun parse := by
  intro input head overlayTail protectedFlags hidden blocks owners word used hstack
    baseLayout overlayLayout hall hboundary compatible hused pre post input_eq alpha
    hstable hstart hframes hend resources parkingContext hfree hcredit ownerLayout shadowLayout
    ticketOwnerLayout ticketShadowContext ticketTransientHead hactive transientHead
    scratchHead
  cases overlayTail with
  | nil =>
      have howned : head.flags ≠ [] := overlayLayout.head_block_ne
      have hlater : protectedFlags ≠ [] → head.mark.later = true := by
        intro hne
        apply overlayLayout.head_later
        simpa using hne
      have hstack' : stack = head.flags ++ protectedFlags ++ hidden := by
        simpa using hstack
      have compatible' : EventCompatible parse (head.flags :: blocks) := by
        simpa using compatible
      have hframes' : List.Disjoint (head.owner :: owners)
          (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
            pre post input_eq alpha (.index head :: word)).frameOwners := by
        simpa using hframes
      have hstart' : ScheduleInvariant
          (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
            pre post input_eq alpha (.index head :: word)) := by
        simpa using hstart
      let resources' : ScheduleRunResources parse pre
          (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
            pre post input_eq alpha (.index head :: word)) := by
        simpa using resources
      have ownerLayout' : EventOwnedLayout parse resources'.window
          (head.flags :: blocks) (head.owner :: owners) := by
        simpa [resources'] using ownerLayout
      have shadowLayout' : ShadowStartLayout parse resources'.window
          (head.flags :: blocks) (head.owner :: owners) := by
        simpa [resources'] using shadowLayout
      have ticketOwnerLayout' : resources'.tickets.EventTicketLayout parse
          resources'.window (head.flags :: blocks) (head.owner :: owners) := by
        simpa [resources'] using ticketOwnerLayout
      have ticketShadowContext' : resources'.TicketShadowContextExtends
          (head.flags :: blocks) (head.owner :: owners) := by
        simpa [resources'] using ticketShadowContext
      have hall' : ∀ k < head.flags.length + protectedFlags.length,
          parse.ConsumesAt k := by
        intro k hk
        apply hall
        simpa using hk
      have hboundary' : ¬ parse.ConsumesAt
          (head.flags.length + protectedFlags.length) := by
        simpa using hboundary
      let startParkingContext : OverlayParkingContext resources' [head] blocks owners := by
        simpa [resources'] using parkingContext
      have ticketTransientHead' : ∀ hinput : 0 < input.length,
          IndexTicket.transient hinput ∈
              (liveScheduleCursor parse (hall' 0 (by
                have := List.length_pos_of_ne_nil howned
                omega)) pre post input_eq alpha (.index head :: word)).indexTickets
                resources'.tickets.ticketOf →
            resources'.tickets.ticketOf head.owner = IndexTicket.transient hinput := by
        simpa [resources'] using ticketTransientHead
      have hactive' : resources'.ownerLedger.active = head.owner :: owners := by
        simpa [resources'] using hactive
      have transientHead' : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
              (liveScheduleCursor parse (hall' 0 (by
                have := List.length_pos_of_ne_nil howned
                omega)) pre post input_eq alpha (.index head :: word)).indexOwners →
            head.owner = ProductiveOwnerWindow.transientOwner (g := g) hinput := by
        simpa using transientHead
      have scratchHead' : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
              (liveScheduleCursor parse (hall' 0 (by
                have := List.length_pos_of_ne_nil howned
                omega)) pre post input_eq alpha (.index head :: word)).indexOwners →
            head.owner = ProductiveOwnerWindow.scratchOwner (g := g) hinput := by
        simpa using scratchHead
      clear hstack
      rw [List.append_assoc] at hstack'
      subst stack
      have hownedPos : 0 < head.flags.length := List.length_pos_of_ne_nil howned
      have hlast : parse.ConsumesAt (head.flags.length - 1) := by
        apply hall'
        omega
      have hevents : ∀ d ∈ parse.eventDepths, head.flags.length - 1 < d := by
        intro d hd
        have hdpos := hpositive d hd
        have hfirst := BlockLayout.Boundary.first_length_le_of_pos howned
          (compatible'.boundary d hd) hdpos
        omega
      rcases exists_popContinuation_of_eventFree_block_with_owners
          (block := head.flags) (suffix := protectedFlags ++ hidden)
          parse head.denotes hlast hevents with
        ⟨continuation, hcount, hconsumes, heventShift, hownerShift⟩
      have hproductive : continuation.rest.productiveCount = parse.productiveCount := by
        rw [continuation.rest.productiveCount_eq_twice_yield_length_sub_one,
          parse.productiveCount_eq_twice_yield_length_sub_one]
      have compatibleRest : EventCompatible continuation.rest blocks :=
        EventCompatible.tailOfShift howned compatible'
          (fun d hd => (heventShift d).1 hd)
      have htailEndpointPos : ∀ i : Fin blocks.length,
          0 < blockEndpoint blocks i :=
        blockEndpoint_pos_of_blocks_nonempty baseLayout.erase.blocks_nonempty
      have residualOwnerLayout : EventOwnedLayout continuation.rest
          (resources'.window.transport hproductive) blocks owners :=
        ownerLayout'.atomicPopTail compatibleRest htailEndpointPos hproductive
          heventShift hownerShift
      have residualShadowLayout : ShadowStartLayout continuation.rest
          (resources'.window.transport hproductive) blocks owners :=
        shadowLayout'.tail
          (fun candidate hout =>
            OutsideShadowWindow.transport resources'.window hproductive hout)
          (by
            intro i hd
            have hd' : blockStart blocks i ∈ continuation.rest.eventDepths :=
              (heventShift _).2 hd
            refine ⟨hd', ?_⟩
            apply Fin.ext
            simp only [ProductiveOwnerWindow.shadowEventOwner_val,
              ProductiveOwnerWindow.transport_base]
            rw [hownerShift])
      have houtsideShift : ∀ candidate,
          OutsideProductiveWindow resources'.window candidate →
            OutsideProductiveWindow (resources'.window.transport hproductive) candidate :=
        fun candidate hout =>
          EventOwnedFrames.outside_transport resources'.window hproductive hout
      have hframeOwnerShift :
          ∀ event : {d : ℕ // d ∈ parse.eventDepths},
            ∃ residualEvent : {d : ℕ // d ∈ continuation.rest.eventDepths},
              resources'.window.eventOwner event.val event.property =
                (resources'.window.transport hproductive).eventOwner
                  residualEvent.val residualEvent.property := by
        intro event
        have hge : head.flags.length ≤ event.val := by
          have := hevents event.val event.property
          omega
        let d := event.val - head.flags.length
        have heq : head.flags.length + d = event.val := by
          dsimp [d]
          omega
        have hd : d ∈ continuation.rest.eventDepths :=
          (heventShift d).2 (by simpa [heq] using event.property)
        refine ⟨⟨d, hd⟩, ?_⟩
        apply Fin.ext
        simp only [ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.transport_base]
        rw [hownerShift]
        simp only [heq]
      let parentUsed : parse.ConsumesAt 0 := hall' 0 (by omega)
      let parentTask : ScheduleTask g input :=
        scheduleTaskOfParse parse pre post input_eq (.live parentUsed)
      have hownerEq (mode : TaskMode continuation.rest) :
          (scheduleTaskOfParse continuation.rest pre post input_eq mode).owner =
            parentTask.owner := by
        apply Fin.ext
        rfl
      have hunframed : head.owner ∉
          (liveScheduleCursor parse parentUsed pre post input_eq alpha
        (.index head :: word)).frameOwners := by
        intro hmem
        exact (List.disjoint_left.mp hframes') (by simp) hmem
      have hshadowActive : resources'.shadowLedger.active = head.owner :: owners :=
        resources'.shadow_active_eq.trans hactive'
      rcases ticketShadowContext' with
        ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
      have hfullBlocks : resources'.ticketShadowBlocks =
          head.flags :: (blocks ++ parkedBlocks) := by
        simpa only [List.cons_append] using hcontextBlocks
      have hfullOwners : resources'.ticketShadowOwners =
          head.owner :: (owners ++ parkedOwners) := by
        simpa only [List.cons_append] using hcontextOwners
      have hfullPhysicalNodup :
          (head.owner :: (owners ++ parkedOwners)).Nodup := by
        have hnodup := resources'.ticketShadowOwners_nodup
        rw [hfullOwners] at hnodup
        exact hnodup
      have oldResidualFullShadowLayout : ShadowStartLayout continuation.rest
          (resources'.window.transport hproductive) (blocks ++ parkedBlocks)
            (resources'.tickets.semanticOwners (owners ++ parkedOwners)) := by
        have hfull := resources'.ticketShadowLayout
        rw [hfullBlocks, hfullOwners] at hfull
        exact hfull.tail
          (fun candidate hout =>
            OutsideShadowWindow.transport resources'.window hproductive hout)
          (by
            intro i hd
            have hd' : blockStart (blocks ++ parkedBlocks) i ∈
                continuation.rest.eventDepths := (heventShift _).2 hd
            refine ⟨hd', ?_⟩
            apply Fin.ext
            simp only [ProductiveOwnerWindow.shadowEventOwner_val,
              ProductiveOwnerWindow.transport_base]
            rw [hownerShift])
      by_cases hprotected : protectedFlags = []
      · subst protectedFlags
        have hblocksNil : blocks = [] :=
          baseLayout.erase.blocks_eq_nil_of_flags_eq_nil rfl
        have hownersNil : owners = [] := by
          have hlength := baseLayout.owners_length
          rw [hblocksNil] at hlength
          exact List.length_eq_zero_iff.mp (by simpa using hlength)
        subst owners
        have hwordUsed : word = used := baseLayout.word_eq_used_of_flags_eq_nil rfl
        subst used
        have hunused : ¬ continuation.rest.ConsumesAt 0 := by
          intro hrest
          apply hboundary'
          have hp := (hconsumes 0).1 hrest
          simpa using hp
        let residualTask : ScheduleTask g input :=
          scheduleTaskOfParse continuation.rest pre post input_eq (.plain hunused)
        have hresidualInv : ScheduleInvariant
            ⟨alpha ++ [.dollar], .task residualTask, word⟩ := by
          apply ScheduleInvariant.popErase alpha word parentTask residualTask head
            (hownerEq (.plain hunused)) hunframed
          simpa [liveScheduleCursor, parentTask] using hstart'
        have hindices :
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: word)).indexOwners.Perm
              (head.owner ::
                (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners) := by
          simp [liveScheduleCursor, ScheduleCursor.indexOwners,
            ScheduleCursor.word, ScheduleAtom.indexOwner?]
        have htasks :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).taskOwners =
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).taskOwners := by
          simp [liveScheduleCursor, ScheduleCursor.taskOwners,
            ScheduleCursor.word, ScheduleAtom.taskOwner?, residualTask, parentTask,
            hownerEq (.plain hunused)]
        have hrightLedger :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).right.filterMap
                ScheduleAtom.indexOwner? = [] ++ resources'.ownerLedger.outside := by
          have hright := resources'.ownerLedger.right_eq
          rw [hactive'] at hright
          simpa [liveScheduleCursor, ScheduleAtom.indexOwner?] using hright
        have hframeEq :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).frameOwners =
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).frameOwners := by
          simp [liveScheduleCursor, ScheduleCursor.frameOwners, ScheduleCursor.word,
            ScheduleAtom.closeOwner?, List.filterMap_append]
        have hsemanticFrames : EventOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).frameOwners := by
          rw [hframeEq]
          apply resources'.ownerLedger.frames.transport
          intro candidate hcandidate
          rcases hcandidate with hout | ⟨event, howner⟩
          · exact Or.inl (houtsideShift candidate hout)
          · rcases hframeOwnerShift event with ⟨residualEvent, hshift⟩
            exact Or.inr ⟨residualEvent, howner.trans hshift⟩
        have hprefixLedger : PrefixFrameLedger
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word) :=
          resources'.ownerLedger.prefixLedger.transport (by rfl) (by rw [hframeEq])
        let residualLedger : ScheduleOwnerLedger continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word) :=
          resources'.ownerLedger.eraseHead
            (resources'.window.transport hproductive) hactive' hrightLedger
            (fun owner hmem => houtsideShift owner
              (resources'.ownerLedger.outside_at owner hmem))
            hsemanticFrames hprefixLedger
        have hrightShadow :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).right.filterMap
                ScheduleAtom.indexOwner? = [] ++ resources'.shadowLedger.outside := by
          have hright := resources'.shadowLedger.right_eq
          rw [hshadowActive] at hright
          simpa [liveScheduleCursor, ScheduleAtom.indexOwner?] using hright
        have hshadowFrames : ShadowOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).frameOwners := by
          rw [hframeEq]
          exact resources'.shadowLedger.frames.transportEqual hproductive
        let residualShadowLedger : ShadowOwnerLedger continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word) :=
          resources'.shadowLedger.eraseHead
            (resources'.window.transport hproductive) hshadowActive hrightShadow
            (fun owner hmem => OutsideShadowWindow.transport resources'.window hproductive
              (resources'.shadowLedger.outside_at owner hmem))
            hshadowFrames hprefixLedger
        let residualTickets := resources'.tickets.release head.owner hindices
        have hticketActive : resources'.ticketOwnerLedger.active =
            resources'.tickets.semanticOwnerOf head.owner :: [] := by
          rw [resources'.ticket_active_eq, hactive']
          simp [IndexTicketLedger.semanticOwners]
        have hticketShadowActive : resources'.ticketShadowLedger.active =
            resources'.tickets.semanticOwnerOf head.owner ::
              resources'.tickets.semanticOwners parkedOwners := by
          rw [resources'.ticket_shadow_active_eq, hfullOwners]
          simp [IndexTicketLedger.semanticOwners]
        have hrightTicket :
            residualTickets.semanticCursor.right.filterMap ScheduleAtom.indexOwner? =
              [] ++ resources'.ticketOwnerLedger.outside := by
          have hright := resources'.ticketOwnerLedger.right_eq
          rw [hticketActive] at hright
          simpa [residualTickets, IndexTicketLedger.semanticCursor,
            IndexTicketLedger.semanticOwnerOf, liveScheduleCursor,
            ScheduleCursor.relabelTicketOwners, ScheduleAtom.relabelTicketOwner,
            ScheduleAtom.indexOwner?] using hright
        have hticketFrameEq : residualTickets.semanticCursor.frameOwners =
            resources'.tickets.semanticCursor.frameOwners := by
          rw [IndexTicketLedger.semanticCursor_frameOwners,
            IndexTicketLedger.semanticCursor_frameOwners, hframeEq]
          simp [residualTickets]
        have hticketPrefix : PrefixFrameLedger residualTickets.semanticCursor :=
          resources'.ticketOwnerLedger.prefixLedger.transport
            (List.Perm.refl _)
            (by rw [hticketFrameEq])
        have hticketFrames : EventOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          rw [hticketFrameEq]
          apply resources'.ticketOwnerLedger.frames.transport
          intro candidate hcandidate
          rcases hcandidate with hout | ⟨event, howner⟩
          · exact Or.inl (houtsideShift candidate hout)
          · rcases hframeOwnerShift event with ⟨residualEvent, hshift⟩
            exact Or.inr ⟨residualEvent, howner.trans hshift⟩
        let residualTicketLedger : residualTickets.SemanticScheduleOwnerLedger
            continuation.rest (resources'.window.transport hproductive) :=
          resources'.ticketOwnerLedger.eraseHead
            (resources'.window.transport hproductive) hticketActive hrightTicket
            (fun owner hmem => houtsideShift owner
              (resources'.ticketOwnerLedger.outside_at owner hmem))
            hticketFrames hticketPrefix
        have hrightTicketShadow :
            residualTickets.semanticCursor.right.filterMap ScheduleAtom.indexOwner? =
              residualTickets.semanticOwners parkedOwners ++
                resources'.ticketShadowLedger.outside := by
          have hright := resources'.ticketShadowLedger.right_eq
          rw [hticketShadowActive] at hright
          simpa [residualTickets, IndexTicketLedger.semanticCursor,
            IndexTicketLedger.semanticOwnerOf, IndexTicketLedger.semanticOwners,
            liveScheduleCursor,
            ScheduleCursor.relabelTicketOwners, ScheduleAtom.relabelTicketOwner,
            ScheduleAtom.indexOwner?] using hright
        have hticketShadowFrames : ShadowOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          rw [hticketFrameEq]
          exact resources'.ticketShadowLedger.frames.transportEqual hproductive
        let residualTicketShadowLedger : residualTickets.SemanticShadowOwnerLedger
            continuation.rest (resources'.window.transport hproductive) :=
          resources'.ticketShadowLedger.eraseHead
            (resources'.window.transport hproductive) hticketShadowActive
            hrightTicketShadow
            (fun owner hmem => OutsideShadowWindow.transport resources'.window hproductive
              (resources'.ticketShadowLedger.outside_at owner hmem))
            hticketShadowFrames hticketPrefix
        have residualFullShadowLayout : residualTickets.ShadowTicketLayout
            continuation.rest (resources'.window.transport hproductive)
              (blocks ++ parkedBlocks) parkedOwners := by
          simpa [residualTickets] using oldResidualFullShadowLayout
        have residualFullShadowOwnersSubset : parkedOwners ⊆
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners := by
          intro candidate hcandidate
          have hcontext : candidate ∈ resources'.ticketShadowOwners := by
            rw [hfullOwners]
            exact List.mem_cons_of_mem head.owner hcandidate
          have hold := resources'.ticketShadowOwners_subset hcontext
          rcases List.mem_cons.mp (hindices.mem_iff.mp hold) with heq | hnew
          · subst candidate
            exact False.elim ((List.nodup_cons.mp hfullPhysicalNodup).1 hcandidate)
          · exact hnew
        have residualFullShadowOwnersNodup : parkedOwners.Nodup :=
          (List.nodup_cons.mp hfullPhysicalNodup).2
        have hticketTransientResidualFree : ∀ hinput : 0 < input.length,
            IndexTicket.transient hinput ∉
              (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexTickets
                residualTickets.ticketOf := by
          intro hinput hmem
          have hperm := hindices.map resources'.tickets.ticketOf
          have hmemOld : IndexTicket.transient hinput ∈
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexTickets resources'.tickets.ticketOf := by
            rw [ScheduleCursor.indexTickets]
            apply hperm.mem_iff.mpr
            exact List.mem_cons_of_mem _ (by
              simpa [residualTickets, ScheduleCursor.indexTickets] using hmem)
          have hhead := ticketTransientHead' hinput hmemOld
          have hnodup := hperm.nodup_iff.mp resources'.tickets.tickets_nodup
          have htailFresh := (List.nodup_cons.mp hnodup).1
          apply htailFresh
          simpa [hhead, residualTickets, ScheduleCursor.indexTickets] using hmem
        have htransientResidualFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
              (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners := by
          intro hinput hmem
          have holdMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners :=
            hindices.mem_iff.mpr (List.mem_cons_of_mem head.owner hmem)
          have heq := transientHead' hinput holdMem
          have holdNodup :
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners.Nodup :=
            (List.nodup_append.mp resources'.pool.all_nodup).1
          have hnewNodup := hindices.nodup_iff.mp holdNodup
          exact (List.nodup_cons.mp hnewNodup).1 (by simpa [heq] using hmem)
        have hscratchResidualFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
              (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners := by
          intro hinput hmem
          have holdMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners :=
            hindices.mem_iff.mpr (List.mem_cons_of_mem head.owner hmem)
          have heq := scratchHead' hinput holdMem
          have holdNodup :
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners.Nodup :=
            (List.nodup_append.mp resources'.pool.all_nodup).1
          have hnewNodup := hindices.nodup_iff.mp holdNodup
          exact (List.nodup_cons.mp hnewNodup).1 (by simpa [heq] using hmem)
        let residualResources : ScheduleRunResources continuation.rest pre
            ⟨alpha ++ [.dollar], .task residualTask, word⟩ :=
          resources'.releaseOwned head.owner hindices htasks hproductive residualLedger
            residualTicketLedger (by rfl)
            (blocks ++ parkedBlocks) parkedOwners
            residualFullShadowOwnersSubset residualFullShadowOwnersNodup
            residualTicketShadowLedger (by rfl) residualFullShadowLayout
            residualShadowLedger (by rfl) hcredit
        have residualParkingBelow : residualResources.tickets.ParkingBelow
            residualResources.window := by
          cases startParkingContext with
          | strict below =>
              have hp := below.release head.owner hindices
              simpa [residualResources, residualTickets] using
                hp.transport_mono (List.Perm.refl _) (by rfl)
          | attached restore =>
              rcases restore.base_head with
                ⟨block, tailBlocks, tailOwners, hrestoreBlocks, _⟩
              rw [hblocksNil] at hrestoreBlocks
              simp at hrestoreBlocks
        have hpos : pre.length ≤ input.length := by
          rw [input_eq]
          simp
        let startState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hstart'
        let residualState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hresidualInv
        have hpop : ScheduleReaches g input startState residualState := by
          apply ScheduleReaches.single
          have hstep := composite_popPlainErase_at input head.relation head.mark
            continuation.edge pre.length (alpha.map ScheduleAtom.workSym)
            (word.map ScheduleAtom.workSym)
          simpa [startState, residualState, scheduleStateOfCursor, ScheduleState.config,
            liveScheduleCursor, parentTask, residualTask, scheduleTaskOfParse,
            ScheduleCursor.erase, ScheduleAtom.workSym, ScheduleTask.workSym,
            List.map_append] using hstep
        obtain ⟨next, tail, rfl⟩ := List.exists_cons_of_ne_nil hused
        have hrun := (ordinaryIH continuation.rest hcount).1 hunused pre post input_eq
          alpha next tail hstable (by
            simpa [residualTask, plainScheduleCursor] using hresidualInv)
          hend (by
            simpa [residualTask, plainScheduleCursor] using residualResources)
          (by simp [residualResources]) (by
            simpa [residualTask, plainScheduleCursor] using residualParkingBelow)
          (by rfl) ShadowStartLayout.nil (by
            simpa [residualTask, plainScheduleCursor, residualTickets] using
              hticketTransientResidualFree) (by
            simpa [residualTask, plainScheduleCursor] using htransientResidualFree)
          (by
            simpa [residualTask, plainScheduleCursor] using hscratchResidualFree)
        have hrun' : ScheduleReaches g input residualState
            (scheduleStateOfCursor (pre ++ w).length (by
              rw [input_eq]
              simp) (scheduleWordCursor alpha (next :: tail)) hend) := by
          simpa [residualState, residualTask, plainScheduleCursor,
            scheduleStateOfCursor] using hrun
        simpa [startState, scheduleStateOfCursor] using hpop.trans hrun'
      · have residualUsed : continuation.rest.ConsumesAt 0 := by
          have hp : parse.ConsumesAt head.flags.length := hall' head.flags.length (by
            have := List.length_pos_of_ne_nil hprotected
            omega)
          exact (hconsumes 0).2 (by simpa using hp)
        let residualTask : ScheduleTask g input :=
          scheduleTaskOfParse continuation.rest pre post input_eq (.live residualUsed)
        have hresidualInv : ScheduleInvariant
            ⟨alpha ++ [.dollar], .task residualTask, word⟩ := by
          apply ScheduleInvariant.popErase alpha word parentTask residualTask head
            (hownerEq (.live residualUsed)) hunframed
          simpa [liveScheduleCursor, parentTask] using hstart'
        have hindices :
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: word)).indexOwners.Perm
              (head.owner ::
                (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners) := by
          simp [liveScheduleCursor, ScheduleCursor.indexOwners,
            ScheduleCursor.word, ScheduleAtom.indexOwner?]
        have htasks :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).taskOwners =
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).taskOwners := by
          simp [liveScheduleCursor, ScheduleCursor.taskOwners,
            ScheduleCursor.word, ScheduleAtom.taskOwner?, residualTask, parentTask,
            hownerEq (.live residualUsed)]
        have hrightLedger :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).right.filterMap
                ScheduleAtom.indexOwner? = owners ++ resources'.ownerLedger.outside := by
          have hright := resources'.ownerLedger.right_eq
          rw [hactive'] at hright
          simpa [liveScheduleCursor, ScheduleAtom.indexOwner?] using hright
        have hframeEq :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).frameOwners =
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).frameOwners := by
          simp [liveScheduleCursor, ScheduleCursor.frameOwners, ScheduleCursor.word,
            ScheduleAtom.closeOwner?, List.filterMap_append]
        have hsemanticFrames : EventOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).frameOwners := by
          rw [hframeEq]
          apply resources'.ownerLedger.frames.transport
          intro candidate hcandidate
          rcases hcandidate with hout | ⟨event, howner⟩
          · exact Or.inl (houtsideShift candidate hout)
          · rcases hframeOwnerShift event with ⟨residualEvent, hshift⟩
            exact Or.inr ⟨residualEvent, howner.trans hshift⟩
        have hprefixLedger : PrefixFrameLedger
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word) :=
          resources'.ownerLedger.prefixLedger.transport (by rfl) (by rw [hframeEq])
        let residualLedger : ScheduleOwnerLedger continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word) :=
          resources'.ownerLedger.eraseHead
            (resources'.window.transport hproductive) hactive' hrightLedger
            (fun owner hmem => houtsideShift owner
              (resources'.ownerLedger.outside_at owner hmem))
            hsemanticFrames hprefixLedger
        have hrightShadow :
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).right.filterMap
                ScheduleAtom.indexOwner? = owners ++ resources'.shadowLedger.outside := by
          have hright := resources'.shadowLedger.right_eq
          rw [hshadowActive] at hright
          simpa [liveScheduleCursor, ScheduleAtom.indexOwner?] using hright
        have hshadowFrames : ShadowOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).frameOwners := by
          rw [hframeEq]
          exact resources'.shadowLedger.frames.transportEqual hproductive
        let residualShadowLedger : ShadowOwnerLedger continuation.rest
            (resources'.window.transport hproductive)
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word) :=
          resources'.shadowLedger.eraseHead
            (resources'.window.transport hproductive) hshadowActive hrightShadow
            (fun owner hmem => OutsideShadowWindow.transport resources'.window hproductive
              (resources'.shadowLedger.outside_at owner hmem))
            hshadowFrames hprefixLedger
        let residualTickets := resources'.tickets.release head.owner hindices
        have hticketActive : resources'.ticketOwnerLedger.active =
            resources'.tickets.semanticOwnerOf head.owner ::
              resources'.tickets.semanticOwners owners := by
          rw [resources'.ticket_active_eq, hactive']
          simp [IndexTicketLedger.semanticOwners]
        have hticketShadowActive : resources'.ticketShadowLedger.active =
            resources'.tickets.semanticOwnerOf head.owner ::
              resources'.tickets.semanticOwners (owners ++ parkedOwners) := by
          rw [resources'.ticket_shadow_active_eq, hfullOwners]
          simp [IndexTicketLedger.semanticOwners]
        have hrightTicket :
            residualTickets.semanticCursor.right.filterMap ScheduleAtom.indexOwner? =
              residualTickets.semanticOwners owners ++
                resources'.ticketOwnerLedger.outside := by
          have hright := resources'.ticketOwnerLedger.right_eq
          rw [hticketActive] at hright
          simpa [residualTickets, IndexTicketLedger.semanticCursor,
            IndexTicketLedger.semanticOwnerOf, IndexTicketLedger.semanticOwners,
            liveScheduleCursor, ScheduleCursor.relabelTicketOwners,
            ScheduleAtom.relabelTicketOwner, ScheduleAtom.indexOwner?] using hright
        have hticketFrameEq : residualTickets.semanticCursor.frameOwners =
            resources'.tickets.semanticCursor.frameOwners := by
          rw [IndexTicketLedger.semanticCursor_frameOwners,
            IndexTicketLedger.semanticCursor_frameOwners, hframeEq]
          simp [residualTickets]
        have hticketPrefix : PrefixFrameLedger residualTickets.semanticCursor :=
          resources'.ticketOwnerLedger.prefixLedger.transport
            (List.Perm.refl _)
            (by rw [hticketFrameEq])
        have hticketFrames : EventOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          rw [hticketFrameEq]
          apply resources'.ticketOwnerLedger.frames.transport
          intro candidate hcandidate
          rcases hcandidate with hout | ⟨event, howner⟩
          · exact Or.inl (houtsideShift candidate hout)
          · rcases hframeOwnerShift event with ⟨residualEvent, hshift⟩
            exact Or.inr ⟨residualEvent, howner.trans hshift⟩
        let residualTicketLedger : residualTickets.SemanticScheduleOwnerLedger
            continuation.rest (resources'.window.transport hproductive) :=
          resources'.ticketOwnerLedger.eraseHead
            (resources'.window.transport hproductive) hticketActive hrightTicket
            (fun owner hmem => houtsideShift owner
              (resources'.ticketOwnerLedger.outside_at owner hmem))
            hticketFrames hticketPrefix
        have hrightTicketShadow :
            residualTickets.semanticCursor.right.filterMap ScheduleAtom.indexOwner? =
              residualTickets.semanticOwners (owners ++ parkedOwners) ++
                resources'.ticketShadowLedger.outside := by
          have hright := resources'.ticketShadowLedger.right_eq
          rw [hticketShadowActive] at hright
          simpa [residualTickets, IndexTicketLedger.semanticCursor,
            IndexTicketLedger.semanticOwnerOf, IndexTicketLedger.semanticOwners,
            liveScheduleCursor, ScheduleCursor.relabelTicketOwners,
            ScheduleAtom.relabelTicketOwner, ScheduleAtom.indexOwner?] using hright
        have hticketShadowFrames : ShadowOwnedFrames continuation.rest
            (resources'.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          rw [hticketFrameEq]
          exact resources'.ticketShadowLedger.frames.transportEqual hproductive
        let residualTicketShadowLedger : residualTickets.SemanticShadowOwnerLedger
            continuation.rest (resources'.window.transport hproductive) :=
          resources'.ticketShadowLedger.eraseHead
            (resources'.window.transport hproductive) hticketShadowActive
            hrightTicketShadow
            (fun owner hmem => OutsideShadowWindow.transport resources'.window hproductive
              (resources'.ticketShadowLedger.outside_at owner hmem))
            hticketShadowFrames hticketPrefix
        have oldResidualTicketOwnerLayout : EventOwnedLayout continuation.rest
            (resources'.window.transport hproductive) blocks
              (resources'.tickets.semanticOwners owners) :=
          ticketOwnerLayout'.atomicPopTail compatibleRest htailEndpointPos hproductive
            heventShift hownerShift
        have residualTicketOwnerLayout : residualTickets.EventTicketLayout
            continuation.rest (resources'.window.transport hproductive) blocks owners := by
          simpa [residualTickets] using oldResidualTicketOwnerLayout
        have residualFullShadowLayout : residualTickets.ShadowTicketLayout
            continuation.rest (resources'.window.transport hproductive)
              (blocks ++ parkedBlocks) (owners ++ parkedOwners) := by
          simpa [residualTickets] using oldResidualFullShadowLayout
        have residualFullShadowOwnersSubset : owners ++ parkedOwners ⊆
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners := by
          intro candidate hcandidate
          have hcontext : candidate ∈ resources'.ticketShadowOwners := by
            rw [hfullOwners]
            exact List.mem_cons_of_mem head.owner hcandidate
          have hold := resources'.ticketShadowOwners_subset hcontext
          rcases List.mem_cons.mp (hindices.mem_iff.mp hold) with heq | hnew
          · subst candidate
            exact False.elim ((List.nodup_cons.mp hfullPhysicalNodup).1 hcandidate)
          · exact hnew
        have residualFullShadowOwnersNodup : (owners ++ parkedOwners).Nodup :=
          (List.nodup_cons.mp hfullPhysicalNodup).2
        have hticketTransientResidualFree : ∀ hinput : 0 < input.length,
            IndexTicket.transient hinput ∉
              (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexTickets
                residualTickets.ticketOf := by
          intro hinput hmem
          have hperm := hindices.map resources'.tickets.ticketOf
          have hmemOld : IndexTicket.transient hinput ∈
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexTickets resources'.tickets.ticketOf := by
            rw [ScheduleCursor.indexTickets]
            apply hperm.mem_iff.mpr
            exact List.mem_cons_of_mem _ (by
              simpa [residualTickets, ScheduleCursor.indexTickets] using hmem)
          have hhead := ticketTransientHead' hinput hmemOld
          have hnodup := hperm.nodup_iff.mp resources'.tickets.tickets_nodup
          have htailFresh := (List.nodup_cons.mp hnodup).1
          apply htailFresh
          simpa [hhead, residualTickets, ScheduleCursor.indexTickets] using hmem
        have htransientResidualFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
              (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners := by
          intro hinput hmem
          have holdMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners :=
            hindices.mem_iff.mpr (List.mem_cons_of_mem head.owner hmem)
          have heq := transientHead' hinput holdMem
          have holdNodup :
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners.Nodup :=
            (List.nodup_append.mp resources'.pool.all_nodup).1
          have hnewNodup := hindices.nodup_iff.mp holdNodup
          exact (List.nodup_cons.mp hnewNodup).1 (by simpa [heq] using hmem)
        have hscratchResidualFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
              (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners := by
          intro hinput hmem
          have holdMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners :=
            hindices.mem_iff.mpr (List.mem_cons_of_mem head.owner hmem)
          have heq := scratchHead' hinput holdMem
          have holdNodup :
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (.index head :: word)).indexOwners.Nodup :=
            (List.nodup_append.mp resources'.pool.all_nodup).1
          have hnewNodup := hindices.nodup_iff.mp holdNodup
          exact (List.nodup_cons.mp hnewNodup).1 (by simpa [heq] using hmem)
        let residualResources : ScheduleRunResources continuation.rest pre
            ⟨alpha ++ [.dollar], .task residualTask, word⟩ :=
          resources'.releaseOwned head.owner hindices htasks hproductive residualLedger
            residualTicketLedger (by rfl)
            (blocks ++ parkedBlocks) (owners ++ parkedOwners)
            residualFullShadowOwnersSubset residualFullShadowOwnersNodup
            residualTicketShadowLedger (by rfl) residualFullShadowLayout
            residualShadowLedger (by rfl) hcredit
        have hallRest : ∀ k < protectedFlags.length,
            continuation.rest.ConsumesAt k := by
          intro k hk
          apply (hconsumes k).2
          apply hall'
          omega
        have hboundaryRest : ¬ continuation.rest.ConsumesAt protectedFlags.length := by
          intro hrest
          apply hboundary'
          exact (hconsumes protectedFlags.length).1 hrest
        have hframesRest : List.Disjoint owners
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq alpha word).frameOwners := by
          apply List.disjoint_left.mpr
          intro owner howner hframe
          exact (List.disjoint_left.mp hframes') (List.mem_cons_of_mem _ howner) (by
            simpa [liveScheduleCursor, residualTask, parentTask,
              ScheduleCursor.frameOwners, ScheduleCursor.word,
              ScheduleAtom.closeOwner?] using hframe)
        have hpos : pre.length ≤ input.length := by
          rw [input_eq]
          simp
        let startState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hstart'
        let residualState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hresidualInv
        have hpop : ScheduleReaches g input startState residualState := by
          apply ScheduleReaches.single
          have hstep := composite_popLiveErase_at input head.relation head.mark
            continuation.edge (hlater hprotected) pre.length
            (alpha.map ScheduleAtom.workSym) (word.map ScheduleAtom.workSym)
          simpa [startState, residualState, scheduleStateOfCursor, ScheduleState.config,
            liveScheduleCursor, parentTask, residualTask, scheduleTaskOfParse,
            ScheduleCursor.erase, ScheduleAtom.workSym, ScheduleTask.workSym,
            List.map_append] using hstep
        cases startParkingContext with
        | strict below =>
            have residualParkingBelow : residualResources.tickets.ParkingBelow
                residualResources.window := by
              have hp := below.release head.owner hindices
              simpa [residualResources, residualTickets] using
                hp.transport_mono (List.Perm.refl _) (by rfl)
            have hrun := (ordinaryIH continuation.rest hcount).2 protectedFlags hidden
              blocks owners word used rfl hprotected hallRest hboundaryRest baseLayout
              compatibleRest pre post input_eq alpha hstable (by
                simpa [liveScheduleCursor, residualTask] using hresidualInv) hframesRest hend
              (by simpa [liveScheduleCursor, residualTask] using residualResources)
              (by simp [residualResources]) (by
                simpa [liveScheduleCursor, residualTask] using residualParkingBelow)
              residualOwnerLayout residualShadowLayout residualTicketOwnerLayout
              ⟨parkedBlocks, parkedOwners, rfl, rfl⟩ (by
                simpa [liveScheduleCursor, residualTask, residualTickets] using
                  hticketTransientResidualFree) (by rfl)
              (by simpa [liveScheduleCursor, residualTask] using htransientResidualFree)
              (by simpa [liveScheduleCursor, residualTask] using hscratchResidualFree)
            have hrun' : ScheduleReaches g input residualState
                (scheduleStateOfCursor (pre ++ w).length (by
                  rw [input_eq]
                  simp) (scheduleWordCursor alpha used) hend) := by
              simpa [residualState, residualTask, liveScheduleCursor,
                scheduleStateOfCursor] using hrun
            simpa [startState, scheduleStateOfCursor] using hpop.trans hrun'
        | attached restore =>
            rcases restore with
              ⟨marker, baseHead, parkingBound, markerLive, markerTicket,
                restoreTicket, restoreNonparking, restoreNotScratch,
                restoreNotTransient, restoreOutside, restoreAvailable,
                restoreDepth, restoreDepthLe, restoreAligned⟩
            rcases baseHead with
              ⟨baseHeadFlags, baseTailBlocks, baseTailOwners, rfl, rfl⟩
            have hheadNeMarker : head.owner ≠ marker := by
              intro heq
              apply (List.nodup_cons.mp hfullPhysicalNodup).1
              simp [heq]
            have residualOverlayParking : residualResources.tickets.OverlayParking
                residualResources.window marker := by
              have hp : resources'.tickets.OverlayParking resources'.window marker :=
                IndexTicketLedger.OverlayParking.ofParked parkingBound markerLive markerTicket
              have hp' := hp.release_ne head.owner hindices hheadNeMarker
              simpa [residualResources, residualTickets] using
                hp'.transport_mono (List.Perm.refl _) (by rfl)
            have htargetFresh : restoreTicket ∉
                (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexTickets
                  residualTickets.ticketOf := by
              rcases restoreAvailable with holdFresh | ⟨idx, hidx, hidxTicket⟩
              · exact resources'.tickets.release_preserves_fresh head.owner hindices holdFresh
              · have hidxEq : idx = head := by simpa using hidx
                subst idx
                simpa [hidxTicket] using
                  resources'.tickets.release_owner_ticket_fresh head.owner hindices
            have htargetOutside : OutsideProductiveWindow residualResources.window
                (IndexTicket.semanticOwner (g := g) restoreTicket) := by
              simpa [residualResources] using
                (EventOwnedFrames.outside_transport resources'.window hproductive
                  restoreOutside)
            have hdepthLe : restoreDepth ≤ head.flags.length := by
              simpa using restoreDepthLe
            have htargetShadow :
                (∃ hzero : 0 ∈ continuation.rest.eventDepths,
                  IndexTicket.semanticOwner (g := g) restoreTicket =
                    residualResources.window.shadowEventOwner 0 hzero) ∨
                OutsideShadowWindow residualResources.window
                  (IndexTicket.semanticOwner (g := g) restoreTicket) := by
              have hraw :
                  (∃ hzero : 0 ∈ continuation.rest.eventDepths,
                    IndexTicket.semanticOwner (g := g) restoreTicket =
                      (resources'.window.transport hproductive).shadowEventOwner 0 hzero) ∨
                  OutsideShadowWindow (resources'.window.transport hproductive)
                    (IndexTicket.semanticOwner (g := g) restoreTicket) := by
                rcases restoreAligned with ⟨hd, haligned⟩ | houtside
                · have hdepthGe : head.flags.length ≤ restoreDepth := by
                    have := hevents restoreDepth hd
                    omega
                  have hdepthEq : restoreDepth = head.flags.length := by omega
                  have hzero : 0 ∈ continuation.rest.eventDepths := by
                    apply (heventShift 0).2
                    simpa [hdepthEq] using hd
                  left
                  refine ⟨hzero, ?_⟩
                  rw [haligned]
                  apply Fin.ext
                  simp only [ProductiveOwnerWindow.shadowEventOwner_val,
                    ProductiveOwnerWindow.transport_base]
                  rw [hownerShift]
                  simp [hdepthEq]
                · exact Or.inr
                    (OutsideShadowWindow.transport resources'.window hproductive houtside)
              simpa [residualResources] using hraw
            have hbaseOwnersNodup : (marker :: baseTailOwners).Nodup :=
              (List.nodup_append.mp residualFullShadowOwnersNodup).1
            have hmarkerMem : marker ∈
                (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).indexOwners :=
              residualFullShadowOwnersSubset (by simp)
            have hmarkerFrameFresh : marker ∉
                (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) word).frameOwners := by
              intro hmem
              exact (List.disjoint_left.mp hframesRest)
                (show marker ∈ marker :: baseTailOwners by simp) (by
                simpa [liveScheduleCursor, residualTask] using hmem)
            have residualTicketShadowLayout : residualTickets.ShadowTicketLayout
                continuation.rest (resources'.window.transport hproductive)
                (baseHeadFlags :: baseTailBlocks) (marker :: baseTailOwners) := by
              have hfull : ShadowStartLayout continuation.rest
                  (resources'.window.transport hproductive)
                  ((baseHeadFlags :: baseTailBlocks) ++ parkedBlocks)
                  (residualTickets.semanticOwners (marker :: baseTailOwners) ++
                    residualTickets.semanticOwners parkedOwners) := by
                have hfull := residualFullShadowLayout
                change ShadowStartLayout continuation.rest
                  (resources'.window.transport hproductive)
                  ((baseHeadFlags :: baseTailBlocks) ++ parkedBlocks)
                  (residualTickets.semanticOwners
                    ((marker :: baseTailOwners) ++ parkedOwners)) at hfull
                simpa [IndexTicketLedger.semanticOwners, List.map_append] using hfull
              exact ShadowStartLayout.appendLeft hfull (by
                simpa [IndexTicketLedger.semanticOwners] using baseLayout.owners_length)
            have hactiveResidual : residualResources.ownerLedger.active =
                marker :: baseTailOwners := by rfl
            let restored := residualResources.restoreParkedActiveHead
              (head := marker) (block := baseHeadFlags)
              (blocks := baseTailBlocks) (owners := baseTailOwners)
              hactiveResidual hbaseOwnersNodup
              (by exact ⟨parkedBlocks, parkedOwners, rfl, rfl⟩)
              (by simpa [residualResources, residualTickets] using residualTicketOwnerLayout)
              (by simpa [residualResources, residualTickets] using
                residualTicketShadowLayout)
              hmarkerMem hmarkerFrameFresh hresidualInv.frameOwners_subset_indexOwners
              residualOverlayParking restoreTicket (by
                simpa [residualResources, residualTickets] using htargetFresh)
              restoreNotScratch restoreNotTransient restoreNonparking htargetOutside
              htargetShadow (by
                simpa [residualResources, residualTickets] using
                  hticketTransientResidualFree)
            let restoredResources := restored.resources
            have hrun := (ordinaryIH continuation.rest hcount).2 protectedFlags hidden
              (baseHeadFlags :: baseTailBlocks) (marker :: baseTailOwners)
              word used rfl hprotected hallRest hboundaryRest baseLayout compatibleRest pre post
              input_eq alpha hstable (by
                simpa [liveScheduleCursor, residualTask] using hresidualInv) hframesRest hend
              (by simpa [restoredResources, liveScheduleCursor, residualTask] using
                restoredResources)
              (by simp [restoredResources, ActiveHeadTicketRestoration.resources,
                residualResources])
              (by simpa [restoredResources] using restored.parkingBelow)
              (by simpa [restoredResources] using residualOwnerLayout)
              (by simpa [restoredResources] using residualShadowLayout)
              (by simpa [restoredResources] using restored.eventLayout)
              (by
                simpa [restoredResources] using
                  (show residualResources.TicketShadowContextExtends
                    (baseHeadFlags :: baseTailBlocks)
                    (marker :: baseTailOwners) from
                    ⟨parkedBlocks, parkedOwners, rfl, rfl⟩))
              (by simpa [restoredResources, liveScheduleCursor, residualTask] using
                restored.transient_fresh)
              (by simpa [restoredResources] using hactiveResidual)
              (by simpa [liveScheduleCursor, residualTask] using htransientResidualFree)
              (by simpa [liveScheduleCursor, residualTask] using hscratchResidualFree)
            have hrun' : ScheduleReaches g input residualState
                (scheduleStateOfCursor (pre ++ w).length (by
                  rw [input_eq]
                  simp) (scheduleWordCursor alpha used) hend) := by
              simpa [residualState, residualTask, liveScheduleCursor,
                scheduleStateOfCursor] using hrun
            simpa [startState, scheduleStateOfCursor] using hpop.trans hrun'
  | cons next overlayRest =>
      let lowerOverlay : List (ScheduleIndex g input) := next :: overlayRest
      let lowerFlags : List g.flag :=
        ScheduleOverlay.flags lowerOverlay protectedFlags
      let lowerBlocks : List (List g.flag) :=
        ScheduleOverlay.blocks lowerOverlay ++ blocks
      let lowerOwners : List (Fin (10 * input.length)) :=
        ScheduleOverlay.owners lowerOverlay owners
      let lowerWord : List (ScheduleAtom g input) :=
        ScheduleOverlay.word lowerOverlay word
      let lowerUsed : List (ScheduleAtom g input) :=
        ScheduleOverlay.used lowerOverlay used
      have lowerOverlayLayout : AdjacentOverlayLayout baseLayout lowerOverlay := by
        simpa [lowerOverlay] using overlayLayout.tail
      let lowerLayout : ScheduleBlockLayout g input lowerFlags lowerBlocks lowerOwners
          lowerWord lowerUsed := by
        simpa [lowerFlags, lowerBlocks, lowerOwners, lowerWord, lowerUsed] using
          lowerOverlayLayout.toProtected
      have howned : head.flags ≠ [] := overlayLayout.head_block_ne
      have lowerNonempty : lowerFlags ≠ [] := by
        intro hnil
        have hnextNil : next.flags = [] := by
          have hparts := List.append_eq_nil_iff.mp (by
            simpa [lowerFlags, lowerOverlay] using hnil)
          exact hparts.1
        exact lowerOverlayLayout.head_block_ne hnextNil
      have headLater : lowerFlags ≠ [] → head.mark.later = true := by
        intro _
        apply overlayLayout.head_later
        simpa [lowerFlags, lowerOverlay] using lowerNonempty
      have hstackHead : stack = head.flags ++ lowerFlags ++ hidden := by
        simpa [lowerFlags, lowerOverlay] using hstack
      clear hstack
      rw [List.append_assoc] at hstackHead
      subst stack
      have compatibleHead : EventCompatible parse (head.flags :: lowerBlocks) := by
        simpa [lowerBlocks, lowerOverlay] using compatible
      have hframesHead : List.Disjoint (head.owner :: lowerOwners)
          (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
            pre post input_eq alpha (.index head :: lowerWord)).frameOwners := by
        simpa [lowerOwners, lowerWord, lowerOverlay] using hframes
      have hstartHead : ScheduleInvariant
          (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
            pre post input_eq alpha (.index head :: lowerWord)) := by
        simpa [lowerWord, lowerOverlay] using hstart
      let startResources : ScheduleRunResources parse pre
          (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
            pre post input_eq alpha (.index head :: lowerWord)) := by
        simpa [lowerWord, lowerOverlay] using resources
      let startParkingContext : OverlayParkingContext startResources
          (head :: lowerOverlay) blocks owners := by
        simpa [startResources, lowerWord, lowerOverlay] using parkingContext
      have ownerLayoutHead : EventOwnedLayout parse startResources.window
          (head.flags :: lowerBlocks) (head.owner :: lowerOwners) := by
        simpa [startResources, lowerBlocks, lowerOwners, lowerOverlay] using ownerLayout
      have shadowLayoutHead : ShadowStartLayout parse startResources.window
          (head.flags :: lowerBlocks) (head.owner :: lowerOwners) := by
        simpa [startResources, lowerBlocks, lowerOwners, lowerOverlay] using shadowLayout
      have ticketOwnerLayoutHead : startResources.tickets.EventTicketLayout parse
          startResources.window (head.flags :: lowerBlocks)
            (head.owner :: lowerOwners) := by
        simpa [startResources, lowerBlocks, lowerOwners, lowerOverlay] using
          ticketOwnerLayout
      have ticketShadowLayoutHead : startResources.TicketShadowContextExtends
          (head.flags :: lowerBlocks) (head.owner :: lowerOwners) := by
        simpa [startResources, lowerBlocks, lowerOwners, lowerOverlay] using
          ticketShadowContext
      have hactiveHead : startResources.ownerLedger.active =
          head.owner :: lowerOwners := by
        simpa [startResources, lowerOwners, lowerOverlay] using hactive
      have ticketTransientHeadHead : ∀ hinput : 0 < input.length,
          IndexTicket.transient hinput ∈
              (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
                pre post input_eq alpha (.index head :: lowerWord)).indexTickets
                  startResources.tickets.ticketOf →
            startResources.tickets.ticketOf head.owner =
              IndexTicket.transient hinput := by
        simpa [startResources, lowerWord, lowerOverlay] using ticketTransientHead
      have transientHeadHead : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
              (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
                pre post input_eq alpha (.index head :: lowerWord)).indexOwners →
            head.owner = ProductiveOwnerWindow.transientOwner (g := g) hinput := by
        simpa [lowerWord, lowerOverlay] using transientHead
      have scratchHeadHead : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
              (liveScheduleCursor parse (hall 0 overlayLayout.flags_length_pos)
                pre post input_eq alpha (.index head :: lowerWord)).indexOwners →
            head.owner = ProductiveOwnerWindow.scratchOwner (g := g) hinput := by
        simpa [lowerWord, lowerOverlay] using scratchHead
      have hallHead : ∀ k < (head.flags ++ lowerFlags).length,
          parse.ConsumesAt k := by
        intro k hk
        apply hall
        simpa [lowerFlags, lowerOverlay] using hk
      have hboundaryHead : ¬ parse.ConsumesAt (head.flags ++ lowerFlags).length := by
        simpa [lowerFlags, lowerOverlay] using hboundary
      have hownedPos : 0 < head.flags.length := List.length_pos_of_ne_nil howned
      have hlast : parse.ConsumesAt (head.flags.length - 1) := by
        apply hallHead
        simp only [List.length_append]
        omega
      have hevents : ∀ d ∈ parse.eventDepths, head.flags.length - 1 < d := by
        intro d hd
        have hdpos := hpositive d hd
        have hfirst := BlockLayout.Boundary.first_length_le_of_pos howned
          (compatibleHead.boundary d hd) hdpos
        omega
      rcases exists_popContinuation_of_eventFree_block_with_owners
          (block := head.flags) (suffix := lowerFlags ++ hidden)
          parse head.denotes hlast hevents with
        ⟨continuation, hcount, hconsumes, heventShift, hownerShift⟩
      have hproductive : continuation.rest.productiveCount = parse.productiveCount := by
        rw [continuation.rest.productiveCount_eq_twice_yield_length_sub_one,
          parse.productiveCount_eq_twice_yield_length_sub_one]
      have compatibleRest : EventCompatible continuation.rest lowerBlocks :=
        EventCompatible.tailOfShift howned compatibleHead
          (fun d hd => (heventShift d).1 hd)
      have htailEndpointPos : ∀ i : Fin lowerBlocks.length,
          0 < blockEndpoint lowerBlocks i :=
        blockEndpoint_pos_of_blocks_nonempty lowerLayout.erase.blocks_nonempty
      have residualOwnerLayout : EventOwnedLayout continuation.rest
          (startResources.window.transport hproductive) lowerBlocks lowerOwners :=
        ownerLayoutHead.atomicPopTail compatibleRest htailEndpointPos hproductive
          heventShift hownerShift
      have residualShadowLayout : ShadowStartLayout continuation.rest
          (startResources.window.transport hproductive) lowerBlocks lowerOwners :=
        shadowLayoutHead.tail
          (fun candidate hout =>
            OutsideShadowWindow.transport startResources.window hproductive hout)
          (by
            intro i hd
            have hd' : blockStart lowerBlocks i ∈ continuation.rest.eventDepths :=
              (heventShift _).2 hd
            refine ⟨hd', ?_⟩
            apply Fin.ext
            simp only [ProductiveOwnerWindow.shadowEventOwner_val,
              ProductiveOwnerWindow.transport_base]
            rw [hownerShift])
      have houtsideShift : ∀ candidate,
          OutsideProductiveWindow startResources.window candidate →
            OutsideProductiveWindow (startResources.window.transport hproductive) candidate :=
        fun candidate hout =>
          EventOwnedFrames.outside_transport startResources.window hproductive hout
      have hframeOwnerShift :
          ∀ event : {d : ℕ // d ∈ parse.eventDepths},
            ∃ residualEvent : {d : ℕ // d ∈ continuation.rest.eventDepths},
              startResources.window.eventOwner event.val event.property =
                (startResources.window.transport hproductive).eventOwner
                  residualEvent.val residualEvent.property := by
        intro event
        have hge : head.flags.length ≤ event.val := by
          have := hevents event.val event.property
          omega
        let d := event.val - head.flags.length
        have heq : head.flags.length + d = event.val := by
          dsimp [d]
          omega
        have hd : d ∈ continuation.rest.eventDepths :=
          (heventShift d).2 (by simpa [heq] using event.property)
        refine ⟨⟨d, hd⟩, ?_⟩
        apply Fin.ext
        simp only [ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.transport_base]
        rw [hownerShift]
        simp only [heq]
      let parentUsed : parse.ConsumesAt 0 := hallHead 0 (by
        simp only [List.length_append]
        omega)
      let parentTask : ScheduleTask g input :=
        scheduleTaskOfParse parse pre post input_eq (.live parentUsed)
      have hownerEq (mode : TaskMode continuation.rest) :
          (scheduleTaskOfParse continuation.rest pre post input_eq mode).owner =
            parentTask.owner := by
        apply Fin.ext
        rfl
      have hunframed : head.owner ∉
          (liveScheduleCursor parse parentUsed pre post input_eq alpha
        (.index head :: lowerWord)).frameOwners := by
        intro hmem
        exact (List.disjoint_left.mp hframesHead) (by simp) hmem
      have hshadowActive : startResources.shadowLedger.active = head.owner :: lowerOwners :=
        startResources.shadow_active_eq.trans hactiveHead
      rcases ticketShadowLayoutHead with
        ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
      have hfullBlocks : startResources.ticketShadowBlocks =
          head.flags :: (lowerBlocks ++ parkedBlocks) := by
        simpa only [List.cons_append] using hcontextBlocks
      have hfullOwners : startResources.ticketShadowOwners =
          head.owner :: (lowerOwners ++ parkedOwners) := by
        simpa only [List.cons_append] using hcontextOwners
      have hfullPhysicalNodup :
          (head.owner :: (lowerOwners ++ parkedOwners)).Nodup := by
        have hnodup := startResources.ticketShadowOwners_nodup
        rw [hfullOwners] at hnodup
        exact hnodup
      have oldResidualFullShadowLayout : ShadowStartLayout continuation.rest
          (startResources.window.transport hproductive) (lowerBlocks ++ parkedBlocks)
            (startResources.tickets.semanticOwners (lowerOwners ++ parkedOwners)) := by
        have hfull := startResources.ticketShadowLayout
        rw [hfullBlocks, hfullOwners] at hfull
        exact hfull.tail
          (fun candidate hout =>
            OutsideShadowWindow.transport startResources.window hproductive hout)
          (by
            intro i hd
            have hd' : blockStart (lowerBlocks ++ parkedBlocks) i ∈
                continuation.rest.eventDepths := (heventShift _).2 hd
            refine ⟨hd', ?_⟩
            apply Fin.ext
            simp only [ProductiveOwnerWindow.shadowEventOwner_val,
              ProductiveOwnerWindow.transport_base]
            rw [hownerShift])
    
      have residualUsed : continuation.rest.ConsumesAt 0 := by
        have hp : parse.ConsumesAt head.flags.length := hallHead head.flags.length (by
          have := List.length_pos_of_ne_nil lowerNonempty
          simp only [List.length_append]
          omega)
        exact (hconsumes 0).2 (by simpa using hp)
      let residualTask : ScheduleTask g input :=
        scheduleTaskOfParse continuation.rest pre post input_eq (.live residualUsed)
      have hresidualInv : ScheduleInvariant
          ⟨alpha ++ [.dollar], .task residualTask, lowerWord⟩ := by
        apply ScheduleInvariant.popErase alpha lowerWord parentTask residualTask head
          (hownerEq (.live residualUsed)) hunframed
        simpa [liveScheduleCursor, parentTask] using hstart
      have hindices :
          (liveScheduleCursor parse parentUsed pre post input_eq alpha
            (.index head :: lowerWord)).indexOwners.Perm
            (head.owner ::
              (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).indexOwners) := by
        simp [liveScheduleCursor, ScheduleCursor.indexOwners,
          ScheduleCursor.word, ScheduleAtom.indexOwner?]
      have htasks :
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).taskOwners =
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: lowerWord)).taskOwners := by
        simp [liveScheduleCursor, ScheduleCursor.taskOwners,
          ScheduleCursor.word, ScheduleAtom.taskOwner?, residualTask, parentTask,
          hownerEq (.live residualUsed)]
      have hrightLedger :
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).right.filterMap
              ScheduleAtom.indexOwner? = lowerOwners ++ startResources.ownerLedger.outside := by
        have hright := startResources.ownerLedger.right_eq
        rw [hactiveHead] at hright
        simpa [liveScheduleCursor, ScheduleAtom.indexOwner?] using hright
      have hframeEq :
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).frameOwners =
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: lowerWord)).frameOwners := by
        simp [liveScheduleCursor, ScheduleCursor.frameOwners, ScheduleCursor.word,
          ScheduleAtom.closeOwner?, List.filterMap_append]
      have hsemanticFrames : EventOwnedFrames continuation.rest
          (startResources.window.transport hproductive)
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).frameOwners := by
        rw [hframeEq]
        apply startResources.ownerLedger.frames.transport
        intro candidate hcandidate
        rcases hcandidate with hout | ⟨event, howner⟩
        · exact Or.inl (houtsideShift candidate hout)
        · rcases hframeOwnerShift event with ⟨residualEvent, hshift⟩
          exact Or.inr ⟨residualEvent, howner.trans hshift⟩
      have hprefixLedger : PrefixFrameLedger
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord) :=
        startResources.ownerLedger.prefixLedger.transport (by rfl) (by rw [hframeEq])
      let residualLedger : ScheduleOwnerLedger continuation.rest
          (startResources.window.transport hproductive)
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord) :=
        startResources.ownerLedger.eraseHead
          (startResources.window.transport hproductive) hactiveHead hrightLedger
          (fun owner hmem => houtsideShift owner
            (startResources.ownerLedger.outside_at owner hmem))
          hsemanticFrames hprefixLedger
      have hrightShadow :
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).right.filterMap
              ScheduleAtom.indexOwner? = lowerOwners ++ startResources.shadowLedger.outside := by
        have hright := startResources.shadowLedger.right_eq
        rw [hshadowActive] at hright
        simpa [liveScheduleCursor, ScheduleAtom.indexOwner?] using hright
      have hshadowFrames : ShadowOwnedFrames continuation.rest
          (startResources.window.transport hproductive)
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).frameOwners := by
        rw [hframeEq]
        exact startResources.shadowLedger.frames.transportEqual hproductive
      let residualShadowLedger : ShadowOwnerLedger continuation.rest
          (startResources.window.transport hproductive)
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord) :=
        startResources.shadowLedger.eraseHead
          (startResources.window.transport hproductive) hshadowActive hrightShadow
          (fun owner hmem => OutsideShadowWindow.transport startResources.window hproductive
            (startResources.shadowLedger.outside_at owner hmem))
          hshadowFrames hprefixLedger
      let residualTickets := startResources.tickets.release head.owner hindices
      have hticketActive : startResources.ticketOwnerLedger.active =
          startResources.tickets.semanticOwnerOf head.owner ::
            startResources.tickets.semanticOwners lowerOwners := by
        rw [startResources.ticket_active_eq, hactiveHead]
        simp [IndexTicketLedger.semanticOwners]
      have hticketShadowActive : startResources.ticketShadowLedger.active =
          startResources.tickets.semanticOwnerOf head.owner ::
            startResources.tickets.semanticOwners (lowerOwners ++ parkedOwners) := by
        rw [startResources.ticket_shadow_active_eq, hfullOwners]
        simp [IndexTicketLedger.semanticOwners]
      have hrightTicket :
          residualTickets.semanticCursor.right.filterMap ScheduleAtom.indexOwner? =
            residualTickets.semanticOwners lowerOwners ++
              startResources.ticketOwnerLedger.outside := by
        have hright := startResources.ticketOwnerLedger.right_eq
        rw [hticketActive] at hright
        simpa [residualTickets, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf, IndexTicketLedger.semanticOwners,
          liveScheduleCursor, ScheduleCursor.relabelTicketOwners,
          ScheduleAtom.relabelTicketOwner, ScheduleAtom.indexOwner?] using hright
      have hticketFrameEq : residualTickets.semanticCursor.frameOwners =
          startResources.tickets.semanticCursor.frameOwners := by
        rw [IndexTicketLedger.semanticCursor_frameOwners,
          IndexTicketLedger.semanticCursor_frameOwners, hframeEq]
        simp [residualTickets]
      have hticketPrefix : PrefixFrameLedger residualTickets.semanticCursor :=
        startResources.ticketOwnerLedger.prefixLedger.transport
          (List.Perm.refl _)
          (by rw [hticketFrameEq])
      have hticketFrames : EventOwnedFrames continuation.rest
          (startResources.window.transport hproductive)
          residualTickets.semanticCursor.frameOwners := by
        rw [hticketFrameEq]
        apply startResources.ticketOwnerLedger.frames.transport
        intro candidate hcandidate
        rcases hcandidate with hout | ⟨event, howner⟩
        · exact Or.inl (houtsideShift candidate hout)
        · rcases hframeOwnerShift event with ⟨residualEvent, hshift⟩
          exact Or.inr ⟨residualEvent, howner.trans hshift⟩
      let residualTicketLedger : residualTickets.SemanticScheduleOwnerLedger
          continuation.rest (startResources.window.transport hproductive) :=
        startResources.ticketOwnerLedger.eraseHead
          (startResources.window.transport hproductive) hticketActive hrightTicket
          (fun owner hmem => houtsideShift owner
            (startResources.ticketOwnerLedger.outside_at owner hmem))
          hticketFrames hticketPrefix
      have hrightTicketShadow :
          residualTickets.semanticCursor.right.filterMap ScheduleAtom.indexOwner? =
            residualTickets.semanticOwners (lowerOwners ++ parkedOwners) ++
              startResources.ticketShadowLedger.outside := by
        have hright := startResources.ticketShadowLedger.right_eq
        rw [hticketShadowActive] at hright
        simpa [residualTickets, IndexTicketLedger.semanticCursor,
          IndexTicketLedger.semanticOwnerOf, IndexTicketLedger.semanticOwners,
          liveScheduleCursor, ScheduleCursor.relabelTicketOwners,
          ScheduleAtom.relabelTicketOwner, ScheduleAtom.indexOwner?] using hright
      have hticketShadowFrames : ShadowOwnedFrames continuation.rest
          (startResources.window.transport hproductive)
          residualTickets.semanticCursor.frameOwners := by
        rw [hticketFrameEq]
        exact startResources.ticketShadowLedger.frames.transportEqual hproductive
      let residualTicketShadowLedger : residualTickets.SemanticShadowOwnerLedger
          continuation.rest (startResources.window.transport hproductive) :=
        startResources.ticketShadowLedger.eraseHead
          (startResources.window.transport hproductive) hticketShadowActive
          hrightTicketShadow
          (fun owner hmem => OutsideShadowWindow.transport startResources.window hproductive
            (startResources.ticketShadowLedger.outside_at owner hmem))
          hticketShadowFrames hticketPrefix
      have oldResidualTicketOwnerLayout : EventOwnedLayout continuation.rest
          (startResources.window.transport hproductive) lowerBlocks
            (startResources.tickets.semanticOwners lowerOwners) :=
        ticketOwnerLayoutHead.atomicPopTail compatibleRest htailEndpointPos hproductive
          heventShift hownerShift
      have residualTicketOwnerLayout : residualTickets.EventTicketLayout
          continuation.rest (startResources.window.transport hproductive) lowerBlocks lowerOwners := by
        simpa [residualTickets] using oldResidualTicketOwnerLayout
      have residualFullShadowLayout : residualTickets.ShadowTicketLayout
          continuation.rest (startResources.window.transport hproductive)
            (lowerBlocks ++ parkedBlocks) (lowerOwners ++ parkedOwners) := by
        simpa [residualTickets] using oldResidualFullShadowLayout
      have residualFullShadowOwnersSubset : lowerOwners ++ parkedOwners ⊆
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).indexOwners := by
        intro candidate hcandidate
        have hcontext : candidate ∈ startResources.ticketShadowOwners := by
          rw [hfullOwners]
          exact List.mem_cons_of_mem head.owner hcandidate
        have hold := startResources.ticketShadowOwners_subset hcontext
        rcases List.mem_cons.mp (hindices.mem_iff.mp hold) with heq | hnew
        · subst candidate
          exact False.elim ((List.nodup_cons.mp hfullPhysicalNodup).1 hcandidate)
        · exact hnew
      have residualFullShadowOwnersNodup : (lowerOwners ++ parkedOwners).Nodup :=
        (List.nodup_cons.mp hfullPhysicalNodup).2
      have hticketTransientResidualFree : ∀ hinput : 0 < input.length,
          IndexTicket.transient hinput ∉
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).indexTickets
              residualTickets.ticketOf := by
        intro hinput hmem
        have hperm := hindices.map startResources.tickets.ticketOf
        have hmemOld : IndexTicket.transient hinput ∈
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: lowerWord)).indexTickets startResources.tickets.ticketOf := by
          rw [ScheduleCursor.indexTickets]
          apply hperm.mem_iff.mpr
          exact List.mem_cons_of_mem _ (by
            simpa [residualTickets, ScheduleCursor.indexTickets] using hmem)
        have hhead := ticketTransientHeadHead hinput hmemOld
        have hnodup := hperm.nodup_iff.mp startResources.tickets.tickets_nodup
        have htailFresh := (List.nodup_cons.mp hnodup).1
        apply htailFresh
        simpa [hhead, residualTickets, ScheduleCursor.indexTickets] using hmem
      have htransientResidualFree : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).indexOwners := by
        intro hinput hmem
        have holdMem : ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: lowerWord)).indexOwners :=
          hindices.mem_iff.mpr (List.mem_cons_of_mem head.owner hmem)
        have heq := transientHeadHead hinput holdMem
        have holdNodup :
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: lowerWord)).indexOwners.Nodup :=
          (List.nodup_append.mp startResources.pool.all_nodup).1
        have hnewNodup := hindices.nodup_iff.mp holdNodup
        exact (List.nodup_cons.mp hnewNodup).1 (by simpa [heq] using hmem)
      have hscratchResidualFree : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask) lowerWord).indexOwners := by
        intro hinput hmem
        have holdMem : ProductiveOwnerWindow.scratchOwner (g := g) hinput ∈
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: lowerWord)).indexOwners :=
          hindices.mem_iff.mpr (List.mem_cons_of_mem head.owner hmem)
        have heq := scratchHeadHead hinput holdMem
        have holdNodup :
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (.index head :: lowerWord)).indexOwners.Nodup :=
          (List.nodup_append.mp startResources.pool.all_nodup).1
        have hnewNodup := hindices.nodup_iff.mp holdNodup
        exact (List.nodup_cons.mp hnewNodup).1 (by simpa [heq] using hmem)
      let residualResources : ScheduleRunResources continuation.rest pre
          ⟨alpha ++ [.dollar], .task residualTask, lowerWord⟩ :=
        startResources.releaseOwned head.owner hindices htasks hproductive residualLedger
          residualTicketLedger (by rfl)
          (lowerBlocks ++ parkedBlocks) (lowerOwners ++ parkedOwners)
          residualFullShadowOwnersSubset residualFullShadowOwnersNodup
          residualTicketShadowLedger (by rfl) residualFullShadowLayout
          residualShadowLedger (by rfl) hcredit
      have residualCredit : 0 < residualResources.charged := by
        rw [residualResources.charged_eq_indices]
        simp [lowerWord, lowerOverlay, ScheduleCursor.indexOwners,
          ScheduleCursor.word, ScheduleAtom.indexOwner?]
        omega
      have hallRest : ∀ k < lowerFlags.length,
          continuation.rest.ConsumesAt k := by
        intro k hk
        apply (hconsumes k).2
        apply hallHead
        simp only [List.length_append]
        omega
      have hboundaryRest : ¬ continuation.rest.ConsumesAt lowerFlags.length := by
        intro hrest
        apply hboundaryHead
        simpa only [List.length_append] using (hconsumes lowerFlags.length).1 hrest
      have hframesRest : List.Disjoint lowerOwners
          (liveScheduleCursor continuation.rest residualUsed pre post input_eq alpha lowerWord).frameOwners := by
        apply List.disjoint_left.mpr
        intro owner howner hframe
        exact (List.disjoint_left.mp hframesHead) (List.mem_cons_of_mem _ howner) (by
          simpa [liveScheduleCursor, residualTask, parentTask,
            ScheduleCursor.frameOwners, ScheduleCursor.word,
            ScheduleAtom.closeOwner?] using hframe)
      have hpos : pre.length ≤ input.length := by
        rw [input_eq]
        simp
      let startState : ScheduleState g input :=
        scheduleStateOfCursor pre.length hpos _ hstart
      let residualState : ScheduleState g input :=
        scheduleStateOfCursor pre.length hpos _ hresidualInv
      have hpop : ScheduleReaches g input startState residualState := by
        apply ScheduleReaches.single
        have hstep := composite_popLiveErase_at input head.relation head.mark
          continuation.edge (headLater lowerNonempty) pre.length
          (alpha.map ScheduleAtom.workSym) (lowerWord.map ScheduleAtom.workSym)
        simpa [startState, residualState, scheduleStateOfCursor, ScheduleState.config,
          liveScheduleCursor, parentTask, residualTask, scheduleTaskOfParse,
          ScheduleCursor.erase, ScheduleAtom.workSym, ScheduleTask.workSym,
          List.map_append] using hstep
  
  
      have hallRestOverlay : ∀ k <
          (ScheduleOverlay.flags lowerOverlay protectedFlags).length,
          continuation.rest.ConsumesAt k := by
        simpa [lowerFlags] using hallRest
      have hboundaryRestOverlay : ¬ continuation.rest.ConsumesAt
          (ScheduleOverlay.flags lowerOverlay protectedFlags).length := by
        simpa [lowerFlags] using hboundaryRest
      have hframesRestOverlay : List.Disjoint
          (ScheduleOverlay.owners lowerOverlay owners)
          (liveScheduleCursor continuation.rest residualUsed pre post input_eq alpha
            (ScheduleOverlay.word lowerOverlay word)).frameOwners := by
        simpa [lowerOwners, lowerWord] using hframesRest
      have residualBaseLayout := baseLayout
      have residualOverlayLayout : AdjacentOverlayLayout residualBaseLayout lowerOverlay := by
        exact lowerOverlayLayout
      let residualParkingContext : OverlayParkingContext residualResources
          lowerOverlay blocks owners := by
        cases startParkingContext with
        | strict below =>
            apply OverlayParkingContext.strict
            have hp := below.release head.owner hindices
            simpa [residualResources, residualTickets] using
              hp.transport_mono (List.Perm.refl _) (by rfl)
        | attached restore =>
            rcases restore with
              ⟨marker, baseHead, parkingBound, markerLive, markerTicket,
                restoreTicket, restoreNonparking, restoreNotScratch,
                restoreNotTransient, restoreOutside, restoreAvailable,
                restoreDepth, restoreDepthLe, restoreAligned⟩
            have hmarkerBase : marker ∈ owners := by
              rcases baseHead with
                ⟨baseHeadFlags, baseTailBlocks, baseTailOwners,
                  hbaseBlocks, hbaseOwners⟩
              rw [hbaseOwners]
              simp
            have hmarkerLower : marker ∈ lowerOwners := by
              simpa [lowerOwners, ScheduleOverlay.owners] using
                (List.mem_append_right (lowerOverlay.map ScheduleIndex.owner) hmarkerBase)
            have hheadNeMarker : head.owner ≠ marker := by
              intro heq
              apply overlayLayout.head_fresh
              rw [heq]
              simpa [lowerOwners, lowerOverlay] using hmarkerLower
            have residualParkingBound : residualResources.tickets.ParkingAtOrBelow
                residualResources.window := by
              have hp := parkingBound.release head.owner hindices
              simpa [residualResources, residualTickets] using
                hp.transport_mono (List.Perm.refl _) (by rfl)
            have residualMarkerLive : marker ∈
                (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask)
                  lowerWord).indexOwners := by
              have hclass := hindices.mem_iff.mp markerLive
              rcases List.mem_cons.mp hclass with heq | hmem
              · exact False.elim (hheadNeMarker heq.symm)
              · exact hmem
            have residualMarkerTicket : residualTickets.ticketOf marker =
                (startResources.window.transport hproductive).parkingTicket := by
              simpa [residualTickets] using markerTicket
            have residualRestoreOutside : OutsideProductiveWindow
                (startResources.window.transport hproductive)
                (IndexTicket.semanticOwner (g := g) restoreTicket) :=
              EventOwnedFrames.outside_transport startResources.window hproductive
                restoreOutside
            have residualAvailable :
                restoreTicket ∉
                    (ScheduleCursor.mk (alpha ++ [.dollar]) (.task residualTask)
                      lowerWord).indexTickets residualTickets.ticketOf ∨
                  ∃ idx ∈ lowerOverlay,
                    residualTickets.ticketOf idx.owner = restoreTicket := by
              rcases restoreAvailable with holdFresh | ⟨idx, hidx, hidxTicket⟩
              · exact Or.inl
                  (startResources.tickets.release_preserves_fresh
                    head.owner hindices holdFresh)
              · rcases List.mem_cons.mp hidx with hidxHead | hidxLower
                · subst idx
                  left
                  simpa [hidxTicket] using
                    startResources.tickets.release_owner_ticket_fresh head.owner hindices
                · right
                  exact ⟨idx, hidxLower, by simpa [residualTickets] using hidxTicket⟩
            have residualDepthLe : restoreDepth - head.flags.length ≤
                (ScheduleOverlay.flags lowerOverlay []).length := by
              have hold : restoreDepth ≤
                  head.flags.length + (ScheduleOverlay.flags lowerOverlay []).length := by
                simpa only [ScheduleOverlay.flags_cons, List.length_append] using
                  restoreDepthLe
              omega
            have residualAligned :
                (∃ hd : restoreDepth - head.flags.length ∈
                    continuation.rest.eventDepths,
                  IndexTicket.semanticOwner (g := g) restoreTicket =
                    (startResources.window.transport hproductive).shadowEventOwner
                      (restoreDepth - head.flags.length) hd) ∨
                OutsideShadowWindow (startResources.window.transport hproductive)
                  (IndexTicket.semanticOwner (g := g) restoreTicket) := by
              rcases restoreAligned with ⟨hd, haligned⟩ | houtside
              · have hdepthGe : head.flags.length ≤ restoreDepth := by
                  have := hevents restoreDepth hd
                  omega
                have hsum : head.flags.length +
                    (restoreDepth - head.flags.length) = restoreDepth := by omega
                have hresidualDepth : restoreDepth - head.flags.length ∈
                    continuation.rest.eventDepths := by
                  apply (heventShift _).2
                  simpa [hsum] using hd
                left
                refine ⟨hresidualDepth, ?_⟩
                rw [haligned]
                apply Fin.ext
                simp only [ProductiveOwnerWindow.shadowEventOwner_val,
                  ProductiveOwnerWindow.transport_base]
                rw [hownerShift]
                simp only [hsum]
              · exact Or.inr
                  (OutsideShadowWindow.transport startResources.window hproductive houtside)
            apply OverlayParkingContext.attached
            exact {
              marker := marker
              base_head := baseHead
              parkingAtOrBelow := by
                simpa [residualResources, residualTickets] using residualParkingBound
              marker_live := by
                simpa [residualResources] using residualMarkerLive
              marker_ticket := by
                simpa [residualResources, residualTickets] using residualMarkerTicket
              restore := restoreTicket
              restore_nonparking := restoreNonparking
              restore_not_scratch := restoreNotScratch
              restore_not_transient := restoreNotTransient
              restore_outside_primary := by
                simpa [residualResources] using residualRestoreOutside
              available := by
                simpa [residualResources, residualTickets] using residualAvailable
              depth := restoreDepth - head.flags.length
              depth_le := residualDepthLe
              aligned := by
                simpa [residualResources] using residualAligned
            }
      have hrun := overlayIH continuation.rest hcount next overlayRest protectedFlags
        hidden blocks owners word used rfl residualBaseLayout residualOverlayLayout
        hallRestOverlay hboundaryRestOverlay (by
          simpa [lowerBlocks, lowerOverlay] using compatibleRest) hused pre post input_eq
        alpha hstable (by
          simpa [lowerWord, lowerOverlay, liveScheduleCursor, residualTask] using hresidualInv)
        hframesRestOverlay hend
        (by simpa [lowerWord, lowerOverlay, liveScheduleCursor, residualTask] using
          residualResources)
        (by simpa [lowerWord, lowerOverlay, liveScheduleCursor, residualTask] using
          residualParkingContext)
        (by
          have hrelease := ScheduleRunResources.releaseOwned_free
            (resources := startResources) head.owner hindices htasks hproductive
              residualLedger residualTicketLedger (by rfl)
              (lowerBlocks ++ parkedBlocks) (lowerOwners ++ parkedOwners)
              residualFullShadowOwnersSubset residualFullShadowOwnersNodup
              residualTicketShadowLedger (by rfl) residualFullShadowLayout
              residualShadowLedger (by rfl) hcredit
          simpa [residualResources] using hrelease)
        (by simpa [residualResources] using residualCredit)
        residualOwnerLayout residualShadowLayout residualTicketOwnerLayout
        ⟨parkedBlocks, parkedOwners, rfl, rfl⟩
        (by
          intro hinput hmem
          exfalso
          apply hticketTransientResidualFree hinput
          simpa [lowerWord, lowerOverlay, liveScheduleCursor, residualTask,
            residualResources, residualTickets] using hmem)
        (by rfl)
        (by
          intro hinput hmem
          exfalso
          apply htransientResidualFree hinput
          simpa [lowerWord, lowerOverlay, liveScheduleCursor, residualTask] using hmem)
        (by
          intro hinput hmem
          exfalso
          apply hscratchResidualFree hinput
          simpa [lowerWord, lowerOverlay, liveScheduleCursor, residualTask] using hmem)
      have hrun' : ScheduleReaches g input residualState
          (scheduleStateOfCursor (pre ++ w).length (by
            rw [input_eq]
            simp) (scheduleWordCursor alpha used) hend) := by
        simpa [residualState, residualTask, lowerWord, lowerOverlay,
          liveScheduleCursor, scheduleStateOfCursor] using hrun
      simpa [startState, hstartHead, scheduleStateOfCursor] using hpop.trans hrun'

end Aho
end IndexedGrammar

end
