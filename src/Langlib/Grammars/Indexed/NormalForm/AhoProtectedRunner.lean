module

public import Langlib.Grammars.Indexed.NormalForm.AhoEventCompatibility
public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleMoves
public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleResources
public import Langlib.Grammars.Indexed.NormalForm.AhoPushOwnerFreshness
public import Langlib.Grammars.Indexed.NormalForm.AhoTicketSeal
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayMode

@[expose]
public section

/-!
# Atomic protected-block execution

A protected task whose current parse has no productive event at depth zero may consume its
entire first represented block at once.  The exact continuation transport then supplies a
strictly smaller residual parse; opening and closing the corresponding scheduler frame preserves
both the ghost ownership invariant and the resource credit equality.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- A nonempty concrete layout prefix exposes at least one input atom. -/
public theorem ScheduleBlockLayout.input_ne_nil_of_flags_ne
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used)
    (hne : flags ≠ []) : word ≠ [] := by
  induction layout with
  | nil tail => exact False.elim (hne rfl)
  | cons idx block_ne hindex hdollar hlater fresh rest ih =>
      intro hnil
      have hlength := congrArg List.length hnil
      simp at hlength

/-- Marking the selected blocks of a nonempty layout likewise leaves a nonempty output word. -/
public theorem ScheduleBlockLayout.output_ne_nil_of_flags_ne
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used)
    (hne : flags ≠ []) : used ≠ [] := by
  induction layout with
  | nil tail => exact False.elim (hne rfl)
  | cons idx block_ne hindex hdollar hlater fresh rest ih =>
      intro hnil
      have hlength := congrArg List.length hnil
      simp at hlength

/-- Reassemble the complete cursor owner ledger after the first active block becomes an open
frame.  Runner-specific zipper arithmetic is confined to the four supplied transport facts. -/
private def ScheduleOwnerLedger.openHead
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

/-- Reassemble the shadow ledger after the first active block becomes an open frame. -/
private def ShadowOwnerLedger.openHead
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

/-- Transport runner resources across a cursor change which preserves persistent indices and
task owners, and across a residual parse with the same productive count. -/
private def ScheduleRunResources.transportAtomicPop
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack residualStack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B residualStack w}
    {pre : List T} {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old)
    (hindices : new.indexOwners = old.indexOwners)
    (htasks : new.taskOwners.Perm old.taskOwners)
    (hproductive : residual.productiveCount = parse.productiveCount)
    (ownerLedger : ScheduleOwnerLedger residual
      (resources.window.transport hproductive) new)
    (tickets : IndexTicketLedger new)
    (parkingAtOrBelow : tickets.ParkingAtOrBelow
      (resources.window.transport hproductive))
    (ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger residual
      (resources.window.transport hproductive))
    (ticket_active_eq : ticketOwnerLedger.active =
      tickets.semanticOwners ownerLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ new.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger : tickets.SemanticShadowOwnerLedger residual
      (resources.window.transport hproductive))
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      tickets.semanticOwners ticketShadowOwners)
    (ticketShadowLayout : tickets.ShadowTicketLayout residual
      (resources.window.transport hproductive) ticketShadowBlocks ticketShadowOwners)
    (shadowLedger : ShadowOwnerLedger residual
      (resources.window.transport hproductive) new)
    (shadow_active_eq : shadowLedger.active = ownerLedger.active) :
    ScheduleRunResources residual pre new where
  pool := {
    free := resources.pool.free
    all_nodup := by simpa [hindices] using resources.pool.all_nodup
    all_perm := by simpa [hindices] using resources.pool.all_perm }
  window := resources.window.transport hproductive
  parkingAtOrBelow := parkingAtOrBelow
  ownerLedger := ownerLedger
  tickets := tickets
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
  charged := resources.charged
  charged_eq_indices := by simpa [hindices] using resources.charged_eq_indices
  charged_le_indices := by simpa [hindices] using resources.charged_le_indices
  productive_le_credit := by
    rw [hproductive]
    exact resources.productive_le_credit
  task_locality := by
    intro owner howner
    apply resources.task_locality owner
    exact htasks.mem_iff.mp howner

@[simp] private theorem ScheduleRunResources.transportAtomicPop_charged
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack residualStack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B residualStack w}
    {pre : List T} {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old)
    (hindices : new.indexOwners = old.indexOwners)
    (htasks : new.taskOwners.Perm old.taskOwners)
    (hproductive : residual.productiveCount = parse.productiveCount)
    (ownerLedger : ScheduleOwnerLedger residual
      (resources.window.transport hproductive) new)
    (tickets : IndexTicketLedger new)
    (parkingAtOrBelow : tickets.ParkingAtOrBelow
      (resources.window.transport hproductive))
    (ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger residual
      (resources.window.transport hproductive))
    (ticket_active_eq : ticketOwnerLedger.active =
      tickets.semanticOwners ownerLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ new.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger : tickets.SemanticShadowOwnerLedger residual
      (resources.window.transport hproductive))
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      tickets.semanticOwners ticketShadowOwners)
    (ticketShadowLayout : tickets.ShadowTicketLayout residual
      (resources.window.transport hproductive) ticketShadowBlocks ticketShadowOwners)
    (shadowLedger : ShadowOwnerLedger residual
      (resources.window.transport hproductive) new)
    (shadow_active_eq : shadowLedger.active = ownerLedger.active) :
    (resources.transportAtomicPop hindices htasks hproductive ownerLedger tickets
      parkingAtOrBelow
      ticketOwnerLedger ticket_active_eq ticketShadowBlocks ticketShadowOwners
      ticketShadowOwners_subset ticketShadowOwners_nodup ticketShadowLedger
      ticket_shadow_active_eq ticketShadowLayout shadowLedger shadow_active_eq).charged =
      resources.charged := rfl

@[simp] private theorem ScheduleRunResources.transportAtomicPop_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack residualStack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B residualStack w}
    {pre : List T} {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old)
    (hindices : new.indexOwners = old.indexOwners)
    (htasks : new.taskOwners.Perm old.taskOwners)
    (hproductive : residual.productiveCount = parse.productiveCount)
    (ownerLedger : ScheduleOwnerLedger residual
      (resources.window.transport hproductive) new)
    (tickets : IndexTicketLedger new)
    (parkingAtOrBelow : tickets.ParkingAtOrBelow
      (resources.window.transport hproductive))
    (ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger residual
      (resources.window.transport hproductive))
    (ticket_active_eq : ticketOwnerLedger.active =
      tickets.semanticOwners ownerLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ new.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger : tickets.SemanticShadowOwnerLedger residual
      (resources.window.transport hproductive))
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      tickets.semanticOwners ticketShadowOwners)
    (ticketShadowLayout : tickets.ShadowTicketLayout residual
      (resources.window.transport hproductive) ticketShadowBlocks ticketShadowOwners)
    (shadowLedger : ShadowOwnerLedger residual
      (resources.window.transport hproductive) new)
    (shadow_active_eq : shadowLedger.active = ownerLedger.active) :
    (resources.transportAtomicPop hindices htasks hproductive ownerLedger tickets
      parkingAtOrBelow
      ticketOwnerLedger ticket_active_eq ticketShadowBlocks ticketShadowOwners
      ticketShadowOwners_subset ticketShadowOwners_nodup ticketShadowLedger
      ticket_shadow_active_eq ticketShadowLayout shadowLedger shadow_active_eq).pool.free =
      resources.pool.free := rfl

/-- Execute the first protected block whenever depth zero is not a productive event.  This is
the common protected-mode step used after structural pops (and after unary normalization): it
does not depend on the syntactic constructor at the root of the parse. -/
public theorem protectedScheduleRun_atomicPop
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (hpositive : ∀ d ∈ parse.eventDepths, 0 < d)
    (ih : ∀ {B : g.nt} {residualStack : List g.flag}
      (residual : NFParse g B residualStack w),
      residual.nodeCount < parse.nodeCount → OrdinaryScheduleRuns residual) :
    ProtectedScheduleRun parse := by
  intro input visible hidden blocks owners word used hstack hne hall hboundary
    layout compatible pre post input_eq alpha hstable hstart hframes hend
    resources hcredit parkingBelow ownerLayout shadowLayout ticketOwnerLayout
    ticketShadowContext ticketTransientFree hactive transientFree scratchFree
  cases layout with
  | nil tail => exact False.elim (hne rfl)
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh restLayout =>
      rw [List.append_assoc] at hstack
      subst stack
      rcases ticketShadowContext with
        ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
      have hblockPos : 0 < idx.flags.length := List.length_pos_of_ne_nil block_ne
      have hlast : parse.ConsumesAt (idx.flags.length - 1) := by
        apply hall
        simp only [List.length_append]
        omega
      have hevents : ∀ d ∈ parse.eventDepths, idx.flags.length - 1 < d := by
        intro d hd
        have hdpos := hpositive d hd
        have hfirst := BlockLayout.Boundary.first_length_le_of_pos block_ne
          (compatible.boundary d hd) hdpos
        omega
      rcases exists_popContinuation_of_eventFree_block_with_owners
          parse idx.denotes hlast hevents with
        ⟨continuation, hcount, hconsumes, heventShift, hownerShift⟩
      have hproductive : continuation.rest.productiveCount = parse.productiveCount := by
        rw [continuation.rest.productiveCount_eq_twice_yield_length_sub_one,
          parse.productiveCount_eq_twice_yield_length_sub_one]
      have compatibleRest : EventCompatible continuation.rest blocks :=
        EventCompatible.tailOfShift block_ne compatible
          (fun d hd => (heventShift d).1 hd)
      have htailEndpointPos : ∀ i : Fin blocks.length,
          0 < blockEndpoint blocks i :=
        blockEndpoint_pos_of_blocks_nonempty restLayout.erase.blocks_nonempty
      have residualOwnerLayout : EventOwnedLayout continuation.rest
          (resources.window.transport hproductive) blocks owners :=
        ownerLayout.atomicPopTail compatibleRest htailEndpointPos hproductive
          heventShift hownerShift
      have residualShadowLayout : ShadowStartLayout continuation.rest
          (resources.window.transport hproductive) blocks owners :=
        shadowLayout.tail
          (fun candidate hout =>
            OutsideShadowWindow.transport resources.window hproductive hout)
          (by
            intro i hd
            have hd' : blockStart blocks i ∈ continuation.rest.eventDepths :=
              (heventShift _).2 hd
            refine ⟨hd', ?_⟩
            apply Fin.ext
            simp only [ProductiveOwnerWindow.shadowEventOwner_val,
              ProductiveOwnerWindow.transport_base]
            rw [hownerShift])
      have hticketActive : resources.ticketOwnerLedger.active =
          resources.tickets.semanticOwners (idx.owner :: owners) :=
        resources.ticket_active_eq.trans
          (congrArg resources.tickets.semanticOwners hactive)
      have hticketShadowActive : resources.ticketShadowLedger.active =
          resources.tickets.semanticOwners
            (idx.owner :: (owners ++ parkedOwners)) := by
        rw [resources.ticket_shadow_active_eq, hcontextOwners]
        rfl
      have fullTicketShadowLayout : resources.tickets.ShadowTicketLayout parse
          resources.window (idx.flags :: (blocks ++ parkedBlocks))
            (idx.owner :: (owners ++ parkedOwners)) := by
        have hold := resources.ticketShadowLayout
        rw [hcontextBlocks, hcontextOwners] at hold
        simpa only [List.cons_append] using hold
      have hticketHeadShadowOutside : OutsideShadowWindow resources.window
          (resources.tickets.semanticOwnerOf idx.owner) := by
        let i : Fin (idx.flags :: (blocks ++ parkedBlocks)).length := ⟨0, by simp⟩
        rcases fullTicketShadowLayout.owner_at i with hlocal | hout
        · rcases hlocal with ⟨hd, _⟩
          have : 0 < 0 := hpositive 0 (by simpa [i, blockStart] using hd)
          omega
        · simpa [i, blockOwnerAt, IndexTicketLedger.semanticOwners] using hout
      have oldResidualTicketOwnerLayout : EventOwnedLayout continuation.rest
          (resources.window.transport hproductive) blocks
            (resources.tickets.semanticOwners owners) :=
        ticketOwnerLayout.atomicPopTail compatibleRest htailEndpointPos hproductive
          heventShift hownerShift
      have oldResidualTicketShadowLayout : ShadowStartLayout continuation.rest
          (resources.window.transport hproductive) (blocks ++ parkedBlocks)
            (resources.tickets.semanticOwners (owners ++ parkedOwners)) :=
        fullTicketShadowLayout.tail
          (fun candidate hout =>
            OutsideShadowWindow.transport resources.window hproductive hout)
          (by
            intro i hd
            have hd' : blockStart (blocks ++ parkedBlocks) i ∈
                continuation.rest.eventDepths := (heventShift _).2 hd
            refine ⟨hd', ?_⟩
            apply Fin.ext
            simp only [ProductiveOwnerWindow.shadowEventOwner_val,
              ProductiveOwnerWindow.transport_base]
            rw [hownerShift])
      have hshadowActive : resources.shadowLedger.active = idx.owner :: owners :=
        resources.shadow_active_eq.trans hactive
      have hheadShadowOutside : OutsideShadowWindow resources.window idx.owner := by
        let i : Fin (idx.flags :: blocks).length := ⟨0, by simp⟩
        rcases shadowLayout.owner_at i with hlocal | hout
        · rcases hlocal with ⟨hd, _⟩
          have : 0 < 0 := hpositive 0 (by simpa [i, blockStart] using hd)
          omega
        · simpa [i, blockOwnerAt] using hout
      have houtsideShift : ∀ candidate,
          OutsideProductiveWindow resources.window candidate →
            OutsideProductiveWindow (resources.window.transport hproductive) candidate :=
        fun candidate hout =>
          EventOwnedFrames.outside_transport resources.window hproductive hout
      have hheadOwnerShift : ∀ hd : idx.flags.length ∈ parse.eventDepths,
          ∃ hd0 : 0 ∈ continuation.rest.eventDepths,
            resources.window.eventOwner idx.flags.length hd =
              (resources.window.transport hproductive).eventOwner 0 hd0 := by
        intro hd
        have hd0 : 0 ∈ continuation.rest.eventDepths :=
          (heventShift 0).2 (by simpa using hd)
        refine ⟨hd0, ?_⟩
        apply Fin.ext
        simp only [ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.transport_base]
        rw [hownerShift]
        simp
      have hframeOwnerShift :
          ∀ event : {d : ℕ // d ∈ parse.eventDepths},
            ∃ residualEvent : {d : ℕ // d ∈ continuation.rest.eventDepths},
              resources.window.eventOwner event.val event.property =
                (resources.window.transport hproductive).eventOwner
                  residualEvent.val residualEvent.property := by
        intro event
        have hge : idx.flags.length ≤ event.val := by
          have := hevents event.val event.property
          omega
        let d := event.val - idx.flags.length
        have heq : idx.flags.length + d = event.val := by
          dsimp [d]
          omega
        have hd : d ∈ continuation.rest.eventDepths :=
          (heventShift d).2 (by simp [heq])
        refine ⟨⟨d, hd⟩, ?_⟩
        apply Fin.ext
        simp only [ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.transport_base]
        rw [hownerShift]
        simp only [heq]
      let parentUsed : parse.ConsumesAt 0 := hall 0 (by
        simp only [List.length_append]
        omega)
      let parentTask : ScheduleTask g input :=
        scheduleTaskOfParse parse pre post input_eq (.live parentUsed)
      let selected : ScheduleAtom g input := .index idx.markUsed
      let innerAlpha : List (ScheduleAtom g input) :=
        alpha ++ [ScheduleAtom.dollar] ++ beta ++ [selected]
      have hinnerStable : StablePrefix (innerAlpha.map ScheduleAtom.workSym) := by
        dsimp [innerAlpha, selected]
        rw [List.map_append]
        change StablePrefix
          (((alpha ++ [ScheduleAtom.dollar] ++ beta).map ScheduleAtom.workSym) ++
            [WorkSym.index idx.relation idx.mark.markUsed])
        exact stablePrefix_append_usedIndex
          ((alpha ++ [ScheduleAtom.dollar] ++ beta).map ScheduleAtom.workSym)
          idx.relation idx.mark
      have hframeFresh : idx.owner ∉
          (liveScheduleCursor parse parentUsed pre post input_eq alpha
            (beta ++ .index idx :: tail)).frameOwners := by
        intro hmem
        exact hframes (by simp) hmem
      by_cases hflags : flags = []
      · subst flags
        have hownersNil : owners = [] := by
          have hblocksNil : blocks = [] :=
            restLayout.erase.blocks_eq_nil_of_flags_eq_nil rfl
          have hlength := restLayout.owners_length
          rw [hblocksNil] at hlength
          exact List.length_eq_zero_iff.mp (by simpa using hlength)
        have hunused : ¬ continuation.rest.ConsumesAt 0 := by
          intro hused
          apply hboundary
          have := (hconsumes 0).1 hused
          simpa using this
        let residualTask : ScheduleTask g input :=
          scheduleTaskOfParse continuation.rest pre post input_eq (.plain hunused)
        have htaskOwner : residualTask.owner = parentTask.owner := by
          apply Fin.ext
          rfl
        have hinsideStart : ScheduleInvariant
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail) := by
          have hpop := ScheduleInvariant.popFrame alpha beta tail parentTask residualTask idx
            htaskOwner hframeFresh (by
              simpa [liveScheduleCursor, parentTask] using hstart)
          simpa [plainScheduleCursor, innerAlpha, selected, residualTask,
            List.append_assoc] using hpop
        have htail : tail = tail' := restLayout.word_eq_used_of_flags_eq_nil rfl
        subst tail'
        have hindices :
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).indexOwners =
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (beta ++ .index idx :: tail)).indexOwners := by
          simp [plainScheduleCursor, liveScheduleCursor, innerAlpha, selected,
            ScheduleCursor.indexOwners, ScheduleCursor.word,
            ScheduleAtom.indexOwner?, List.filterMap_append, List.append_assoc]
        have htasks :
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).taskOwners.Perm
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (beta ++ .index idx :: tail)).taskOwners := by
          simp only [plainScheduleCursor, liveScheduleCursor,
            ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?,
            List.filterMap_cons, List.filterMap_nil, List.append_nil,
            List.filterMap_append, innerAlpha, selected]
          rw [htaskOwner]
          simpa only [List.append_assoc] using
            List.Perm.append_left (alpha.filterMap ScheduleAtom.taskOwner?)
              (List.perm_middle
                (l₁ := beta.filterMap ScheduleAtom.taskOwner?)
                (l₂ := tail.filterMap ScheduleAtom.taskOwner?)
                (a := parentTask.owner))
        have hrightLedger :
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).right.filterMap
                ScheduleAtom.indexOwner? =
              owners ++ resources.ownerLedger.outside := by
          have hright := resources.ownerLedger.right_eq
          rw [hactive] at hright
          simpa [plainScheduleCursor, liveScheduleCursor,
            hindex.filterMap_indexOwner_eq_nil, ScheduleAtom.indexOwner?,
            List.filterMap_append] using hright
        have hframePerm :
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).frameOwners.Perm
              (idx.owner ::
                (liveScheduleCursor parse parentUsed pre post input_eq alpha
                  (beta ++ .index idx :: tail)).frameOwners) := by
          simpa [plainScheduleCursor, liveScheduleCursor, innerAlpha, selected,
            ScheduleCursor.frameOwners, ScheduleCursor.word,
            ScheduleAtom.closeOwner?, List.filterMap_append,
            List.append_assoc] using
            (List.perm_middle
              (l₁ := alpha.filterMap ScheduleAtom.closeOwner? ++
                beta.filterMap ScheduleAtom.closeOwner?)
              (l₂ := tail.filterMap ScheduleAtom.closeOwner?)
              (a := idx.owner))
        have hsemanticFrames : EventOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).frameOwners := by
          have hopened := resources.ownerLedger.frames.atomicPop ownerLayout
            houtsideShift hheadOwnerShift hframeOwnerShift
          exact hopened.perm hframePerm
        have hprefixInsert :
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).left.filterMap
                ScheduleAtom.indexOwner? |>.Perm
              (idx.owner ::
                (liveScheduleCursor parse parentUsed pre post input_eq alpha
                  (beta ++ .index idx :: tail)).left.filterMap
                    ScheduleAtom.indexOwner?) := by
          simp [plainScheduleCursor, liveScheduleCursor, innerAlpha, selected,
            hindex.filterMap_indexOwner_eq_nil, ScheduleAtom.indexOwner?,
            List.filterMap_append]
        have hprefixLedger : PrefixFrameLedger
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail) := by
          apply resources.ownerLedger.prefixLedger.insert idx.owner
          · exact hprefixInsert
          · exact hframePerm
        let residualLedger : ScheduleOwnerLedger continuation.rest
            (resources.window.transport hproductive)
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail) :=
          resources.ownerLedger.openHead
            (resources.window.transport hproductive) hactive hrightLedger
            (fun owner hmem => houtsideShift owner
              (resources.ownerLedger.outside_at owner hmem))
            hsemanticFrames hprefixLedger
        let residualTickets : IndexTicketLedger
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail) :=
          resources.tickets.transport (by rw [hindices])
        have residualParkingBelow : residualTickets.ParkingBelow
            (resources.window.transport hproductive) := by
          exact parkingBelow.transport_mono
            (hindices ▸ List.Perm.refl _) (by simp)
        have hticketFramePerm : residualTickets.semanticCursor.frameOwners.Perm
            (resources.tickets.semanticOwnerOf idx.owner ::
              resources.tickets.semanticCursor.frameOwners) := by
          rw [residualTickets.semanticCursor_frameOwners,
            resources.tickets.semanticCursor_frameOwners]
          simpa [residualTickets] using
            hframePerm.map resources.tickets.semanticOwnerOf
        let residualTicketPrefixLedger :
            PrefixFrameLedger residualTickets.semanticCursor :=
          resources.ticketOwnerLedger.prefixLedger.insert
            (resources.tickets.semanticOwnerOf idx.owner)
            (by
              change
                (((plainScheduleCursor continuation.rest hunused pre post input_eq
                    innerAlpha (.close idx.owner) tail).left.map
                    (ScheduleAtom.relabelTicketOwner
                      residualTickets.semanticOwnerOf)).filterMap
                    ScheduleAtom.indexOwner?).Perm
                  (resources.tickets.semanticOwnerOf idx.owner ::
                    (((liveScheduleCursor parse parentUsed pre post input_eq alpha
                      (beta ++ .index idx :: tail)).left.map
                      (ScheduleAtom.relabelTicketOwner
                        resources.tickets.semanticOwnerOf)).filterMap
                      ScheduleAtom.indexOwner?))
              rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner,
                ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
              have hfun : residualTickets.semanticOwnerOf =
                  resources.tickets.semanticOwnerOf := by
                funext owner
                rfl
              rw [hfun]
              exact hprefixInsert.map resources.tickets.semanticOwnerOf)
            hticketFramePerm
        have hrightTicket :
            residualTickets.semanticCursor.right.filterMap
                ScheduleAtom.indexOwner? =
              residualTickets.semanticOwners owners ++
                resources.ticketOwnerLedger.outside := by
          have hright := resources.ticketOwnerLedger.right_eq
          rw [hticketActive] at hright
          rw [residualTickets.semanticCursor_right_indexOwners]
          rw [resources.tickets.semanticCursor_right_indexOwners] at hright
          simpa [residualTickets, IndexTicketLedger.semanticOwners,
            plainScheduleCursor, liveScheduleCursor,
            hindex.filterMap_indexOwner_eq_nil, ScheduleAtom.indexOwner?,
            List.filterMap_append] using hright
        have hticketSemanticFrames : EventOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          have hopened := resources.ticketOwnerLedger.frames.atomicPop
            ticketOwnerLayout houtsideShift hheadOwnerShift hframeOwnerShift
          exact hopened.perm hticketFramePerm
        let residualTicketLedger : residualTickets.SemanticScheduleOwnerLedger
            continuation.rest (resources.window.transport hproductive) :=
          resources.ticketOwnerLedger.openHead
            (resources.window.transport hproductive) hticketActive hrightTicket
            (fun owner hmem => houtsideShift owner
              (resources.ticketOwnerLedger.outside_at owner hmem))
            hticketSemanticFrames residualTicketPrefixLedger
        have hrightTicketShadow :
            residualTickets.semanticCursor.right.filterMap
                ScheduleAtom.indexOwner? =
              residualTickets.semanticOwners (owners ++ parkedOwners) ++
                resources.ticketShadowLedger.outside := by
          have hright := resources.ticketShadowLedger.right_eq
          rw [hticketShadowActive] at hright
          rw [residualTickets.semanticCursor_right_indexOwners]
          rw [resources.tickets.semanticCursor_right_indexOwners] at hright
          simpa [residualTickets, IndexTicketLedger.semanticOwners,
            plainScheduleCursor, liveScheduleCursor,
            hindex.filterMap_indexOwner_eq_nil, ScheduleAtom.indexOwner?,
            List.filterMap_append] using hright
        have hticketShadowFrames : ShadowOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          have hopened : ShadowOwnedFrames continuation.rest
              (resources.window.transport hproductive)
              (resources.tickets.semanticOwnerOf idx.owner ::
                resources.tickets.semanticCursor.frameOwners) :=
            ShadowOwnedFrames.cons
              (OutsideShadowWindow.transport resources.window hproductive
                hticketHeadShadowOutside)
              (resources.ticketShadowLedger.frames.transportEqual hproductive)
          exact hopened.perm hticketFramePerm
        let residualTicketShadowLedger : residualTickets.SemanticShadowOwnerLedger
            continuation.rest (resources.window.transport hproductive) :=
          resources.ticketShadowLedger.openHead
            (resources.window.transport hproductive) hticketShadowActive
            hrightTicketShadow
            (fun owner hmem =>
              OutsideShadowWindow.transport resources.window hproductive
                (resources.ticketShadowLedger.outside_at owner hmem))
            hticketShadowFrames residualTicketPrefixLedger
        have residualTicketActive : residualTicketLedger.active =
            residualTickets.semanticOwners residualLedger.active := by
          change resources.tickets.semanticOwners owners =
            residualTickets.semanticOwners owners
          rfl
        have residualTicketShadowActive : residualTicketShadowLedger.active =
            residualTickets.semanticOwners (owners ++ parkedOwners) := by
          rfl
        have residualTicketOwnerLayout : residualTickets.EventTicketLayout
            continuation.rest (resources.window.transport hproductive) blocks
              owners := by
          simpa [residualTickets] using oldResidualTicketOwnerLayout
        have residualTicketShadowLayout : residualTickets.ShadowTicketLayout
            continuation.rest (resources.window.transport hproductive)
              (blocks ++ parkedBlocks) (owners ++ parkedOwners) := by
          simpa [residualTickets] using oldResidualTicketShadowLayout
        have residualTicketShadowOwnersSubset : owners ++ parkedOwners ⊆
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).indexOwners := by
          intro owner howner
          rw [hindices]
          apply resources.ticketShadowOwners_subset
          rw [hcontextOwners]
          simpa only [List.cons_append] using List.mem_cons_of_mem idx.owner howner
        have residualTicketShadowOwnersNodup :
            (owners ++ parkedOwners).Nodup := by
          have hold := resources.ticketShadowOwners_nodup
          rw [hcontextOwners] at hold
          exact (List.nodup_cons.mp (by simpa only [List.cons_append] using hold)).2
        have hrightShadow :
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).right.filterMap
                ScheduleAtom.indexOwner? =
              owners ++ resources.shadowLedger.outside := by
          have hright := resources.shadowLedger.right_eq
          rw [hshadowActive] at hright
          simpa [plainScheduleCursor, liveScheduleCursor,
            hindex.filterMap_indexOwner_eq_nil, ScheduleAtom.indexOwner?,
            List.filterMap_append] using hright
        have hshadowFrames : ShadowOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail).frameOwners := by
          have hopened : ShadowOwnedFrames continuation.rest
              (resources.window.transport hproductive)
              (idx.owner ::
                (liveScheduleCursor parse parentUsed pre post input_eq alpha
                  (beta ++ .index idx :: tail)).frameOwners) :=
            ShadowOwnedFrames.cons
              (OutsideShadowWindow.transport resources.window hproductive
                hheadShadowOutside)
              (resources.shadowLedger.frames.transportEqual hproductive)
          exact hopened.perm hframePerm
        let residualShadowLedger : ShadowOwnerLedger continuation.rest
            (resources.window.transport hproductive)
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail) :=
          resources.shadowLedger.openHead
            (resources.window.transport hproductive) hshadowActive hrightShadow
            (fun owner hmem =>
              OutsideShadowWindow.transport resources.window hproductive
                (resources.shadowLedger.outside_at owner hmem))
            hshadowFrames hprefixLedger
        have hresidualTransientFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
              (plainScheduleCursor continuation.rest hunused pre post input_eq
                innerAlpha (.close idx.owner) tail).indexOwners := by
          intro hinput hmem
          apply transientFree hinput
          rwa [← hindices]
        have hresidualTicketTransientFree : ∀ hinput : 0 < input.length,
            IndexTicket.transient hinput ∉
              (plainScheduleCursor continuation.rest hunused pre post input_eq
                innerAlpha (.close idx.owner) tail).indexTickets
                  residualTickets.ticketOf := by
          intro hinput
          simpa [residualTickets, ScheduleCursor.indexTickets, hindices] using
            ticketTransientFree hinput
        have hresidualScratchFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
              (plainScheduleCursor continuation.rest hunused pre post input_eq
                innerAlpha (.close idx.owner) tail).indexOwners := by
          intro hinput hmem
          apply scratchFree hinput
          rwa [← hindices]
        let residualResources : ScheduleRunResources continuation.rest pre
            (plainScheduleCursor continuation.rest hunused pre post input_eq
              innerAlpha (.close idx.owner) tail) :=
          resources.transportAtomicPop hindices htasks hproductive residualLedger
            residualTickets residualParkingBelow.toAtOrBelow residualTicketLedger
            residualTicketActive
            (blocks ++ parkedBlocks) (owners ++ parkedOwners)
            residualTicketShadowOwnersSubset residualTicketShadowOwnersNodup
            residualTicketShadowLedger residualTicketShadowActive
            residualTicketShadowLayout residualShadowLedger (by rfl)
        have hpos : pre.length ≤ input.length := by
          rw [input_eq]
          simp
        let startState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hstart
        let insideStartState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hinsideStart
        have hpopRun : ScheduleReaches g input startState insideStartState := by
          apply ScheduleReaches.single
          have hstep := continuation.composite_popPlain input idx.mark pre.length
            (alpha.map ScheduleAtom.workSym) (beta.map ScheduleAtom.workSym)
            (tail.map ScheduleAtom.workSym) hindex.erase
          simpa [startState, insideStartState, scheduleStateOfCursor,
            ScheduleState.config, liveScheduleCursor, plainScheduleCursor,
            parentTask, residualTask, scheduleTaskOfParse, innerAlpha, selected,
            ScheduleCursor.erase, ScheduleAtom.workSym, ScheduleTask.workSym,
            List.map_append, List.append_assoc] using hstep
        cases beta with
        | nil =>
            have hendFresh : idx.owner ∉
                (ScheduleCursor.mk (alpha ++ [.dollar]) selected tail).frameOwners := by
              intro hmem
              apply hframeFresh
              simpa [liveScheduleCursor, selected, ScheduleCursor.frameOwners,
                ScheduleCursor.word, ScheduleAtom.closeOwner?] using hmem
            have hendOwned : idx.owner ∈
                (ScheduleCursor.mk (alpha ++ [.dollar]) selected tail).indexOwners := by
              simp [selected, ScheduleCursor.indexOwners, ScheduleCursor.word,
                ScheduleAtom.indexOwner?]
            have hinsideEnd : ScheduleInvariant
                (scheduleWordCursor innerAlpha (.close idx.owner :: tail)) := by
              have hprepared := ScheduleInvariant.prepareReturnFrame alpha [] tail selected
                idx.owner hendFresh hendOwned (by
                  simpa [scheduleWordCursor, selected] using hend)
              simpa [scheduleWordCursor, innerAlpha, selected, List.append_assoc] using hprepared
            let insideEndState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) _ hinsideEnd
            have hinsideRun := (ih continuation.rest hcount).1 hunused pre post input_eq
              innerAlpha (.close idx.owner) tail hinnerStable hinsideStart hinsideEnd
              residualResources (by
                simpa [residualResources] using hcredit)
              (by simpa [residualResources] using residualParkingBelow)
              (by
                change owners = []
                exact hownersNil)
              ShadowStartLayout.nil
              hresidualTicketTransientFree
              hresidualTransientFree
              hresidualScratchFree
            have hinsideRun' : ScheduleReaches g input insideStartState insideEndState := by
              simpa [insideStartState, insideEndState, scheduleStateOfCursor] using hinsideRun
            let endState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) (scheduleWordCursor alpha (selected :: tail)) hend
            have hreturn : ScheduleReaches g input insideEndState endState := by
              apply ScheduleReaches.single
              have hstep := composite_returnFrame_at input (pre ++ w).length
                (alpha.map ScheduleAtom.workSym) selected.workSym []
                (tail.map ScheduleAtom.workSym) (by
                  simp [selected, ScheduleAtom.workSym]) (by
                  simp [DollarFree])
              simpa [insideEndState, endState, scheduleStateOfCursor,
                ScheduleState.config, scheduleWordCursor, innerAlpha, selected,
                ScheduleCursor.erase, ScheduleAtom.workSym, List.map_append,
                List.append_assoc] using hstep
            simpa [startState, endState, selected, scheduleStateOfCursor] using
              hpopRun.trans (hinsideRun'.trans hreturn)
        | cons next gap =>
            have hnext : next ≠ ScheduleAtom.dollar := by
              intro heq
              subst next
              exact hdollar (by simp)
            have hgapDollar : ScheduleDollarFree (gap ++ [selected]) := by
              apply ScheduleDollarFree.append
              · intro hmem
                exact hdollar (by simp [hmem])
              · simp [ScheduleDollarFree, selected]
            have hendFresh : idx.owner ∉
                (ScheduleCursor.mk (alpha ++ [.dollar]) next
                  ((gap ++ [selected]) ++ tail)).frameOwners := by
              have heq :
                  (ScheduleCursor.mk (alpha ++ [.dollar]) next
                    ((gap ++ [selected]) ++ tail)).frameOwners =
                  (liveScheduleCursor parse parentUsed pre post input_eq alpha
                    (next :: gap ++ .index idx :: tail)).frameOwners := by
                cases next <;>
                  simp [liveScheduleCursor, selected,
                    ScheduleCursor.frameOwners, ScheduleCursor.word,
                    ScheduleAtom.closeOwner?, List.filterMap_append,
                    List.append_assoc]
              intro hmem
              exact hframeFresh (heq ▸ hmem)
            have hendOwned : idx.owner ∈
                (ScheduleCursor.mk (alpha ++ [.dollar]) next
                  ((gap ++ [selected]) ++ tail)).indexOwners := by
              have hselected : idx.owner ∈
                  [selected].filterMap ScheduleAtom.indexOwner? := by
                simp [selected, ScheduleAtom.indexOwner?]
              have hmiddle : idx.owner ∈
                  (gap ++ [selected]).filterMap ScheduleAtom.indexOwner? := by
                rw [List.filterMap_append]
                exact List.mem_append_right _ hselected
              have hright : idx.owner ∈
                  ((gap ++ [selected]) ++ tail).filterMap
                    ScheduleAtom.indexOwner? := by
                rw [List.filterMap_append]
                exact List.mem_append_left _ hmiddle
              simp only [ScheduleCursor.indexOwners_mk]
              exact List.mem_append_right _ hright
            have hinsideEnd : ScheduleInvariant
                (scheduleWordCursor innerAlpha (.close idx.owner :: tail)) := by
              have hprepared := ScheduleInvariant.prepareReturnFrame alpha
                (gap ++ [selected]) tail next idx.owner hendFresh hendOwned (by
                  simpa [scheduleWordCursor, selected, List.append_assoc] using hend)
              simpa [scheduleWordCursor, innerAlpha, selected, List.append_assoc] using hprepared
            let insideEndState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) _ hinsideEnd
            have hinsideRun := (ih continuation.rest hcount).1 hunused pre post input_eq
              innerAlpha (.close idx.owner) tail hinnerStable hinsideStart hinsideEnd
              residualResources (by
                simpa [residualResources] using hcredit)
              (by simpa [residualResources] using residualParkingBelow)
              (by
                change owners = []
                exact hownersNil)
              ShadowStartLayout.nil
              hresidualTicketTransientFree
              hresidualTransientFree
              hresidualScratchFree
            have hinsideRun' : ScheduleReaches g input insideStartState insideEndState := by
              simpa [insideStartState, insideEndState, scheduleStateOfCursor] using hinsideRun
            let endState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) (scheduleWordCursor alpha
                  (next :: gap ++ selected :: tail)) hend
            have hreturn : ScheduleReaches g input insideEndState endState := by
              apply ScheduleReaches.single
              have hnextWork : next.workSym ≠ WorkSym.dollar := by
                cases next with
                | task task =>
                    cases task with
                    | mk A stack yield parse taskPre taskPost taskInput mode =>
                        cases mode <;>
                          simp [ScheduleAtom.workSym, ScheduleTask.workSym]
                | terminal owner a => simp [ScheduleAtom.workSym]
                | index index => simp [ScheduleAtom.workSym]
                | dollar => exact False.elim (hnext rfl)
                | close owner => simp [ScheduleAtom.workSym]
                | hash => simp [ScheduleAtom.workSym]
              have hstep := composite_returnFrame_at input (pre ++ w).length
                (alpha.map ScheduleAtom.workSym) next.workSym
                ((gap ++ [selected]).map ScheduleAtom.workSym)
                (tail.map ScheduleAtom.workSym)
                hnextWork
                hgapDollar.erase
              simpa [insideEndState, endState, scheduleStateOfCursor,
                ScheduleState.config, scheduleWordCursor, innerAlpha, selected,
                ScheduleCursor.erase, ScheduleAtom.workSym, List.map_append,
                List.append_assoc] using hstep
            simpa [startState, endState, selected, scheduleStateOfCursor,
              List.append_assoc] using hpopRun.trans (hinsideRun'.trans hreturn)
      · have residualUsed : continuation.rest.ConsumesAt 0 := by
          have hp : parse.ConsumesAt idx.flags.length := hall idx.flags.length (by
            have := List.length_pos_of_ne_nil hflags
            simp only [List.length_append]
            omega)
          exact (hconsumes 0).2 (by simpa using hp)
        let residualTask : ScheduleTask g input :=
          scheduleTaskOfParse continuation.rest pre post input_eq (.live residualUsed)
        have htaskOwner : residualTask.owner = parentTask.owner := by
          apply Fin.ext
          rfl
        have hinsideStart : ScheduleInvariant
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)) := by
          have hpop := ScheduleInvariant.popFrame alpha beta tail parentTask residualTask idx
            htaskOwner hframeFresh (by
              simpa [liveScheduleCursor, parentTask] using hstart)
          simpa [liveScheduleCursor, innerAlpha, selected, residualTask,
            List.append_assoc] using hpop
        have hindices :
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).indexOwners =
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (beta ++ .index idx :: tail)).indexOwners := by
          simp [liveScheduleCursor, innerAlpha, selected,
            ScheduleCursor.indexOwners, ScheduleCursor.word,
            ScheduleAtom.indexOwner?, List.filterMap_append, List.append_assoc]
        have htasks :
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).taskOwners.Perm
            (liveScheduleCursor parse parentUsed pre post input_eq alpha
              (beta ++ .index idx :: tail)).taskOwners := by
          simp only [liveScheduleCursor, ScheduleCursor.taskOwners_mk,
            ScheduleAtom.taskOwner?, List.filterMap_cons, List.filterMap_nil,
            List.append_nil, List.filterMap_append, innerAlpha, selected]
          rw [htaskOwner]
          simpa only [List.append_assoc] using
            List.Perm.append_left (alpha.filterMap ScheduleAtom.taskOwner?)
              (List.perm_middle
                (l₁ := beta.filterMap ScheduleAtom.taskOwner?)
                (l₂ := tail.filterMap ScheduleAtom.taskOwner?)
                (a := parentTask.owner))
        have hrightLedger :
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).right.filterMap
                ScheduleAtom.indexOwner? =
              owners ++ resources.ownerLedger.outside := by
          have hright := resources.ownerLedger.right_eq
          rw [hactive] at hright
          simpa [liveScheduleCursor, hindex.filterMap_indexOwner_eq_nil,
            ScheduleAtom.indexOwner?, List.filterMap_append] using hright
        have hframePerm :
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).frameOwners.Perm
              (idx.owner ::
                (liveScheduleCursor parse parentUsed pre post input_eq alpha
                  (beta ++ .index idx :: tail)).frameOwners) := by
          simpa [liveScheduleCursor, innerAlpha, selected,
            ScheduleCursor.frameOwners, ScheduleCursor.word,
            ScheduleAtom.closeOwner?, List.filterMap_append,
            List.append_assoc] using
            (List.perm_middle
              (l₁ := alpha.filterMap ScheduleAtom.closeOwner? ++
                beta.filterMap ScheduleAtom.closeOwner?)
              (l₂ := tail.filterMap ScheduleAtom.closeOwner?)
              (a := idx.owner))
        have hsemanticFrames : EventOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).frameOwners := by
          have hopened := resources.ownerLedger.frames.atomicPop ownerLayout
            houtsideShift hheadOwnerShift hframeOwnerShift
          exact hopened.perm hframePerm
        have hprefixInsert :
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).left.filterMap
                ScheduleAtom.indexOwner? |>.Perm
              (idx.owner ::
                (liveScheduleCursor parse parentUsed pre post input_eq alpha
                  (beta ++ .index idx :: tail)).left.filterMap
                    ScheduleAtom.indexOwner?) := by
          simp [liveScheduleCursor, innerAlpha, selected,
            hindex.filterMap_indexOwner_eq_nil, ScheduleAtom.indexOwner?,
            List.filterMap_append]
        have hprefixLedger : PrefixFrameLedger
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)) := by
          apply resources.ownerLedger.prefixLedger.insert idx.owner
          · exact hprefixInsert
          · exact hframePerm
        let residualLedger : ScheduleOwnerLedger continuation.rest
            (resources.window.transport hproductive)
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)) :=
          resources.ownerLedger.openHead
            (resources.window.transport hproductive) hactive hrightLedger
            (fun owner hmem => houtsideShift owner
              (resources.ownerLedger.outside_at owner hmem))
            hsemanticFrames hprefixLedger
        let residualTickets : IndexTicketLedger
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)) :=
          resources.tickets.transport (by rw [hindices])
        have residualParkingBelow : residualTickets.ParkingBelow
            (resources.window.transport hproductive) := by
          exact parkingBelow.transport_mono
            (hindices ▸ List.Perm.refl _) (by simp)
        have hticketFramePerm : residualTickets.semanticCursor.frameOwners.Perm
            (resources.tickets.semanticOwnerOf idx.owner ::
              resources.tickets.semanticCursor.frameOwners) := by
          rw [residualTickets.semanticCursor_frameOwners,
            resources.tickets.semanticCursor_frameOwners]
          simpa [residualTickets] using
            hframePerm.map resources.tickets.semanticOwnerOf
        let residualTicketPrefixLedger :
            PrefixFrameLedger residualTickets.semanticCursor :=
          resources.ticketOwnerLedger.prefixLedger.insert
            (resources.tickets.semanticOwnerOf idx.owner)
            (by
              change
                (((liveScheduleCursor continuation.rest residualUsed pre post
                    input_eq innerAlpha (.close idx.owner :: tail)).left.map
                    (ScheduleAtom.relabelTicketOwner
                      residualTickets.semanticOwnerOf)).filterMap
                    ScheduleAtom.indexOwner?).Perm
                  (resources.tickets.semanticOwnerOf idx.owner ::
                    (((liveScheduleCursor parse parentUsed pre post input_eq alpha
                      (beta ++ .index idx :: tail)).left.map
                      (ScheduleAtom.relabelTicketOwner
                        resources.tickets.semanticOwnerOf)).filterMap
                      ScheduleAtom.indexOwner?))
              rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner,
                ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
              have hfun : residualTickets.semanticOwnerOf =
                  resources.tickets.semanticOwnerOf := by
                funext owner
                rfl
              rw [hfun]
              exact hprefixInsert.map resources.tickets.semanticOwnerOf)
            hticketFramePerm
        have hrightTicket :
            residualTickets.semanticCursor.right.filterMap
                ScheduleAtom.indexOwner? =
              residualTickets.semanticOwners owners ++
                resources.ticketOwnerLedger.outside := by
          have hright := resources.ticketOwnerLedger.right_eq
          rw [hticketActive] at hright
          rw [residualTickets.semanticCursor_right_indexOwners]
          rw [resources.tickets.semanticCursor_right_indexOwners] at hright
          simpa [residualTickets, IndexTicketLedger.semanticOwners,
            liveScheduleCursor, hindex.filterMap_indexOwner_eq_nil,
            ScheduleAtom.indexOwner?, List.filterMap_append] using hright
        have hticketSemanticFrames : EventOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          have hopened := resources.ticketOwnerLedger.frames.atomicPop
            ticketOwnerLayout houtsideShift hheadOwnerShift hframeOwnerShift
          exact hopened.perm hticketFramePerm
        let residualTicketLedger : residualTickets.SemanticScheduleOwnerLedger
            continuation.rest (resources.window.transport hproductive) :=
          resources.ticketOwnerLedger.openHead
            (resources.window.transport hproductive) hticketActive hrightTicket
            (fun owner hmem => houtsideShift owner
              (resources.ticketOwnerLedger.outside_at owner hmem))
            hticketSemanticFrames residualTicketPrefixLedger
        have hrightTicketShadow :
            residualTickets.semanticCursor.right.filterMap
                ScheduleAtom.indexOwner? =
              residualTickets.semanticOwners (owners ++ parkedOwners) ++
                resources.ticketShadowLedger.outside := by
          have hright := resources.ticketShadowLedger.right_eq
          rw [hticketShadowActive] at hright
          rw [residualTickets.semanticCursor_right_indexOwners]
          rw [resources.tickets.semanticCursor_right_indexOwners] at hright
          simpa [residualTickets, IndexTicketLedger.semanticOwners,
            liveScheduleCursor, hindex.filterMap_indexOwner_eq_nil,
            ScheduleAtom.indexOwner?, List.filterMap_append] using hright
        have hticketShadowFrames : ShadowOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            residualTickets.semanticCursor.frameOwners := by
          have hopened : ShadowOwnedFrames continuation.rest
              (resources.window.transport hproductive)
              (resources.tickets.semanticOwnerOf idx.owner ::
                resources.tickets.semanticCursor.frameOwners) :=
            ShadowOwnedFrames.cons
              (OutsideShadowWindow.transport resources.window hproductive
                hticketHeadShadowOutside)
              (resources.ticketShadowLedger.frames.transportEqual hproductive)
          exact hopened.perm hticketFramePerm
        let residualTicketShadowLedger : residualTickets.SemanticShadowOwnerLedger
            continuation.rest (resources.window.transport hproductive) :=
          resources.ticketShadowLedger.openHead
            (resources.window.transport hproductive) hticketShadowActive
            hrightTicketShadow
            (fun owner hmem =>
              OutsideShadowWindow.transport resources.window hproductive
                (resources.ticketShadowLedger.outside_at owner hmem))
            hticketShadowFrames residualTicketPrefixLedger
        have residualTicketActive : residualTicketLedger.active =
            residualTickets.semanticOwners residualLedger.active := by
          change resources.tickets.semanticOwners owners =
            residualTickets.semanticOwners owners
          rfl
        have residualTicketShadowActive : residualTicketShadowLedger.active =
            residualTickets.semanticOwners (owners ++ parkedOwners) := by
          rfl
        have residualTicketOwnerLayout : residualTickets.EventTicketLayout
            continuation.rest (resources.window.transport hproductive) blocks
              owners := by
          simpa [residualTickets] using oldResidualTicketOwnerLayout
        have residualTicketShadowLayout : residualTickets.ShadowTicketLayout
            continuation.rest (resources.window.transport hproductive)
              (blocks ++ parkedBlocks) (owners ++ parkedOwners) := by
          simpa [residualTickets] using oldResidualTicketShadowLayout
        have residualTicketShadowOwnersSubset : owners ++ parkedOwners ⊆
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).indexOwners := by
          intro owner howner
          rw [hindices]
          apply resources.ticketShadowOwners_subset
          rw [hcontextOwners]
          simpa only [List.cons_append] using List.mem_cons_of_mem idx.owner howner
        have residualTicketShadowOwnersNodup :
            (owners ++ parkedOwners).Nodup := by
          have hold := resources.ticketShadowOwners_nodup
          rw [hcontextOwners] at hold
          exact (List.nodup_cons.mp (by simpa only [List.cons_append] using hold)).2
        have hrightShadow :
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).right.filterMap
                ScheduleAtom.indexOwner? =
              owners ++ resources.shadowLedger.outside := by
          have hright := resources.shadowLedger.right_eq
          rw [hshadowActive] at hright
          simpa [liveScheduleCursor, hindex.filterMap_indexOwner_eq_nil,
            ScheduleAtom.indexOwner?, List.filterMap_append] using hright
        have hshadowFrames : ShadowOwnedFrames continuation.rest
            (resources.window.transport hproductive)
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).frameOwners := by
          have hopened : ShadowOwnedFrames continuation.rest
              (resources.window.transport hproductive)
              (idx.owner ::
                (liveScheduleCursor parse parentUsed pre post input_eq alpha
                  (beta ++ .index idx :: tail)).frameOwners) :=
            ShadowOwnedFrames.cons
              (OutsideShadowWindow.transport resources.window hproductive
                hheadShadowOutside)
              (resources.shadowLedger.frames.transportEqual hproductive)
          exact hopened.perm hframePerm
        let residualShadowLedger : ShadowOwnerLedger continuation.rest
            (resources.window.transport hproductive)
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)) :=
          resources.shadowLedger.openHead
            (resources.window.transport hproductive) hshadowActive hrightShadow
            (fun owner hmem =>
              OutsideShadowWindow.transport resources.window hproductive
                (resources.shadowLedger.outside_at owner hmem))
            hshadowFrames hprefixLedger
        have hresidualTransientFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
              (liveScheduleCursor continuation.rest residualUsed pre post input_eq
                innerAlpha (.close idx.owner :: tail)).indexOwners := by
          intro hinput hmem
          apply transientFree hinput
          rwa [← hindices]
        have hresidualTicketTransientFree : ∀ hinput : 0 < input.length,
            IndexTicket.transient hinput ∉
              (liveScheduleCursor continuation.rest residualUsed pre post input_eq
                innerAlpha (.close idx.owner :: tail)).indexTickets
                  residualTickets.ticketOf := by
          intro hinput
          simpa [residualTickets, ScheduleCursor.indexTickets, hindices] using
            ticketTransientFree hinput
        have hresidualScratchFree : ∀ hinput : 0 < input.length,
            ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
              (liveScheduleCursor continuation.rest residualUsed pre post input_eq
                innerAlpha (.close idx.owner :: tail)).indexOwners := by
          intro hinput hmem
          apply scratchFree hinput
          rwa [← hindices]
        let residualResources : ScheduleRunResources continuation.rest pre
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)) :=
          resources.transportAtomicPop hindices htasks hproductive residualLedger
            residualTickets residualParkingBelow.toAtOrBelow residualTicketLedger
            residualTicketActive
            (blocks ++ parkedBlocks) (owners ++ parkedOwners)
            residualTicketShadowOwnersSubset residualTicketShadowOwnersNodup
            residualTicketShadowLedger residualTicketShadowActive
            residualTicketShadowLayout residualShadowLedger (by rfl)
        have hallRest : ∀ k < flags.length,
            continuation.rest.ConsumesAt k := by
          intro k hk
          apply (hconsumes k).2
          apply hall
          simp only [List.length_append]
          omega
        have hboundaryRest : ¬ continuation.rest.ConsumesAt flags.length := by
          intro hrest
          apply hboundary
          have hp := (hconsumes flags.length).1 hrest
          simpa [List.length_append, Nat.add_assoc] using hp
        have crossed : ScheduleBlockLayout g input flags blocks owners
            (.close idx.owner :: tail) (.close idx.owner :: tail') := by
          simpa using restLayout.prepend [.close idx.owner]
            (by simp [ScheduleIndexFree]) (by simp [ScheduleDollarFree])
        have hframesRest : List.Disjoint owners
            (liveScheduleCursor continuation.rest residualUsed pre post input_eq
              innerAlpha (.close idx.owner :: tail)).frameOwners := by
          apply List.disjoint_left.mpr
          intro owner howner hframe
          have hownerNe : owner ≠ idx.owner := by
            intro heq
            apply fresh
            simpa [heq] using howner
          have hframeCases : owner = idx.owner ∨ owner ∈
              (liveScheduleCursor parse parentUsed pre post input_eq alpha
                (beta ++ .index idx :: tail)).frameOwners := by
            simp only [liveScheduleCursor, innerAlpha, selected,
              ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?,
              List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
              List.append_nil, List.mem_append, List.mem_cons] at hframe ⊢
            aesop
          rcases hframeCases with heq | hold
          · exact hownerNe heq
          · exact (List.disjoint_left.mp hframes)
              (List.mem_cons_of_mem idx.owner howner) hold
        have hpos : pre.length ≤ input.length := by
          rw [input_eq]
          simp
        let startState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hstart
        let insideStartState : ScheduleState g input :=
          scheduleStateOfCursor pre.length hpos _ hinsideStart
        have hpopRun : ScheduleReaches g input startState insideStartState := by
          apply ScheduleReaches.single
          have hstep := continuation.composite_popLive input idx.mark (hlater hflags)
            pre.length (alpha.map ScheduleAtom.workSym)
            (beta.map ScheduleAtom.workSym) (tail.map ScheduleAtom.workSym) hindex.erase
          simpa [startState, insideStartState, scheduleStateOfCursor,
            ScheduleState.config, liveScheduleCursor, parentTask, residualTask,
            scheduleTaskOfParse, innerAlpha, selected, ScheduleCursor.erase,
            ScheduleAtom.workSym, ScheduleTask.workSym, List.map_append,
            List.append_assoc] using hstep
        cases beta with
        | nil =>
            have hendFresh : idx.owner ∉
                (ScheduleCursor.mk (alpha ++ [.dollar]) selected tail').frameOwners := by
              have htailFrames := restLayout.frameOwners_eq
              intro hmem
              apply hframeFresh
              simpa [liveScheduleCursor, selected, ScheduleCursor.frameOwners,
                ScheduleCursor.word, ScheduleAtom.closeOwner?, htailFrames] using hmem
            have hendOwned : idx.owner ∈
                (ScheduleCursor.mk (alpha ++ [.dollar]) selected tail').indexOwners := by
              simp [selected, ScheduleCursor.indexOwners, ScheduleCursor.word,
                ScheduleAtom.indexOwner?]
            have hinsideEnd : ScheduleInvariant
                (scheduleWordCursor innerAlpha (.close idx.owner :: tail')) := by
              have hprepared := ScheduleInvariant.prepareReturnFrame alpha [] tail' selected
                idx.owner hendFresh hendOwned (by
                  simpa [scheduleWordCursor, selected] using hend)
              simpa [scheduleWordCursor, innerAlpha, selected, List.append_assoc] using hprepared
            let insideEndState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) _ hinsideEnd
            have hinsideRun := (ih continuation.rest hcount).2 flags hidden blocks owners
              (.close idx.owner :: tail) (.close idx.owner :: tail') rfl hflags
              hallRest hboundaryRest crossed compatibleRest pre post input_eq innerAlpha
              hinnerStable hinsideStart hframesRest hinsideEnd residualResources (by
                simpa [residualResources] using hcredit)
              (by simpa [residualResources] using residualParkingBelow)
              (by simpa [residualResources] using residualOwnerLayout)
              (by simpa [residualResources] using residualShadowLayout)
              (by simpa [residualResources] using residualTicketOwnerLayout)
              (by
                refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
                · rfl
                · rfl)
              (by simpa [residualResources] using hresidualTicketTransientFree)
              (by rfl)
              hresidualTransientFree
              hresidualScratchFree
            have hinsideRun' : ScheduleReaches g input insideStartState insideEndState := by
              simpa [insideStartState, insideEndState, liveScheduleCursor,
                scheduleStateOfCursor] using hinsideRun
            let endState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) (scheduleWordCursor alpha (selected :: tail')) hend
            have hreturn : ScheduleReaches g input insideEndState endState := by
              apply ScheduleReaches.single
              have hstep := composite_returnFrame_at input (pre ++ w).length
                (alpha.map ScheduleAtom.workSym) selected.workSym []
                (tail'.map ScheduleAtom.workSym) (by
                  simp [selected, ScheduleAtom.workSym]) (by simp [DollarFree])
              simpa [insideEndState, endState, scheduleStateOfCursor,
                ScheduleState.config, scheduleWordCursor, innerAlpha, selected,
                ScheduleCursor.erase, ScheduleAtom.workSym, List.map_append,
                List.append_assoc] using hstep
            simpa [startState, endState, selected, scheduleStateOfCursor] using
              hpopRun.trans (hinsideRun'.trans hreturn)
        | cons next gap =>
            have hnext : next ≠ ScheduleAtom.dollar := by
              intro heq
              subst next
              exact hdollar (by simp)
            have hgapDollar : ScheduleDollarFree (gap ++ [selected]) := by
              apply ScheduleDollarFree.append
              · intro hmem
                exact hdollar (by simp [hmem])
              · simp [ScheduleDollarFree, selected]
            have hendFresh : idx.owner ∉
                (ScheduleCursor.mk (alpha ++ [.dollar]) next
                  ((gap ++ [selected]) ++ tail')).frameOwners := by
              have htailFrames := restLayout.frameOwners_eq
              have heq :
                  (ScheduleCursor.mk (alpha ++ [.dollar]) next
                    ((gap ++ [selected]) ++ tail')).frameOwners =
                  (liveScheduleCursor parse parentUsed pre post input_eq alpha
                    (next :: gap ++ .index idx :: tail)).frameOwners := by
                cases next <;>
                  simp [liveScheduleCursor, selected,
                    ScheduleCursor.frameOwners, ScheduleCursor.word,
                    ScheduleAtom.closeOwner?, List.filterMap_append,
                    List.append_assoc, htailFrames]
              intro hmem
              exact hframeFresh (heq ▸ hmem)
            have hendOwned : idx.owner ∈
                (ScheduleCursor.mk (alpha ++ [.dollar]) next
                  ((gap ++ [selected]) ++ tail')).indexOwners := by
              have hselected : idx.owner ∈
                  [selected].filterMap ScheduleAtom.indexOwner? := by
                simp [selected, ScheduleAtom.indexOwner?]
              have hmiddle : idx.owner ∈
                  (gap ++ [selected]).filterMap ScheduleAtom.indexOwner? := by
                rw [List.filterMap_append]
                exact List.mem_append_right _ hselected
              have hright : idx.owner ∈
                  ((gap ++ [selected]) ++ tail').filterMap
                    ScheduleAtom.indexOwner? := by
                rw [List.filterMap_append]
                exact List.mem_append_left _ hmiddle
              simp only [ScheduleCursor.indexOwners_mk]
              exact List.mem_append_right _ hright
            have hinsideEnd : ScheduleInvariant
                (scheduleWordCursor innerAlpha (.close idx.owner :: tail')) := by
              have hprepared := ScheduleInvariant.prepareReturnFrame alpha
                (gap ++ [selected]) tail' next idx.owner hendFresh hendOwned (by
                  simpa [scheduleWordCursor, selected, List.append_assoc] using hend)
              simpa [scheduleWordCursor, innerAlpha, selected, List.append_assoc] using hprepared
            let insideEndState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) _ hinsideEnd
            have hinsideRun := (ih continuation.rest hcount).2 flags hidden blocks owners
              (.close idx.owner :: tail) (.close idx.owner :: tail') rfl hflags
              hallRest hboundaryRest crossed compatibleRest pre post input_eq innerAlpha
              hinnerStable hinsideStart hframesRest hinsideEnd residualResources (by
                simpa [residualResources] using hcredit)
              (by simpa [residualResources] using residualParkingBelow)
              (by simpa [residualResources] using residualOwnerLayout)
              (by simpa [residualResources] using residualShadowLayout)
              (by simpa [residualResources] using residualTicketOwnerLayout)
              (by
                refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
                · rfl
                · rfl)
              (by simpa [residualResources] using hresidualTicketTransientFree)
              (by rfl)
              hresidualTransientFree
              hresidualScratchFree
            have hinsideRun' : ScheduleReaches g input insideStartState insideEndState := by
              simpa [insideStartState, insideEndState, liveScheduleCursor,
                scheduleStateOfCursor] using hinsideRun
            let endState : ScheduleState g input :=
              scheduleStateOfCursor (pre ++ w).length (by
                rw [input_eq]
                simp) (scheduleWordCursor alpha
                  (next :: gap ++ selected :: tail')) hend
            have hreturn : ScheduleReaches g input insideEndState endState := by
              apply ScheduleReaches.single
              have hnextWork : next.workSym ≠ WorkSym.dollar := by
                cases next with
                | task task =>
                    cases task with
                    | mk A stack yield parse taskPre taskPost taskInput mode =>
                        cases mode <;>
                          simp [ScheduleAtom.workSym, ScheduleTask.workSym]
                | terminal owner a => simp [ScheduleAtom.workSym]
                | index index => simp [ScheduleAtom.workSym]
                | dollar => exact False.elim (hnext rfl)
                | close owner => simp [ScheduleAtom.workSym]
                | hash => simp [ScheduleAtom.workSym]
              have hstep := composite_returnFrame_at input (pre ++ w).length
                (alpha.map ScheduleAtom.workSym) next.workSym
                ((gap ++ [selected]).map ScheduleAtom.workSym)
                (tail'.map ScheduleAtom.workSym) hnextWork hgapDollar.erase
              simpa [insideEndState, endState, scheduleStateOfCursor,
                ScheduleState.config, scheduleWordCursor, innerAlpha, selected,
                ScheduleCursor.erase, ScheduleAtom.workSym, List.map_append,
                List.append_assoc] using hstep
            simpa [startState, endState, selected, scheduleStateOfCursor,
              List.append_assoc] using hpopRun.trans (hinsideRun'.trans hreturn)
namespace ShadowStartLayout

/-- Prepend a singleton push block after aligning the old head either with child depth one or
with a ticket outside the child shadow window.  In the protected no-depth-one branch the
second alternative parks the old protected head, while the new overlay head uses the
transient ticket. -/
private def pushFreshAlignHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {block : List g.flag} {blocks : List (List g.flag)}
    {oldHead alignedHead newHead : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout (NFParse.push hr hlhs hc hrhs rest) window
      (block :: blocks) (oldHead :: owners))
    (hnew :
      (∃ hzero : 0 ∈ rest.eventDepths,
        newHead = window.pushChild.shadowEventOwner 0 hzero) ∨
      OutsideShadowWindow window.pushChild newHead)
    (hold :
      (∃ hone : 1 ∈ rest.eventDepths,
        alignedHead = window.pushChild.shadowEventOwner 1 hone) ∨
      OutsideShadowWindow window.pushChild alignedHead) :
    ShadowStartLayout rest window.pushChild ([f] :: block :: blocks)
      (newHead :: alignedHead :: owners) where
  owners_length := by simpa using layout.owners_length
  block_nonempty candidate hmem := by
    rcases List.mem_cons.mp hmem with rfl | htail
    · simp
    · exact layout.block_nonempty candidate htail
  owner_at i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [blockOwnerAt, blockStart] using hnew
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [blockOwnerAt, blockStart] using hold
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

/-- The ticket-level data needed by the common protected fresh-push runner.  The old head may
either rotate to the canonical child depth-one shadow ticket or move to a wholly outside
parking ticket; the remainder of the machine run is identical. -/
private structure ProtectedFreshPushHeadAlignment
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
    (normal : TicketHeadNormalization resources head block blocks owners) where
  tickets : IndexTicketLedger cursor
  parkingAtOrBelow : tickets.ParkingAtOrBelow resources.window
  head_parking : tickets.ticketOf head = resources.window.parkingTicket
  oldSemantic : Fin (10 * input.length)
  head_semantic : tickets.semanticOwnerOf head = oldSemantic
  transient_fresh : ∀ hinput : 0 < input.length,
    IndexTicket.transient hinput ∉ cursor.indexTickets tickets.ticketOf
  unchanged_normal : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
    tickets.ticketOf owner = normal.tickets.ticketOf owner
  restore : IndexTicket input
  restore_eq : restore = normal.tickets.ticketOf head
  restore_fresh : restore ∉ cursor.indexTickets tickets.ticketOf
  restore_nonparking : restore.Nonparking
  restore_not_scratch : ∀ hinput : 0 < input.length,
    restore ≠ IndexTicket.scratch hinput
  restore_not_transient : ∀ hinput : 0 < input.length,
    restore ≠ IndexTicket.transient hinput
  restore_outside_parent : OutsideProductiveWindow resources.window
    (IndexTicket.semanticOwner (g := g) restore)
  restore_shadow_zero : ∃ hzero : 0 ∈
      (NFParse.push hr hlhs hc hrhs rest).eventDepths,
    IndexTicket.semanticOwner (g := g) restore =
      resources.window.shadowEventOwner 0 hzero
  old_outside_parent : OutsideProductiveWindow resources.window oldSemantic
  old_shadow_child :
    (∃ hone : 1 ∈ rest.eventDepths,
      oldSemantic = resources.window.pushChild.shadowEventOwner 1 hone) ∨
    OutsideShadowWindow resources.window.pushChild oldSemantic

/-- Park a normalized old head at the canonical ticket of the current productive window. -/
private def TicketHeadNormalization.parkForProtectedFreshPush
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w} {pre : List T}
    {cursor : ScheduleCursor g input}
    {resources : ScheduleRunResources
      (NFParse.push hr hlhs hc hrhs rest) pre cursor}
    {head : Fin (10 * input.length)} {block : List g.flag}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (normal : TicketHeadNormalization resources head block blocks owners)
    (hzero : 0 ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths)
    (hbelow : normal.tickets.ParkingBelow resources.window)
    (hhead : head ∈ cursor.indexOwners)
    (houtPrimary : OutsideProductiveWindow resources.window
      (IndexTicket.semanticOwner (g := g) resources.window.parkingTicket))
    (houtShadow : OutsideShadowWindow resources.window.pushChild
      (IndexTicket.semanticOwner (g := g) resources.window.parkingTicket)) :
    ProtectedFreshPushHeadAlignment resources normal := by
  let target : IndexTicket input := resources.window.parkingTicket
  have htargetFresh : target ∉ cursor.indexTickets normal.tickets.ticketOf := by
    simpa [target] using hbelow.parkingTicket_fresh
  have htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput := fun hinput => by
    simpa [target] using
      IndexTicket.parking_ne_scratch resources.window.parkingSlot hinput
  have htargetNotTransient : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.transient hinput := fun hinput => by
    simpa [target] using
      IndexTicket.parking_ne_transient resources.window.parkingSlot hinput
  let parked := normal.tickets.reticket head target hhead htargetFresh
    htargetNotScratch
  have hheadTicket : parked.ticketOf head = target := by
    exact normal.tickets.reticket_ticketOf_owner head target hhead htargetFresh
      htargetNotScratch
  have hunchanged : ∀ owner ∈ cursor.indexOwners, owner ≠ head →
      parked.ticketOf owner = normal.tickets.ticketOf owner := by
    intro owner howner hne
    exact normal.tickets.reticket_ticketOf_eq_of_mem_ne head target hhead
      htargetFresh htargetNotScratch howner hne
  have htransientFresh : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∉ cursor.indexTickets parked.ticketOf := by
    intro hinput hmem
    rw [ScheduleCursor.indexTickets] at hmem
    rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
    by_cases heqHead : owner = head
    · subst owner
      rw [hheadTicket] at heq
      exact htargetNotTransient hinput heq
    · rw [hunchanged owner howner heqHead] at heq
      apply normal.transient_fresh hinput
      rw [ScheduleCursor.indexTickets]
      exact List.mem_map.mpr ⟨owner, howner, heq⟩
  exact {
    tickets := parked
    parkingAtOrBelow := by
      simpa [parked, target] using hbelow.reticket_parkingTicket head hhead
        htargetFresh htargetNotScratch
    head_parking := by simpa [target] using hheadTicket
    oldSemantic := IndexTicket.semanticOwner (g := g) target
    head_semantic := by
      simp [IndexTicketLedger.semanticOwnerOf, hheadTicket]
    transient_fresh := htransientFresh
    unchanged_normal := hunchanged
    restore := normal.tickets.ticketOf head
    restore_eq := rfl
    restore_fresh := by
      simpa [parked] using normal.tickets.reticket_old_fresh head target hhead
        htargetFresh htargetNotScratch
    restore_nonparking := by
      rw [normal.head_shadow hzero]
      exact resources.window.shadowEventTicket_nonparking 0 hzero
    restore_not_scratch := by
      intro hinput heq
      have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
      rw [normal.head_shadow hzero] at hsemantic
      simp only [ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
        IndexTicket.semanticOwner_scratch] at hsemantic
      exact resources.window.shadowEventOwner_ne_scratchOwner hzero hinput hsemantic
    restore_not_transient := by
      intro hinput heq
      have hsemantic := congrArg (IndexTicket.semanticOwner (g := g)) heq
      rw [normal.head_shadow hzero] at hsemantic
      simp only [ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
        IndexTicket.semanticOwner_transient] at hsemantic
      exact resources.window.shadowEventOwner_ne_transientOwner hzero hinput hsemantic
    restore_outside_parent := by
      right
      rw [normal.head_shadow hzero]
      have hlocal := (NFParse.push hr hlhs hc hrhs rest).eventOwnerNat_lt_productiveCount
        hzero
      have hend := resources.window.end_le
      simp only [ProductiveOwnerWindow.semanticOwner_shadowEventTicket,
        ProductiveOwnerWindow.shadowEventOwner_val, shadowOwnerOffset]
      omega
    restore_shadow_zero := by
      refine ⟨hzero, ?_⟩
      rw [normal.head_shadow hzero]
      exact resources.window.semanticOwner_shadowEventTicket 0 hzero
    old_outside_parent := houtPrimary
    old_shadow_child := Or.inr houtShadow
  }

/-- A push above a protected stack starts a fresh adjacent overlay block. The protected layout
remains unchanged below it, while the overlay runner owns and eventually erases the singleton. -/
public theorem protectedScheduleRun_pushFresh
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: stack) w)
    (hparentZero :
      0 ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths)
    (restOverlay : OverlayScheduleRun rest) :
    ProtectedScheduleRun (NFParse.push hr hlhs hc hrhs rest) := by
  intro input visible hidden blocks owners word used hstack hne hall hboundary
    layout compatible pre post input_eq alpha hstable hstart hframes hend
    resources hfree parkingBelow ownerLayout shadowLayout ticketOwnerLayout
    ticketShadowContext ticketTransientFree hactive transientFree scratchFree
  let parent : NFParse g A stack w := .push hr hlhs hc hrhs rest
  let parentUsed : parent.ConsumesAt 0 := hall 0
    (List.length_pos_of_ne_nil hne)
  let childUsed : rest.ConsumesAt 0 :=
    rest.consumesAt_of_consumesAt_succ 0 parentUsed
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.live parentUsed)
  let childTask : ScheduleTask g input :=
    scheduleTaskOfParse rest pre post input_eq (.live childUsed)
  let startCursor : ScheduleCursor g input :=
    liveScheduleCursor parent parentUsed pre post input_eq alpha word
  have hstart' : ScheduleInvariant startCursor := by
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using hstart
  have hinputPos : 0 < input.length := by
    have hw := rest.yield_length_pos
    have hlen := congrArg List.length input_eq
    simp only [List.length_append] at hlen
    omega
  have hblocksNe : blocks ≠ [] := by
    intro hblocks
    apply hne
    have hflags := layout.flags_eq_flatten
    simpa [hblocks] using hflags
  obtain ⟨block, blocks, rfl⟩ := List.exists_cons_of_ne_nil hblocksNe
  have hownersNe : owners ≠ [] := by
    intro howners
    have hlength := layout.owners_length
    simp [howners] at hlength
  obtain ⟨head, owners, rfl⟩ := List.exists_cons_of_ne_nil hownersNe
  have hheadMemRaw : head ∈
      (liveScheduleCursor parent parentUsed pre post input_eq alpha word).indexOwners := by
    apply resources.active_subset_indexOwners
    rw [hactive]
    simp
  have hfocusRaw :
      List.filterMap ScheduleAtom.indexOwner?
        [((liveScheduleCursor parent parentUsed pre post input_eq alpha word).focus)] = [] := by
    rfl
  have hheadFrameFreshRaw : head ∉
      (liveScheduleCursor parent parentUsed pre post input_eq alpha word).frameOwners := by
    exact (List.disjoint_left.mp hframes) (by simp)
  let normal := resources.normalizeTransientHead hinputPos hactive
    layout.owners_nodup ticketShadowContext ticketOwnerLayout
    (by simpa [parent] using hparentZero)
    (by simpa [parent] using hheadMemRaw)
    (by simpa [parent] using hfocusRaw)
    (by simpa [parent] using hheadFrameFreshRaw)
    (by
      intro candidate hcandidate
      exact hstart.frameOwners_subset_indexOwners hcandidate)
    (by
      intro hmem
      exact False.elim (ticketTransientFree hinputPos hmem))
  have normalParkingBelow : normal.tickets.ParkingBelow resources.window := by
    exact normal.parkingBelow hparentZero parkingBelow
  let alignment : ProtectedFreshPushHeadAlignment resources normal := by
    have houtPrimary : OutsideProductiveWindow resources.window
        (IndexTicket.semanticOwner (g := g)
          resources.window.parkingTicket) := by
      right
      have hend := resources.window.end_le
      simp only [IndexTicket.semanticOwner,
        ProductiveOwnerWindow.parkingTicket_val]
      omega
    have houtShadow : OutsideShadowWindow resources.window.pushChild
        (IndexTicket.semanticOwner (g := g)
          resources.window.parkingTicket) := by
      right
      have hend := resources.window.pushChild.end_le
      simp only [IndexTicket.semanticOwner,
        ProductiveOwnerWindow.parkingTicket_val, shadowOwnerOffset]
      omega
    exact normal.parkForProtectedFreshPush (by simpa [parent] using hparentZero)
      normalParkingBelow
      (by simpa [parent] using hheadMemRaw) houtPrimary houtShadow
  let startLedger : ScheduleOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      resources.ownerLedger
  let startTickets : IndexTicketLedger startCursor := by
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      alignment.tickets
  let normalTickets : IndexTicketLedger startCursor := by
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      normal.tickets
  let normalTicketOwnerLedger : normalTickets.SemanticScheduleOwnerLedger parent
      resources.window := by
    simpa [normalTickets, startCursor, parent, parentTask, liveScheduleCursor] using
      normal.ticketOwnerLedger
  let normalTicketShadowLedger : normalTickets.SemanticShadowOwnerLedger parent
      resources.window := by
    simpa [normalTickets, startCursor, parent, parentTask, liveScheduleCursor] using
      normal.ticketShadowLedger
  let startShadowLedger : ShadowOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      resources.shadowLedger
  have startActive : startLedger.active = head :: owners := by
    simpa [startLedger, startCursor, parent, parentTask, liveScheduleCursor] using
      hactive
  rcases ticketShadowContext with
    ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩
  have normalTicketActive : normalTicketOwnerLedger.active =
      normalTickets.semanticOwners (head :: owners) := by
    have hbase : normalTicketOwnerLedger.active =
        normalTickets.semanticOwners startLedger.active := by
      simpa [normalTicketOwnerLedger, normalTickets, startLedger, startCursor,
        parent, parentTask, liveScheduleCursor] using normal.ticket_active_eq
    exact hbase.trans (congrArg normalTickets.semanticOwners startActive)
  have normalTicketShadowActive : normalTicketShadowLedger.active =
      normalTickets.semanticOwners (head :: (owners ++ parkedOwners)) := by
    have hbase : normalTicketShadowLedger.active =
        normalTickets.semanticOwners resources.ticketShadowOwners := by
      simpa [normalTicketShadowLedger, normalTickets, startCursor, parent,
        parentTask, liveScheduleCursor] using normal.ticket_shadow_active_eq
    rw [hcontextOwners] at hbase
    simpa only [List.cons_append] using hbase
  have normalTicketOwnerLayout : normalTickets.EventTicketLayout parent
      resources.window (block :: blocks) (head :: owners) := by
    simpa [normalTickets, startCursor, parent, parentTask, liveScheduleCursor] using
      normal.eventLayout
  have normalTicketShadowLayout : normalTickets.ShadowTicketLayout parent
      resources.window (block :: (blocks ++ parkedBlocks))
        (head :: (owners ++ parkedOwners)) := by
    have hold := normal.fullShadowLayout
    rw [hcontextBlocks, hcontextOwners] at hold
    simpa only [List.cons_append] using hold
  have startTicketTransientFree : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∉
        startCursor.indexTickets startTickets.ticketOf := by
    intro hinput
    simpa [startTickets, startCursor, parent, parentTask, liveScheduleCursor] using
      alignment.transient_fresh hinput
  have startOwnerLayout : EventOwnedLayout parent resources.window (block :: blocks)
      startLedger.active := by
    rw [startActive]
    exact ownerLayout
  have startShadowActiveEq : startShadowLedger.active = startLedger.active := by
    simpa [startShadowLedger, startLedger, startCursor, parent, parentTask,
      liveScheduleCursor] using resources.shadow_active_eq
  have startRightNodup :
      (head :: (owners ++ startLedger.outside)).Nodup := by
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
    have hrightNodup := hstart'.indexOwners_nodup.sublist hrightSublist
    rw [startLedger.right_eq, startActive] at hrightNodup
    simpa only [List.cons_append] using hrightNodup
  have hheadRightTailFresh : head ∉ owners ++ startLedger.outside :=
    (List.nodup_cons.mp startRightNodup).1
  have htransientStart : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
        startCursor.indexOwners := by
    intro hinput
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      transientFree hinput
  have hscratchStart : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
        startCursor.indexOwners := by
    intro hinput
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      scratchFree hinput
  obtain ⟨newOwner, freeTail, hfreeEq⟩ := List.exists_cons_of_ne_nil hfree
  have hnewFresh : newOwner ∉ startCursor.indexOwners :=
    resources.pool.head_fresh hfreeEq
  have hnewFree : newOwner ∈ resources.pool.free := by simp [hfreeEq]
  have hnewGeneric : newOwner ∈ genericOwnerRange g input := by
    exact resources.pool.all_perm.mem_iff.mp
      (List.mem_append_right startCursor.indexOwners hnewFree)
  have hheadOwner :
      ((∃ h₁ : 1 ∈ rest.eventDepths,
          newOwner = resources.window.pushChild.eventOwner 1 h₁) ∨
        OutsideProductiveWindow resources.window.pushChild newOwner) :=
    Or.inr (resources.window.pushChild.genericOwner_outside hnewGeneric)
  have hnewShadowOutside : OutsideShadowWindow resources.window.pushChild newOwner :=
    OutsideShadowWindow.genericOwner resources.window.pushChild hnewGeneric
  have hnewTransientNe : ∀ hinput : 0 < input.length,
      newOwner ≠ ProductiveOwnerWindow.transientOwner (g := g) hinput := by
    intro hinput heq
    have hge := genericOwnerRange_val_ge hnewGeneric
    have hval := congrArg Fin.val heq
    simp only [genericOwnerOffset, ProductiveOwnerWindow.transientOwner_val] at hge hval
    omega
  have hnewScratchNe : ∀ hinput : 0 < input.length,
      newOwner ≠ ProductiveOwnerWindow.scratchOwner (g := g) hinput := by
    intro hinput heq
    have hge := genericOwnerRange_val_ge hnewGeneric
    have hval := congrArg Fin.val heq
    simp only [genericOwnerOffset, ProductiveOwnerWindow.scratchOwner_val] at hge hval
    omega
  have hchildTransientSafe : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.transientOwner (g := g) hinput ∈
          newOwner :: startCursor.indexOwners →
        0 ∉ rest.eventDepths := by
    intro hinput hmem
    rcases List.mem_cons.mp hmem with heq | hold
    · exact False.elim (hnewTransientNe hinput heq.symm)
    · exact False.elim (htransientStart hinput hold)
  let owned : ScheduleIndex g input := {
    flags := [f]
    relation := cflagBase g f
    mark := .laterPending
    denotes := .base f
    owner := newOwner
  }
  let childCursor : ScheduleCursor g input :=
    liveScheduleCursor rest childUsed pre post input_eq alpha (.index owned :: word)
  have htaskOwner : childTask.owner = parentTask.owner := by
    apply Fin.ext
    rfl
  have hchildInv : ScheduleInvariant childCursor := by
    dsimp [childCursor, startCursor]
    exact ScheduleInvariant.plainPushUse (alpha ++ [ScheduleAtom.dollar]) word
      parentTask childTask owned htaskOwner hnewFresh
      (resources.pool.index_count_lt_of_free_ne_nil hfree) hstart'
  have hindexPerm : childCursor.indexOwners.Perm
      (newOwner :: startCursor.indexOwners) := by
    simp only [childCursor, startCursor, liveScheduleCursor,
      ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?,
      List.filterMap_cons, List.filterMap_nil, List.append_nil, owned]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.indexOwner?)
        (l₂ := word.filterMap ScheduleAtom.indexOwner?)
        (a := newOwner))
  let childTicket : IndexTicket input :=
    if 0 ∈ rest.eventDepths then alignment.restore else IndexTicket.transient hinputPos
  have childTicketFresh : childTicket ∉
      startCursor.indexTickets startTickets.ticketOf := by
    dsimp [childTicket]
    split_ifs with hchildZero
    · simpa [startTickets, startCursor, parent, parentTask, liveScheduleCursor] using
        alignment.restore_fresh
    · exact startTicketTransientFree hinputPos
  have childTicketNotScratch : ∀ h : 0 < input.length,
      childTicket ≠ IndexTicket.scratch h := by
    intro h
    dsimp [childTicket]
    split_ifs
    · exact alignment.restore_not_scratch h
    · intro heq
      have hval := congrArg Fin.val heq
      simp only [IndexTicket.transient_val, IndexTicket.scratch_val] at hval
      omega
  have childTicketNonparking : childTicket.Nonparking := by
    dsimp [childTicket]
    split_ifs
    · exact alignment.restore_nonparking
    · exact IndexTicket.transient_nonparking hinputPos
  let childTickets : IndexTicketLedger childCursor :=
    startTickets.allocate newOwner childTicket hnewFresh childTicketFresh
      childTicketNotScratch hindexPerm
  have childParkingAtOrBelow :
      childTickets.ParkingAtOrBelow resources.window.pushChild := by
    have hstart : startTickets.ParkingAtOrBelow resources.window := by
      simpa [startTickets, startCursor, parent, parentTask, liveScheduleCursor] using
        alignment.parkingAtOrBelow
    have hallocated := hstart.allocate_nonparking newOwner
      childTicket hnewFresh childTicketFresh childTicketNotScratch hindexPerm
      childTicketNonparking
    simpa [childTickets] using hallocated.mono (by simp)
  have childTicketOfNewOwner : childTickets.ticketOf newOwner =
      childTicket := by
    simp [childTickets]
  have childTicketOf_eq_of_start_mem
      {candidate : Fin (10 * input.length)}
      (hcandidate : candidate ∈ startCursor.indexOwners) :
      childTickets.ticketOf candidate = startTickets.ticketOf candidate := by
    simpa [childTickets, IndexTicketLedger.allocate] using
      startTickets.insertTicket_eq_of_mem newOwner
        childTicket hcandidate hnewFresh
  have htasks : childCursor.taskOwners = startCursor.taskOwners := by
    simp only [childCursor, startCursor, liveScheduleCursor,
      ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?,
      List.filterMap_cons, List.filterMap_nil]
    rw [htaskOwner]
  have hframesEq : childCursor.frameOwners = startCursor.frameOwners := by
    simp [childCursor, startCursor, liveScheduleCursor,
      ScheduleCursor.frameOwners, ScheduleCursor.word,
      ScheduleAtom.closeOwner?, List.filterMap_append]
  have childTicketFramesEq : childTickets.semanticCursor.frameOwners =
      startTickets.semanticCursor.frameOwners := by
    rw [childTickets.semanticCursor_frameOwners,
      startTickets.semanticCursor_frameOwners, hframesEq]
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [childTicketOf_eq_of_start_mem
      (hstart'.frameOwners_subset_indexOwners hcandidate)]
  have childTicketRightTailEq :
      (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
          childTickets.semanticOwnerOf =
        (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
          startTickets.semanticOwnerOf := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    apply childTicketOf_eq_of_start_mem
    rw [ScheduleCursor.indexOwners_mk]
    exact List.mem_append_right _ hcandidate
  have childSemanticSelectedTailEq : childTickets.semanticOwners owners =
      startTickets.semanticOwners owners := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [childTicketOf_eq_of_start_mem]
    rw [ScheduleCursor.indexOwners_mk]
    apply List.mem_append_right
    rw [startLedger.right_eq, startActive]
    exact List.mem_append_left _ (List.mem_cons_of_mem head hcandidate)
  have childSemanticContextTailEq :
      childTickets.semanticOwners (owners ++ parkedOwners) =
        startTickets.semanticOwners (owners ++ parkedOwners) := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    rw [childTicketOf_eq_of_start_mem]
    have hold : candidate ∈ resources.ticketShadowOwners := by
      rw [hcontextOwners]
      exact List.mem_cons_of_mem head hcandidate
    simpa [startCursor, parent, parentTask, liveScheduleCursor] using
      resources.ticketShadowOwners_subset hold
  have childSemanticOldHead : childTickets.semanticOwnerOf head =
      alignment.oldSemantic := by
    calc
      childTickets.semanticOwnerOf head = startTickets.semanticOwnerOf head := by
        simp only [IndexTicketLedger.semanticOwnerOf]
        rw [childTicketOf_eq_of_start_mem hheadMemRaw]
      _ = alignment.oldSemantic := by
        simpa [startTickets, startCursor, parent, parentTask,
          liveScheduleCursor] using alignment.head_semantic
  have startSemanticSelectedTailEqNormal :
      startTickets.semanticOwners owners = normalTickets.semanticOwners owners := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    have hcandidateIndex : candidate ∈ startCursor.indexOwners := by
      apply resources.active_subset_indexOwners
      rw [hactive]
      exact List.mem_cons_of_mem head hcandidate
    have hcandidateNe : candidate ≠ head := by
      intro heq
      subst candidate
      exact (List.nodup_cons.mp layout.owners_nodup).1 hcandidate
    simpa [startTickets, normalTickets, startCursor, parent, parentTask,
      liveScheduleCursor] using
        alignment.unchanged_normal candidate hcandidateIndex hcandidateNe
  have startSemanticContextTailEqNormal :
      startTickets.semanticOwners (owners ++ parkedOwners) =
        normalTickets.semanticOwners (owners ++ parkedOwners) := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    have hcandidateContext : candidate ∈ resources.ticketShadowOwners := by
      rw [hcontextOwners]
      exact List.mem_cons_of_mem head hcandidate
    have hcandidateIndex : candidate ∈ startCursor.indexOwners := by
      simpa [startCursor, parent, parentTask, liveScheduleCursor] using
        resources.ticketShadowOwners_subset hcandidateContext
    have hcandidateNe : candidate ≠ head := by
      intro heq
      subst candidate
      have hcontextNodup := resources.ticketShadowOwners_nodup
      rw [hcontextOwners] at hcontextNodup
      exact (List.nodup_cons.mp hcontextNodup).1 hcandidate
    simpa [startTickets, normalTickets, startCursor, parent, parentTask,
      liveScheduleCursor] using
        alignment.unchanged_normal candidate hcandidateIndex hcandidateNe
  have childTicketFramesEqNormal : childTickets.semanticCursor.frameOwners =
      normalTickets.semanticCursor.frameOwners := by
    rw [childTicketFramesEq]
    rw [startTickets.semanticCursor_frameOwners,
      normalTickets.semanticCursor_frameOwners]
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    have hcandidateIndex := hstart'.frameOwners_subset_indexOwners hcandidate
    have hcandidateNe : candidate ≠ head := by
      intro heq
      subst candidate
      exact hheadFrameFreshRaw hcandidate
    simpa [startTickets, normalTickets, startCursor, parent, parentTask,
      liveScheduleCursor] using
        alignment.unchanged_normal candidate hcandidateIndex hcandidateNe
  have childSemanticOutsideEqNormal :
      childTickets.semanticOwners startLedger.outside =
        normalTickets.semanticOwners startLedger.outside := by
    apply List.map_congr_left
    intro candidate hcandidate
    simp only [IndexTicketLedger.semanticOwnerOf]
    apply congrArg (IndexTicket.semanticOwner (g := g))
    rw [childTicketOf_eq_of_start_mem]
    · have hcandidateIndex : candidate ∈ startCursor.indexOwners := by
        rw [ScheduleCursor.indexOwners_mk]
        apply List.mem_append_right
        rw [startLedger.right_eq, startActive]
        exact List.mem_append_right (head :: owners) hcandidate
      have hcandidateNe : candidate ≠ head := by
        intro heq
        subst candidate
        exact hheadRightTailFresh
          (List.mem_append_right owners hcandidate)
      simpa [startTickets, normalTickets, startCursor, parent, parentTask,
        liveScheduleCursor] using
          alignment.unchanged_normal candidate hcandidateIndex hcandidateNe
    · rw [ScheduleCursor.indexOwners_mk]
      apply List.mem_append_right
      rw [startLedger.right_eq, startActive]
      exact List.mem_append_right (head :: owners) hcandidate
  let childPrefixLedger : PrefixFrameLedger childCursor :=
    startLedger.prefixLedger.transport
      (by rfl)
      (by rw [hframesEq])
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
  let childOwnerLayout : EventOwnedLayout rest resources.window.pushChild
      (owned.flags :: block :: blocks) (owned.owner :: head :: owners) := by
    simpa [owned] using ownerLayout.pushFresh hheadOwner
  let childOwnerLedger : ScheduleOwnerLedger rest resources.window.pushChild
      childCursor := {
    active := newOwner :: head :: owners
    outside := startLedger.outside
    right_eq := by
      have hright := startLedger.right_eq
      rw [startActive] at hright
      simpa [childCursor, startCursor, owned, liveScheduleCursor,
        ScheduleAtom.indexOwner?] using congrArg (List.cons newOwner) hright
    outside_at := fun candidate hcandidate =>
      EventOwnedLayout.outside_pushChild resources.window
        (startLedger.outside_at candidate hcandidate)
    frames := by
      rw [hframesEq]
      exact startLedger.frames.push
    prefixLedger := childPrefixLedger
  }
  have childSemanticHead : childTickets.semanticOwnerOf newOwner =
      IndexTicket.semanticOwner (g := g) childTicket := by
    simp [IndexTicketLedger.semanticOwnerOf, childTicketOfNewOwner]
  have childSemanticHeadOutsidePrimary : OutsideProductiveWindow
      resources.window.pushChild (childTickets.semanticOwnerOf newOwner) := by
    rw [childSemanticHead]
    dsimp [childTicket]
    split_ifs with hchildZero
    · simpa [ProductiveOwnerWindow.pushChild] using alignment.restore_outside_parent
    · exact resources.window.pushChild.transientOwner_outside hinputPos
  have childSemanticHeadShadow :
      (∃ hzero : 0 ∈ rest.eventDepths,
        childTickets.semanticOwnerOf newOwner =
          resources.window.pushChild.shadowEventOwner 0 hzero) ∨
      OutsideShadowWindow resources.window.pushChild
        (childTickets.semanticOwnerOf newOwner) := by
    rw [childSemanticHead]
    dsimp [childTicket]
    split_ifs with hchildZero
    · left
      refine ⟨hchildZero, ?_⟩
      rcases alignment.restore_shadow_zero with ⟨parentZero, hrestore⟩
      rw [hrestore]
      have hshift := resources.window.shadowEventOwner_push parentZero
      have hpreimage : NFParse.pushEventPreimage rest.eventDepths 0 = 0 := by
        simp [NFParse.pushEventPreimage, hchildZero]
      simpa [hpreimage] using hshift
    · right
      exact OutsideShadowWindow.transientOwner resources.window.pushChild hinputPos
  have alignedOldOutsideParent : OutsideProductiveWindow resources.window
      alignment.oldSemantic := by
    exact alignment.old_outside_parent
  let alignedParentTicketOwnerLayout : EventOwnedLayout parent resources.window
      (block :: blocks)
      (alignment.oldSemantic :: normalTickets.semanticOwners owners) :=
    normalTicketOwnerLayout.reownerHeadOutside alignedOldOutsideParent
  let childTicketOwnerLayout : childTickets.EventTicketLayout rest
      resources.window.pushChild (owned.flags :: block :: blocks)
        (owned.owner :: head :: owners) := by
    change EventOwnedLayout rest resources.window.pushChild ([f] :: block :: blocks)
      (childTickets.semanticOwnerOf newOwner :: childTickets.semanticOwnerOf head ::
        childTickets.semanticOwners owners)
    rw [childSemanticOldHead, childSemanticSelectedTailEq,
      startSemanticSelectedTailEqNormal]
    exact alignedParentTicketOwnerLayout.pushFresh
      (Or.inr childSemanticHeadOutsidePrimary)
  have normalTicketOwnerOutsideEq : normalTicketOwnerLedger.outside =
      normalTickets.semanticOwners startLedger.outside := by
    have heq := normalTicketOwnerLedger.right_eq
    rw [normalTickets.semanticCursor_right_indexOwners,
      startLedger.right_eq, startActive, List.map_append,
      normalTicketActive] at heq
    have heq' :
        normalTickets.semanticOwners (head :: owners) ++
            normalTickets.semanticOwners startLedger.outside =
          normalTickets.semanticOwners (head :: owners) ++
            normalTicketOwnerLedger.outside := by
      simpa only [IndexTicketLedger.semanticOwners] using heq
    exact (List.append_cancel_left heq').symm
  let childTicketOwnerLedger : childTickets.SemanticScheduleOwnerLedger rest
      resources.window.pushChild := {
    active := childTickets.semanticOwners (newOwner :: head :: owners)
    outside := normalTicketOwnerLedger.outside
    right_eq := by
      rw [childTickets.semanticCursor_right_indexOwners]
      change childTickets.semanticOwnerOf newOwner ::
          (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
            childTickets.semanticOwnerOf = _
      rw [startLedger.right_eq, startActive]
      simp only [List.map_append, List.map_cons,
        IndexTicketLedger.semanticOwners]
      rw [childSemanticOldHead]
      rw [show owners.map childTickets.semanticOwnerOf =
          owners.map normalTickets.semanticOwnerOf by
        simpa [IndexTicketLedger.semanticOwners] using
          childSemanticSelectedTailEq.trans startSemanticSelectedTailEqNormal]
      rw [show startLedger.outside.map childTickets.semanticOwnerOf =
          startLedger.outside.map normalTickets.semanticOwnerOf by
        simpa [IndexTicketLedger.semanticOwners] using
          childSemanticOutsideEqNormal]
      rw [normalTicketOwnerOutsideEq]
      simp [IndexTicketLedger.semanticOwners]
    outside_at := fun candidate hcandidate =>
      EventOwnedLayout.outside_pushChild resources.window
        (normalTicketOwnerLedger.outside_at candidate hcandidate)
    frames := by
      rw [childTicketFramesEqNormal]
      exact normalTicketOwnerLedger.frames.push
    prefixLedger := childTicketPrefixLedger
  }
  let childShadowLedger : ShadowOwnerLedger rest resources.window.pushChild
      childCursor := {
    active := newOwner :: head :: owners
    outside := startShadowLedger.outside
    right_eq := by
      have hright := startShadowLedger.right_eq
      have hshadowActive : startShadowLedger.active = head :: owners :=
        startShadowActiveEq.trans startActive
      rw [hshadowActive] at hright
      simpa [childCursor, startCursor, owned, liveScheduleCursor,
        ScheduleAtom.indexOwner?] using congrArg (List.cons newOwner) hright
    outside_at := fun candidate hcandidate => by
      simpa [ProductiveOwnerWindow.pushChild] using
        OutsideShadowWindow.transport resources.window (by rfl)
          (startShadowLedger.outside_at candidate hcandidate)
    frames := by
      rw [hframesEq]
      simpa [ProductiveOwnerWindow.pushChild] using
        startShadowLedger.frames.transportEqual (residual := rest) (by rfl)
    prefixLedger := childPrefixLedger
  }
  have childSemanticContextTailEqNormal :
      childTickets.semanticOwners (owners ++ parkedOwners) =
        normalTickets.semanticOwners (owners ++ parkedOwners) :=
    childSemanticContextTailEq.trans startSemanticContextTailEqNormal
  have childSemanticParkedEqNormal :
      childTickets.semanticOwners parkedOwners =
        normalTickets.semanticOwners parkedOwners := by
    have hcontext := childSemanticContextTailEqNormal
    simp only [IndexTicketLedger.semanticOwners, List.map_append] at hcontext ⊢
    have howners : owners.map childTickets.semanticOwnerOf =
        owners.map normalTickets.semanticOwnerOf := by
      simpa [IndexTicketLedger.semanticOwners] using
        childSemanticSelectedTailEq.trans startSemanticSelectedTailEqNormal
    rw [howners] at hcontext
    exact List.append_cancel_left hcontext
  have childSemanticOutsideAndTailEqNormal :
      childTickets.semanticOwners (owners ++ startLedger.outside) =
        normalTickets.semanticOwners (owners ++ startLedger.outside) := by
    simpa [IndexTicketLedger.semanticOwners, List.map_append] using
      congrArg₂ (fun left right => left ++ right)
        (childSemanticSelectedTailEq.trans startSemanticSelectedTailEqNormal)
        childSemanticOutsideEqNormal
  have normalTicketShadowTailEq :
      normalTickets.semanticOwners (owners ++ startLedger.outside) =
        normalTickets.semanticOwners (owners ++ parkedOwners) ++
          normalTicketShadowLedger.outside := by
    have heq := normalTicketShadowLedger.right_eq
    rw [normalTickets.semanticCursor_right_indexOwners,
      startLedger.right_eq, startActive, normalTicketShadowActive] at heq
    have htail := congrArg List.tail heq
    simpa [IndexTicketLedger.semanticOwners] using htail
  let childTicketShadowLedger : childTickets.SemanticShadowOwnerLedger rest
      resources.window.pushChild := {
    active := childTickets.semanticOwners
      (newOwner :: head :: (owners ++ parkedOwners))
    outside := normalTicketShadowLedger.outside
    right_eq := by
      rw [childTickets.semanticCursor_right_indexOwners]
      change childTickets.semanticOwnerOf newOwner ::
          (startCursor.right.filterMap ScheduleAtom.indexOwner?).map
            childTickets.semanticOwnerOf = _
      rw [startLedger.right_eq, startActive]
      simp only [List.map_cons, List.map_append]
      rw [childSemanticOldHead]
      simp only [IndexTicketLedger.semanticOwners, List.map_cons, List.map_append]
      rw [show owners.map childTickets.semanticOwnerOf =
          owners.map normalTickets.semanticOwnerOf by
        simpa [IndexTicketLedger.semanticOwners] using
          childSemanticSelectedTailEq.trans startSemanticSelectedTailEqNormal]
      rw [show startLedger.outside.map childTickets.semanticOwnerOf =
          startLedger.outside.map normalTickets.semanticOwnerOf by
        simpa [IndexTicketLedger.semanticOwners] using
          childSemanticOutsideEqNormal]
      rw [childSemanticOldHead]
      rw [show parkedOwners.map childTickets.semanticOwnerOf =
          parkedOwners.map normalTickets.semanticOwnerOf by
        simpa [IndexTicketLedger.semanticOwners] using
          childSemanticParkedEqNormal]
      simpa [IndexTicketLedger.semanticOwners, List.map_append,
        List.append_assoc] using congrArg
          (fun tail => childTickets.semanticOwnerOf newOwner ::
            alignment.oldSemantic :: tail)
          normalTicketShadowTailEq
    outside_at := fun candidate hcandidate => by
      simpa [ProductiveOwnerWindow.pushChild] using
        OutsideShadowWindow.transport resources.window (residual := rest) (by rfl)
          (normalTicketShadowLedger.outside_at candidate hcandidate)
    frames := by
      rw [childTicketFramesEqNormal]
      simpa [ProductiveOwnerWindow.pushChild] using
        normalTicketShadowLedger.frames.transportEqual
          (residual := rest) (by rfl)
    prefixLedger := childTicketPrefixLedger
  }
  let childTicketShadowLayout : childTickets.ShadowTicketLayout rest
      resources.window.pushChild
      (owned.flags :: block :: (blocks ++ parkedBlocks))
      (owned.owner :: head :: (owners ++ parkedOwners)) := by
    change ShadowStartLayout rest resources.window.pushChild
      ([f] :: block :: (blocks ++ parkedBlocks))
      (childTickets.semanticOwnerOf newOwner :: childTickets.semanticOwnerOf head ::
        childTickets.semanticOwners (owners ++ parkedOwners))
    rw [childSemanticOldHead,
      childSemanticContextTailEqNormal]
    exact normalTicketShadowLayout.pushFreshAlignHead
      childSemanticHeadShadow
      alignment.old_shadow_child
  let childPool : IndexOwnerPool childCursor :=
    resources.pool.allocateMember newOwner hnewFree hindexPerm
  let childResources : ScheduleRunResources rest pre childCursor := {
    pool := childPool
    tickets := childTickets
    window := resources.window.pushChild
    parkingAtOrBelow := childParkingAtOrBelow
    ownerLedger := childOwnerLedger
    ticketOwnerLedger := childTicketOwnerLedger
    ticket_active_eq := by rfl
    ticketShadowBlocks := owned.flags :: block :: (blocks ++ parkedBlocks)
    ticketShadowOwners := owned.owner :: head :: (owners ++ parkedOwners)
    ticketShadowOwners_subset := by
      intro candidate hcandidate
      rcases List.mem_cons.mp hcandidate with hnew | hold
      · subst candidate
        simpa [owned] using hindexPerm.mem_iff.mpr
          (by simp : newOwner ∈ newOwner :: startCursor.indexOwners)
      · have holdContext : candidate ∈ resources.ticketShadowOwners := by
          rw [hcontextOwners]
          exact hold
        have holdStart : candidate ∈ startCursor.indexOwners := by
          simpa [startCursor, parent, parentTask, liveScheduleCursor] using
            resources.ticketShadowOwners_subset holdContext
        exact hindexPerm.mem_iff.mpr (List.mem_cons_of_mem newOwner holdStart)
    ticketShadowOwners_nodup := by
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        apply hnewFresh
        have holdContext : newOwner ∈ resources.ticketShadowOwners := by
          rw [hcontextOwners]
          exact hmem
        simpa [startCursor, parent, parentTask, liveScheduleCursor] using
          resources.ticketShadowOwners_subset holdContext
      · have hold := resources.ticketShadowOwners_nodup
        rw [hcontextOwners] at hold
        simpa only [List.cons_append] using hold
    ticketShadowLedger := childTicketShadowLedger
    ticket_shadow_active_eq := by rfl
    ticketShadowLayout := childTicketShadowLayout
    shadowLedger := childShadowLedger
    shadow_active_eq := by rfl
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
      have hfreeLen := (List.perm_cons_erase hnewFree).length_eq
      change rest.productiveCount ≤ resources.charged + 1 +
        (resources.pool.free.erase newOwner).length
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
  let childRestoreData : OverlayRestoreData childResources [owned]
      (block :: blocks) (head :: owners) := {
    marker := head
    base_head := ⟨block, blocks, owners, rfl, rfl⟩
    parkingAtOrBelow := by
      simpa [childResources] using childParkingAtOrBelow
    marker_live := by
      apply hindexPerm.mem_iff.mpr
      exact List.mem_cons_of_mem newOwner hheadMemRaw
    marker_ticket := by
      change childTickets.ticketOf head = childResources.window.parkingTicket
      calc
        childTickets.ticketOf head = startTickets.ticketOf head :=
          childTicketOf_eq_of_start_mem hheadMemRaw
        _ = resources.window.parkingTicket := by
          simpa [startTickets, startCursor, parent, parentTask,
            liveScheduleCursor] using alignment.head_parking
        _ = childResources.window.parkingTicket := rfl
    restore := alignment.restore
    restore_nonparking := alignment.restore_nonparking
    restore_not_scratch := alignment.restore_not_scratch
    restore_not_transient := alignment.restore_not_transient
    restore_outside_primary := by
      simpa [childResources, ProductiveOwnerWindow.pushChild] using
        alignment.restore_outside_parent
    available := by
      by_cases hchildZero : 0 ∈ rest.eventDepths
      · right
        refine ⟨owned, by simp, ?_⟩
        change childTickets.ticketOf newOwner = alignment.restore
        exact childTicketOfNewOwner.trans (by simp [childTicket, hchildZero])
      · left
        have hrestoreFresh : alignment.restore ∉
            startCursor.indexTickets startTickets.ticketOf := by
          simpa [startTickets, startCursor, parent, parentTask,
            liveScheduleCursor] using alignment.restore_fresh
        have hne : alignment.restore ≠ childTicket := by
          simpa [childTicket, hchildZero] using
            alignment.restore_not_transient hinputPos
        change alignment.restore ∉
          childCursor.indexTickets childTickets.ticketOf
        exact startTickets.allocate_preserves_fresh newOwner childTicket
          alignment.restore hnewFresh childTicketFresh childTicketNotScratch
          hindexPerm hrestoreFresh hne
    depth := NFParse.pushEventPreimage rest.eventDepths 0
    depth_le := by
      by_cases hchildZero : 0 ∈ rest.eventDepths <;>
        simp [NFParse.pushEventPreimage, owned, hchildZero]
    aligned := by
      left
      refine ⟨NFParse.pushEventPreimage_mem hparentZero, ?_⟩
      rcases alignment.restore_shadow_zero with ⟨parentZero, hrestore⟩
      have hshift := resources.window.shadowEventOwner_push parentZero
      simpa [childResources] using hrestore.trans hshift
  }
  let childParkingContext : OverlayParkingContext childResources [owned]
      (block :: blocks) (head :: owners) := .attached childRestoreData
  let childOverlayLayout : AdjacentOverlayLayout layout [owned] :=
    AdjacentOverlayLayout.singleton layout owned (by simp [owned])
      (by intro _; rfl) (by
        intro hmem
        apply hnewFresh
        apply resources.active_subset_indexOwners
        rw [hactive]
        exact hmem)
  have childFree : childResources.pool.free ≠ [] := by
    apply childResources.free_ne_nil_of_index_count_lt
    simpa [childResources] using childTickets.index_count_lt hinputPos
  have hchildCredit : 0 < childResources.charged := by
    dsimp [childResources]
    omega
  have hallRest : ∀ k < owned.flags.length + visible.length,
      rest.ConsumesAt k := by
    intro k hk
    cases k with
    | zero => exact childUsed
    | succ k =>
        have hk' : k < visible.length := by
          simp only [owned, List.length_singleton] at hk
          omega
        simpa [parent, NFParse.ConsumesAt] using hall k hk'
  have hboundaryRest :
      ¬ rest.ConsumesAt (owned.flags.length + visible.length) := by
    simpa [parent, owned, NFParse.ConsumesAt, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hboundary
  have hstackRest : f :: stack = owned.flags ++ visible ++ hidden := by
    simp [owned, hstack]
  have compatibleRest : EventCompatible rest (owned.flags :: block :: blocks) := by
    simpa [owned] using EventCompatible.pushFresh compatible
  have hword : word ≠ [] := layout.input_ne_nil_of_flags_ne hne
  have hused : used ≠ [] := layout.output_ne_nil_of_flags_ne hne
  have hframesRest : List.Disjoint (owned.owner :: head :: owners)
      childCursor.frameOwners := by
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
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos startCursor hstart'
  let childState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos childCursor hchildInv
  have hpush : ScheduleReaches g input startState childState := by
    obtain ⟨next, tail, hwordEq⟩ := List.exists_cons_of_ne_nil hword
    subst word
    apply ScheduleReaches.single
    have hstep := composite_livePushFresh_at input
      (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) pre.length
      (alpha.map ScheduleAtom.workSym) next.workSym
      (tail.map ScheduleAtom.workSym)
    simpa [startState, childState, scheduleStateOfCursor, ScheduleState.config,
      startCursor, childCursor, liveScheduleCursor, parentTask, childTask, parent, owned,
      scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
      ScheduleTask.workSym, List.map_append] using hstep
  let childShadowLayout : ShadowStartLayout rest childResources.window
      (owned.flags :: block :: blocks) (owned.owner :: head :: owners) :=
    childResources.genericShadowStartLayout (by
      simp [childResources, childOwnerLedger, owned])
      (by simpa [owned] using childOwnerLayout.owners_length)
      (by
        intro block hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · simp [owned]
        · exact shadowLayout.block_nonempty block htail)
  have childTicketShadowContext : childResources.TicketShadowContextExtends
      (owned.flags :: block :: blocks) (owned.owner :: head :: owners) := by
    refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
    · simp [childResources, owned]
    · simp [childResources, owned]
  have childTicketTransientHead : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∈
          childCursor.indexTickets childResources.tickets.ticketOf →
        childResources.tickets.ticketOf owned.owner =
          IndexTicket.transient hinput := by
    intro hinput hmem
    change IndexTicket.transient hinput ∈
      childCursor.indexTickets childTickets.ticketOf at hmem
    have hallocated := startTickets.allocate_ticket_eq_of_mem_of_fresh
      newOwner childTicket (IndexTicket.transient hinput)
      hnewFresh childTicketFresh childTicketNotScratch hindexPerm
      (startTicketTransientFree hinput) hmem
    change childTickets.ticketOf newOwner = IndexTicket.transient hinput
    exact childTicketOfNewOwner.trans hallocated
  have hrestRun := restOverlay (input := input) owned [] visible hidden
    (block :: blocks) (head :: owners) word used
    (by simpa using hstackRest) layout childOverlayLayout
    (by simpa using hallRest) (by simpa using hboundaryRest)
    (by simpa using compatibleRest) hused pre post input_eq alpha hstable
    (by simpa [childCursor, liveScheduleCursor] using hchildInv)
    (by simpa using hframesRest) hend childResources childParkingContext childFree
    hchildCredit (by simpa using childOwnerLayout)
    (by simpa using childShadowLayout) (by simpa using childTicketOwnerLayout)
    (by simpa using childTicketShadowContext)
    (by simpa using childTicketTransientHead)
    (by rfl) (by
      intro hinput hmem
      rcases List.mem_cons.mp (hindexPerm.mem_iff.mp hmem) with heq | hold
      · simpa [owned] using heq.symm
      · exact False.elim (htransientStart hinput hold)) (by
      intro hinput hmem
      rcases List.mem_cons.mp (hindexPerm.mem_iff.mp hmem) with heq | hold
      · simpa [owned] using heq.symm
      · exact False.elim (hscratchStart hinput hold))
  simpa [startState, childState, parent, parentTask, liveScheduleCursor,
    scheduleStateOfCursor] using hpush.trans hrestRun

/-- A terminal parse never enters protected mode. -/
public theorem protectedScheduleRun_terminal_false
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    ProtectedScheduleRun (NFParse.terminal (σ := stack) hr hlhs hc hrhs) := by
  intro input visible hidden blocks owners word used hstack hne hall
  have htop := hall 0 (List.length_pos_of_ne_nil hne)
  simp [NFParse.ConsumesAt] at htop

end Aho
end IndexedGrammar
