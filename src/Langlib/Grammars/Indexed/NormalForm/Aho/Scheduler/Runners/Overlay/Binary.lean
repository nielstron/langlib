module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Runners.Overlay.Interface
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Runners.Protected.Structural

@[expose]
public section

/-!
# Binary events in a copy-on-write overlay

At a binary fork the complete adjacent overlay becomes shared by the two children.  We can
therefore forget its branch-local classification, run the existing protected binary scheduler
on `AdjacentOverlayLayout.toProtected`, and then erase the marked private indices one at a time.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Erase a marked adjacent prefix from left to right.  Removing an index does not change the
frame-owner list, so the single disjointness certificate for the marked word remains valid at
every recursive step. -/
private theorem eraseMarkedOverlay
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input))
    (used : List (ScheduleAtom g input)) (hused : used ≠ [])
    (inputPos : ℕ) (hpos : inputPos ≤ input.length)
    (alpha : List (ScheduleAtom g input))
    (hstart : ScheduleInvariant
      (scheduleWordCursor alpha (ScheduleOverlay.used overlay used)))
    (hend : ScheduleInvariant (scheduleWordCursor alpha used))
    (hunframed : ∀ idx ∈ overlay, idx.owner ∉
      (scheduleWordCursor alpha
        (ScheduleOverlay.used overlay used)).frameOwners) :
    ScheduleReaches g input
      (scheduleStateOfCursor inputPos hpos _ hstart)
      (scheduleStateOfCursor inputPos hpos _ hend) := by
  induction overlay with
  | nil =>
      simpa using ScheduleReaches.refl
        (scheduleStateOfCursor inputPos hpos (scheduleWordCursor alpha used) hend)
  | cons idx overlay ih =>
      have htailUsed : ScheduleOverlay.used overlay used ≠ [] := by
        simp [ScheduleOverlay.used, hused]
      obtain ⟨next, tail, htail⟩ := List.exists_cons_of_ne_nil htailUsed
      have hheadUnframed : idx.owner ∉
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.index idx.markUsed)
            (next :: tail)).frameOwners := by
        have hold := hunframed idx (by simp)
        rw [ScheduleOverlay.used_cons] at hold
        change idx.owner ∉
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.index idx.markUsed)
            (ScheduleOverlay.used overlay used)).frameOwners at hold
        simpa only [htail] using hold
      have herasedInv : ScheduleInvariant
          (scheduleWordCursor alpha (ScheduleOverlay.used overlay used)) := by
        have hcurrent : ScheduleInvariant
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.index idx.markUsed)
              (next :: tail)) := by
          rw [ScheduleOverlay.used_cons] at hstart
          change ScheduleInvariant
            (ScheduleCursor.mk (alpha ++ [.dollar]) (.index idx.markUsed)
              (ScheduleOverlay.used overlay used)) at hstart
          simpa only [htail] using hstart
        have herased := ScheduleInvariant.eraseIndex alpha tail idx.markUsed next
          hheadUnframed hcurrent
        simpa only [htail, scheduleWordCursor] using herased
      let startState : ScheduleState g input :=
        scheduleStateOfCursor inputPos hpos
          (scheduleWordCursor alpha
            (ScheduleOverlay.used (idx :: overlay) used)) hstart
      let erasedState : ScheduleState g input :=
        scheduleStateOfCursor inputPos hpos
          (scheduleWordCursor alpha (ScheduleOverlay.used overlay used)) herasedInv
      have herase : ScheduleReaches g input startState erasedState := by
        apply ScheduleReaches.single
        have hstep := composite_eraseIndex_at input idx.relation
          idx.mark.markUsed (by cases idx.mark <;> rfl) inputPos
          (alpha.map ScheduleAtom.workSym) next.workSym
          (tail.map ScheduleAtom.workSym)
        simpa [startState, erasedState, scheduleStateOfCursor,
          ScheduleState.config, ScheduleOverlay.used_cons, scheduleWordCursor, htail,
          ScheduleCursor.erase, ScheduleAtom.workSym, ScheduleIndex.markUsed,
          List.map_append] using hstep
      have htailUnframed : ∀ candidate ∈ overlay, candidate.owner ∉
          (scheduleWordCursor alpha
            (ScheduleOverlay.used overlay used)).frameOwners := by
        intro candidate hcandidate
        have hold := hunframed candidate (by simp [hcandidate])
        rw [ScheduleOverlay.used_cons] at hold
        change candidate.owner ∉
          (ScheduleCursor.mk (alpha ++ [.dollar]) (.index idx.markUsed)
            (ScheduleOverlay.used overlay used)).frameOwners at hold
        rw [htail]
        cases next <;>
          simpa [htail, scheduleWordCursor, ScheduleCursor.frameOwners,
            ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append,
            List.append_assoc] using hold
      have hrest := ih herasedInv htailUnframed
      exact herase.trans hrest

/-- Seal an arbitrary nonempty overlay at a binary fork, reuse the protected binary runner on
the resulting full block layout, and erase every private marked index before returning to the
protected base endpoint. -/
public theorem overlayScheduleRun_binary
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (leftParse : NFParse g B stack u) (rightParse : NFParse g C stack v)
    (leftRuns : OrdinaryScheduleRuns leftParse)
    (rightRuns : OrdinaryScheduleRuns rightParse) :
    OverlayScheduleRun
      (NFParse.binary hr hlhs hc hrhs leftParse rightParse) := by
  intro input head overlayTail protectedFlags hidden blocks owners word used hstack
    baseLayout overlayLayout hall hboundary compatible hused pre post input_eq alpha
    hstable hstart hframes hend resources baseParking hfree _hcredit ownerLayout shadowLayout
    ticketOwnerLayout ticketShadowContext ticketTransientHead hactive transientHead
    scratchHead
  let parent : NFParse g A stack (u ++ v) :=
    .binary hr hlhs hc hrhs leftParse rightParse
  let overlay : List (ScheduleIndex g input) := head :: overlayTail
  let visible : List g.flag := ScheduleOverlay.flags overlay protectedFlags
  let fullBlocks : List (List g.flag) := ScheduleOverlay.blocks overlay ++ blocks
  let fullOwners : List (Fin (10 * input.length)) :=
    ScheduleOverlay.owners overlay owners
  let fullWord : List (ScheduleAtom g input) := ScheduleOverlay.word overlay word
  let fullUsed : List (ScheduleAtom g input) := ScheduleOverlay.used overlay used
  have hvis : visible ≠ [] := by
    intro hnil
    have hpos := overlayLayout.flags_length_pos
    have hpos' : 0 < visible.length := by
      simpa [visible, overlay] using hpos
    simp [hnil] at hpos'
  let fullLayout : ScheduleBlockLayout g input visible fullBlocks fullOwners
      fullWord fullUsed := by
    simpa [visible, fullBlocks, fullOwners, fullWord, fullUsed, overlay] using
      overlayLayout.toProtected
  let parentUsed : parent.ConsumesAt 0 := hall 0 overlayLayout.flags_length_pos
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.live parentUsed)
  let startCursor : ScheduleCursor g input :=
    liveScheduleCursor parent parentUsed pre post input_eq alpha fullWord
  have hstart' : ScheduleInvariant startCursor := by
    simpa [startCursor, parent, parentTask, fullWord, overlay,
      liveScheduleCursor] using hstart
  have hframesStart : List.Disjoint fullOwners startCursor.frameOwners := by
    simpa [fullOwners, overlay, startCursor, parent, parentTask, fullWord,
      liveScheduleCursor] using hframes
  have hinputPos : 0 < input.length := by
    have hu := leftParse.yield_length_pos
    have hlen := congrArg List.length input_eq
    simp only [List.length_append] at hlen
    omega
  have hparentZero : 0 ∈ parent.eventDepths := by
    simp [parent, NFParse.eventDepths]
  have hheadMem : head.owner ∈ startCursor.indexOwners := by
    apply resources.active_subset_indexOwners
    rw [hactive]
    simp
  have hfocusNoIndex :
      [startCursor.focus].filterMap ScheduleAtom.indexOwner? = [] := by
    simp [startCursor, liveScheduleCursor, ScheduleAtom.indexOwner?]
  have hheadFrameFresh : head.owner ∉ startCursor.frameOwners := by
    apply (List.disjoint_left.mp hframesStart)
    simp [fullOwners, overlay]
  let normal := resources.normalizeTransientHead hinputPos
    (by simpa [fullOwners, overlay] using hactive)
    (by simpa [fullOwners, overlay, fullLayout] using fullLayout.owners_nodup)
    (by simpa [fullBlocks, fullOwners, overlay] using ticketShadowContext)
    (by simpa [fullBlocks, fullOwners, overlay] using ticketOwnerLayout)
    hparentZero
    (by simpa [startCursor, parent, parentTask, fullWord, overlay,
      liveScheduleCursor] using hheadMem)
    (by simpa [startCursor, parent, parentTask, fullWord, overlay,
      liveScheduleCursor] using hfocusNoIndex)
    (by simpa [startCursor, parent, parentTask, fullWord, overlay,
      liveScheduleCursor] using hheadFrameFresh)
    (by simpa [startCursor, parent, parentTask, fullWord, overlay,
      liveScheduleCursor] using hstart'.frameOwners_subset_indexOwners)
    (ticketTransientHead hinputPos)
  let normalResources := normal.resources
  have normalTicketShadowContext :
      normalResources.TicketShadowContextExtends fullBlocks fullOwners := by
    simpa [normalResources, TicketHeadNormalization.resources, fullBlocks,
      fullOwners, overlay] using ticketShadowContext
  have hstackVisible : stack = visible ++ hidden := by
    simpa [visible, overlay] using hstack
  have hmarkedParent : ScheduleInvariant
      (ScheduleCursor.mk (alpha ++ [.dollar]) (.task parentTask) fullUsed) := by
    apply ScheduleInvariant.replaceRight (alpha ++ [ScheduleAtom.dollar])
      (.task parentTask) fullLayout
    simpa [startCursor, liveScheduleCursor] using hstart'
  have hmarked : ScheduleInvariant (scheduleWordCursor alpha fullUsed) := by
    have hfinish := ScheduleInvariant.finishTask (alpha ++ [ScheduleAtom.dollar])
      parentTask (fullUsed.headD .hash) (fullUsed.tail) ?_
    · simpa [scheduleWordCursor, fullUsed, ScheduleOverlay.used, overlay, hused] using
        hfinish
    · simpa [fullUsed, ScheduleOverlay.used, overlay, hused] using hmarkedParent
  have hprePos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  have hendPos : (pre ++ (u ++ v)).length ≤ input.length := by
    rw [input_eq]
    simp
  have hprotected : ScheduleReaches g input
      (scheduleStateOfCursor pre.length hprePos startCursor hstart')
      (scheduleStateOfCursor (pre ++ (u ++ v)).length hendPos
        (scheduleWordCursor alpha fullUsed) hmarked) := by
    have run := protectedScheduleRun_binary_atOrBelow hr hlhs hc hrhs
      leftParse rightParse leftRuns rightRuns
      (input := input) visible hidden fullBlocks fullOwners fullWord fullUsed
      hstackVisible hvis
      (by simpa [visible, overlay] using hall)
      (by simpa [visible, overlay] using hboundary)
      fullLayout
      (by simpa [fullBlocks, overlay] using compatible)
      pre post input_eq alpha hstable
      (by simpa [startCursor, parent, parentTask, liveScheduleCursor] using hstart')
      (by simpa [fullOwners, fullWord, overlay, startCursor, parent, parentTask,
        liveScheduleCursor] using hframes)
      (by simpa using hmarked)
      normalResources
      (by simpa [normalResources, TicketHeadNormalization.resources] using hfree)
      (by simpa [normalResources, TicketHeadNormalization.resources] using
        normal.parkingAtOrBelow)
      (by simpa [normalResources, TicketHeadNormalization.resources,
        fullBlocks, fullOwners, overlay] using ownerLayout)
      (by simpa [normalResources, TicketHeadNormalization.resources,
        fullBlocks, fullOwners, overlay] using shadowLayout)
      (by simpa [normalResources, fullBlocks, fullOwners, overlay] using
        normal.eventLayout)
      normalTicketShadowContext
      (by
        intro hinput
        simpa [normalResources, startCursor, parent, parentTask, fullWord, overlay,
          liveScheduleCursor] using normal.transient_fresh hinput)
      (by simpa [normalResources, TicketHeadNormalization.resources,
        fullOwners, overlay] using hactive)
      (by
        intro hinput hmem
        exact False.elim (normalResources.pool.transientOwner_not_mem_indices hinput
          (by simpa [startCursor, parent, parentTask, fullWord, overlay,
            liveScheduleCursor] using hmem)))
      (by
        intro hinput hmem
        exact False.elim (normalResources.pool.scratchOwner_not_mem_indices hinput
          (by simpa [startCursor, parent, parentTask, fullWord, overlay,
            liveScheduleCursor] using hmem)))
    simpa [startCursor, parent, parentTask, visible, fullBlocks, fullOwners,
      fullWord, fullUsed, overlay, liveScheduleCursor, scheduleWordCursor,
      scheduleStateOfCursor] using run
  have hoverlayUnframed : ∀ idx ∈ overlay, idx.owner ∉
      (scheduleWordCursor alpha fullUsed).frameOwners := by
    have hframeEq :
        (scheduleWordCursor alpha fullUsed).frameOwners = startCursor.frameOwners := by
      have hfullUsed : fullUsed =
          .index head.markUsed :: ScheduleOverlay.used overlayTail used := rfl
      have hlayoutFrames := fullLayout.frameOwners_eq
      rw [hfullUsed] at hlayoutFrames ⊢
      simp only [List.filterMap_cons, ScheduleAtom.closeOwner?] at hlayoutFrames
      simp only [scheduleWordCursor, startCursor, liveScheduleCursor,
        ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?,
        List.filterMap_cons, List.filterMap_nil, List.append_nil]
      rw [hlayoutFrames]
    intro idx hidx hframe
    have hownerFull : idx.owner ∈ fullOwners := by
      have hoverlayOwner : idx.owner ∈ overlay.map ScheduleIndex.owner :=
        List.mem_map.mpr ⟨idx, hidx, rfl⟩
      simpa [fullOwners, ScheduleOverlay.owners] using
        List.mem_append_left owners hoverlayOwner
    apply (List.disjoint_left.mp hframesStart) hownerFull
    rw [← hframeEq]
    exact hframe
  have herase := eraseMarkedOverlay overlay used hused
    (pre ++ (u ++ v)).length hendPos alpha hmarked hend hoverlayUnframed
  have hprotected' : ScheduleReaches g input
      (scheduleStateOfCursor pre.length (by
        rw [input_eq]
        simp) startCursor hstart')
      (scheduleStateOfCursor (pre ++ (u ++ v)).length hendPos
        (scheduleWordCursor alpha fullUsed) hmarked) := by
    simpa using hprotected
  simpa [startCursor, parent, parentTask, fullWord, fullUsed, overlay,
    liveScheduleCursor, scheduleStateOfCursor] using hprotected'.trans herase

end Aho
end IndexedGrammar

end
