module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.GhostLayout

@[expose]
public section

/-!
# Invariant-preserving scheduler moves

The compressed runner changes the focused payload one elementary Aho move at a time.  This
module isolates the corresponding ownership arithmetic.  The lemmas are deliberately phrased
at cursor level: semantic runner modes may choose their own task constructors, and only need to
prove the resulting owner equalities or freshness facts.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace ScheduleInvariant

/-! ## Generic owner insertion and deletion -/

/-- Insert one fresh task/terminal owner while adding exactly one ghost square. -/
public theorem insertTaskOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input}
    (hinv : ScheduleInvariant old) (owner : Fin input.length)
    (hfresh : owner ∉ old.taskOwners)
    (htasks : new.taskOwners.Perm (owner :: old.taskOwners))
    (hindices : new.indexOwners = old.indexOwners)
    (hframes : new.frameOwners = old.frameOwners)
    (hlength : new.word.length = old.word.length + 1) :
    ScheduleInvariant new := by
  have htaskNodup : new.taskOwners.Nodup :=
    htasks.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hinv.taskOwners_nodup⟩)
  have htaskLength : new.taskOwners.length = old.taskOwners.length + 1 := by
    have := htasks.length_eq
    simp at this
    omega
  have hindexLength := congrArg List.length hindices
  have hframeLength := congrArg List.length hframes
  refine ⟨htaskNodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hindices] using hinv.indexOwners_nodup
  · simpa [hframes] using hinv.frameOwners_nodup
  · simpa [hindices, hframes] using hinv.frameOwners_subset_indexOwners
  · simpa using htaskNodup.length_le_card
  · simpa [hindices] using hinv.indexCount_le
  · have hshape := hinv.shape_bound
    simp only [ScheduleCursor.frameCount] at hshape ⊢
    omega

/-- Insert one fresh persistent-index owner while adding exactly one ghost square. -/
public theorem insertIndexOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input}
    (hinv : ScheduleInvariant old) (owner : Fin (10 * input.length))
    (hfresh : owner ∉ old.indexOwners)
    (hcapacity : old.indexOwners.length < 6 * input.length)
    (htasks : new.taskOwners = old.taskOwners)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hframes : new.frameOwners = old.frameOwners)
    (hlength : new.word.length = old.word.length + 1) :
    ScheduleInvariant new := by
  have hindexNodup : new.indexOwners.Nodup :=
    hindices.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hinv.indexOwners_nodup⟩)
  have hindexLength : new.indexOwners.length = old.indexOwners.length + 1 := by
    have := hindices.length_eq
    simp at this
    omega
  have htaskLength := congrArg List.length htasks
  have hframeLength := congrArg List.length hframes
  refine ⟨?_, hindexNodup, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [htasks] using hinv.taskOwners_nodup
  · simpa [hframes] using hinv.frameOwners_nodup
  · intro frame hframe
    have holdFrame : frame ∈ old.frameOwners := by simpa [hframes] using hframe
    have holdIndex := hinv.frameOwners_subset_indexOwners holdFrame
    have hnewIndex : owner :: old.indexOwners ~ new.indexOwners := hindices.symm
    exact hnewIndex.mem_iff.mp (List.mem_cons_of_mem owner holdIndex)
  · simpa [htasks] using hinv.taskCount_le
  · omega
  · have hshape := hinv.shape_bound
    simp only [ScheduleCursor.frameCount] at hshape ⊢
    omega

/-- Delete one task/terminal owner together with its unique ghost square. -/
public theorem removeTaskOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (hinv : ScheduleInvariant old)
    (owner : Fin input.length)
    (htasks : old.taskOwners.Perm (owner :: new.taskOwners))
    (hindices : new.indexOwners = old.indexOwners)
    (hframes : new.frameOwners = old.frameOwners)
    (hlength : old.word.length = new.word.length + 1) :
    ScheduleInvariant new := by
  have hconsNodup : (owner :: new.taskOwners).Nodup :=
    htasks.nodup_iff.mp hinv.taskOwners_nodup
  have htaskNodup := (List.nodup_cons.mp hconsNodup).2
  have htaskLength : old.taskOwners.length = new.taskOwners.length + 1 := by
    have := htasks.length_eq
    simp at this
    omega
  have hindexLength := congrArg List.length hindices
  have hframeLength := congrArg List.length hframes
  refine ⟨htaskNodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hindices] using hinv.indexOwners_nodup
  · simpa [hframes] using hinv.frameOwners_nodup
  · simpa [hindices, hframes] using hinv.frameOwners_subset_indexOwners
  · exact le_trans (by omega) hinv.taskCount_le
  · simpa [hindices] using hinv.indexCount_le
  · have hshape := hinv.shape_bound
    simp only [ScheduleCursor.frameCount] at hshape ⊢
    omega

/-- Open one frame charged to an existing persistent index.  The two new ghost squares are the
inner `$` and its matching `close`. -/
public theorem insertFrameOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (hinv : ScheduleInvariant old)
    (owner : Fin (10 * input.length))
    (hfresh : owner ∉ old.frameOwners)
    (htasks : new.taskOwners.Perm old.taskOwners)
    (hindices : new.indexOwners = old.indexOwners)
    (hframes : new.frameOwners.Perm (owner :: old.frameOwners))
    (hownerIndex : owner ∈ new.indexOwners)
    (hlength : new.word.length = old.word.length + 2) :
    ScheduleInvariant new := by
  have htaskNodup : new.taskOwners.Nodup :=
    htasks.nodup_iff.mpr hinv.taskOwners_nodup
  have hframeNodup : new.frameOwners.Nodup :=
    hframes.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hinv.frameOwners_nodup⟩)
  have htaskLength := htasks.length_eq
  have hindexLength := congrArg List.length hindices
  have hframeLength : new.frameOwners.length = old.frameOwners.length + 1 := by
    have := hframes.length_eq
    simp at this
    omega
  refine ⟨htaskNodup, ?_, hframeNodup, ?_, ?_, ?_, ?_⟩
  · simpa [hindices] using hinv.indexOwners_nodup
  · intro frame hframe
    have hcons : frame ∈ owner :: old.frameOwners := hframes.mem_iff.mp hframe
    simp only [List.mem_cons] at hcons
    rcases hcons with hEq | hOld
    · simpa [hEq] using hownerIndex
    · have holdIndex := hinv.frameOwners_subset_indexOwners hOld
      simpa [hindices] using holdIndex
  · simpa using htaskNodup.length_le_card
  · simpa [hindices] using hinv.indexCount_le
  · have hshape := hinv.shape_bound
    simp only [ScheduleCursor.frameCount] at hshape ⊢
    omega

/-- Close one frame and remove its `$`/`close` delimiter pair. -/
public theorem removeFrameOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (hinv : ScheduleInvariant old)
    (owner : Fin (10 * input.length))
    (htasks : new.taskOwners = old.taskOwners)
    (hindices : new.indexOwners = old.indexOwners)
    (hframes : old.frameOwners.Perm (owner :: new.frameOwners))
    (hlength : old.word.length = new.word.length + 2) :
    ScheduleInvariant new := by
  have hconsNodup : (owner :: new.frameOwners).Nodup :=
    hframes.nodup_iff.mp hinv.frameOwners_nodup
  have hframeNodup := (List.nodup_cons.mp hconsNodup).2
  have htaskLength := congrArg List.length htasks
  have hindexLength := congrArg List.length hindices
  have hframeLength : old.frameOwners.length = new.frameOwners.length + 1 := by
    have := hframes.length_eq
    simp at this
    omega
  refine ⟨?_, ?_, hframeNodup, ?_, ?_, ?_, ?_⟩
  · simpa [htasks] using hinv.taskOwners_nodup
  · simpa [hindices] using hinv.indexOwners_nodup
  · intro frame hframe
    have hnewOld : frame ∈ old.frameOwners :=
      hframes.mem_iff.mpr (List.mem_cons_of_mem owner hframe)
    have holdIndex := hinv.frameOwners_subset_indexOwners hnewOld
    simpa [hindices] using holdIndex
  · simpa [htasks] using hinv.taskCount_le
  · simpa [hindices] using hinv.indexCount_le
  · have hshape := hinv.shape_bound
    simp only [ScheduleCursor.frameCount] at hshape ⊢
    omega

/-- Remove one persistent index which is not charged by an open frame. -/
public theorem removeIndexOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (hinv : ScheduleInvariant old)
    (owner : Fin (10 * input.length))
    (hunframed : owner ∉ old.frameOwners)
    (htasks : new.taskOwners = old.taskOwners)
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners))
    (hframes : new.frameOwners = old.frameOwners)
    (hlength : old.word.length = new.word.length + 1) :
    ScheduleInvariant new := by
  have hconsNodup : (owner :: new.indexOwners).Nodup :=
    hindices.nodup_iff.mp hinv.indexOwners_nodup
  have hindexNodup := (List.nodup_cons.mp hconsNodup).2
  have htaskLength := congrArg List.length htasks
  have hindexLength : old.indexOwners.length = new.indexOwners.length + 1 := by
    have := hindices.length_eq
    simp at this
    omega
  have hframeLength := congrArg List.length hframes
  refine ⟨?_, hindexNodup, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [htasks] using hinv.taskOwners_nodup
  · simpa [hframes] using hinv.frameOwners_nodup
  · intro frame hframe
    have holdFrame : frame ∈ old.frameOwners := by simpa [hframes] using hframe
    have holdIndex := hinv.frameOwners_subset_indexOwners holdFrame
    have hcons : frame ∈ owner :: new.indexOwners := hindices.mem_iff.mp holdIndex
    simp only [List.mem_cons] at hcons
    rcases hcons with hEq | hNew
    · exact False.elim (hunframed (hEq ▸ holdFrame))
    · exact hNew
  · simpa [htasks] using hinv.taskCount_le
  · have hold := hinv.indexCount_le
    omega
  · have hshape := hinv.shape_bound
    simp only [ScheduleCursor.frameCount] at hshape ⊢
    omega

/-! ## Focused plain-mode cursor changes -/

/-- Replace a focused task by another task with the same terminal owner. -/
public theorem replaceTask_sameOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left right : List (ScheduleAtom g input))
    (oldTask newTask : ScheduleTask g input)
    (howner : newTask.owner = oldTask.owner)
    (hinv : ScheduleInvariant ⟨left, .task oldTask, right⟩) :
    ScheduleInvariant ⟨left, .task newTask, right⟩ := by
  apply ScheduleInvariant.of_ownerFields_eq hinv
  · simp [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?, howner]
  · simp [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?]
  · simp [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?]
  · simp [ScheduleCursor.word]

/-- The plain binary move replaces one task by its two ordered children.  The left child keeps
the parent owner; freshness of the right child is the only new ownership obligation. -/
public theorem plainBinary
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left right : List (ScheduleAtom g input))
    (parent leftTask rightTask : ScheduleTask g input)
    (hleftOwner : leftTask.owner = parent.owner)
    (hrightFresh : rightTask.owner ∉
      (ScheduleCursor.mk left (.task parent) right).taskOwners)
    (hinv : ScheduleInvariant ⟨left, .task parent, right⟩) :
    ScheduleInvariant ⟨left, .task leftTask, .task rightTask :: right⟩ := by
  apply ScheduleInvariant.insertTaskOwner hinv rightTask.owner hrightFresh
  · simp only [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?,
      List.filterMap_cons, List.filterMap_nil]
    rw [hleftOwner]
    simpa only [List.append_assoc, List.append_nil] using
      (List.perm_middle (l₁ := left.filterMap ScheduleAtom.taskOwner? ++ [parent.owner])
        (l₂ := right.filterMap ScheduleAtom.taskOwner?) (a := rightTask.owner))
  · simp [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?]
  · simp [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?]
  · simp [ScheduleCursor.word]
    omega

/-- A plain push whose new flag is irrelevant only changes the task certificate. -/
public theorem plainPushSkip
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left right : List (ScheduleAtom g input))
    (parent child : ScheduleTask g input)
    (howner : child.owner = parent.owner)
    (hinv : ScheduleInvariant ⟨left, .task parent, right⟩) :
    ScheduleInvariant ⟨left, .task child, right⟩ :=
  replaceTask_sameOwner left right parent child howner hinv

/-- A plain push which starts a relevant block keeps the task owner and allocates one fresh
persistent index immediately to its right. -/
public theorem plainPushUse
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left right : List (ScheduleAtom g input))
    (parent child : ScheduleTask g input) (idx : ScheduleIndex g input)
    (htaskOwner : child.owner = parent.owner)
    (hindexFresh : idx.owner ∉
      (ScheduleCursor.mk left (.task parent) right).indexOwners)
    (hcapacity :
      (ScheduleCursor.mk left (.task parent) right).indexOwners.length <
        6 * input.length)
    (hinv : ScheduleInvariant ⟨left, .task parent, right⟩) :
    ScheduleInvariant ⟨left, .task child, .index idx :: right⟩ := by
  apply ScheduleInvariant.insertIndexOwner hinv idx.owner hindexFresh hcapacity
  · simp [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?, htaskOwner]
  · simp only [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    simpa only [List.append_assoc, List.append_nil] using
      (List.perm_middle (l₁ := left.filterMap ScheduleAtom.indexOwner?)
        (l₂ := right.filterMap ScheduleAtom.indexOwner?) (a := idx.owner))
  · simp [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?]
  · simp [ScheduleCursor.word]
    omega

/-- Replace a focused live task and its adjacent represented block without changing either
persistent owner.  This is the invariant part of `livePushCompress`. -/
public theorem livePushCompress
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left right : List (ScheduleAtom g input))
    (parent child : ScheduleTask g input)
    (oldIndex newIndex : ScheduleIndex g input)
    (htaskOwner : child.owner = parent.owner)
    (hindexOwner : newIndex.owner = oldIndex.owner)
    (hinv : ScheduleInvariant
      ⟨left, .task parent, .index oldIndex :: right⟩) :
    ScheduleInvariant ⟨left, .task child, .index newIndex :: right⟩ := by
  apply ScheduleInvariant.of_ownerFields_eq hinv
  · simp [ScheduleCursor.taskOwners, ScheduleCursor.word,
      ScheduleAtom.taskOwner?, List.filterMap_append, htaskOwner]
  · simp [ScheduleCursor.indexOwners, ScheduleCursor.word,
      ScheduleAtom.indexOwner?, List.filterMap_append, hindexOwner]
  · simp [ScheduleCursor.frameOwners, ScheduleCursor.word,
      ScheduleAtom.closeOwner?, List.filterMap_append]
  · simp [ScheduleCursor.word]

/-- Emitting the terminal of a plain leaf preserves its task owner exactly. -/
public theorem plainTerminal
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left right : List (ScheduleAtom g input))
    (task : ScheduleTask g input) (a : T)
    (hinv : ScheduleInvariant ⟨left, .task task, right⟩) :
    ScheduleInvariant ⟨left, .terminal task.owner a, right⟩ := by
  apply ScheduleInvariant.of_ownerFields_eq hinv
  · simp [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?]
  · simp [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?]
  · simp [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?]
  · simp [ScheduleCursor.word]

/-- Matching an emitted terminal removes its owner and focuses the following square. -/
public theorem matchTerminal
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left : List (ScheduleAtom g input)) (owner : Fin input.length) (a : T)
    (next : ScheduleAtom g input) (right : List (ScheduleAtom g input))
    (hinv : ScheduleInvariant ⟨left, .terminal owner a, next :: right⟩) :
    ScheduleInvariant ⟨left, next, right⟩ := by
  have htaskNext :
      (next :: right).filterMap ScheduleAtom.taskOwner? =
        [next].filterMap ScheduleAtom.taskOwner? ++
          right.filterMap ScheduleAtom.taskOwner? := by
    cases next <;> simp [ScheduleAtom.taskOwner?]
  have hindexNext :
      (next :: right).filterMap ScheduleAtom.indexOwner? =
        [next].filterMap ScheduleAtom.indexOwner? ++
          right.filterMap ScheduleAtom.indexOwner? := by
    cases next <;> simp [ScheduleAtom.indexOwner?]
  have hframeNext :
      (next :: right).filterMap ScheduleAtom.closeOwner? =
        [next].filterMap ScheduleAtom.closeOwner? ++
          right.filterMap ScheduleAtom.closeOwner? := by
    cases next <;> simp [ScheduleAtom.closeOwner?]
  apply ScheduleInvariant.removeTaskOwner hinv owner
  · simp only [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?, htaskNext,
      List.filterMap_cons, List.filterMap_nil]
    simpa only [List.append_assoc, List.append_nil] using
      (List.perm_middle (l₁ := left.filterMap ScheduleAtom.taskOwner?)
        (l₂ := [next].filterMap ScheduleAtom.taskOwner? ++
          right.filterMap ScheduleAtom.taskOwner?) (a := owner))
  · simp only [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?, hindexNext,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    exact List.append_assoc _ _ _
  · simp only [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?, hframeNext,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    exact List.append_assoc _ _ _
  · simp [ScheduleCursor.word]
    omega

/-- Remove a completed focused task payload and expose its continuation.  Recursive runner
endpoints use this owner-level inverse of task creation. -/
public theorem finishTask
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left : List (ScheduleAtom g input)) (task : ScheduleTask g input)
    (next : ScheduleAtom g input) (right : List (ScheduleAtom g input))
    (hinv : ScheduleInvariant ⟨left, .task task, next :: right⟩) :
    ScheduleInvariant ⟨left, next, right⟩ := by
  have htaskNext :
      (next :: right).filterMap ScheduleAtom.taskOwner? =
        [next].filterMap ScheduleAtom.taskOwner? ++
          right.filterMap ScheduleAtom.taskOwner? := by
    cases next <;> simp [ScheduleAtom.taskOwner?]
  have hindexNext :
      (next :: right).filterMap ScheduleAtom.indexOwner? =
        [next].filterMap ScheduleAtom.indexOwner? ++
          right.filterMap ScheduleAtom.indexOwner? := by
    cases next <;> simp [ScheduleAtom.indexOwner?]
  have hframeNext :
      (next :: right).filterMap ScheduleAtom.closeOwner? =
        [next].filterMap ScheduleAtom.closeOwner? ++
          right.filterMap ScheduleAtom.closeOwner? := by
    cases next <;> simp [ScheduleAtom.closeOwner?]
  apply ScheduleInvariant.removeTaskOwner hinv task.owner
  · simp only [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?, htaskNext,
      List.filterMap_cons, List.filterMap_nil]
    simpa only [List.append_assoc] using
      (List.perm_middle (l₁ := left.filterMap ScheduleAtom.taskOwner?)
        (l₂ := [next].filterMap ScheduleAtom.taskOwner? ++
          right.filterMap ScheduleAtom.taskOwner?) (a := task.owner))
  · simp only [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?, hindexNext,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    exact List.append_assoc _ _ _
  · simp only [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?, hframeNext,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    exact List.append_assoc _ _ _
  · simp [ScheduleCursor.word]
    omega

/-! ## Pop-frame cursor changes -/

/-- Pop and immediately erase an adjacent compressed block. No frame is opened: the selected
index is owned by the active call, so after applying its relation the residual task may reuse
that owner. -/
public theorem popErase
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (alpha tail : List (ScheduleAtom g input))
    (task residual : ScheduleTask g input) (idx : ScheduleIndex g input)
    (htaskOwner : residual.owner = task.owner)
    (hunframed : idx.owner ∉
      (ScheduleCursor.mk (alpha ++ [.dollar]) (.task task)
        (.index idx :: tail)).frameOwners)
    (hinv : ScheduleInvariant
      ⟨alpha ++ [.dollar], .task task, .index idx :: tail⟩) :
    ScheduleInvariant ⟨alpha ++ [.dollar], .task residual, tail⟩ := by
  apply ScheduleInvariant.removeIndexOwner hinv idx.owner hunframed
  · simp [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?, htaskOwner]
  · simp only [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.indexOwner?)
        (l₂ := tail.filterMap ScheduleAtom.indexOwner?) (a := idx.owner))
  · simp [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?]
  · simp [ScheduleCursor.word]
    omega

/-- Consume a selected index, mark it used, and open the frame in which the residual task runs.
The task may cross arbitrary task payloads in `gap`; owner permutation, rather than syntactic
list equality, is therefore the appropriate invariant statement. -/
public theorem popFrame
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (alpha gap tail : List (ScheduleAtom g input))
    (task residual : ScheduleTask g input) (idx : ScheduleIndex g input)
    (htaskOwner : residual.owner = task.owner)
    (hframeFresh : idx.owner ∉
      (ScheduleCursor.mk (alpha ++ [.dollar]) (.task task)
        (gap ++ .index idx :: tail)).frameOwners)
    (hinv : ScheduleInvariant
      ⟨alpha ++ [.dollar], .task task, gap ++ .index idx :: tail⟩) :
    ScheduleInvariant
      ⟨alpha ++ [.dollar] ++ gap ++ [.index idx.markUsed, .dollar],
        .task residual, .close idx.owner :: tail⟩ := by
  apply ScheduleInvariant.insertFrameOwner hinv idx.owner hframeFresh
  · simp only [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      List.append_nil]
    rw [htaskOwner]
    let a := alpha.filterMap ScheduleAtom.taskOwner?
    let b := gap.filterMap ScheduleAtom.taskOwner?
    let c := tail.filterMap ScheduleAtom.taskOwner?
    have hnew : a ++ b ++ task.owner :: c ~ task.owner :: (a ++ b ++ c) := by
      simpa only [List.append_assoc] using
        (List.perm_middle (l₁ := a ++ b) (l₂ := c) (a := task.owner))
    have hold : a ++ task.owner :: b ++ c ~ task.owner :: (a ++ b ++ c) := by
      simpa only [List.append_assoc] using
        (List.perm_middle (l₁ := a) (l₂ := b ++ c) (a := task.owner))
    simpa only [a, b, c, List.append_assoc, List.singleton_append] using
      hnew.trans hold.symm
  · simp [ScheduleCursor.word,
      ScheduleCursor.indexOwners, ScheduleAtom.indexOwner?,
      ScheduleIndex.markUsed, List.filterMap_append, List.append_assoc]
  · simp only [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      List.append_nil]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := alpha.filterMap ScheduleAtom.closeOwner? ++
          gap.filterMap ScheduleAtom.closeOwner?)
        (l₂ := tail.filterMap ScheduleAtom.closeOwner?) (a := idx.owner))
  · simp [ScheduleCursor.indexOwners, ScheduleCursor.word,
      ScheduleAtom.indexOwner?, List.filterMap_append]
  · simp [ScheduleCursor.word]
    omega

/-- Return from a completed pop frame.  The saved square `next` and `gap` are restored outside
the frame while the matching close charge disappears. -/
public theorem returnFrame
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (alpha gap tail : List (ScheduleAtom g input))
    (next : ScheduleAtom g input) (owner : Fin (10 * input.length))
    (hinv : ScheduleInvariant
      ⟨alpha ++ [.dollar, next] ++ gap ++ [.dollar], .close owner, tail⟩) :
    ScheduleInvariant ⟨alpha ++ [.dollar], next, gap ++ tail⟩ := by
  apply ScheduleInvariant.removeFrameOwner hinv owner
  · cases next <;>
      simp [ScheduleCursor.taskOwners, ScheduleCursor.word,
        ScheduleAtom.taskOwner?, List.filterMap_append, List.append_assoc]
  · cases next <;>
      simp [ScheduleCursor.indexOwners, ScheduleCursor.word,
        ScheduleAtom.indexOwner?, List.filterMap_append, List.append_assoc]
  · simp only [ScheduleCursor.frameOwners, ScheduleCursor.word,
      List.filterMap_append, ScheduleAtom.closeOwner?, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
    let a := alpha.filterMap ScheduleAtom.closeOwner?
    let n := [next].filterMap ScheduleAtom.closeOwner?
    let b := gap.filterMap ScheduleAtom.closeOwner?
    let c := tail.filterMap ScheduleAtom.closeOwner?
    cases next <;>
      simpa only [a, n, b, c, ScheduleAtom.closeOwner?, List.filterMap_cons,
        List.filterMap_nil, List.append_nil, List.append_assoc,
        List.singleton_append] using
        (List.perm_middle (l₁ := a ++ n ++ b) (l₂ := c) (a := owner))
  · simp [ScheduleCursor.word]
    omega

/-- Reconstruct the invariant expected immediately before `returnFrame`.  This is the inverse
accounting move used to provide a recursive subrun with its required endpoint invariant. -/
public theorem prepareReturnFrame
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (alpha gap tail : List (ScheduleAtom g input))
    (next : ScheduleAtom g input) (owner : Fin (10 * input.length))
    (hfresh : owner ∉
      (ScheduleCursor.mk (alpha ++ [.dollar]) next (gap ++ tail)).frameOwners)
    (howned : owner ∈
      (ScheduleCursor.mk (alpha ++ [.dollar]) next (gap ++ tail)).indexOwners)
    (hinv : ScheduleInvariant ⟨alpha ++ [.dollar], next, gap ++ tail⟩) :
    ScheduleInvariant
      ⟨alpha ++ [.dollar, next] ++ gap ++ [.dollar], .close owner, tail⟩ := by
  apply ScheduleInvariant.insertFrameOwner hinv owner hfresh
  · cases next <;>
      simp [ScheduleCursor.taskOwners, ScheduleCursor.word,
        ScheduleAtom.taskOwner?, List.filterMap_append, List.append_assoc]
  · cases next <;>
      simp [ScheduleCursor.indexOwners, ScheduleCursor.word,
        ScheduleAtom.indexOwner?, List.filterMap_append, List.append_assoc]
  · simp only [ScheduleCursor.frameOwners, ScheduleCursor.word,
      List.filterMap_append, ScheduleAtom.closeOwner?, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
    let a := alpha.filterMap ScheduleAtom.closeOwner?
    let n := [next].filterMap ScheduleAtom.closeOwner?
    let b := gap.filterMap ScheduleAtom.closeOwner?
    let c := tail.filterMap ScheduleAtom.closeOwner?
    cases next <;>
      simpa only [a, n, b, c, ScheduleAtom.closeOwner?, List.filterMap_cons,
        List.filterMap_nil, List.append_nil, List.append_assoc,
        List.singleton_append] using
        (List.perm_middle (l₁ := a ++ n ++ b) (l₂ := c) (a := owner))
  · cases next <;>
      simpa [ScheduleCursor.indexOwners, ScheduleCursor.word,
        ScheduleAtom.indexOwner?, List.filterMap_append, List.append_assoc] using howned
  · simp [ScheduleCursor.word]
    omega

/-- Erase an unframed used index and expose the square following it. -/
public theorem eraseIndex
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (alpha tail : List (ScheduleAtom g input))
    (idx : ScheduleIndex g input) (next : ScheduleAtom g input)
    (hunframed : idx.owner ∉
      (ScheduleCursor.mk (alpha ++ [.dollar]) (.index idx)
        (next :: tail)).frameOwners)
    (hinv : ScheduleInvariant
      ⟨alpha ++ [.dollar], .index idx, next :: tail⟩) :
    ScheduleInvariant ⟨alpha ++ [.dollar], next, tail⟩ := by
  have htaskNext :
      (next :: tail).filterMap ScheduleAtom.taskOwner? =
        [next].filterMap ScheduleAtom.taskOwner? ++
          tail.filterMap ScheduleAtom.taskOwner? := by
    cases next <;> simp [ScheduleAtom.taskOwner?]
  have hindexNext :
      (next :: tail).filterMap ScheduleAtom.indexOwner? =
        [next].filterMap ScheduleAtom.indexOwner? ++
          tail.filterMap ScheduleAtom.indexOwner? := by
    cases next <;> simp [ScheduleAtom.indexOwner?]
  have hframeNext :
      (next :: tail).filterMap ScheduleAtom.closeOwner? =
        [next].filterMap ScheduleAtom.closeOwner? ++
          tail.filterMap ScheduleAtom.closeOwner? := by
    cases next <;> simp [ScheduleAtom.closeOwner?]
  apply ScheduleInvariant.removeIndexOwner hinv idx.owner hunframed
  · simp only [ScheduleCursor.taskOwners_mk, ScheduleAtom.taskOwner?, htaskNext,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    exact List.append_assoc _ _ _
  · simp only [ScheduleCursor.indexOwners_mk, ScheduleAtom.indexOwner?, hindexNext,
      List.filterMap_cons, List.filterMap_nil]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap ScheduleAtom.indexOwner?)
        (l₂ := [next].filterMap ScheduleAtom.indexOwner? ++
          tail.filterMap ScheduleAtom.indexOwner?) (a := idx.owner))
  · simp only [ScheduleCursor.frameOwners_mk, ScheduleAtom.closeOwner?, hframeNext,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    exact List.append_assoc _ _ _
  · simp [ScheduleCursor.word]
    omega

end ScheduleInvariant
end Aho
end IndexedGrammar
