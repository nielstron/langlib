module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.BoundedAccounting

@[expose]
public section

/-!
# Owner-annotated compressed block layouts

This module mirrors `BlockLayout` before scheduler annotations are erased.  Each physical block
is represented by one `ScheduleIndex`, and the layout index records its persistent owner.  This
makes owner alignment and duplicate-freedom available to the bounded runner while erasure remains
exactly the already-verified physical layout.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- A ghost segment contains no scheduler index atom. -/
public def ScheduleIndexFree {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (xs : List (ScheduleAtom g input)) : Prop :=
  ∀ idx, ScheduleAtom.index idx ∉ xs

/-- A ghost segment contains no scheduler `$` atom. -/
public def ScheduleDollarFree {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (xs : List (ScheduleAtom g input)) : Prop :=
  ScheduleAtom.dollar ∉ xs

namespace ScheduleIndexFree

public theorem append {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {xs ys : List (ScheduleAtom g input)}
    (hxs : ScheduleIndexFree xs) (hys : ScheduleIndexFree ys) :
    ScheduleIndexFree (xs ++ ys) := by
  intro idx hmem
  simp only [List.mem_append] at hmem
  exact hmem.elim (hxs idx) (hys idx)

/-- Erasing an index-free ghost gap produces an index-free physical gap. -/
public theorem erase {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {xs : List (ScheduleAtom g input)}
    (hfree : ScheduleIndexFree xs) :
    IndexFree (xs.map ScheduleAtom.workSym) := by
  intro R d hmem
  rcases List.mem_map.mp hmem with ⟨atom, hatom, heq⟩
  cases atom with
  | task task =>
      cases task with
      | mk A stack yield parse pre post input_eq mode =>
          cases mode <;> simp [ScheduleAtom.workSym, ScheduleTask.workSym] at heq
  | terminal owner a => simp [ScheduleAtom.workSym] at heq
  | index idx => exact hfree idx hatom
  | dollar => simp [ScheduleAtom.workSym] at heq
  | close owner => simp [ScheduleAtom.workSym] at heq
  | hash => simp [ScheduleAtom.workSym] at heq

@[simp] public theorem filterMap_indexOwner_eq_nil
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {xs : List (ScheduleAtom g input)}
    (hfree : ScheduleIndexFree xs) :
    xs.filterMap ScheduleAtom.indexOwner? = [] := by
  induction xs with
  | nil => rfl
  | cons atom xs ih =>
      have hhead : ∀ idx, atom ≠ ScheduleAtom.index idx := by
        intro idx heq
        apply hfree idx
        simp [heq]
      have htail : ScheduleIndexFree xs := by
        intro idx hmem
        exact hfree idx (by simp [hmem])
      cases atom <;> simp_all [ScheduleAtom.indexOwner?]

end ScheduleIndexFree

namespace ScheduleDollarFree

public theorem append {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {xs ys : List (ScheduleAtom g input)}
    (hxs : ScheduleDollarFree xs) (hys : ScheduleDollarFree ys) :
    ScheduleDollarFree (xs ++ ys) := by
  intro hmem
  simp only [List.mem_append] at hmem
  exact hmem.elim hxs hys

/-- Erasing a dollar-free ghost gap produces a dollar-free physical gap. -/
public theorem erase {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {xs : List (ScheduleAtom g input)}
    (hfree : ScheduleDollarFree xs) :
    DollarFree (xs.map ScheduleAtom.workSym) := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨atom, hatom, heq⟩
  cases atom with
  | task task =>
      cases task with
      | mk A stack yield parse pre post input_eq mode =>
          cases mode <;> simp [ScheduleAtom.workSym, ScheduleTask.workSym] at heq
  | terminal owner a => simp [ScheduleAtom.workSym] at heq
  | index idx => simp [ScheduleAtom.workSym] at heq
  | dollar => exact hfree hatom
  | close owner => simp [ScheduleAtom.workSym] at heq
  | hash => simp [ScheduleAtom.workSym] at heq

end ScheduleDollarFree

/-- Mark one scheduler index used without changing its denotation or persistent owner. -/
public def ScheduleIndex.markUsed {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (idx : ScheduleIndex g input) : ScheduleIndex g input where
  flags := idx.flags
  relation := idx.relation
  mark := idx.mark.markUsed
  denotes := idx.denotes
  owner := idx.owner

namespace ScheduleIndex

@[simp] public theorem markUsed_flags {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (idx : ScheduleIndex g input) : idx.markUsed.flags = idx.flags := rfl

@[simp] public theorem markUsed_relation {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (idx : ScheduleIndex g input) :
    idx.markUsed.relation = idx.relation := rfl

@[simp] public theorem markUsed_mark {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (idx : ScheduleIndex g input) :
    idx.markUsed.mark = idx.mark.markUsed := rfl

@[simp] public theorem markUsed_owner {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (idx : ScheduleIndex g input) : idx.markUsed.owner = idx.owner := rfl

@[simp] public theorem markUsed_idem {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (idx : ScheduleIndex g input) :
    idx.markUsed.markUsed = idx.markUsed := by
  cases idx with
  | mk flags relation mark denotes owner =>
      cases mark <;> rfl

@[simp] public theorem markUsed_later {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (idx : ScheduleIndex g input) :
    idx.markUsed.mark.later = idx.mark.later := by
  cases idx with
  | mk flags relation mark denotes owner =>
      cases mark <;> rfl

end ScheduleIndex

/-- A ghost compressed visible-stack layout, indexed by the persistent owner of every selected
block.  Gaps may contain tasks, terminals, and `close`, but neither another index nor `$`. -/
public inductive ScheduleBlockLayout (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) :
    List g.flag → List (List g.flag) →
      List (Fin (10 * input.length)) →
      List (ScheduleAtom g input) → List (ScheduleAtom g input) → Prop where
  | nil (tail : List (ScheduleAtom g input)) :
      ScheduleBlockLayout g input [] [] [] tail tail
  | cons {flags : List g.flag} {blocks : List (List g.flag)}
      {owners : List (Fin (10 * input.length))}
      {beta tail tail' : List (ScheduleAtom g input)}
      (idx : ScheduleIndex g input)
      (block_ne : idx.flags ≠ [])
      (indexFree : ScheduleIndexFree beta)
      (dollarFree : ScheduleDollarFree beta)
      (later : flags ≠ [] → idx.mark.later = true)
      (fresh : idx.owner ∉ owners)
      (rest : ScheduleBlockLayout g input flags blocks owners tail tail') :
      ScheduleBlockLayout g input (idx.flags ++ flags) (idx.flags :: blocks)
        (idx.owner :: owners)
        (beta ++ ScheduleAtom.index idx :: tail)
        (beta ++ ScheduleAtom.index idx.markUsed :: tail')

namespace ScheduleBlockLayout

/-- Owner and block indices always have the same length. -/
public theorem owners_length {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    owners.length = blocks.length := by
  induction layout with
  | nil tail => rfl
  | cons idx block_ne indexFree dollarFree later fresh rest ih => simp [ih]

/-- Selected block owners are pairwise distinct. -/
public theorem owners_nodup {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    owners.Nodup := by
  induction layout with
  | nil tail => exact .nil
  | cons idx block_ne indexFree dollarFree later fresh rest ih =>
      exact List.nodup_cons.mpr ⟨fresh, ih⟩

/-- A ghost layout directly supplies the generic persistent ownership carrier. -/
public def blockOwnership {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    BlockOwnership (10 * input.length) blocks where
  owners := owners
  owners_length := layout.owners_length
  owners_nodup := layout.owners_nodup

/-- Erasing ghost annotations produces the corresponding physical compressed layout. -/
public theorem erase {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    BlockLayout g flags blocks (word.map ScheduleAtom.workSym)
      (used.map ScheduleAtom.workSym) := by
  induction layout with
  | nil tail => simpa using BlockLayout.nil (g := g) (tail.map ScheduleAtom.workSym)
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      simpa [List.map_append, ScheduleAtom.workSym, ScheduleIndex.markUsed] using
        BlockLayout.cons (R := idx.relation) (d := idx.mark)
          block_ne idx.denotes hindex.erase hdollar.erase hlater ih

/-- The concrete visible prefix is exactly the flattening of the ghost block partition. -/
public theorem flags_eq_flatten {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    flags = blocks.flatten :=
  layout.erase.flags_eq_flatten

/-- Re-selecting an already used ghost layout leaves every atom and owner unchanged. -/
public theorem idempotent {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    ScheduleBlockLayout g input flags blocks owners used used := by
  induction layout with
  | nil tail => exact .nil tail
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      simpa using ScheduleBlockLayout.cons (idx := idx.markUsed)
        block_ne hindex hdollar (fun hne => by simpa using hlater hne)
        (by simpa using fresh) ih

/-- Insert an index- and dollar-free ghost prefix before the first selected block. -/
public theorem prepend {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (pref : List (ScheduleAtom g input)) (hindex : ScheduleIndexFree pref)
    (hdollar : ScheduleDollarFree pref)
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    ScheduleBlockLayout g input flags blocks owners (pref ++ word) (pref ++ used) := by
  induction layout with
  | nil tail => exact .nil (pref ++ tail)
  | @cons flags blocks owners beta tail tail' idx block_ne hbetaIndex hbetaDollar
      hlater fresh rest ih =>
      simpa [List.append_assoc] using ScheduleBlockLayout.cons (idx := idx)
        block_ne (hindex.append hbetaIndex) (hdollar.append hbetaDollar)
        hlater fresh rest

/-- Restrict a ghost layout to its first `n` whole blocks and aligned owners. -/
public theorem splitTake {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (n : ℕ) (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    ∃ middle,
      ScheduleBlockLayout g input (blocks.take n).flatten (blocks.take n)
        (owners.take n) word middle ∧
      ScheduleBlockLayout g input flags blocks owners middle used := by
  induction layout generalizing n with
  | nil tail =>
      exact ⟨tail, by simpa using ScheduleBlockLayout.nil (g := g) (input := input) tail,
        ScheduleBlockLayout.nil (g := g) (input := input) tail⟩
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      cases n with
      | zero =>
          exact ⟨_, .nil _, ScheduleBlockLayout.cons idx block_ne hindex hdollar
            hlater fresh rest⟩
      | succ n =>
          rcases ih n with ⟨middle, hprefix, hremain⟩
          let next := beta ++ ScheduleAtom.index idx.markUsed :: middle
          refine ⟨next, ?_, ?_⟩
          · simpa using ScheduleBlockLayout.cons (idx := idx)
              block_ne hindex hdollar (fun hne => hlater (by
                intro hflags
                have hblocks : blocks = [] :=
                  rest.erase.blocks_eq_nil_of_flags_eq_nil hflags
                subst blocks
                simp at hne))
              (fun hmem => fresh (List.mem_of_mem_take hmem)) hprefix
          · simpa [next] using ScheduleBlockLayout.cons (idx := idx.markUsed)
              block_ne hindex hdollar (fun hne => by simpa using hlater hne)
              (by simpa using fresh) hremain

/-- The selected ghost prefixes expose their owner list exactly; the arbitrary common tail may
contain additional unselected indices. -/
public theorem exists_selectedPrefixes {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    ∃ selected selectedUsed tail,
      word = selected ++ tail ∧ used = selectedUsed ++ tail ∧
      selected.filterMap ScheduleAtom.indexOwner? = owners ∧
      selectedUsed.filterMap ScheduleAtom.indexOwner? = owners := by
  induction layout with
  | nil tail => exact ⟨[], [], tail, by simp⟩
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      rcases ih with ⟨selected, selectedUsed, commonTail,
        hword, hused, howners, hownersUsed⟩
      refine ⟨beta ++ ScheduleAtom.index idx :: selected,
        beta ++ ScheduleAtom.index idx.markUsed :: selectedUsed, commonTail,
        ?_, ?_, ?_, ?_⟩
      · rw [hword]
        simp [List.append_assoc]
      · rw [hused]
        simp [List.append_assoc]
      · simp [List.filterMap_append, hindex.filterMap_indexOwner_eq_nil,
          ScheduleAtom.indexOwner?, howners]
      · simp [List.filterMap_append, hindex.filterMap_indexOwner_eq_nil,
          ScheduleAtom.indexOwner?, hownersUsed]

/-- Marking selected indices preserves every owner carried by an open frame. -/
public theorem frameOwners_eq {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    word.filterMap ScheduleAtom.closeOwner? =
      used.filterMap ScheduleAtom.closeOwner? := by
  induction layout with
  | nil tail => rfl
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      simp only [List.filterMap_append, List.filterMap_cons,
        ScheduleAtom.closeOwner?]
      exact congrArg (beta.filterMap ScheduleAtom.closeOwner? ++ ·) ih

/-- Marking selected indices preserves every pending-task/terminal owner. -/
public theorem taskOwners_eq {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    word.filterMap ScheduleAtom.taskOwner? =
      used.filterMap ScheduleAtom.taskOwner? := by
  induction layout with
  | nil tail => rfl
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      simp only [List.filterMap_append, List.filterMap_cons,
        ScheduleAtom.taskOwner?]
      exact congrArg (beta.filterMap ScheduleAtom.taskOwner? ++ ·) ih

/-- Marking changes no physical or ghost word length. -/
public theorem word_length_eq {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    word.length = used.length := by
  induction layout with
  | nil tail => rfl
  | cons idx block_ne indexFree dollarFree later fresh rest ih => simp [ih]

/-- With no represented concrete flags there are no selected indices, so input and marked
output words are definitionally the same common tail. -/
public theorem word_eq_used_of_flags_eq_nil
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used)
    (hflags : flags = []) : word = used := by
  cases layout with
  | nil tail => rfl
  | cons idx block_ne indexFree dollarFree later fresh rest =>
      have hlength := congrArg List.length hflags
      simp only [List.length_append, List.length_nil] at hlength
      have hzero : idx.flags.length = 0 := by omega
      have hempty : idx.flags = [] := by simpa using hzero
      exact False.elim (block_ne hempty)

/-- The selected-owner contribution is an exact prefix of the full index-owner list; the same
unselected suffix occurs before and after marking. -/
public theorem exists_indexOwnersSuffix {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    ∃ suffix,
      word.filterMap ScheduleAtom.indexOwner? = owners ++ suffix ∧
      used.filterMap ScheduleAtom.indexOwner? = owners ++ suffix := by
  rcases layout.exists_selectedPrefixes with
    ⟨selected, selectedUsed, tail, hword, hused, howners, hownersUsed⟩
  refine ⟨tail.filterMap ScheduleAtom.indexOwner?, ?_, ?_⟩
  · rw [hword, List.filterMap_append, howners]
  · rw [hused, List.filterMap_append, hownersUsed]

/-- Marking selected indices preserves the complete index-owner sequence. -/
public theorem indexOwners_eq {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    word.filterMap ScheduleAtom.indexOwner? =
      used.filterMap ScheduleAtom.indexOwner? := by
  rcases layout.exists_indexOwnersSuffix with ⟨suffix, hword, hused⟩
  exact hword.trans hused.symm

end ScheduleBlockLayout

namespace ScheduleCursor

@[simp] public theorem taskOwners_mk
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left : List (ScheduleAtom g input)) (focus : ScheduleAtom g input)
    (right : List (ScheduleAtom g input)) :
    (ScheduleCursor.mk left focus right).taskOwners =
      left.filterMap ScheduleAtom.taskOwner? ++
        [focus].filterMap ScheduleAtom.taskOwner? ++
          right.filterMap ScheduleAtom.taskOwner? := by
  cases focus <;>
    simp [ScheduleCursor.taskOwners, ScheduleCursor.word, List.filterMap_append,
      ScheduleAtom.taskOwner?]

@[simp] public theorem indexOwners_mk
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left : List (ScheduleAtom g input)) (focus : ScheduleAtom g input)
    (right : List (ScheduleAtom g input)) :
    (ScheduleCursor.mk left focus right).indexOwners =
      left.filterMap ScheduleAtom.indexOwner? ++
        [focus].filterMap ScheduleAtom.indexOwner? ++
          right.filterMap ScheduleAtom.indexOwner? := by
  cases focus <;>
    simp [ScheduleCursor.indexOwners, ScheduleCursor.word, List.filterMap_append,
      ScheduleAtom.indexOwner?]

@[simp] public theorem frameOwners_mk
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (left : List (ScheduleAtom g input)) (focus : ScheduleAtom g input)
    (right : List (ScheduleAtom g input)) :
    (ScheduleCursor.mk left focus right).frameOwners =
      left.filterMap ScheduleAtom.closeOwner? ++
        [focus].filterMap ScheduleAtom.closeOwner? ++
          right.filterMap ScheduleAtom.closeOwner? := by
  cases focus <;>
    simp [ScheduleCursor.frameOwners, ScheduleCursor.word, List.filterMap_append,
      ScheduleAtom.closeOwner?]

end ScheduleCursor

namespace ScheduleInvariant

/-- Transport the global invariant across a cursor change which preserves all three owner lists
and total ghost-word length. -/
public theorem of_ownerFields_eq
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (hinv : ScheduleInvariant old)
    (htasks : new.taskOwners = old.taskOwners)
    (hindices : new.indexOwners = old.indexOwners)
    (hframes : new.frameOwners = old.frameOwners)
    (hlength : new.word.length = old.word.length) :
    ScheduleInvariant new := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [htasks] using hinv.taskOwners_nodup
  · simpa [hindices] using hinv.indexOwners_nodup
  · simpa [hframes] using hinv.frameOwners_nodup
  · simpa [htasks, hindices, hframes] using hinv.frameOwners_subset_indexOwners
  · simpa [htasks] using hinv.taskCount_le
  · simpa [hindices] using hinv.indexCount_le
  · simpa [ScheduleCursor.frameCount, htasks, hindices, hframes, hlength] using
      hinv.shape_bound

/-- Marking all selected blocks in the right segment preserves the complete scheduler invariant. -/
public theorem replaceRight
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (left : List (ScheduleAtom g input)) (focus : ScheduleAtom g input)
    (layout : ScheduleBlockLayout g input flags blocks owners word used)
    (hinv : ScheduleInvariant (ScheduleCursor.mk left focus word)) :
    ScheduleInvariant (ScheduleCursor.mk left focus used) := by
  apply ScheduleInvariant.of_ownerFields_eq hinv
  · simp only [ScheduleCursor.taskOwners_mk]
    exact congrArg (left.filterMap ScheduleAtom.taskOwner? ++
      [focus].filterMap ScheduleAtom.taskOwner? ++ ·) layout.taskOwners_eq.symm
  · simp only [ScheduleCursor.indexOwners_mk]
    exact congrArg (left.filterMap ScheduleAtom.indexOwner? ++
      [focus].filterMap ScheduleAtom.indexOwner? ++ ·) layout.indexOwners_eq.symm
  · simp only [ScheduleCursor.frameOwners_mk]
    exact congrArg (left.filterMap ScheduleAtom.closeOwner? ++
      [focus].filterMap ScheduleAtom.closeOwner? ++ ·) layout.frameOwners_eq.symm
  · simp [ScheduleCursor.word, layout.word_length_eq]

end ScheduleInvariant
end Aho
end IndexedGrammar
