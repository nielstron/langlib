module

public import Langlib.Grammars.Indexed.NormalForm.AhoScheduleResources

@[expose]
public section

/-!
# Relabelling ghost owners

Index and frame owners are scheduler annotations: they disappear under `workSym`.  This file
packages owner changes at the cursor and layout layers and proves that erasure is unchanged.

The physical owner pool is deliberately restricted to `genericOwnerRange`.  Consequently an
arbitrary permutation of the ambient `Fin (10 * input.length)` carrier does not transport an
`IndexOwnerPool`; pool-aware relabelling must separately prove preservation of that range.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

namespace ScheduleIndex

/-- Change only the ghost owner of a compressed index. -/
public def reowner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    ScheduleIndex g input where
  flags := idx.flags
  relation := idx.relation
  mark := idx.mark
  denotes := idx.denotes
  owner := owner

@[simp] public theorem reowner_flags
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    (idx.reowner owner).flags = idx.flags := rfl

@[simp] public theorem reowner_relation
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    (idx.reowner owner).relation = idx.relation := rfl

@[simp] public theorem reowner_mark
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    (idx.reowner owner).mark = idx.mark := rfl

@[simp] public theorem reowner_owner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    (idx.reowner owner).owner = owner := rfl

@[simp] public theorem reowner_markUsed
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    (idx.reowner owner).markUsed = idx.markUsed.reowner owner := by
  cases idx
  rfl

end ScheduleIndex

namespace ScheduleAtom

/-- Relabel compressed-index atoms, leaving frame-closing owners untouched. -/
public def mapIndexOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    ScheduleAtom g input → ScheduleAtom g input
  | .index idx => .index (idx.reowner (f idx.owner))
  | atom => atom

/-- Relabel every persistent owner: both compressed indices and matching frame closes. -/
public def relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    ScheduleAtom g input → ScheduleAtom g input
  | .index idx => .index (idx.reowner (f idx.owner))
  | .close owner => .close (f owner)
  | atom => atom

/-- Compatibility alias emphasizing that all persistent-owner occurrences are mapped. -/
public abbrev mapOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :=
  relabelOwner (g := g) f

@[simp] public theorem workSym_mapIndexOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.mapIndexOwner f).workSym = atom.workSym := by
  cases atom <;> rfl

@[simp] public theorem workSym_relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.relabelOwner f).workSym = atom.workSym := by
  cases atom <;> rfl

@[simp] public theorem taskOwner?_relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.relabelOwner f).taskOwner? = atom.taskOwner? := by
  cases atom <;> rfl

@[simp] public theorem indexOwner?_mapIndexOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.mapIndexOwner f).indexOwner? = atom.indexOwner?.map f := by
  cases atom <;> rfl

@[simp] public theorem indexOwner?_relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.relabelOwner f).indexOwner? = atom.indexOwner?.map f := by
  cases atom <;> rfl

@[simp] public theorem closeOwner?_mapIndexOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.mapIndexOwner f).closeOwner? = atom.closeOwner? := by
  cases atom <;> rfl

@[simp] public theorem closeOwner?_relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.relabelOwner f).closeOwner? = atom.closeOwner?.map f := by
  cases atom <;> rfl

/-- Filtering index owners commutes with relabelling an arbitrary atom list. -/
@[simp] public theorem filterMap_indexOwner_relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (word : List (ScheduleAtom g input)) :
    (word.map (ScheduleAtom.relabelOwner f)).filterMap
        ScheduleAtom.indexOwner? =
      (word.filterMap ScheduleAtom.indexOwner?).map f := by
  induction word with
  | nil => rfl
  | cons atom word ih =>
      rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, ih]
      cases atom <;>
        simp [ScheduleAtom.relabelOwner, ScheduleAtom.indexOwner?]

/-- Filtering frame owners commutes with relabelling an arbitrary atom list. -/
@[simp] public theorem filterMap_closeOwner_relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (word : List (ScheduleAtom g input)) :
    (word.map (ScheduleAtom.relabelOwner f)).filterMap
        ScheduleAtom.closeOwner? =
      (word.filterMap ScheduleAtom.closeOwner?).map f := by
  induction word with
  | nil => rfl
  | cons atom word ih =>
      rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, ih]
      cases atom <;>
        simp [ScheduleAtom.relabelOwner, ScheduleAtom.closeOwner?]

end ScheduleAtom

namespace ScheduleIndexFree

/-- Owner relabelling cannot introduce an index into an index-free gap. -/
public theorem relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {xs : List (ScheduleAtom g input)} (hfree : ScheduleIndexFree xs)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    ScheduleIndexFree (xs.map (ScheduleAtom.relabelOwner f)) := by
  intro idx hmem
  rcases List.mem_map.mp hmem with ⟨atom, hatom, heq⟩
  cases atom with
  | index old =>
      exact hfree old hatom
  | task task => simp [ScheduleAtom.relabelOwner] at heq
  | terminal owner terminal => simp [ScheduleAtom.relabelOwner] at heq
  | dollar => simp [ScheduleAtom.relabelOwner] at heq
  | close owner => simp [ScheduleAtom.relabelOwner] at heq
  | hash => simp [ScheduleAtom.relabelOwner] at heq

end ScheduleIndexFree

namespace ScheduleDollarFree

/-- Owner relabelling cannot introduce a dollar into a dollar-free gap. -/
public theorem relabelOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {xs : List (ScheduleAtom g input)} (hfree : ScheduleDollarFree xs)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    ScheduleDollarFree (xs.map (ScheduleAtom.relabelOwner f)) := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨atom, hatom, heq⟩
  cases atom <;> simp [ScheduleAtom.relabelOwner] at heq
  exact hfree hatom

end ScheduleDollarFree

namespace ScheduleCursor

/-- Apply one persistent-owner relabelling throughout a cursor. -/
public def relabelOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    ScheduleCursor g input :=
  ⟨cursor.left.map (ScheduleAtom.relabelOwner f),
    cursor.focus.relabelOwner f,
    cursor.right.map (ScheduleAtom.relabelOwner f)⟩

@[simp] public theorem relabelOwners_left
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).left =
      cursor.left.map (ScheduleAtom.relabelOwner f) := rfl

@[simp] public theorem relabelOwners_focus
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).focus = cursor.focus.relabelOwner f := rfl

@[simp] public theorem relabelOwners_right
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).right =
      cursor.right.map (ScheduleAtom.relabelOwner f) := rfl

@[simp] public theorem relabelOwners_word
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).word =
      cursor.word.map (ScheduleAtom.relabelOwner f) := by
  simp [relabelOwners, ScheduleCursor.word, List.map_append]

@[simp] public theorem relabelOwners_erase
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).erase = cursor.erase := by
  cases cursor
  simp [relabelOwners, ScheduleCursor.erase]

@[simp] public theorem relabelOwners_taskOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).taskOwners = cursor.taskOwners := by
  simp only [ScheduleCursor.taskOwners, relabelOwners_word, List.filterMap_map]
  induction cursor.word with
  | nil => rfl
  | cons atom word ih =>
      rw [List.filterMap_cons, List.filterMap_cons, ih]
      cases atom <;> simp [Function.comp_apply]

@[simp] public theorem relabelOwners_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).indexOwners = cursor.indexOwners.map f := by
  simp only [ScheduleCursor.indexOwners, relabelOwners_word, List.filterMap_map]
  induction cursor.word with
  | nil => rfl
  | cons atom word ih =>
      rw [List.filterMap_cons, List.filterMap_cons, ih]
      cases atom <;>
        simp [Function.comp_apply, ScheduleAtom.relabelOwner,
          ScheduleAtom.indexOwner?]

@[simp] public theorem relabelOwners_frameOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).frameOwners = cursor.frameOwners.map f := by
  simp only [ScheduleCursor.frameOwners, relabelOwners_word, List.filterMap_map]
  induction cursor.word with
  | nil => rfl
  | cons atom word ih =>
      rw [List.filterMap_cons, List.filterMap_cons, ih]
      cases atom <;>
        simp [Function.comp_apply, ScheduleAtom.relabelOwner,
          ScheduleAtom.closeOwner?]

@[simp] public theorem relabelOwners_frameCount
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).frameCount = cursor.frameCount := by
  simp [ScheduleCursor.frameCount]

@[simp] public theorem relabelOwners_word_length
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelOwners f).word.length = cursor.word.length := by
  simp

end ScheduleCursor

namespace ScheduleInvariant

/-- An injective owner map transports every qualitative and quantitative scheduler invariant. -/
public theorem relabelOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (hinv : ScheduleInvariant cursor)
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (hf : Function.Injective f) :
    ScheduleInvariant (cursor.relabelOwners f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hinv.taskOwners_nodup
  · simpa using hinv.indexOwners_nodup.map hf
  · simpa using hinv.frameOwners_nodup.map hf
  · intro owner hmem
    rcases List.mem_map.mp (by simpa using hmem) with ⟨old, hold, rfl⟩
    simpa using List.mem_map.mpr
      ⟨old, hinv.frameOwners_subset_indexOwners hold, rfl⟩
  · simpa using hinv.taskCount_le
  · simpa using hinv.indexCount_le
  · simpa [ScheduleCursor.frameCount] using hinv.shape_bound

end ScheduleInvariant

namespace ScheduleBlockLayout

/-- Relabel every selected index and every frame occurrence in a ghost block layout. -/
public theorem relabelOwners
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks owners word used)
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (hf : Function.Injective f) :
    ScheduleBlockLayout g input flags blocks (owners.map f)
      (word.map (ScheduleAtom.relabelOwner f))
      (used.map (ScheduleAtom.relabelOwner f)) := by
  induction layout with
  | nil tail =>
      simpa using
        (ScheduleBlockLayout.nil (g := g) (input := input)
          (tail.map (ScheduleAtom.relabelOwner f)))
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      simp only [List.map_cons, List.map_append, ScheduleAtom.relabelOwner,
        ScheduleIndex.markUsed_owner]
      apply ScheduleBlockLayout.cons (idx := idx.reowner (f idx.owner))
      · simpa using block_ne
      · exact hindex.relabelOwner f
      · exact hdollar.relabelOwner f
      · simpa using hlater
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
        exact fresh ((hf heq) ▸ howner)
      · simpa using ih

/-- Swap the head owner of a nonempty selected layout while leaving all tail-owner labels fixed.
The words are relabelled globally so matching frame closes remain synchronized. -/
public theorem reownerHead
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {oldOwner newOwner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (layout : ScheduleBlockLayout g input flags blocks (oldOwner :: owners) word used)
    (hnew : newOwner ∉ owners) :
    ScheduleBlockLayout g input flags blocks (newOwner :: owners)
      (word.map (ScheduleAtom.relabelOwner (Equiv.swap oldOwner newOwner)))
      (used.map (ScheduleAtom.relabelOwner (Equiv.swap oldOwner newOwner))) := by
  have hold : oldOwner ∉ owners :=
    (List.nodup_cons.mp layout.owners_nodup).1
  have htail : owners.map (Equiv.swap oldOwner newOwner) = owners := by
    calc
      owners.map (Equiv.swap oldOwner newOwner) = owners.map id := by
        apply List.map_congr_left
        intro owner howner
        apply Equiv.swap_apply_of_ne_of_ne
        · intro heq
          exact hold (heq ▸ howner)
        · intro heq
          exact hnew (heq ▸ howner)
      _ = owners := List.map_id owners
  simpa [htail] using
    layout.relabelOwners (Equiv.swap oldOwner newOwner)
      (Equiv.swap oldOwner newOwner).injective

end ScheduleBlockLayout

end Aho
end IndexedGrammar
