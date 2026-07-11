module

public import Langlib.Grammars.Indexed.NormalForm.AhoGhostLayout

@[expose]
public section

/-!
# Branch-local compressed-index overlays

A protected compressed block may be shared by a pending sibling and therefore cannot be
updated in place.  A branch which pushes above that shared suffix instead keeps a overlay,
adjacent copy-on-write prefix.  The head of this prefix is the mutable compressed accumulator;
temporary event-boundary blocks may be consed above it and popped again without forgetting that
the lower head is still overlay.

This file is deliberately ghost-only.  An overlay index erases to the existing
`WorkSym.index`, so all operations are already certified by `livePushFresh`,
`livePushCompress`, the adjacent pop-and-erase moves, and `eraseIndex`.  The only missing datum
in the runner is which adjacent lower indices remain branch-local.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Computed overlay words and ledgers -/

namespace ScheduleOverlay

/-- Concrete flag blocks carried by the overlay overlay, nearest block first. -/
public def blocks
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input)) : List (List g.flag) :=
  overlay.map ScheduleIndex.flags

/-- The complete visible flag prefix after placing an overlay above a protected suffix. -/
public def flags
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input)) (baseSuffix : List g.flag) : List g.flag :=
  (blocks overlay).flatten ++ baseSuffix

/-- Persistent owners of the overlay followed by those of the protected suffix. -/
public def owners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input))
    (baseSuffix : List (Fin (10 * input.length))) :
    List (Fin (10 * input.length)) :=
  overlay.map ScheduleIndex.owner ++ baseSuffix

/-- Physical scheduler word with every overlay overlay block adjacent to the active task. -/
public def word
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input))
    (baseSuffix : List (ScheduleAtom g input)) : List (ScheduleAtom g input) :=
  overlay.map ScheduleAtom.index ++ baseSuffix

/-- Endpoint word after every overlay block and every protected block has been marked used. -/
public def used
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input))
    (baseSuffix : List (ScheduleAtom g input)) : List (ScheduleAtom g input) :=
  overlay.map (fun idx => ScheduleAtom.index idx.markUsed) ++ baseSuffix

@[simp] public theorem blocks_nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T} :
    blocks (g := g) (input := input) [] = [] := rfl

@[simp] public theorem blocks_cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (overlay : List (ScheduleIndex g input)) :
    blocks (idx :: overlay) = idx.flags :: blocks overlay := rfl

@[simp] public theorem flags_nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (baseSuffix : List g.flag) :
    flags (g := g) (input := input) [] baseSuffix = baseSuffix := by
  simp [flags]

@[simp] public theorem flags_cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (overlay : List (ScheduleIndex g input))
    (baseSuffix : List g.flag) :
    flags (idx :: overlay) baseSuffix = idx.flags ++ flags overlay baseSuffix := by
  simp [flags, blocks, List.append_assoc]

@[simp] public theorem owners_nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (baseSuffix : List (Fin (10 * input.length))) :
    owners (g := g) (input := input) [] baseSuffix = baseSuffix := by
  simp [owners]

@[simp] public theorem owners_cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (overlay : List (ScheduleIndex g input))
    (baseSuffix : List (Fin (10 * input.length))) :
    owners (idx :: overlay) baseSuffix = idx.owner :: owners overlay baseSuffix := by
  simp [owners]

@[simp] public theorem word_nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (baseSuffix : List (ScheduleAtom g input)) :
    word (g := g) (input := input) [] baseSuffix = baseSuffix := by
  simp [word]

@[simp] public theorem word_cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (overlay : List (ScheduleIndex g input))
    (baseSuffix : List (ScheduleAtom g input)) :
    word (idx :: overlay) baseSuffix = .index idx :: word overlay baseSuffix := by
  simp [word]

@[simp] public theorem used_nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (baseSuffix : List (ScheduleAtom g input)) :
    used (g := g) (input := input) [] baseSuffix = baseSuffix := by
  simp [used]

@[simp] public theorem used_cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (overlay : List (ScheduleIndex g input))
    (baseSuffix : List (ScheduleAtom g input)) :
    used (idx :: overlay) baseSuffix =
      .index idx.markUsed :: used overlay baseSuffix := by
  simp [used]

@[simp] public theorem blocks_length
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input)) :
    (blocks overlay).length = overlay.length := by
  simp [blocks]

@[simp] public theorem privateOwners_length
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (overlay : List (ScheduleIndex g input)) :
    (overlay.map ScheduleIndex.owner).length = overlay.length := by
  simp

end ScheduleOverlay

/-! ## Adjacent overlay certificate -/

/-- An adjacent overlay index prefix layered over an already certified protected layout.

The certificate is indexed only by the list of overlay `ScheduleIndex` records.  All other
objects are computed by `ScheduleOverlay`, which makes consing a fresh block, replacing the
mutable head, and popping a temporary head exact operations rather than transports between
existential layouts.
-/
public inductive AdjacentOverlayLayout
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    (base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed) :
    List (ScheduleIndex g input) → Prop where
  | nil : AdjacentOverlayLayout base []
  | cons {overlay : List (ScheduleIndex g input)}
      (idx : ScheduleIndex g input)
      (block_ne : idx.flags ≠ [])
      (later : ScheduleOverlay.flags overlay protectedFlags ≠ [] →
        idx.mark.later = true)
      (fresh : idx.owner ∉ ScheduleOverlay.owners overlay protectedOwners)
      (rest : AdjacentOverlayLayout base overlay) :
      AdjacentOverlayLayout base (idx :: overlay)

namespace AdjacentOverlayLayout

/-- The empty overlay prefix is the protected layout itself. -/
public def empty
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    (base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed) :
    AdjacentOverlayLayout base [] :=
  .nil

/-- Put one mutable overlay block above a protected suffix. -/
public def singleton
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    (base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed)
    (idx : ScheduleIndex g input) (block_ne : idx.flags ≠ [])
    (later : protectedFlags ≠ [] → idx.mark.later = true)
    (fresh : idx.owner ∉ protectedOwners) :
    AdjacentOverlayLayout base [idx] := by
  apply AdjacentOverlayLayout.cons idx block_ne
  · simpa using later
  · simpa using fresh
  · exact .nil

/-- Cons a new overlay event-boundary block above an existing overlay. -/
public def push
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay)
    (idx : ScheduleIndex g input) (block_ne : idx.flags ≠ [])
    (later : ScheduleOverlay.flags overlay protectedFlags ≠ [] →
      idx.mark.later = true)
    (fresh : idx.owner ∉ ScheduleOverlay.owners overlay protectedOwners) :
    AdjacentOverlayLayout base (idx :: overlay) :=
  .cons idx block_ne later fresh layout

/-- Pop the adjacent overlay head while retaining the lower copy-on-write classification. -/
public theorem tail
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {head : ScheduleIndex g input} {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base (head :: overlay)) :
    AdjacentOverlayLayout base overlay := by
  cases layout with
  | cons _ _ _ _ rest => exact rest

public theorem head_block_ne
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {head : ScheduleIndex g input} {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base (head :: overlay)) :
    head.flags ≠ [] := by
  cases layout with
  | cons _ block_ne _ _ _ => exact block_ne

public theorem head_later
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {head : ScheduleIndex g input} {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base (head :: overlay))
    (hlower : ScheduleOverlay.flags overlay protectedFlags ≠ []) :
    head.mark.later = true := by
  cases layout with
  | cons _ _ later _ _ => exact later hlower

public theorem head_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {head : ScheduleIndex g input} {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base (head :: overlay)) :
    head.owner ∉ ScheduleOverlay.owners overlay protectedOwners := by
  cases layout with
  | cons _ _ _ fresh _ => exact fresh

/-- A nonempty overlay supplies the live-focus premise used by every overlay runner state. -/
public theorem flags_length_pos
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {head : ScheduleIndex g input} {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base (head :: overlay)) :
    0 < (ScheduleOverlay.flags (head :: overlay) protectedFlags).length := by
  rw [ScheduleOverlay.flags_cons, List.length_append]
  exact Nat.add_pos_left (List.length_pos_of_ne_nil layout.head_block_ne) _

/-- Replace only the mutable head.  This is the ghost counterpart of `livePushCompress`.
The lower overlay stack and the shared protected base are unchanged. -/
public theorem replaceHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {head replacement : ScheduleIndex g input}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base (head :: overlay))
    (block_ne : replacement.flags ≠ [])
    (owner_eq : replacement.owner = head.owner)
    (later_eq : replacement.mark.later = head.mark.later) :
    AdjacentOverlayLayout base (replacement :: overlay) := by
  cases layout with
  | cons _ _ later fresh rest =>
      apply AdjacentOverlayLayout.cons replacement block_ne
      · intro hlower
        rw [later_eq]
        exact later hlower
      · simpa [owner_eq] using fresh
      · exact rest

/-- Forget copy-on-write status and seal every overlay block into the ordinary protected layout.
This is used exactly when a binary fork starts sharing the overlay between its children. -/
public theorem toProtected
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay) :
    ScheduleBlockLayout g input
      (ScheduleOverlay.flags overlay protectedFlags)
      (ScheduleOverlay.blocks overlay ++ protectedBlocks)
      (ScheduleOverlay.owners overlay protectedOwners)
      (ScheduleOverlay.word overlay protectedWord)
      (ScheduleOverlay.used overlay protectedUsed) := by
  induction layout with
  | nil =>
      simpa using base
  | @cons overlay idx block_ne later fresh rest ih =>
      have hindex : ScheduleIndexFree ([] : List (ScheduleAtom g input)) := by
        simp [ScheduleIndexFree]
      have hdollar : ScheduleDollarFree ([] : List (ScheduleAtom g input)) := by
        simp [ScheduleDollarFree]
      simpa using ScheduleBlockLayout.cons idx block_ne hindex hdollar later fresh ih

/-- All overlay and protected owners are duplicate-free. -/
public theorem owners_nodup
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay) :
    (ScheduleOverlay.owners overlay protectedOwners).Nodup :=
  layout.toProtected.owners_nodup

/-- Overlay owners are duplicate-free independently of the protected suffix. -/
public theorem private_owners_nodup
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay) :
    (overlay.map ScheduleIndex.owner).Nodup := by
  exact (List.nodup_append.mp layout.owners_nodup).1

/-- No branch-local owner aliases an owner in the shared protected suffix. -/
public theorem private_disjoint_protected
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay) :
    List.Disjoint (overlay.map ScheduleIndex.owner) protectedOwners := by
  rw [List.disjoint_left]
  intro owner hoverlay hprotected
  exact (List.nodup_append.mp layout.owners_nodup).2.2
    owner hoverlay owner hprotected rfl

/-- Every block in the sealed overlay/protected layout is nonempty. -/
public theorem blocks_nonempty
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay) :
    ∀ block ∈ ScheduleOverlay.blocks overlay ++ protectedBlocks, block ≠ [] :=
  layout.toProtected.erase.blocks_nonempty

/-- The complete visible prefix is exactly the flattening of the sealed block list. -/
public theorem flags_eq_flatten
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay) :
    ScheduleOverlay.flags overlay protectedFlags =
      (ScheduleOverlay.blocks overlay ++ protectedBlocks).flatten :=
  layout.toProtected.flags_eq_flatten

/-- Sealing preserves the exact block/owner alignment required by the protected runner. -/
public theorem owners_length
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {protectedFlags : List g.flag} {protectedBlocks : List (List g.flag)}
    {protectedOwners : List (Fin (10 * input.length))}
    {protectedWord protectedUsed : List (ScheduleAtom g input)}
    {base : ScheduleBlockLayout g input protectedFlags protectedBlocks protectedOwners
      protectedWord protectedUsed}
    {overlay : List (ScheduleIndex g input)}
    (layout : AdjacentOverlayLayout base overlay) :
    (ScheduleOverlay.owners overlay protectedOwners).length =
      (ScheduleOverlay.blocks overlay ++ protectedBlocks).length :=
  layout.toProtected.owners_length

end AdjacentOverlayLayout

end Aho
end IndexedGrammar

end
