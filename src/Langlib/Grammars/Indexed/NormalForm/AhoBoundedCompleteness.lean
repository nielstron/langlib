module

public import Langlib.Grammars.Indexed.NormalForm.AhoCompleteness
public import Mathlib.Data.List.SplitLengths
public import Mathlib.Data.Finset.Sort

@[expose]
public section

/-!
# The compressed-block budget along a consumption route

Unary push/pop stretches of a chosen consumption route may be compressed into one index block.
Crossing a binary node ends the current stretch and starts another one.  Thus the number of
maximal binary-free chunks is one plus the number of binary barriers on the route.

`barrierOwners` already charges every barrier to a distinct terminal in the off-route child.
The missing final charge is a terminal in the child followed by the route.  Adding this owner
makes the bound sharp: the number of chunks, rather than merely the number of barriers, is at
most the terminal yield length.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace NFParse
namespace ConsumeRoute

/-- A terminal position that stays inside the branch followed by a consumption route. -/
public def followedOwner
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} :
    ConsumeRoute g p k → Fin w.length
  | .binaryLeft (u := u) (v := v) route =>
      embedLeft u v route.followedOwner
  | .binaryRight (u := u) (v := v) route =>
      embedRight u v route.followedOwner
  | .popHere (rest := rest) =>
      ⟨0, rest.yield_length_pos⟩
  | .popTail route => route.followedOwner
  | .push route => route.followedOwner

/-- The on-route terminal owner is disjoint from every off-route barrier owner. -/
public theorem followedOwner_not_mem_barrierOwners
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.followedOwner ∉ route.barrierOwners := by
  induction route with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      intro hmem
      rw [barrierOwners, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · have hval := congrArg Fin.val hhead
        simp only [followedOwner, embedLeft] at hval
        exact (Nat.ne_of_lt route.followedOwner.isLt) hval
      · rcases List.mem_map.mp htail with ⟨owner, howner, heq⟩
        have heq' : route.followedOwner = owner :=
          embedLeft_injective u v heq.symm
        exact ih (heq' ▸ howner)
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      intro hmem
      rw [barrierOwners, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · have hval := congrArg Fin.val hhead
        have hu := left.yield_length_pos
        simp only [followedOwner, embedRight] at hval
        omega
      · rcases List.mem_map.mp htail with ⟨owner, howner, heq⟩
        have heq' : route.followedOwner = owner :=
          embedRight_injective u v heq.symm
        exact ih (heq' ▸ howner)
  | popHere => simp [barrierOwners]
  | popTail route ih => simpa [barrierOwners, followedOwner] using ih
  | push route ih => simpa [barrierOwners, followedOwner] using ih

/-- The terminal followed by the route together with all off-route charges is duplicate-free. -/
public theorem followedOwner_cons_barrierOwners_nodup
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    (route.followedOwner :: route.barrierOwners).Nodup := by
  rw [List.nodup_cons]
  exact ⟨route.followedOwner_not_mem_barrierOwners, route.barrierOwners_nodup⟩

/-- There is room for both every binary barrier and the final followed branch in the yield. -/
public theorem barrierOwners_length_add_one_le
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.barrierOwners.length + 1 ≤ w.length := by
  have hcard := route.followedOwner_cons_barrierOwners_nodup.length_le_card
  simpa [Nat.add_comm] using hcard

/-- Number of maximal binary-free chunks on a consumption route.  Unary constructors stay in
the current chunk; each binary constructor starts exactly one further chunk. -/
public def noBinaryChunkCount
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} : ConsumeRoute g p k → ℕ
  | .binaryLeft route => route.noBinaryChunkCount + 1
  | .binaryRight route => route.noBinaryChunkCount + 1
  | .popHere => 1
  | .popTail route => route.noBinaryChunkCount
  | .push route => route.noBinaryChunkCount

/-- Chunk count is precisely one plus the existing barrier count. -/
public theorem noBinaryChunkCount_eq_barrierOwners_length_add_one
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.noBinaryChunkCount = route.barrierOwners.length + 1 := by
  induction route with
  | binaryLeft route ih => simp [noBinaryChunkCount, barrierOwners, ih, Nat.add_assoc]
  | binaryRight route ih => simp [noBinaryChunkCount, barrierOwners, ih, Nat.add_assoc]
  | popHere => simp [noBinaryChunkCount, barrierOwners]
  | popTail route ih => simpa [noBinaryChunkCount, barrierOwners] using ih
  | push route ih => simpa [noBinaryChunkCount, barrierOwners] using ih

/-- A route is one maximal chunk exactly when it is binary-free. -/
public theorem noBinary_iff_chunkCount_eq_one
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.NoBinary ↔ route.noBinaryChunkCount = 1 := by
  rw [route.noBinary_iff_barrierOwners_nil,
    route.noBinaryChunkCount_eq_barrierOwners_length_add_one]
  constructor
  · intro hnil
    rw [hnil]
    rfl
  · intro hlen
    have : route.barrierOwners.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this

/-- The number of compressed blocks needed by the maximal binary-free decomposition is bounded
by the terminal yield.  This is the index-payload inequality needed by `ScheduleInvariant`. -/
public theorem noBinaryChunkCount_le_yield_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.noBinaryChunkCount ≤ w.length := by
  rw [route.noBinaryChunkCount_eq_barrierOwners_length_add_one]
  exact route.barrierOwners_length_add_one_le

/-! ### Prefix truncation of a chosen consumption route -/

/-- Follow the same branch choices only as far as a shallower inherited occurrence.  This is a
structural truncation, not a fresh classical choice of route, so it preserves the absence of
binary barriers. -/
public def truncate
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k)
    (j : ℕ) (hjk : j ≤ k) : ConsumeRoute g p j :=
  match route with
  | .binaryLeft inner => .binaryLeft (inner.truncate j hjk)
  | .binaryRight inner => .binaryRight (inner.truncate j hjk)
  | .popHere => by
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst j
      exact .popHere
  | .popTail inner => by
      cases j with
      | zero => exact .popHere
      | succ j =>
          exact .popTail (inner.truncate j (by omega))
  | .push inner =>
      .push (inner.truncate (j + 1) (by omega))
termination_by sizeOf route

/-- Truncating a binary-free route to a shallower occurrence remains binary-free. -/
public theorem truncate_noBinary
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k)
    (hroute : route.NoBinary) (j : ℕ) (hjk : j ≤ k) :
    (route.truncate j hjk).NoBinary := by
  induction route generalizing j with
  | binaryLeft inner ih => exact False.elim hroute
  | binaryRight inner ih => exact False.elim hroute
  | popHere =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst j
      simp [truncate, barrierOwners]
  | popTail inner ih =>
      cases j with
      | zero => simp [truncate, barrierOwners]
      | succ j =>
          simpa [truncate, NoBinary] using ih hroute j (by omega)
  | push inner ih =>
      simpa [truncate, NoBinary] using ih hroute (j + 1) (by omega)

/-- Truncation keeps an initial segment of the original route's barrier charges.  In particular,
it neither invents a binary barrier nor changes the owner assigned to a barrier it retains. -/
public theorem barrierOwners_truncate_prefix
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k)
    (j : ℕ) (hjk : j ≤ k) :
    (route.truncate j hjk).barrierOwners <+: route.barrierOwners := by
  induction route generalizing j with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k inner ih =>
      have htail := (ih j hjk).map (embedLeft u v)
      rcases htail with ⟨suffix, hsuffix⟩
      refine ⟨suffix, ?_⟩
      simpa [truncate, barrierOwners] using
        congrArg (fun tail =>
          (⟨u.length, by
            have hv := right.yield_length_pos
            simp only [List.length_append]
            omega⟩ : Fin (u ++ v).length) :: tail) hsuffix
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k inner ih =>
      have htail := (ih j hjk).map (embedRight u v)
      rcases htail with ⟨suffix, hsuffix⟩
      refine ⟨suffix, ?_⟩
      simpa [truncate, barrierOwners] using
        congrArg (fun tail =>
          (⟨0, by
            have hu := left.yield_length_pos
            simp only [List.length_append]
            omega⟩ : Fin (u ++ v).length) :: tail) hsuffix
  | popHere =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst j
      simp [truncate, barrierOwners]
  | popTail inner ih =>
      cases j with
      | zero => simp [truncate, barrierOwners]
      | succ j => simpa [truncate, barrierOwners] using ih j (by omega)
  | push inner ih =>
      simpa [truncate, barrierOwners] using ih (j + 1) (by omega)

/-- Consequently truncation cannot increase the number of maximal binary-free chunks. -/
public theorem noBinaryChunkCount_truncate_le
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k)
    (j : ℕ) (hjk : j ≤ k) :
    (route.truncate j hjk).noBinaryChunkCount ≤ route.noBinaryChunkCount := by
  rw [(route.truncate j hjk).noBinaryChunkCount_eq_barrierOwners_length_add_one,
    route.noBinaryChunkCount_eq_barrierOwners_length_add_one]
  exact Nat.add_le_add_right (route.barrierOwners_truncate_prefix j hjk).length_le 1

/-- If a structural truncation is unsafe for unary compression, the original route has at least
one binary-barrier owner. -/
public theorem barrierOwners_ne_nil_of_truncate_not_noBinary
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k j : ℕ} (route : ConsumeRoute g p k)
    (hjk : j ≤ k) (hunsafe : ¬ (route.truncate j hjk).NoBinary) :
    route.barrierOwners ≠ [] := by
  intro hnil
  have hroute : route.NoBinary :=
    (route.noBinary_iff_barrierOwners_nil).2 hnil
  exact hunsafe (route.truncate_noBinary hroute j hjk)

/-- Equivalently, an unsafe truncation certifies that the original route needs at least two
maximal binary-free chunks. -/
public theorem two_le_noBinaryChunkCount_of_truncate_not_noBinary
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k j : ℕ} (route : ConsumeRoute g p k)
    (hjk : j ≤ k) (hunsafe : ¬ (route.truncate j hjk).NoBinary) :
    2 ≤ route.noBinaryChunkCount := by
  have hne := route.barrierOwners_ne_nil_of_truncate_not_noBinary hjk hunsafe
  rw [route.noBinaryChunkCount_eq_barrierOwners_length_add_one]
  have hpos := List.length_pos_of_ne_nil hne
  omega

end ConsumeRoute
end NFParse

namespace NFParse

/-- Stack depths at which a productive parse event can end a compressed unary block.

Terminal leaves and binary forks contribute the current depth.  A pop shifts every deeper event
one position away from the root, while a push removes the freshly pushed position. -/
public def eventDepths {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag}
    {w : List T} : NFParse g A stack w → Finset ℕ
  | .binary _ _ _ _ left right => insert 0 (left.eventDepths ∪ right.eventDepths)
  | .pop _ _ _ _ rest => rest.eventDepths.image Nat.succ
  | .push _ _ _ _ rest => rest.eventDepths.image Nat.pred
  | .terminal _ _ _ _ => {0}

end NFParse

namespace Aho
namespace ScheduleTask

/-- Embed a terminal position of a pending task's yield into the complete input word. -/
public def embedYieldOwner {g : IndexedGrammar T} {input : List T}
    (task : ScheduleTask g input) : Fin task.yield.length → Fin input.length :=
  fun owner => ⟨task.pre.length + owner.val, by
    have hlength := congrArg List.length task.input_eq
    simp only [List.length_append] at hlength
    omega⟩

public theorem embedYieldOwner_injective {g : IndexedGrammar T} {input : List T}
    (task : ScheduleTask g input) : Function.Injective task.embedYieldOwner := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [embedYieldOwner] at hval
  omega

/-- The task's ordinary owner is the embedding of the first terminal in its yield. -/
public theorem embedYieldOwner_zero_eq_owner {g : IndexedGrammar T} {input : List T}
    (task : ScheduleTask g input) :
    task.embedYieldOwner ⟨0, task.parse.yield_length_pos⟩ = task.owner := by
  apply Fin.ext
  rfl

/-- Absolute input owners for all compressed blocks in the maximal binary-free decomposition of
a chosen consumption route belonging to this task. -/
public def routeBlockOwners {g : IndexedGrammar T} {input : List T}
    (task : ScheduleTask g input) {k : ℕ}
    (route : NFParse.ConsumeRoute g task.parse k) : List (Fin input.length) :=
  (route.followedOwner :: route.barrierOwners).map task.embedYieldOwner

/-- Block owners belonging to one task are pairwise distinct. -/
public theorem routeBlockOwners_nodup {g : IndexedGrammar T} {input : List T}
    (task : ScheduleTask g input) {k : ℕ}
    (route : NFParse.ConsumeRoute g task.parse k) :
    (task.routeBlockOwners route).Nodup := by
  exact route.followedOwner_cons_barrierOwners_nodup.map task.embedYieldOwner_injective

@[simp] public theorem routeBlockOwners_length {g : IndexedGrammar T}
    {input : List T} (task : ScheduleTask g input) {k : ℕ}
    (route : NFParse.ConsumeRoute g task.parse k) :
    (task.routeBlockOwners route).length = route.noBinaryChunkCount := by
  simp [routeBlockOwners, route.noBinaryChunkCount_eq_barrierOwners_length_add_one,
    Nat.add_comm]

/-- A task's compressed blocks fit within its own yield interval. -/
public theorem routeBlockOwners_length_le_yield {g : IndexedGrammar T}
    {input : List T} (task : ScheduleTask g input) {k : ℕ}
    (route : NFParse.ConsumeRoute g task.parse k) :
    (task.routeBlockOwners route).length ≤ task.yield.length := by
  rw [task.routeBlockOwners_length route]
  exact route.noBinaryChunkCount_le_yield_length

/-- In particular, the local block-owner count satisfies the global input-length budget used by
`ScheduleInvariant.indexCount_le`. -/
public theorem routeBlockOwners_length_le_input {g : IndexedGrammar T}
    {input : List T} (task : ScheduleTask g input) {k : ℕ}
    (route : NFParse.ConsumeRoute g task.parse k) :
    (task.routeBlockOwners route).length ≤ input.length := by
  simpa using (task.routeBlockOwners_nodup route).length_le_card

/-- The yield interval of `left` lies completely before the yield interval of `right`. -/
public def YieldBefore {g : IndexedGrammar T} {input : List T}
    (left right : ScheduleTask g input) : Prop :=
  left.pre.length + left.yield.length ≤ right.pre.length

/-- Owners embedded from disjointly ordered task intervals cannot coincide. -/
public theorem embedYieldOwner_ne_of_yieldBefore {g : IndexedGrammar T}
    {input : List T} {left right : ScheduleTask g input}
    (hbefore : YieldBefore left right)
    (i : Fin left.yield.length) (j : Fin right.yield.length) :
    left.embedYieldOwner i ≠ right.embedYieldOwner j := by
  intro heq
  have hval := congrArg Fin.val heq
  have hi := i.isLt
  have hj := j.isLt
  unfold YieldBefore at hbefore
  simp only [embedYieldOwner] at hval
  exact (by omega)

/-- Compressed-block owner lists from disjoint pending-task intervals are disjoint. -/
public theorem routeBlockOwners_disjoint_of_yieldBefore {g : IndexedGrammar T}
    {input : List T} {left right : ScheduleTask g input}
    (hbefore : YieldBefore left right) {i j : ℕ}
    (leftRoute : NFParse.ConsumeRoute g left.parse i)
    (rightRoute : NFParse.ConsumeRoute g right.parse j) :
    List.Disjoint (left.routeBlockOwners leftRoute)
      (right.routeBlockOwners rightRoute) := by
  rw [List.disjoint_left]
  intro owner hleft hright
  rcases List.mem_map.mp hleft with ⟨leftOwner, _hleftOwner, hleftEq⟩
  rcases List.mem_map.mp hright with ⟨rightOwner, _hrightOwner, hrightEq⟩
  apply left.embedYieldOwner_ne_of_yieldBefore hbefore leftOwner rightOwner
  exact hleftEq.trans hrightEq.symm

/-- Consequently concatenating the compressed blocks of two ordered task intervals preserves
the global no-duplicate ownership invariant. -/
public theorem routeBlockOwners_append_nodup_of_yieldBefore {g : IndexedGrammar T}
    {input : List T} {left right : ScheduleTask g input}
    (hbefore : YieldBefore left right) {i j : ℕ}
    (leftRoute : NFParse.ConsumeRoute g left.parse i)
    (rightRoute : NFParse.ConsumeRoute g right.parse j) :
    (left.routeBlockOwners leftRoute ++ right.routeBlockOwners rightRoute).Nodup :=
  (left.routeBlockOwners_nodup leftRoute).append
    (right.routeBlockOwners_nodup rightRoute)
    (routeBlockOwners_disjoint_of_yieldBefore hbefore leftRoute rightRoute)

end ScheduleTask

/-! ## Persistent ownership of inherited block partitions -/

/-- A block list together with one pairwise-distinct owner in an ambient finite budget for each
block.  The carrier is independent of how a child refines its local event cuts, so ancestor
owners can persist unchanged throughout the runner. -/
public structure BlockOwnership (N : ℕ) {X : Type} (blocks : List X) where
  owners : List (Fin N)
  owners_length : owners.length = blocks.length
  owners_nodup : owners.Nodup

namespace BlockOwnership

public def nil (N : ℕ) {X : Type} : BlockOwnership N ([] : List X) where
  owners := []
  owners_length := rfl
  owners_nodup := .nil

/-- Add a fresh owner in front of an existing aligned block list. -/
public def cons {N : ℕ} {X : Type} {blocks : List X}
    (block : X) (owner : Fin N) (ownership : BlockOwnership N blocks)
    (hfresh : owner ∉ ownership.owners) : BlockOwnership N (block :: blocks) where
  owners := owner :: ownership.owners
  owners_length := by simp [ownership.owners_length]
  owners_nodup := List.nodup_cons.mpr ⟨hfresh, ownership.owners_nodup⟩

/-- Alias emphasizing that the new block/owner is prepended. -/
public def prepend {N : ℕ} {X : Type} {blocks : List X}
    (block : X) (owner : Fin N) (ownership : BlockOwnership N blocks)
    (hfresh : owner ∉ ownership.owners) : BlockOwnership N (block :: blocks) :=
  ownership.cons block owner hfresh

/-- Retain ownership for the first `n` blocks. -/
public def take {N : ℕ} {X : Type} {blocks : List X}
    (n : ℕ) (ownership : BlockOwnership N blocks) :
    BlockOwnership N (blocks.take n) where
  owners := ownership.owners.take n
  owners_length := by simp [ownership.owners_length]
  owners_nodup := ownership.owners_nodup.take

/-- Retain ownership for the blocks after the first `n`. -/
public def drop {N : ℕ} {X : Type} {blocks : List X}
    (n : ℕ) (ownership : BlockOwnership N blocks) :
    BlockOwnership N (blocks.drop n) where
  owners := ownership.owners.drop n
  owners_length := by simp [ownership.owners_length]
  owners_nodup := ownership.owners_nodup.drop

/-- Ownership carriers are disjoint when their concrete owner lists are disjoint. -/
public def Disjoint {N : ℕ} {X Y : Type} {leftBlocks : List X}
    {rightBlocks : List Y} (left : BlockOwnership N leftBlocks)
    (right : BlockOwnership N rightBlocks) : Prop :=
  List.Disjoint left.owners right.owners

public theorem disjoint_comm {N : ℕ} {X Y : Type} {leftBlocks : List X}
    {rightBlocks : List Y} {left : BlockOwnership N leftBlocks}
    {right : BlockOwnership N rightBlocks} :
    Disjoint left right ↔ Disjoint right left :=
  List.disjoint_comm

/-- Concatenate two aligned carriers whose owner sets are disjoint. -/
public def append {N : ℕ} {X : Type} {leftBlocks rightBlocks : List X}
    (left : BlockOwnership N leftBlocks) (right : BlockOwnership N rightBlocks)
    (hdisjoint : Disjoint left right) :
    BlockOwnership N (leftBlocks ++ rightBlocks) where
  owners := left.owners ++ right.owners
  owners_length := by simp [left.owners_length, right.owners_length]
  owners_nodup := left.owners_nodup.append right.owners_nodup hdisjoint

/-- The prefix and suffix inherited from one carrier have disjoint owner sets. -/
public theorem disjoint_take_drop {N : ℕ} {X : Type} {blocks : List X}
    (n : ℕ) (ownership : BlockOwnership N blocks) :
    Disjoint (ownership.take n) (ownership.drop n) := by
  exact List.disjoint_take_drop ownership.owners_nodup (Nat.le_refl n)

/-- Distinct finite owners give the required ambient block-count bound. -/
public theorem blocks_length_le {N : ℕ} {X : Type} {blocks : List X}
    (ownership : BlockOwnership N blocks) : blocks.length ≤ N := by
  rw [← ownership.owners_length]
  simpa using ownership.owners_nodup.length_le_card

end BlockOwnership

/-! ## Revised transient-index accounting -/

/-- Arithmetic form used by the ephemeral compressed-token scheduler.  Tasks still inject into
the `n` terminal positions.  Persistent indices together with the one currently transient index
fit in two copies of those positions, and every open frame is charged to a persistent index. -/
public theorem framed_cell_count_le_eight_mul_of_index_add_one_le_two_mul
    {tasks indices frames n : ℕ}
    (htasks : tasks ≤ n) (hindices : indices + 1 ≤ 2 * n)
    (hframes : frames ≤ indices) (hn : 0 < n) :
    tasks + indices + 2 * frames + 2 ≤ 8 * n := by
  have hn' : 1 ≤ n := hn
  omega

namespace ScheduleInvariant

/-- The existing scheduler invariant's task and shape fields combine with the sharper
ephemeral-index and frame bounds to recover the uniform fifteen-cells-per-terminal estimate. -/
public theorem word_length_le_fifteen_mul_revised
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {cursor : ScheduleCursor g input}
    (hinv : ScheduleInvariant cursor)
    (hindex : cursor.indexOwners.length + 1 ≤ 2 * input.length)
    (hframes : cursor.frameCount ≤ cursor.indexOwners.length)
    (hinput : 0 < input.length) :
    cursor.word.length ≤ 15 * input.length := by
  apply le_trans hinv.shape_bound
  have h := framed_cell_count_le_eight_mul_of_index_add_one_le_two_mul
    hinv.taskCount_le hindex hframes hinput
  omega

end ScheduleInvariant

/-! ## Accounting carried by every compressed-runner edge -/

/-- Does a physical work symbol carry one pending-task or emitted-terminal payload? -/
public def WorkSym.isTaskPayload {g : IndexedGrammar T} : WorkSym g → Bool
  | .terminal _ | .plain _ | .live _ => true
  | _ => false

/-- Does a physical work symbol close one currently open scheduler frame? -/
public def WorkSym.isClose {g : IndexedGrammar T} : WorkSym g → Bool
  | .close => true
  | _ => false

/-- Physical task/terminal payload count of one concrete configuration. -/
public def workTaskCount {g : IndexedGrammar T} (c : Config g) : ℕ :=
  c.work.word.countP WorkSym.isTaskPayload

/-- Physical compressed-index count of one concrete configuration. -/
public def workIndexCount {g : IndexedGrammar T} (c : Config g) : ℕ :=
  c.work.word.countP WorkSym.isIndex

/-- Physical open-frame count, measured by closing delimiters. -/
public def workFrameCount {g : IndexedGrammar T} (c : Config g) : ℕ :=
  c.work.word.countP WorkSym.isClose

/-! ### Exact count formulas for runner configurations -/

@[simp] public theorem workTaskCount_config_mk {g : IndexedGrammar T}
    (inputPos : ℕ) (left : List (WorkSym g)) (focus : WorkSym g)
    (right : List (WorkSym g)) :
    workTaskCount (⟨inputPos, ⟨left, focus, right⟩⟩ : Config g) =
      left.countP WorkSym.isTaskPayload +
        [focus].countP WorkSym.isTaskPayload +
        right.countP WorkSym.isTaskPayload := by
  cases focus <;>
    simp [workTaskCount, WorkCursor.word, WorkSym.isTaskPayload,
      List.countP_append, List.countP_cons, Nat.add_assoc, Nat.add_comm] <;> omega

@[simp] public theorem workIndexCount_config_mk {g : IndexedGrammar T}
    (inputPos : ℕ) (left : List (WorkSym g)) (focus : WorkSym g)
    (right : List (WorkSym g)) :
    workIndexCount (⟨inputPos, ⟨left, focus, right⟩⟩ : Config g) =
      left.countP WorkSym.isIndex + [focus].countP WorkSym.isIndex +
        right.countP WorkSym.isIndex := by
  cases focus <;>
    simp [workIndexCount, WorkCursor.word, WorkSym.isIndex,
      List.countP_append, List.countP_cons, Nat.add_assoc, Nat.add_comm] <;> omega

@[simp] public theorem workFrameCount_config_mk {g : IndexedGrammar T}
    (inputPos : ℕ) (left : List (WorkSym g)) (focus : WorkSym g)
    (right : List (WorkSym g)) :
    workFrameCount (⟨inputPos, ⟨left, focus, right⟩⟩ : Config g) =
      left.countP WorkSym.isClose + [focus].countP WorkSym.isClose +
        right.countP WorkSym.isClose := by
  cases focus <;>
    simp [workFrameCount, WorkCursor.word, WorkSym.isClose,
      List.countP_append, List.countP_cons, Nat.add_assoc, Nat.add_comm] <;> omega

/-- Marking the rightmost index changes no count computed from a mark-insensitive predicate. -/
public theorem countP_markProductivePrefix_of_index_mark_invariant
    {g : IndexedGrammar T} (predicate : WorkSym g → Bool)
    (hmark : ∀ (R : CFlag g) (d : IndexMark),
      predicate (.index R d.markUsed) = predicate (.index R d))
    (xs : List (WorkSym g)) :
    (markProductivePrefix xs).countP predicate = xs.countP predicate := by
  cases hrev : xs.reverse with
  | nil =>
      have hxs : xs = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst xs
      simp
  | cons z zs =>
      have hxs : xs = (z :: zs).reverse := by
        calc
          xs = xs.reverse.reverse := by simp
          _ = (z :: zs).reverse := congrArg List.reverse hrev
      rw [hxs]
      cases z <;> simp [markProductivePrefix, hmark]

@[simp] public theorem countP_isTaskPayload_markProductivePrefix
    {g : IndexedGrammar T} (xs : List (WorkSym g)) :
    (markProductivePrefix xs).countP WorkSym.isTaskPayload =
      xs.countP WorkSym.isTaskPayload := by
  exact countP_markProductivePrefix_of_index_mark_invariant
    WorkSym.isTaskPayload (by simp [WorkSym.isTaskPayload]) xs

@[simp] public theorem countP_isIndex_markProductivePrefix
    {g : IndexedGrammar T} (xs : List (WorkSym g)) :
    (markProductivePrefix xs).countP WorkSym.isIndex =
      xs.countP WorkSym.isIndex := by
  exact countP_markProductivePrefix_of_index_mark_invariant
    WorkSym.isIndex (by simp [WorkSym.isIndex]) xs

@[simp] public theorem countP_isClose_markProductivePrefix
    {g : IndexedGrammar T} (xs : List (WorkSym g)) :
    (markProductivePrefix xs).countP WorkSym.isClose =
      xs.countP WorkSym.isClose := by
  exact countP_markProductivePrefix_of_index_mark_invariant
    WorkSym.isClose (by simp [WorkSym.isClose]) xs

@[simp] public theorem markProductivePrefix_length
    {g : IndexedGrammar T} (xs : List (WorkSym g)) :
    (markProductivePrefix xs).length = xs.length := by
  cases hrev : xs.reverse with
  | nil =>
      have hxs : xs = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst xs
      rfl
  | cons z zs =>
      have hxs : xs = (z :: zs).reverse := by
        calc
          xs = xs.reverse.reverse := by simp
          _ = (z :: zs).reverse := congrArg List.reverse hrev
      rw [hxs]
      cases z <;> simp [markProductivePrefix]

@[simp] public theorem workTaskCount_wordConfig {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha word : List (WorkSym g)) :
    workTaskCount (wordConfig g inputPos alpha word) =
      alpha.countP WorkSym.isTaskPayload + word.countP WorkSym.isTaskPayload := by
  cases word with
  | nil => simp [wordConfig, WorkSym.isTaskPayload, List.countP_append]
  | cons z zs =>
      cases z <;> simp [wordConfig, WorkSym.isTaskPayload, List.countP_append,
        List.countP_cons, Nat.add_assoc, Nat.add_comm] <;> omega

@[simp] public theorem workIndexCount_wordConfig {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha word : List (WorkSym g)) :
    workIndexCount (wordConfig g inputPos alpha word) =
      alpha.countP WorkSym.isIndex + word.countP WorkSym.isIndex := by
  cases word with
  | nil => simp [wordConfig, WorkSym.isIndex, List.countP_append]
  | cons z zs =>
      cases z <;> simp [wordConfig, WorkSym.isIndex, List.countP_append,
        List.countP_cons, Nat.add_assoc, Nat.add_comm] <;> omega

@[simp] public theorem workFrameCount_wordConfig {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha word : List (WorkSym g)) :
    workFrameCount (wordConfig g inputPos alpha word) =
      alpha.countP WorkSym.isClose + word.countP WorkSym.isClose := by
  cases word with
  | nil => simp [wordConfig, WorkSym.isClose, List.countP_append]
  | cons z zs =>
      cases z <;> simp [wordConfig, WorkSym.isClose, List.countP_append,
        List.countP_cons, Nat.add_assoc, Nat.add_comm] <;> omega

@[simp] public theorem workTaskCount_active_plain {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) (A : g.nt) :
    workTaskCount (⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩ : Config g) =
      alpha.countP WorkSym.isTaskPayload + beta.countP WorkSym.isTaskPayload + 1 := by
  simp [List.countP_append, WorkSym.isTaskPayload]
  omega

@[simp] public theorem workIndexCount_active_plain {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) (A : g.nt) :
    workIndexCount (⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩ : Config g) =
      alpha.countP WorkSym.isIndex + beta.countP WorkSym.isIndex := by
  simp [List.countP_append, WorkSym.isIndex]

@[simp] public theorem workFrameCount_active_plain {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) (A : g.nt) :
    workFrameCount (⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩ : Config g) =
      alpha.countP WorkSym.isClose + beta.countP WorkSym.isClose := by
  simp [List.countP_append, WorkSym.isClose]

@[simp] public theorem workTaskCount_active_live {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) (A : g.nt) :
    workTaskCount (⟨inputPos, ⟨alpha ++ [.dollar], .live A, beta⟩⟩ : Config g) =
      alpha.countP WorkSym.isTaskPayload + beta.countP WorkSym.isTaskPayload + 1 := by
  simp [List.countP_append, WorkSym.isTaskPayload]
  omega

@[simp] public theorem workIndexCount_active_live {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) (A : g.nt) :
    workIndexCount (⟨inputPos, ⟨alpha ++ [.dollar], .live A, beta⟩⟩ : Config g) =
      alpha.countP WorkSym.isIndex + beta.countP WorkSym.isIndex := by
  simp [List.countP_append, WorkSym.isIndex]

@[simp] public theorem workFrameCount_active_live {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) (A : g.nt) :
    workFrameCount (⟨inputPos, ⟨alpha ++ [.dollar], .live A, beta⟩⟩ : Config g) =
      alpha.countP WorkSym.isClose + beta.countP WorkSym.isClose := by
  simp [List.countP_append, WorkSym.isClose]

@[simp] public theorem workTaskCount_popOpen_plain {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (R : CFlag g) (d : IndexMark) (B : g.nt) :
    workTaskCount
      (⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .plain B, .close :: gamma⟩⟩ : Config g) =
      alpha.countP WorkSym.isTaskPayload + beta.countP WorkSym.isTaskPayload +
        gamma.countP WorkSym.isTaskPayload + 1 := by
  simp [List.countP_append, WorkSym.isTaskPayload]
  omega

@[simp] public theorem workIndexCount_popOpen_plain {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (R : CFlag g) (d : IndexMark) (B : g.nt) :
    workIndexCount
      (⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .plain B, .close :: gamma⟩⟩ : Config g) =
      alpha.countP WorkSym.isIndex + beta.countP WorkSym.isIndex +
        gamma.countP WorkSym.isIndex + 1 := by
  simp [List.countP_append, WorkSym.isIndex]
  omega

@[simp] public theorem workFrameCount_popOpen_plain {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (R : CFlag g) (d : IndexMark) (B : g.nt) :
    workFrameCount
      (⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .plain B, .close :: gamma⟩⟩ : Config g) =
      alpha.countP WorkSym.isClose + beta.countP WorkSym.isClose +
        gamma.countP WorkSym.isClose + 1 := by
  simp [List.countP_append, WorkSym.isClose]
  omega

@[simp] public theorem workTaskCount_popOpen_live {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (R : CFlag g) (d : IndexMark) (B : g.nt) :
    workTaskCount
      (⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .live B, .close :: gamma⟩⟩ : Config g) =
      alpha.countP WorkSym.isTaskPayload + beta.countP WorkSym.isTaskPayload +
        gamma.countP WorkSym.isTaskPayload + 1 := by
  simp [List.countP_append, WorkSym.isTaskPayload]
  omega

@[simp] public theorem workIndexCount_popOpen_live {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (R : CFlag g) (d : IndexMark) (B : g.nt) :
    workIndexCount
      (⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .live B, .close :: gamma⟩⟩ : Config g) =
      alpha.countP WorkSym.isIndex + beta.countP WorkSym.isIndex +
        gamma.countP WorkSym.isIndex + 1 := by
  simp [List.countP_append, WorkSym.isIndex]
  omega

@[simp] public theorem workFrameCount_popOpen_live {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (R : CFlag g) (d : IndexMark) (B : g.nt) :
    workFrameCount
      (⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .live B, .close :: gamma⟩⟩ : Config g) =
      alpha.countP WorkSym.isClose + beta.countP WorkSym.isClose +
        gamma.countP WorkSym.isClose + 1 := by
  simp [List.countP_append, WorkSym.isClose]
  omega

/-- Returning a frame preserves task and index counts and removes exactly its closing marker. -/
public theorem workTaskCount_returnFrame_eq {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g)) (Z : WorkSym g) :
    workTaskCount
      (⟨inputPos, ⟨alpha ++ [.dollar, Z] ++ beta ++ [.dollar], .close, gamma⟩⟩ :
        Config g) =
    workTaskCount
      (⟨inputPos, ⟨alpha ++ [.dollar], Z, beta ++ gamma⟩⟩ : Config g) := by
  cases Z <;> simp [List.countP_append, WorkSym.isTaskPayload] <;> omega

public theorem workIndexCount_returnFrame_eq {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g)) (Z : WorkSym g) :
    workIndexCount
      (⟨inputPos, ⟨alpha ++ [.dollar, Z] ++ beta ++ [.dollar], .close, gamma⟩⟩ :
        Config g) =
    workIndexCount
      (⟨inputPos, ⟨alpha ++ [.dollar], Z, beta ++ gamma⟩⟩ : Config g) := by
  cases Z <;> simp [List.countP_append, WorkSym.isIndex] <;> omega

public theorem workFrameCount_returnFrame_eq_add_one {g : IndexedGrammar T}
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g)) (Z : WorkSym g) :
    workFrameCount
      (⟨inputPos, ⟨alpha ++ [.dollar, Z] ++ beta ++ [.dollar], .close, gamma⟩⟩ :
        Config g) =
    workFrameCount
      (⟨inputPos, ⟨alpha ++ [.dollar], Z, beta ++ gamma⟩⟩ : Config g) + 1 := by
  cases Z <;> simp [List.countP_append, WorkSym.isClose] <;> omega

/-- Accounting for one concrete compressed-runner configuration. Every count is computed from
the physical word itself; event-depth invariants prove the count bounds, while `shape_bound`
records the delimiter layout. -/
public structure CompressedAccounting (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) (c : Config g) : Prop where
  taskCount_le : workTaskCount c ≤ input.length
  indexCount_add_one_le : workIndexCount c + 1 ≤ 2 * input.length
  frameCount_le_indexCount : workFrameCount c ≤ workIndexCount c
  shape_bound : c.work.word.length ≤
    workTaskCount c + workIndexCount c + 2 * workFrameCount c + 2

namespace CompressedAccounting

/-- Package explicit bounds on the three physical count functions. -/
public theorem of_physical_bounds {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c : Config g}
    (htasks : workTaskCount c ≤ input.length)
    (hindices : workIndexCount c + 1 ≤ 2 * input.length)
    (hframes : workFrameCount c ≤ workIndexCount c)
    (hshape : c.work.word.length ≤
      workTaskCount c + workIndexCount c + 2 * workFrameCount c + 2) :
    CompressedAccounting g input c :=
  ⟨htasks, hindices, hframes, hshape⟩

/-- The revised arithmetic turns a local accounting witness into the physical work-tape bound. -/
public theorem within {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c : Config g} (accounting : CompressedAccounting g input c)
    (hinput : 0 < input.length) : c.Within (15 * input.length) := by
  apply le_trans accounting.shape_bound
  have h := framed_cell_count_le_eight_mul_of_index_add_one_le_two_mul
    accounting.taskCount_le accounting.indexCount_add_one_le
    accounting.frameCount_le_indexCount hinput
  omega

end CompressedAccounting

/-- The initial work word has one task payload and no indices or frames. -/
public theorem initialConfig_compressedAccounting
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (hinput : 0 < input.length) :
    CompressedAccounting g input (initialConfig g) := by
  apply CompressedAccounting.of_physical_bounds
  all_goals
    simp [workTaskCount, workIndexCount, workFrameCount, initialConfig,
      WorkCursor.word, WorkSym.isTaskPayload, WorkSym.isIndex, WorkSym.isClose]
  all_goals omega

/-- The final work word has no task, index, or frame payload. -/
public theorem finalConfig_compressedAccounting
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (hinput : 0 < input.length) :
    CompressedAccounting g input (finalConfig g input.length) := by
  apply CompressedAccounting.of_physical_bounds
  all_goals
    simp [workTaskCount, workIndexCount, workFrameCount, finalConfig,
      WorkCursor.word, WorkSym.isTaskPayload, WorkSym.isIndex, WorkSym.isClose]
  all_goals omega

/-- Composite reachability with an event-depth accounting witness on the initial configuration
and on both endpoints of every edge.  This shape composes at exact `Config` endpoints and prevents
a runner proof from silently passing through an unbounded intermediate configuration. -/
public def CompressedReaches (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) (c c' : Config g) : Prop :=
  CompressedAccounting g input c ∧
    Relation.ReflTransGen
      (fun x y => CompositeStep g input x y ∧
        CompressedAccounting g input x ∧ CompressedAccounting g input y) c c'

namespace CompressedReaches

public theorem refl {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c : Config g} (hc : CompressedAccounting g input c) :
    CompressedReaches g input c c :=
  ⟨hc, Relation.ReflTransGen.refl⟩

public theorem single {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c c' : Config g}
    (hc : CompressedAccounting g input c) (hstep : CompositeStep g input c c')
    (hc' : CompressedAccounting g input c') :
    CompressedReaches g input c c' :=
  ⟨hc, Relation.ReflTransGen.single ⟨hstep, hc, hc'⟩⟩

public theorem trans {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c₁ c₂ c₃ : Config g}
    (h₁₂ : CompressedReaches g input c₁ c₂)
    (h₂₃ : CompressedReaches g input c₂ c₃) :
    CompressedReaches g input c₁ c₃ :=
  ⟨h₁₂.1, h₁₂.2.trans h₂₃.2⟩

/-- The last configuration of an accounted trace retains an accounting witness, including in
the reflexive case. -/
public theorem target_accounting {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c c' : Config g} (run : CompressedReaches g input c c') :
    CompressedAccounting g input c' := by
  rcases Relation.ReflTransGen.cases_tail run.2 with heq | ⟨_, _, edge⟩
  · subst c'
    exact run.1
  · exact edge.2.2

/-- Forget accounting annotations and retain ordinary composite reachability. -/
public theorem toReflTransGen {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c c' : Config g} (run : CompressedReaches g input c c') :
    Relation.ReflTransGen (CompositeStep g input) c c' :=
  run.2.mono fun _ _ edge => edge.1

/-- Every accounted compressed trace is a bounded composite trace at the desired linear bound. -/
public theorem toBoundedReaches {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {c c' : Config g} (hinput : 0 < input.length)
    (run : CompressedReaches g input c c') :
    BoundedReaches g input (15 * input.length) c c' := by
  refine ⟨run.1.within hinput, ?_⟩
  exact run.2.mono fun _ _ edge =>
    ⟨edge.1, edge.2.1.within hinput, edge.2.2.within hinput⟩

end CompressedReaches

/-! ## Binary-free block continuations -/

private theorem neutral_of_push_neutral_pop_for_transport
    {g : IndexedGrammar T} {A B X Y : g.nt} {f : g.flag}
    (hpush : PushRule g A B f) (hneutral : Neutral g B X)
    (hpop : AugPop g f X Y) : Neutral g A Y := by
  have h₁ : g.Derives [ISym.indexed A []] [ISym.indexed B [f]] :=
    deri_of_tran (pushRule_transforms hpush [])
  have h₂ : g.Derives [ISym.indexed B [f]] [ISym.indexed X [f]] :=
    Neutral.lift_suffix hneutral [f]
  have h₃ : g.Derives [ISym.indexed X [f]] [ISym.indexed Y []] :=
    augPop_derives hpop []
  exact h₁.trans (h₂.trans h₃)

/-- Strengthening of `consumeRoute_popContinuation_noBinary`: after the whole compressed block
through occurrence `k` is popped, consumption by the residual parse at position `j` is exactly
consumption by the original parse at position `k + 1 + j`.  Thus an atomic multi-flag pop can
continue against lower compressed blocks without losing the live/plain boundary information. -/
public theorem consumeRoute_popContinuation_noBinary_with_consumption
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ}
    (route : NFParse.ConsumeRoute g p k) (hroute : route.NoBinary) :
    ∃ Y suffix, ∃ rest : NFParse g Y suffix w,
      suffix = stack.drop (k + 1) ∧
      PopPath g A (stack.take (k + 1)) Y ∧
      rest.nodeCount < p.nodeCount ∧
      (∀ j, rest.ConsumesAt j ↔ p.ConsumesAt (k + 1 + j)) ∧
      ∀ d, d ∈ rest.eventDepths ↔ k + 1 + d ∈ p.eventDepths := by
  induction route with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @popHere A B f stack w r hr hlhs hc hrhs rest =>
      refine ⟨B, stack, rest, by simp, ?_, ?_, ?_, ?_⟩
      · simpa using (PopPath.one (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩))
      · simp [NFParse.nodeCount]
      · intro j
        have hidx : 0 + 1 + j = j + 1 := by omega
        rw [hidx]
        exact (NFParse.consumesAt_pop_succ_iff hr hlhs hc hrhs rest j).symm
      · intro d
        constructor
        · intro hd
          exact Finset.mem_image.mpr ⟨d, hd, by omega⟩
        · intro hd
          rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
          have : e = d := by omega
          simpa [this] using he
  | @popTail A B f stack w r hr hlhs hc hrhs rest k route ih =>
      rcases ih hroute with
        ⟨Y, suffix, residual, hsuffix, path, hcount, hconsumes, hevents⟩
      refine ⟨Y, suffix, residual, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc] using hsuffix
      · simpa [Nat.add_assoc] using
          (PopPath.cons (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) path)
      · simp only [NFParse.nodeCount]
        omega
      · intro j
        rw [hconsumes j]
        have hidx : (k + 1) + 1 + j = (k + 1 + j) + 1 := by omega
        rw [hidx]
        exact (NFParse.consumesAt_pop_succ_iff hr hlhs hc hrhs rest
          (k + 1 + j)).symm
      · intro d
        constructor
        · intro hd
          have hrest := (hevents d).1 hd
          exact Finset.mem_image.mpr ⟨k + 1 + d, hrest, by omega⟩
        · intro hd
          rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
          have heq : e = k + 1 + d := by omega
          exact (hevents d).2 (by simpa [heq] using he)
  | @push A B f stack w r hr hlhs hc hrhs rest k route ih =>
      have hused : (NFParse.push hr hlhs hc hrhs rest).ConsumesAt k :=
        route.toConsumesAt
      have hk : k < stack.length :=
        (NFParse.push hr hlhs hc hrhs rest).consumesAt_lt_stack_length hused
      cases stack with
      | nil => simp at hk
      | cons f' stack =>
          rcases ih hroute with
            ⟨Y, suffix, residual, hsuffix, path, hcount, hconsumes, hevents⟩
          have path' : PopPath g B (f :: f' :: stack.take k) Y := by
            simpa [Nat.add_assoc] using path
          rcases path'.uncons with ⟨Z, hpop, restPath⟩
          have hcancel : Neutral g A Z :=
            neutral_of_push_neutral_pop_for_transport
              ⟨r, hr, hlhs, hc, hrhs⟩ (Neutral.refl g B) hpop
          refine ⟨Y, suffix, residual, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [Nat.add_assoc] using hsuffix
          · simpa using restPath.preNeutral hcancel
          · simp only [NFParse.nodeCount]
            omega
          · intro j
            rw [hconsumes j]
            have hidx : (k + 1) + 1 + j = (k + 1 + j) + 1 := by omega
            rw [hidx]
            exact (NFParse.consumesAt_push_iff hr hlhs hc hrhs rest
              (k + 1 + j)).symm
          · intro d
            constructor
            · intro hd
              have hrest := (hevents d).1 hd
              exact Finset.mem_image.mpr ⟨k + 2 + d, hrest, by
                simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩
            · intro hd
              rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
              have heq : e = k + 2 + d := by
                cases e with
                | zero => simp at hed; omega
                | succ e =>
                    simp only [Nat.pred_succ] at hed
                    omega
              exact (hevents d).2 (by simpa [heq, Nat.add_assoc] using he)

/-! ## Visible prefixes represented by compressed blocks -/

/-- A compressed visible-stack layout.  `flags` is partitioned by the nonempty lists in
`blocks`; every block is represented by one relation token which denotes exactly that concrete
flag list.  Gaps may contain ordinary control symbols (including `close`) but neither another
index nor `$`.  The third and fourth word indices differ only by marking every selected token
used. -/
public inductive BlockLayout (g : IndexedGrammar T) [Fintype g.nt] :
    List g.flag → List (List g.flag) →
      List (WorkSym g) → List (WorkSym g) → Prop where
  | nil (tail : List (WorkSym g)) : BlockLayout g [] [] tail tail
  | cons {block flags : List g.flag} {blocks : List (List g.flag)}
      {beta tail tail' : List (WorkSym g)} {R : CFlag g} {d : IndexMark}
      (block_ne : block ≠ []) (denotes : CFlag.Denotes g block R)
      (indexFree : IndexFree beta) (dollarFree : DollarFree beta)
      (later : flags ≠ [] → d.later = true)
      (rest : BlockLayout g flags blocks tail tail') :
      BlockLayout g (block ++ flags) (block :: blocks)
        (beta ++ WorkSym.index R d :: tail)
        (beta ++ WorkSym.index R d.markUsed :: tail')

namespace BlockLayout

@[simp] public theorem IndexMark.markUsed_idem (d : IndexMark) :
    d.markUsed.markUsed = d.markUsed := by
  cases d <;> rfl

@[simp] public theorem IndexMark.markUsed_later (d : IndexMark) :
    d.markUsed.later = d.later := by
  cases d <;> rfl

/-- The concrete visible prefix is exactly the flattening of its block partition. -/
public theorem flags_eq_flatten {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags blocks word used) :
    flags = blocks.flatten := by
  induction layout with
  | nil tail => rfl
  | cons block_ne denotes indexFree dollarFree later rest ih =>
      simp [ih]

/-- Every member of the partition is a nonempty concrete flag block. -/
public theorem blocks_nonempty {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags blocks word used) :
    ∀ block ∈ blocks, block ≠ [] := by
  induction layout with
  | nil tail => simp
  | @cons block flags blocks beta tail tail' R d hblock hden hindex hdollar
      hlater rest ih =>
      intro candidate hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hblock
      · exact ih candidate hmem

/-- Every relation stored by the layout retains a concrete denotation witness. -/
public theorem head_denotation {g : IndexedGrammar T} [Fintype g.nt]
    {block : List g.flag} {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags (block :: blocks) word used) :
    ∃ (beta tail tail' : List (WorkSym g)) (R : CFlag g) (d : IndexMark),
      CFlag.Denotes g block R ∧ block ≠ [] ∧
      IndexFree beta ∧ DollarFree beta ∧
      word = beta ++ WorkSym.index R d :: tail ∧
      used = beta ++ WorkSym.index R d.markUsed :: tail' := by
  cases layout with
  | cons hblock hden hindex hdollar hlater rest =>
      exact ⟨_, _, _, _, _, hden, hblock, hindex, hdollar, rfl, rfl⟩

/-- Re-selecting an all-used block layout is physically idempotent. -/
public theorem idempotent {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags blocks word used) :
    BlockLayout g flags blocks used used := by
  induction layout with
  | nil tail => exact .nil tail
  | @cons block flags blocks beta tail tail' R d hblock hden hindex hdollar
      hlater rest ih =>
      simpa using BlockLayout.cons (R := R) (d := d.markUsed)
        hblock hden hindex hdollar
        (fun hne => by simpa using hlater hne) ih

/-- Insert an ordinary control prefix into the gap before the first selected block. -/
public theorem prepend {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (pref : List (WorkSym g)) (hindex : IndexFree pref)
    (hdollar : DollarFree pref) (layout : BlockLayout g flags blocks word used) :
    BlockLayout g flags blocks (pref ++ word) (pref ++ used) := by
  induction layout with
  | nil tail => exact .nil (pref ++ tail)
  | @cons block flags blocks beta tail tail' R d hblock hden hbetaIndex
      hbetaDollar hlater rest _ih =>
      simpa [List.append_assoc] using BlockLayout.cons (R := R) (d := d)
        hblock hden (hindex.append hbetaIndex) (hdollar.append hbetaDollar)
        hlater rest

/-- A layout with no concrete flags has no blocks.  The nonempty-block invariant is essential:
without it `flatten blocks = []` would not force `blocks = []`. -/
public theorem blocks_eq_nil_of_flags_eq_nil {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags blocks word used) (hflags : flags = []) :
    blocks = [] := by
  cases blocks with
  | nil => rfl
  | cons block blocks =>
      exfalso
      have hblock := layout.blocks_nonempty block (by simp)
      have hflatten := layout.flags_eq_flatten
      rw [hflags] at hflatten
      simp [hblock] at hflatten

/-- Taking the concrete number of flags covered by the first `n` blocks ends exactly at their
physical block boundary. -/
public theorem take_flatten_take {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags blocks word used) (n : ℕ) :
    flags.take (blocks.take n).flatten.length = (blocks.take n).flatten := by
  have hpartition := congrArg List.flatten (List.take_append_drop n blocks)
  simp only [List.flatten_append] at hpartition
  rw [layout.flags_eq_flatten, ← hpartition]
  simp

/-- Restrict a layout to its first `n` whole blocks.  The remaining selected tokens become part
of the intermediate word.  Unlike a flagwise split, this operation can never cut through the
concrete denotation of one compressed relation. -/
public theorem splitTake {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (n : ℕ) (layout : BlockLayout g flags blocks word used) :
    ∃ middle,
      BlockLayout g (blocks.take n).flatten (blocks.take n) word middle ∧
        BlockLayout g flags blocks middle used := by
  induction layout generalizing n with
  | nil tail =>
      exact ⟨tail, by simpa using BlockLayout.nil (g := g) tail,
        BlockLayout.nil (g := g) tail⟩
  | @cons block flags blocks beta tail tail' R d hblock hden hindex hdollar
      hlater rest ih =>
      cases n with
      | zero => exact ⟨_, .nil _, BlockLayout.cons hblock hden hindex hdollar hlater rest⟩
      | succ n =>
          rcases ih n with ⟨middle, hprefix, hremain⟩
          let next := beta ++ WorkSym.index R d.markUsed :: middle
          refine ⟨next, ?_, ?_⟩
          · simpa using BlockLayout.cons (R := R) (d := d)
              hblock hden hindex hdollar (fun hne => hlater (by
                intro hflags
                have hblocks : blocks = [] := rest.blocks_eq_nil_of_flags_eq_nil hflags
                subst blocks
                simp at hne)) hprefix
          · simpa [next] using BlockLayout.cons (R := R) (d := d.markUsed)
              hblock hden hindex hdollar
              (fun hne => by simpa using hlater hne) hremain

/-- A concrete flag position is aligned to the compressed layout when it is the total length of
some whole-block prefix.  The explicit block count is the physical index-token budget at that
boundary. -/
public structure Boundary {g : IndexedGrammar T} [Fintype g.nt]
    (blocks : List (List g.flag)) (flagCount : ℕ) where
  blockCount : ℕ
  blockCount_le : blockCount ≤ blocks.length
  flagCount_eq : flagCount = (blocks.take blockCount).flatten.length

namespace Boundary

/-- Every prefix measured in whole blocks determines an aligned concrete boundary. -/
public def ofBlockCount {g : IndexedGrammar T} [Fintype g.nt]
    (blocks : List (List g.flag)) (blockCount : ℕ)
    (h : blockCount ≤ blocks.length) :
    Boundary blocks (blocks.take blockCount).flatten.length :=
  ⟨blockCount, h, rfl⟩

/-- The initial concrete position is always a block boundary. -/
public def start {g : IndexedGrammar T} [Fintype g.nt]
    (blocks : List (List g.flag)) : Boundary blocks 0 :=
  ⟨0, Nat.zero_le _, by simp⟩

/-- The end of the concrete visible prefix is a block boundary. -/
public def finish {g : IndexedGrammar T} [Fintype g.nt]
    (blocks : List (List g.flag)) : Boundary blocks blocks.flatten.length :=
  ⟨blocks.length, Nat.le_refl _, by simp⟩

/-- Prefixing one concrete block shifts every old boundary by that block's length. -/
public def cons {g : IndexedGrammar T} [Fintype g.nt]
    (block : List g.flag) {blocks : List (List g.flag)} {d : ℕ}
    (boundary : Boundary blocks d) :
    Boundary (block :: blocks) (block.length + d) where
  blockCount := boundary.blockCount + 1
  blockCount_le := by
    simpa only [List.length_cons, Nat.add_comm] using
      Nat.succ_le_succ boundary.blockCount_le
  flagCount_eq := by
    simp only [List.take_succ_cons, List.flatten_cons, List.length_append]
    exact congrArg (block.length + ·) boundary.flagCount_eq

/-- Removing a nonempty first block transports a shifted boundary to the tail partition. -/
public def tail_of_cons {g : IndexedGrammar T} [Fintype g.nt]
    {block : List g.flag} {blocks : List (List g.flag)} {d : ℕ}
    (hblock : block ≠ [])
    (boundary : Boundary (block :: blocks) (block.length + d)) :
    Boundary blocks d := by
  rcases boundary with ⟨blockCount, hle, heq⟩
  cases blockCount with
  | zero =>
      simp only [List.take_zero, List.flatten_nil, List.length_nil] at heq
      have hpos := List.length_pos_of_ne_nil hblock
      omega
  | succ blockCount =>
      refine ⟨blockCount, ?_, ?_⟩
      · simp only [List.length_cons] at hle
        omega
      · simp only [List.take_succ_cons, List.flatten_cons, List.length_append] at heq
        omega

/-- Every positive boundary of a partition beginning with a nonempty block lies at or below
the end of that first block.  This is the arithmetic fact used to show that a first block is
event-free once depth zero is not productive. -/
public theorem first_length_le_of_pos {g : IndexedGrammar T} [Fintype g.nt]
    {block : List g.flag} {blocks : List (List g.flag)} {d : ℕ}
    (hblock : block ≠ []) (boundary : Boundary (block :: blocks) d)
    (hd : 0 < d) : block.length ≤ d := by
  rcases boundary with ⟨blockCount, hle, heq⟩
  cases blockCount with
  | zero =>
      simp only [List.take_zero, List.flatten_nil, List.length_nil] at heq
      omega
  | succ blockCount =>
      simp only [List.take_succ_cons, List.flatten_cons, List.length_append] at heq
      omega

/-- A fresh singleton top block shifts every old boundary by exactly one flag. -/
public def singletonCons {g : IndexedGrammar T} [Fintype g.nt]
    (f : g.flag) {blocks : List (List g.flag)} {d : ℕ}
    (boundary : Boundary blocks d) : Boundary ([f] :: blocks) (d + 1) := by
  simpa [Nat.add_comm] using boundary.cons [f]

/-- Extending the first block by one flag shifts every positive boundary by one while keeping
the same physical block count. -/
public def extendHead_of_pos {g : IndexedGrammar T} [Fintype g.nt]
    (f : g.flag) {block : List g.flag} {blocks : List (List g.flag)} {d : ℕ}
    (hd : 0 < d) (boundary : Boundary (block :: blocks) d) :
    Boundary ((f :: block) :: blocks) (d + 1) := by
  rcases boundary with ⟨blockCount, hle, heq⟩
  cases blockCount with
  | zero =>
      simp only [List.take_zero, List.flatten_nil, List.length_nil] at heq
      omega
  | succ blockCount =>
      refine ⟨blockCount + 1, ?_, ?_⟩
      · simpa only [List.length_cons] using hle
      · simp only [List.take_succ_cons, List.flatten_cons, List.length_append,
          List.length_cons]
        simp only [List.take_succ_cons, List.flatten_cons, List.length_append] at heq
        omega

end Boundary

/-- Split at an explicitly aligned concrete flag position.  The boundary witness makes it
impossible for callers to request a split inside the denotation of a compressed block. -/
public theorem splitAtBoundary {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)} {flagCount : ℕ}
    (layout : BlockLayout g flags blocks word used)
    (boundary : Boundary blocks flagCount) :
    ∃ middle,
      BlockLayout g (flags.take flagCount) (blocks.take boundary.blockCount) word middle ∧
        BlockLayout g flags blocks middle used := by
  rcases layout.splitTake boundary.blockCount with ⟨middle, hprefix, hremain⟩
  refine ⟨middle, ?_, hremain⟩
  have htake : flags.take flagCount = (blocks.take boundary.blockCount).flatten := by
    calc
      flags.take flagCount =
          flags.take (blocks.take boundary.blockCount).flatten.length := by
            exact congrArg (List.take · flags) boundary.flagCount_eq
      _ = (blocks.take boundary.blockCount).flatten :=
        layout.take_flatten_take boundary.blockCount
  simpa only [htake] using hprefix

/-- The selected physical part of a block layout consists of parallel prefixes followed by one
common unselected tail. -/
public theorem exists_selectedPrefixes {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags blocks word used) :
    ∃ selected selectedUsed tail,
      word = selected ++ tail ∧ used = selectedUsed ++ tail ∧
      selected.countP WorkSym.isIndex = blocks.length ∧
      selectedUsed.countP WorkSym.isIndex = blocks.length := by
  induction layout with
  | nil tail => exact ⟨[], [], tail, by simp⟩
  | @cons block flags blocks beta tail tail' R d hblock hden hindex hdollar
      hlater rest ih =>
      rcases ih with ⟨selected, selectedUsed, commonTail,
        hword, hused, hcount, hcountUsed⟩
      refine ⟨beta ++ WorkSym.index R d :: selected,
        beta ++ WorkSym.index R d.markUsed :: selectedUsed, commonTail, ?_, ?_, ?_, ?_⟩
      · rw [hword]
        simp [List.append_assoc]
      · rw [hused]
        simp [List.append_assoc]
      · have hbeta : beta.countP WorkSym.isIndex = 0 := by
          apply List.countP_eq_zero.mpr
          intro z hz
          cases z <;> simp [WorkSym.isIndex]
          rename_i relation mark
          exact hindex relation mark hz
        simp [List.countP_append, WorkSym.isIndex, hbeta, hcount]
      · have hbeta : beta.countP WorkSym.isIndex = 0 := by
          apply List.countP_eq_zero.mpr
          intro z hz
          cases z <;> simp [WorkSym.isIndex]
          rename_i relation mark
          exact hindex relation mark hz
        simp [List.countP_append, WorkSym.isIndex, hbeta, hcountUsed]

/-- Consequently the physical selected-index count is exactly the number of concrete blocks. -/
public theorem exists_selectedPrefix_indexCount_eq_blockCount
    {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {blocks : List (List g.flag)}
    {word used : List (WorkSym g)}
    (layout : BlockLayout g flags blocks word used) :
    ∃ selected tail,
      word = selected ++ tail ∧
      selected.countP WorkSym.isIndex = blocks.length := by
  rcases layout.exists_selectedPrefixes with
    ⟨selected, _selectedUsed, tail, hword, _hused, hcount, _hcountUsed⟩
  exact ⟨selected, tail, hword, hcount⟩

end BlockLayout
end Aho
end IndexedGrammar

namespace IndexedGrammar
namespace NFParse

/-! ## Canonical stack-depth event cuts -/

/-- Every parse has at least the cut contributed by one terminal leaf. -/
public theorem eventDepths_nonempty
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : p.eventDepths.Nonempty := by
  induction p with
  | binary hr hlhs hc hrhs left right ihleft ihright =>
      exact ⟨0, by simp [eventDepths]⟩
  | pop hr hlhs hc hrhs rest ih =>
      rcases ih with ⟨d, hd⟩
      exact ⟨d + 1, Finset.mem_image.mpr ⟨d, hd, by omega⟩⟩
  | push hr hlhs hc hrhs rest ih =>
      rcases ih with ⟨d, hd⟩
      exact ⟨d.pred, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
  | terminal hr hlhs hc hrhs =>
      exact ⟨0, by simp [eventDepths]⟩

/-- Root-stack position `k` is consumed exactly when some canonical event cut lies strictly
below it.  Hence `eventDepths` is a finite cut profile for every consumption decision made by
the bounded scheduler. -/
public theorem consumesAt_iff_exists_mem_eventDepths_lt
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (k : ℕ) :
    p.ConsumesAt k ↔ ∃ d ∈ p.eventDepths, k < d := by
  induction p generalizing k with
  | binary hr hlhs hc hrhs left right ihleft ihright =>
      simp only [ConsumesAt, eventDepths, Finset.mem_insert, Finset.mem_union]
      rw [ihleft, ihright]
      constructor
      · rintro (⟨d, hd, hkd⟩ | ⟨d, hd, hkd⟩)
        · exact ⟨d, Or.inr (Or.inl hd), hkd⟩
        · exact ⟨d, Or.inr (Or.inr hd), hkd⟩
      · rintro ⟨d, hd, hkd⟩
        rcases hd with rfl | hd
        · omega
        · rcases hd with hd | hd
          · exact Or.inl ⟨d, hd, hkd⟩
          · exact Or.inr ⟨d, hd, hkd⟩
  | pop hr hlhs hc hrhs rest ih =>
      cases k with
      | zero =>
          constructor
          · intro _
            rcases rest.eventDepths_nonempty with ⟨d, hd⟩
            exact ⟨d + 1, Finset.mem_image.mpr ⟨d, hd, by omega⟩, by omega⟩
          · intro _
            exact Or.inl rfl
      | succ k =>
          rw [consumesAt_pop_succ_iff, ih]
          constructor
          · rintro ⟨d, hd, hkd⟩
            exact ⟨d + 1, Finset.mem_image.mpr ⟨d, hd, by omega⟩, by omega⟩
          · rintro ⟨d, hd, hkd⟩
            rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
            exact ⟨e, he, by omega⟩
  | push hr hlhs hc hrhs rest ih =>
      rw [consumesAt_push_iff, ih]
      constructor
      · rintro ⟨d, hd, hkd⟩
        have hkpred : k < d.pred := by
          cases d with
          | zero => simp at hkd
          | succ d =>
              simp only [Nat.pred_succ]
              omega
        exact ⟨d.pred, Finset.mem_image.mpr ⟨d, hd, rfl⟩, hkpred⟩
      · rintro ⟨d, hd, hkd⟩
        rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
        have hksucc : k + 1 < e := by
          cases e with
          | zero => simp at hkd
          | succ e =>
              simp only [Nat.pred_succ] at hkd
              omega
        exact ⟨e, he, hksucc⟩
  | terminal hr hlhs hc hrhs =>
      simp [ConsumesAt, eventDepths]

/-- Every canonical event depth denotes an actual cut of the current root stack. -/
public theorem eventDepths_le_stack_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    ∀ d ∈ p.eventDepths, d ≤ stack.length := by
  induction p with
  | binary hr hlhs hc hrhs left right ihleft ihright =>
      intro d hd
      simp only [eventDepths, Finset.mem_insert, Finset.mem_union] at hd
      rcases hd with rfl | hd
      · exact Nat.zero_le _
      · rcases hd with hd | hd
        · exact ihleft d hd
        · exact ihright d hd
  | pop hr hlhs hc hrhs rest ih =>
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
      have := ih e he
      simp only [List.length_cons]
      omega
  | push hr hlhs hc hrhs rest ih =>
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
      have := ih e he
      simp only [List.length_cons] at this
      cases e with
      | zero => exact Nat.zero_le _
      | succ e =>
          simp only [Nat.pred_succ]
          omega
  | terminal hr hlhs hc hrhs =>
      intro d hd
      simp [eventDepths] at hd
      omega

/-- The finite cut profile uses no more entries than all productive parse events. -/
public theorem eventDepths_card_le_productiveCount
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventDepths.card ≤ p.productiveCount := by
  induction p with
  | binary hr hlhs hc hrhs left right ihleft ihright =>
      simp only [productiveCount] at ihleft ihright
      calc
        (insert 0 (left.eventDepths ∪ right.eventDepths)).card ≤
            (left.eventDepths ∪ right.eventDepths).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ left.eventDepths.card + right.eventDepths.card + 1 :=
          Nat.add_le_add_right (Finset.card_union_le _ _) 1
        _ ≤ (NFParse.binary hr hlhs hc hrhs left right).productiveCount := by
          simp only [productiveCount, binaryCount, terminalCount]
          omega
  | pop hr hlhs hc hrhs rest ih =>
      exact le_trans Finset.card_image_le (by
        simpa [productiveCount, binaryCount, terminalCount] using ih)
  | push hr hlhs hc hrhs rest ih =>
      exact le_trans Finset.card_image_le (by
        simpa [productiveCount, binaryCount, terminalCount] using ih)
  | terminal hr hlhs hc hrhs =>
      simp [eventDepths, productiveCount, binaryCount, terminalCount]

/-- There are at most `2|w|-1` distinct event cuts.  This is the global bound needed when the
scheduler allocates at most one compressed index token per canonical cut. -/
public theorem eventDepths_card_le_twice_yield_length_sub_one
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventDepths.card ≤ 2 * w.length - 1 := by
  have hcard := p.eventDepths_card_le_productiveCount
  have ht := p.terminalCount_eq_yield_length
  have hb := p.binaryCount_add_one_eq_terminalCount
  simp only [productiveCount] at hcard
  omega

/-- Productive nodes are exactly the binary nodes plus terminal leaves, hence `2|w|-1`. -/
public theorem productiveCount_eq_twice_yield_length_sub_one
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.productiveCount = 2 * w.length - 1 := by
  have ht := p.terminalCount_eq_yield_length
  have hb := p.binaryCount_add_one_eq_terminalCount
  simp only [productiveCount]
  omega

/-! ## Coherent productive-event owners -/

/-- Canonical inverse used when a push maps event depths through `Nat.pred`.  At depth zero we
prefer the old zero event when it exists; otherwise the unique relevant preimage is one. -/
public def pushEventPreimage (events : Finset ℕ) (d : ℕ) : ℕ :=
  if d = 0 ∧ 0 ∈ events then 0 else d + 1

public theorem pushEventPreimage_mem {events : Finset ℕ} {d : ℕ}
    (hd : d ∈ events.image Nat.pred) : pushEventPreimage events d ∈ events := by
  rcases Finset.mem_image.mp hd with ⟨e, he, hpred⟩
  by_cases hd0 : d = 0
  · by_cases hzero : 0 ∈ events
    · simpa [pushEventPreimage, hd0, hzero] using hzero
    · have heq : e = 1 := by
        cases e with
        | zero => exact False.elim (hzero he)
        | succ e =>
            simp only [Nat.pred_succ] at hpred
            omega
      simpa [pushEventPreimage, hd0, hzero, heq] using he
  · have heq : e = d + 1 := by
      cases e with
      | zero => exact False.elim (hd0 hpred.symm)
      | succ e =>
          simp only [Nat.pred_succ] at hpred
          omega
    simpa [pushEventPreimage, hd0, heq] using he

@[simp] public theorem pred_pushEventPreimage {events : Finset ℕ} {d : ℕ}
    (hd : d ∈ events.image Nat.pred) :
    (pushEventPreimage events d).pred = d := by
  by_cases hd0 : d = 0
  · subst d
    by_cases hzero : 0 ∈ events <;> simp [pushEventPreimage, hzero]
  · simp [pushEventPreimage, hd0]

/-- The canonical push inverse is injective on actual image depths. -/
public theorem pushEventPreimage_injective_on {events : Finset ℕ}
    {d e : ℕ} (hd : d ∈ events.image Nat.pred)
    (he : e ∈ events.image Nat.pred)
    (h : pushEventPreimage events d = pushEventPreimage events e) : d = e := by
  calc
    d = (pushEventPreimage events d).pred := (pred_pushEventPreimage hd).symm
    _ = (pushEventPreimage events e).pred := congrArg Nat.pred h
    _ = e := pred_pushEventPreimage he

/-- The natural-number code underlying a coherent productive-node ID. Binary roots own zero;
left and right child codes occupy disjoint successive ranges. Unary nodes transport codes. -/
public def eventOwnerNat
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (d : ℕ) : ℕ :=
  match p with
  | .terminal _ _ _ _ => 0
  | .pop _ _ _ _ rest => rest.eventOwnerNat (d - 1)
  | .push _ _ _ _ rest =>
      rest.eventOwnerNat (pushEventPreimage rest.eventDepths d)
  | .binary _ _ _ _ left right =>
      if d = 0 then 0
      else if d ∈ left.eventDepths then left.eventOwnerNat d + 1
      else left.productiveCount + right.eventOwnerNat d + 1

/-- Every actual event code fits inside the productive-node count. -/
public theorem eventOwnerNat_lt_productiveCount
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) {d : ℕ} (hd : d ∈ p.eventDepths) :
    p.eventOwnerNat d < p.productiveCount := by
  induction p generalizing d with
  | terminal hr hlhs hc hrhs =>
      simp [eventOwnerNat, productiveCount, binaryCount, terminalCount]
  | pop hr hlhs hc hrhs rest ih =>
      have hd' : d - 1 ∈ rest.eventDepths := by
        rcases Finset.mem_image.mp hd with ⟨x, hx, hxd⟩
        have : d - 1 = x := by omega
        simpa [this] using hx
      simpa [eventOwnerNat, productiveCount, binaryCount, terminalCount] using ih hd'
  | push hr hlhs hc hrhs rest ih =>
      have hd' : pushEventPreimage rest.eventDepths d ∈ rest.eventDepths :=
        pushEventPreimage_mem hd
      simpa [eventOwnerNat, productiveCount, binaryCount, terminalCount] using ih hd'
  | binary hr hlhs hc hrhs left right ihleft ihright =>
      by_cases hd0 : d = 0
      · simp [eventOwnerNat, hd0, productiveCount, binaryCount, terminalCount]
        have := left.binaryCount_add_one_eq_terminalCount
        omega
      · by_cases hleft : d ∈ left.eventDepths
        · have hi := ihleft hleft
          simp only [eventOwnerNat]
          rw [if_neg hd0, if_pos hleft]
          simp only [productiveCount, binaryCount, terminalCount] at hi ⊢
          omega
        · have hright : d ∈ right.eventDepths := by
            simp only [eventDepths, Finset.mem_insert, Finset.mem_union] at hd
            rcases hd with hd | hd
            · exact False.elim (hd0 hd)
            · exact hd.resolve_left hleft
          have hi := ihright hright
          simp only [eventOwnerNat]
          rw [if_neg hd0, if_neg hleft]
          simp only [productiveCount, binaryCount, terminalCount] at hi ⊢
          omega

/-- A coherent productive-node ID for a canonical event depth. -/
public def eventOwner
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (d : ℕ) (hd : d ∈ p.eventDepths) :
    Fin p.productiveCount :=
  ⟨p.eventOwnerNat d, p.eventOwnerNat_lt_productiveCount hd⟩

@[simp] public theorem eventOwner_val
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (d : ℕ) (hd : d ∈ p.eventDepths) :
    (p.eventOwner d hd).val = p.eventOwnerNat d := rfl

/-- The natural-number event codes are injective on actual event depths. -/
public theorem eventOwnerNat_injective
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    ∀ {d e : ℕ} (hd : d ∈ p.eventDepths) (he : e ∈ p.eventDepths),
      p.eventOwnerNat d = p.eventOwnerNat e → d = e := by
  induction p with
  | terminal hr hlhs hc hrhs =>
      intro d e hd he _
      simp [eventDepths] at hd he
      omega
  | pop hr hlhs hc hrhs rest ih =>
      intro d e hd he howner
      have hdpos : 0 < d := by
        rcases Finset.mem_image.mp hd with ⟨x, _hx, hxd⟩
        omega
      have hepos : 0 < e := by
        rcases Finset.mem_image.mp he with ⟨x, _hx, hxe⟩
        omega
      have hd' : d - 1 ∈ rest.eventDepths := by
        rcases Finset.mem_image.mp hd with ⟨x, hx, hxd⟩
        have : d - 1 = x := by omega
        simpa [this] using hx
      have he' : e - 1 ∈ rest.eventDepths := by
        rcases Finset.mem_image.mp he with ⟨x, hx, hxe⟩
        have : e - 1 = x := by omega
        simpa [this] using hx
      simp only [eventOwnerNat] at howner
      have := ih hd' he' howner
      omega
  | push hr hlhs hc hrhs rest ih =>
      intro d e hd he howner
      let d' := pushEventPreimage rest.eventDepths d
      let e' := pushEventPreimage rest.eventDepths e
      have hd' : d' ∈ rest.eventDepths := pushEventPreimage_mem hd
      have he' : e' ∈ rest.eventDepths := pushEventPreimage_mem he
      simp only [eventOwnerNat] at howner
      exact pushEventPreimage_injective_on hd he (ih hd' he' howner)
  | binary hr hlhs hc hrhs left right ihleft ihright =>
      intro d e hd he howner
      by_cases hd0 : d = 0
      · subst d
        by_cases he0 : e = 0
        · exact he0.symm
        · by_cases hel : e ∈ left.eventDepths
          · simp [eventOwnerNat, he0, hel] at howner
          · simp [eventOwnerNat, he0, hel] at howner
      · by_cases he0 : e = 0
        · subst e
          by_cases hdl : d ∈ left.eventDepths
          · simp [eventOwnerNat, hd0, hdl] at howner
          · simp [eventOwnerNat, hd0, hdl] at howner
        · by_cases hdl : d ∈ left.eventDepths
          · by_cases hel : e ∈ left.eventDepths
            · simp only [eventOwnerNat, if_neg hd0, if_neg he0,
                if_pos hdl, if_pos hel] at howner
              exact ihleft hdl hel (by omega)
            · simp only [eventOwnerNat, if_neg hd0, if_neg he0,
                if_pos hdl, if_neg hel] at howner
              have hdOwner := left.eventOwnerNat_lt_productiveCount hdl
              omega
          · by_cases hel : e ∈ left.eventDepths
            · simp only [eventOwnerNat, if_neg hd0, if_neg he0,
                if_neg hdl, if_pos hel] at howner
              have heOwner := left.eventOwnerNat_lt_productiveCount hel
              omega
            · have hdr : d ∈ right.eventDepths := by
                simp only [eventDepths, Finset.mem_insert, Finset.mem_union] at hd
                rcases hd with hd | hd
                · exact False.elim (hd0 hd)
                · exact hd.resolve_left hdl
              have her : e ∈ right.eventDepths := by
                simp only [eventDepths, Finset.mem_insert, Finset.mem_union] at he
                rcases he with he | he
                · exact False.elim (he0 he)
                · exact he.resolve_left hel
              simp only [eventOwnerNat, if_neg hd0, if_neg he0,
                if_neg hdl, if_neg hel] at howner
              exact ihright hdr her (by omega)

/-- Coherent finite event IDs are injective in the represented stack depth. -/
public theorem eventOwner_injective
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    ∀ {d e : ℕ} (hd : d ∈ p.eventDepths) (he : e ∈ p.eventDepths),
      p.eventOwner d hd = p.eventOwner e he → d = e := by
  intro d e hd he howner
  apply p.eventOwnerNat_injective hd he
  exact congrArg Fin.val howner

@[simp] public theorem eventOwnerNat_pop_succ
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag} {stack : List g.flag}
    {w : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (rest : NFParse g B stack w) (d : ℕ) :
    (NFParse.pop hr hlhs hc hrhs rest).eventOwnerNat (d + 1) =
      rest.eventOwnerNat d := by
  simp [eventOwnerNat]

@[simp] public theorem eventOwnerNat_push
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag} {stack : List g.flag}
    {w : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: stack) w) (d : ℕ) :
    (NFParse.push hr hlhs hc hrhs rest).eventOwnerNat d =
      rest.eventOwnerNat (pushEventPreimage rest.eventDepths d) := by
  rfl

@[simp] public theorem eventOwnerNat_binary_zero
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (left : NFParse g B stack u) (right : NFParse g C stack v) :
    (NFParse.binary hr hlhs hc hrhs left right).eventOwnerNat 0 = 0 := by
  simp [eventOwnerNat]

public theorem eventOwnerNat_binary_left
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (left : NFParse g B stack u) (right : NFParse g C stack v)
    {d : ℕ} (hd0 : d ≠ 0) (hd : d ∈ left.eventDepths) :
    (NFParse.binary hr hlhs hc hrhs left right).eventOwnerNat d =
      left.eventOwnerNat d + 1 := by
  simp [eventOwnerNat, hd0, hd]

public theorem eventOwnerNat_binary_right
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (left : NFParse g B stack u) (right : NFParse g C stack v)
    {d : ℕ} (hd0 : d ≠ 0) (hd : d ∉ left.eventDepths) :
    (NFParse.binary hr hlhs hc hrhs left right).eventOwnerNat d =
      left.productiveCount + right.eventOwnerNat d + 1 := by
  simp [eventOwnerNat, hd0, hd]

/-! ## Canonical physical blocks at productive-event cuts -/

/-- Successive widths represented by an increasing list of absolute cut positions. -/
public def successiveWidths (previous : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds => (d - previous) :: successiveWidths d ds

@[simp] public theorem successiveWidths_length (previous : ℕ) (cuts : List ℕ) :
    (successiveWidths previous cuts).length = cuts.length := by
  induction cuts generalizing previous with
  | nil => rfl
  | cons d ds ih => simp [successiveWidths, ih]

/-- Taking the first `n` widths is the same as first taking the corresponding cuts. -/
public theorem successiveWidths_take (previous : ℕ) (cuts : List ℕ) (n : ℕ) :
    (successiveWidths previous cuts).take n =
      successiveWidths previous (cuts.take n) := by
  induction cuts generalizing previous n with
  | nil => simp [successiveWidths]
  | cons d ds ih =>
      cases n with
      | zero => simp [successiveWidths]
      | succ n => simp [successiveWidths, ih]

/-- The widths through cut `i` telescope back to that absolute cut. -/
public theorem successiveWidths_sum_take_add_previous_eq_getElem
    {previous : ℕ} {cuts : List ℕ}
    (hsorted : (previous :: cuts).Pairwise (fun a b => a < b))
    (i : ℕ) (hi : i < cuts.length) :
    ((successiveWidths previous cuts).take (i + 1)).sum + previous = cuts[i] := by
  induction cuts generalizing previous i with
  | nil => simp at hi
  | cons d ds ih =>
      have hparts := List.pairwise_cons.mp hsorted
      have hprevious : previous < d := hparts.1 d (by simp)
      cases i with
      | zero =>
          simp [successiveWidths]
          omega
      | succ i =>
          have hi' : i < ds.length := by simpa using hi
          have htail := ih hparts.2 i hi'
          simp only [successiveWidths, List.take_succ_cons, List.sum_cons,
            List.getElem_cons_succ]
          omega

/-- Every width between consecutive strictly increasing cuts is positive. -/
public theorem successiveWidths_pos
    {previous : ℕ} {cuts : List ℕ}
    (hsorted : (previous :: cuts).Pairwise (fun a b => a < b)) :
    ∀ width ∈ successiveWidths previous cuts, 0 < width := by
  induction cuts generalizing previous with
  | nil => simp [successiveWidths]
  | cons d ds ih =>
      have hparts := List.pairwise_cons.mp hsorted
      have hprevious : previous < d := hparts.1 d (by simp)
      intro width hwidth
      simp only [successiveWidths, List.mem_cons] at hwidth
      rcases hwidth with rfl | hwidth
      · omega
      · exact ih hparts.2 width hwidth

/-- Telescoping widths stay inside any common upper bound for the absolute cuts. -/
public theorem successiveWidths_sum_add_previous_le
    {previous limit : ℕ} {cuts : List ℕ}
    (hprevious : previous ≤ limit)
    (hsorted : (previous :: cuts).Pairwise (fun a b => a < b))
    (hcuts : ∀ d ∈ cuts, d ≤ limit) :
    (successiveWidths previous cuts).sum + previous ≤ limit := by
  induction cuts generalizing previous with
  | nil => simpa [successiveWidths] using hprevious
  | cons d ds ih =>
      have hparts := List.pairwise_cons.mp hsorted
      have hprevious' : previous < d := hparts.1 d (by simp)
      have hd : d ≤ limit := hcuts d (by simp)
      have htail := ih hd hparts.2 (fun e he => hcuts e (by simp [he]))
      simp only [successiveWidths, List.sum_cons]
      omega

/-- Positive productive-event depths, in their unique increasing order. -/
public def eventCuts
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : List ℕ :=
  (p.eventDepths.erase 0).sort (fun a b => a ≤ b)

@[simp] public theorem eventCuts_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventCuts.length = (p.eventDepths.erase 0).card := by
  simp [eventCuts]

public theorem mem_eventCuts_iff
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (d : ℕ) :
    d ∈ p.eventCuts ↔ d ∈ p.eventDepths ∧ d ≠ 0 := by
  simp [eventCuts, and_comm]

/-- Canonical cuts are strictly increasing. -/
public theorem eventCuts_sortedLT
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventCuts.Pairwise (fun a b => a < b) := by
  exact (Finset.sortedLT_sort (p.eventDepths.erase 0)).pairwise

/-- Adding the implicit initial boundary preserves strict increase. -/
public theorem zero_cons_eventCuts_sortedLT
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    (0 :: p.eventCuts).Pairwise (fun a b => a < b) := by
  rw [List.pairwise_cons]
  exact ⟨fun d hd => Nat.pos_of_ne_zero ((p.mem_eventCuts_iff d).1 hd).2,
    p.eventCuts_sortedLT⟩

/-- Every cut is an actual position in the root stack. -/
public theorem eventCuts_le_stack_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    ∀ d ∈ p.eventCuts, d ≤ stack.length := by
  intro d hd
  exact p.eventDepths_le_stack_length d ((p.mem_eventCuts_iff d).1 hd).1

/-- In particular, the last canonical cut lies inside the root stack. -/
public theorem eventCuts_getLast_le_stack_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (hne : p.eventCuts ≠ []) :
    p.eventCuts.getLast hne ≤ stack.length :=
  p.eventCuts_le_stack_length _ (List.getLast_mem hne)

/-- Concrete lengths of the successive canonical event blocks. -/
public def eventWidths
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : List ℕ :=
  successiveWidths 0 p.eventCuts

@[simp] public theorem eventWidths_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventWidths.length = p.eventCuts.length := by
  simp [eventWidths]

public theorem eventWidths_pos
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    ∀ width ∈ p.eventWidths, 0 < width := by
  exact successiveWidths_pos p.zero_cons_eventCuts_sortedLT

/-- The total visible prefix selected by all event cuts fits in the root stack. -/
public theorem eventWidths_sum_le_stack_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventWidths.sum ≤ stack.length := by
  simpa [eventWidths] using successiveWidths_sum_add_previous_le
    (previous := 0) (limit := stack.length) (cuts := p.eventCuts)
    (Nat.zero_le _) p.zero_cons_eventCuts_sortedLT p.eventCuts_le_stack_length

/-- Splitting a list by widths whose total fits returns exactly the corresponding prefix. -/
public theorem flatten_splitLengths_eq_take {X : Type}
    (xs : List X) (widths : List ℕ) (hfit : widths.sum ≤ xs.length) :
    (widths.splitLengths xs).flatten = xs.take widths.sum := by
  induction widths generalizing xs with
  | nil => simp
  | cons width widths ih =>
      simp only [List.sum_cons] at hfit
      have htail : widths.sum ≤ (xs.drop width).length := by
        simp only [List.length_drop]
        omega
      simp only [List.splitLengths_cons, List.flatten_cons, List.sum_cons]
      rw [ih (xs := xs.drop width) htail]
      exact List.take_add.symm

/-- Canonical nonempty concrete flag blocks cut from the consumed root-stack prefix. -/
public def eventBlocks
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : List (List g.flag) :=
  p.eventWidths.splitLengths stack

@[simp] public theorem eventBlocks_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventBlocks.length = p.eventCuts.length := by
  simp [eventBlocks]

/-- Each physical block has exactly its positive successive width. -/
public theorem eventBlocks_map_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventBlocks.map List.length = p.eventWidths := by
  exact List.map_splitLengths_length stack p.eventWidths
    p.eventWidths_sum_le_stack_length

/-- No canonical physical block is empty. -/
public theorem eventBlocks_nonempty
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    ∀ block ∈ p.eventBlocks, block ≠ [] := by
  intro block hblock hnil
  have hzero : 0 ∈ p.eventWidths := by
    rw [← p.eventBlocks_map_length]
    exact List.mem_map.mpr ⟨block, hblock, by simp [hnil]⟩
  exact (Nat.ne_of_gt (p.eventWidths_pos 0 hzero)) rfl

/-- The generated blocks flatten to the concrete stack prefix ending at the final event cut. -/
public theorem eventBlocks_flatten
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventBlocks.flatten = stack.take p.eventWidths.sum := by
  exact flatten_splitLengths_eq_take stack p.eventWidths
    p.eventWidths_sum_le_stack_length

/-- Widths through the `i`th block telescope to the `i`th absolute event cut. -/
public theorem eventWidths_sum_take_eq_getElem
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (i : ℕ) (hi : i < p.eventCuts.length) :
    (p.eventWidths.take (i + 1)).sum = p.eventCuts[i] := by
  simpa [eventWidths] using
    successiveWidths_sum_take_add_previous_eq_getElem
      p.zero_cons_eventCuts_sortedLT i hi

/-- Every prefix of canonical blocks ends at the corresponding absolute event cut. -/
public theorem eventBlocks_take_flatten_eq_take_getElem
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (i : ℕ) (hi : i < p.eventCuts.length) :
    (p.eventBlocks.take (i + 1)).flatten = stack.take p.eventCuts[i] := by
  rw [eventBlocks, List.take_splitLength]
  have hcut : p.eventCuts[i] ≤ stack.length :=
    p.eventCuts_le_stack_length _ (List.getElem_mem hi)
  have hsum := p.eventWidths_sum_take_eq_getElem i hi
  rw [flatten_splitLengths_eq_take]
  · rw [hsum]
  · rwa [hsum]

/-- Numerically, the prefix endpoints of `eventBlocks` are exactly `eventCuts`. -/
public theorem eventBlocks_take_flatten_length_eq_getElem
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (i : ℕ) (hi : i < p.eventCuts.length) :
    (p.eventBlocks.take (i + 1)).flatten.length = p.eventCuts[i] := by
  rw [p.eventBlocks_take_flatten_eq_take_getElem i hi]
  exact List.length_take_of_le
    (p.eventCuts_le_stack_length _ (List.getElem_mem hi))

/-- The canonical cut list has no duplicate endpoints. -/
public theorem eventCuts_nodup
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : p.eventCuts.Nodup := by
  simpa [eventCuts] using
    Finset.sort_nodup (p.eventDepths.erase 0) (fun a b : ℕ => a ≤ b)

/-- Assign a physical block its productive-event-depth owner: the endpoint of that block. -/
public def eventBlockOwner
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (i : Fin p.eventBlocks.length) : ℕ :=
  (p.eventBlocks.take (i.val + 1)).flatten.length

/-- Every physical block owner is an actual productive-event depth. -/
public theorem eventBlockOwner_mem_eventDepths
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (i : Fin p.eventBlocks.length) :
    p.eventBlockOwner i ∈ p.eventDepths := by
  have hi : i.val < p.eventCuts.length := by
    simpa using i.isLt
  rw [eventBlockOwner, p.eventBlocks_take_flatten_length_eq_getElem i.val hi]
  exact ((p.mem_eventCuts_iff p.eventCuts[i.val]).1 (List.getElem_mem hi)).1

/-- Different physical blocks receive different productive-event-depth owners.  This is the
global injection needed for the token budget; unlike one-way boundary compatibility it rules
out arbitrary extra protected-child blocks. -/
public theorem eventBlockOwner_injective
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : Function.Injective p.eventBlockOwner := by
  intro i j hij
  have hi : i.val < p.eventCuts.length := by simpa using i.isLt
  have hj : j.val < p.eventCuts.length := by simpa using j.isLt
  simp only [eventBlockOwner] at hij
  rw [p.eventBlocks_take_flatten_length_eq_getElem i.val hi,
    p.eventBlocks_take_flatten_length_eq_getElem j.val hj] at hij
  apply Fin.ext
  exact p.eventCuts_nodup.getElem_inj_iff.mp hij

/-- Root-capacity owner of a canonical physical block.  Unlike its raw depth endpoint, this ID
is stable under the unary transports and binary embeddings encoded by `eventOwnerNat`. -/
public def eventBlockGlobalOwner
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (i : Fin p.eventBlocks.length) :
    Fin (2 * w.length - 1) :=
  Fin.cast p.productiveCount_eq_twice_yield_length_sub_one
    (p.eventOwner (p.eventBlockOwner i) (p.eventBlockOwner_mem_eventDepths i))

@[simp] public theorem eventBlockGlobalOwner_val
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (i : Fin p.eventBlocks.length) :
    (p.eventBlockGlobalOwner i).val = p.eventOwnerNat (p.eventBlockOwner i) := rfl

/-- Canonical block owners are globally collision-free in the exact `2|w|-1` carrier. -/
public theorem eventBlockGlobalOwner_injective
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : Function.Injective p.eventBlockGlobalOwner := by
  intro i j hij
  have hval : p.eventOwnerNat (p.eventBlockOwner i) =
      p.eventOwnerNat (p.eventBlockOwner j) := congrArg Fin.val hij
  apply p.eventBlockOwner_injective
  apply p.eventOwner_injective (p.eventBlockOwner_mem_eventDepths i)
    (p.eventBlockOwner_mem_eventDepths j)
  apply Fin.ext
  exact hval

/-- Every productive-event depth is a whole-block prefix boundary (with depth zero represented
by the empty block prefix). -/
public theorem exists_eventBlocks_boundary
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) {d : ℕ} (hd : d ∈ p.eventDepths) :
    ∃ blockCount, blockCount ≤ p.eventBlocks.length ∧
      d = (p.eventBlocks.take blockCount).flatten.length := by
  by_cases hd0 : d = 0
  · subst d
    exact ⟨0, Nat.zero_le _, by simp⟩
  · have hcut : d ∈ p.eventCuts := (p.mem_eventCuts_iff d).2 ⟨hd, hd0⟩
    rcases List.mem_iff_getElem.mp hcut with ⟨i, hi, hid⟩
    refine ⟨i + 1, ?_, ?_⟩
    · rw [p.eventBlocks_length]
      omega
    · rw [p.eventBlocks_take_flatten_length_eq_getElem i hi, hid]

/-- The number of canonical physical blocks obeys the same `2|w|-1` bound as event cuts. -/
public theorem eventBlocks_length_le_twice_yield_length_sub_one
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventBlocks.length ≤ 2 * w.length - 1 := by
  rw [p.eventBlocks_length, p.eventCuts_length]
  exact le_trans Finset.card_erase_le
    p.eventDepths_card_le_twice_yield_length_sub_one

/-- Canonical blocks come with a persistent finite ownership carrier of the exact global
`2|w|-1` capacity.  Descendants can retain these owners through `take`/`drop`, so protected
boundaries remain charged even when they are extra relative to the child's local event cuts. -/
public def eventBlocksOwnership
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    Aho.BlockOwnership (2 * w.length - 1) p.eventBlocks where
  owners := List.ofFn p.eventBlockGlobalOwner
  owners_length := by simp
  owners_nodup := List.nodup_ofFn.mpr p.eventBlockGlobalOwner_injective

@[simp] public theorem eventBlocksOwnership_owners
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) :
    p.eventBlocksOwnership.owners = List.ofFn p.eventBlockGlobalOwner := rfl

end NFParse
end IndexedGrammar
