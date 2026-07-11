module

public import Langlib.Grammars.Indexed.NormalForm.AhoEventOwnerLayout
public import Langlib.Grammars.Indexed.NormalForm.AhoGhostLayout

@[expose]
public section

/-!
# Productive-owner provenance for open frames

Selected blocks which cross an atomic pop leave their index in the stable prefix and put a
matching `close` atom in the continuation.  Relative to the current parse, each open frame is
either inherited from outside the active productive window or is the canonical owner of one
of the current parse's productive events.  This file records that provenance independently of
the runner.

It also records the purely syntactic invariant that persistent indices in the cursor prefix
are a permutation of all currently open frame owners.  The latter is deliberately stated up
to permutation: opening nested frames places the selected index and its `close` marker in
opposite traversal orders.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- One open frame is either inherited from outside the active productive window or owns a
canonical event of the current parse. -/
public def EventOwnedFrame
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (owner : Fin (10 * input.length)) : Prop :=
  OutsideProductiveWindow window owner ∨
    ∃ event : {d : ℕ // d ∈ parse.eventDepths},
      owner = window.eventOwner event.val event.property

/-- Productive provenance for every currently open frame owner. -/
public structure EventOwnedFrames
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (owners : List (Fin (10 * input.length))) : Prop where
  owner_at : ∀ owner ∈ owners, EventOwnedFrame parse window owner

namespace EventOwnedFrames

/-- The empty frame stack has canonical provenance. -/
public def nil
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse} :
    EventOwnedFrames parse window [] where
  owner_at _ hmem := by simp at hmem

/-- Add a frame whose provenance is already known. -/
public def cons
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners : List (Fin (10 * input.length))}
    {owner : Fin (10 * input.length)}
    (head : EventOwnedFrame parse window owner)
    (tail : EventOwnedFrames parse window owners) :
    EventOwnedFrames parse window (owner :: owners) where
  owner_at candidate hmem := by
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact head
    · exact tail.owner_at candidate htail

/-- Transport all frame classifications through an arbitrary change of active parse/window. -/
public def transport
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {residualWindow : ProductiveOwnerWindow (input := input) residual}
    {owners : List (Fin (10 * input.length))}
    (frames : EventOwnedFrames parse window owners)
    (shift : ∀ owner, EventOwnedFrame parse window owner →
      EventOwnedFrame residual residualWindow owner) :
    EventOwnedFrames residual residualWindow owners where
  owner_at owner hmem := shift owner (frames.owner_at owner hmem)

/-- Frame provenance is insensitive to the traversal order of the open-frame ledger. -/
public def perm
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners owners' : List (Fin (10 * input.length))}
    (frames : EventOwnedFrames parse window owners)
    (hperm : owners'.Perm owners) :
    EventOwnedFrames parse window owners' where
  owner_at owner hmem := frames.owner_at owner (hperm.mem_iff.mp hmem)

/-- A canonical event owner lies inside its productive window. -/
public theorem eventOwner_not_outside
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {d : ℕ} (hd : d ∈ parse.eventDepths) :
    ¬ OutsideProductiveWindow window (window.eventOwner d hd) := by
  intro hout
  have hlt := parse.eventOwnerNat_lt_productiveCount hd
  simp only [OutsideProductiveWindow,
    ProductiveOwnerWindow.eventOwner_val] at hout
  rcases hout with hout | hout <;> omega

/-- The first aligned block owner is either canonical at the first block endpoint or inherited
from outside the active window. -/
public theorem first_owner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (layout : EventOwnedLayout parse window (block :: blocks) (owner :: owners)) :
    (∃ hd : block.length ∈ parse.eventDepths,
      owner = window.eventOwner block.length hd) ∨
      OutsideProductiveWindow window owner := by
  have h := layout.owner_at
    (⟨0, by simp⟩ : Fin (block :: blocks).length)
  simpa [blockEndpoint, blockOwnerAt] using h

/-- Open the first aligned block as a frame after an atomic pop.  The selected local endpoint
becomes residual depth zero, while every existing canonical frame follows the continuation's
event-owner transport. -/
public def atomicPop
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {residualWindow : ProductiveOwnerWindow (input := input) residual}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)}
    {owners frameOwners : List (Fin (10 * input.length))}
    (layout : EventOwnedLayout parse window (block :: blocks) (owner :: owners))
    (frames : EventOwnedFrames parse window frameOwners)
    (outside : ∀ candidate, OutsideProductiveWindow window candidate →
      OutsideProductiveWindow residualWindow candidate)
    (owner_shift : ∀ hd : block.length ∈ parse.eventDepths,
      ∃ hd0 : 0 ∈ residual.eventDepths,
        window.eventOwner block.length hd = residualWindow.eventOwner 0 hd0)
    (frame_shift : ∀ event : {d : ℕ // d ∈ parse.eventDepths},
      ∃ residualEvent : {d : ℕ // d ∈ residual.eventDepths},
        window.eventOwner event.val event.property =
          residualWindow.eventOwner residualEvent.val residualEvent.property) :
    EventOwnedFrames residual residualWindow (owner :: frameOwners) := by
  apply EventOwnedFrames.cons
  · rcases first_owner layout with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      rcases owner_shift hd with ⟨hd0, heq⟩
      exact Or.inr ⟨⟨0, hd0⟩, howner.trans heq⟩
    · exact Or.inl (outside owner hout)
  · apply frames.transport
    intro candidate hcandidate
    rcases hcandidate with hout | ⟨event, howner⟩
    · exact Or.inl (outside candidate hout)
    · rcases frame_shift event with ⟨residualEvent, hshift⟩
      exact Or.inr ⟨residualEvent, howner.trans hshift⟩

/-- Outside-window ownership is unchanged by an equal-productive-count window transport. -/
public theorem outside_transport
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hcount : residual.productiveCount = parse.productiveCount)
    {owner : Fin (10 * input.length)}
    (hout : OutsideProductiveWindow window owner) :
    OutsideProductiveWindow (window.transport hcount) owner := by
  rcases hout with hout | hout
  · exact Or.inl (by
      simpa [OutsideProductiveWindow, ProductiveOwnerWindow.transport] using hout)
  · exact Or.inr (by
      simpa [OutsideProductiveWindow, ProductiveOwnerWindow.transport, hcount] using hout)

/-- Transport every framed event through the one-position event shift of a concrete pop. -/
public def pop
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
    {rest : NFParse g B stack w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.pop hr hlhs hc hrhs rest)}
    {owners : List (Fin (10 * input.length))}
    (frames : EventOwnedFrames
      (NFParse.pop hr hlhs hc hrhs rest) window owners) :
    EventOwnedFrames rest
      (window.transport (by
        simp [NFParse.productiveCount, NFParse.binaryCount,
          NFParse.terminalCount])) owners := by
  let hcount : rest.productiveCount =
      (NFParse.pop hr hlhs hc hrhs rest).productiveCount := by
    simp [NFParse.productiveCount, NFParse.binaryCount, NFParse.terminalCount]
  apply frames.transport
  intro owner howner
  rcases howner with hout | ⟨event, howner⟩
  · exact Or.inl (outside_transport window hcount hout)
  · rcases event with ⟨e, he⟩
    rcases Finset.mem_image.mp he with ⟨d, hd, hed⟩
    have heq : e = d + 1 := by omega
    subst e
    apply Or.inr
    refine ⟨⟨d, hd⟩, ?_⟩
    exact howner.trans (window.eventOwner_pop_succ hd)

/-- Every framed event of a push follows its canonical child preimage. -/
public def push
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {owners : List (Fin (10 * input.length))}
    (frames : EventOwnedFrames
      (NFParse.push hr hlhs hc hrhs rest) window owners) :
    EventOwnedFrames rest window.pushChild owners := by
  apply frames.transport
  intro owner howner
  rcases howner with hout | ⟨event, howner⟩
  · exact Or.inl (by
      simpa [ProductiveOwnerWindow.pushChild] using
        outside_transport window (by rfl) hout)
  · rcases event with ⟨d, hd⟩
    apply Or.inr
    let childDepth := NFParse.pushEventPreimage rest.eventDepths d
    let childMem : childDepth ∈ rest.eventDepths :=
      NFParse.pushEventPreimage_mem hd
    refine ⟨⟨childDepth, childMem⟩, ?_⟩
    exact howner.trans (window.eventOwner_push hd)

/-- The binary root owner lies strictly before the left child's productive window. -/
public theorem zero_outside_binaryLeft
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    (hd : 0 ∈ (NFParse.binary hr hlhs hc hrhs left right).eventDepths) :
    OutsideProductiveWindow window.binaryLeft (window.eventOwner 0 hd) := by
  left
  have hzero := window.eventOwner_binary_zero_val
  simp only [ProductiveOwnerWindow.binaryLeft_base]
  omega

/-- The binary root owner lies strictly before the right child's productive window. -/
public theorem zero_outside_binaryRight
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    (hd : 0 ∈ (NFParse.binary hr hlhs hc hrhs left right).eventDepths) :
    OutsideProductiveWindow window.binaryRight (window.eventOwner 0 hd) := by
  left
  have hzero := window.eventOwner_binary_zero_val
  simp only [ProductiveOwnerWindow.binaryRight_base]
  have hleft := left.nodeCount_pos
  have hproductive : 0 < left.productiveCount := by
    rw [left.productiveCount_eq_twice_yield_length_sub_one]
    have := left.yield_length_pos
    omega
  omega

/-- A parent frame restricts to the matching left event, or becomes outside the left window. -/
public def binaryLeft
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)}
    {owners : List (Fin (10 * input.length))}
    (frames : EventOwnedFrames
      (NFParse.binary hr hlhs hc hrhs left right) window owners) :
    EventOwnedFrames left window.binaryLeft owners := by
  apply frames.transport
  intro owner howner
  rcases howner with hout | ⟨event, howner⟩
  · exact Or.inl (EventOwnedLayout.outside_binaryLeft window hout)
  · rcases event with ⟨d, hd⟩
    by_cases hd0 : d = 0
    · subst d
      apply Or.inl
      rw [howner]
      exact zero_outside_binaryLeft window hd
    · by_cases hleft : d ∈ left.eventDepths
      · apply Or.inr
        refine ⟨⟨d, hleft⟩, ?_⟩
        exact howner.trans (window.eventOwner_binaryLeft hd0 hleft)
      · apply Or.inl
        have hright : d ∈ right.eventDepths := by
          simp only [NFParse.eventDepths, Finset.mem_insert,
            Finset.mem_union] at hd
          rcases hd with hd | hd
          · exact False.elim (hd0 hd)
          · exact hd.resolve_left hleft
        have heq := window.eventOwner_binaryRight hd0 hleft hright
        have hval := congrArg Fin.val (howner.trans heq)
        simp only [OutsideProductiveWindow,
          ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.binaryLeft_base,
          ProductiveOwnerWindow.binaryRight_base] at hval ⊢
        right
        omega

/-- A parent frame restricts to the matching right event, or becomes outside the right window. -/
public def binaryRight
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)}
    {owners : List (Fin (10 * input.length))}
    (frames : EventOwnedFrames
      (NFParse.binary hr hlhs hc hrhs left right) window owners) :
    EventOwnedFrames right window.binaryRight owners := by
  apply frames.transport
  intro owner howner
  rcases howner with hout | ⟨event, howner⟩
  · exact Or.inl (EventOwnedLayout.outside_binaryRight window hout)
  · rcases event with ⟨d, hd⟩
    by_cases hd0 : d = 0
    · subst d
      apply Or.inl
      rw [howner]
      exact zero_outside_binaryRight window hd
    · by_cases hleft : d ∈ left.eventDepths
      · apply Or.inl
        have heq := window.eventOwner_binaryLeft hd0 hleft
        have hval := congrArg Fin.val (howner.trans heq)
        have hlt := left.eventOwnerNat_lt_productiveCount hleft
        simp only [OutsideProductiveWindow,
          ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.binaryLeft_base,
          ProductiveOwnerWindow.binaryRight_base] at hval ⊢
        left
        omega
      · apply Or.inr
        have hright : d ∈ right.eventDepths := by
          simp only [NFParse.eventDepths, Finset.mem_insert,
            Finset.mem_union] at hd
          rcases hd with hd | hd
          · exact False.elim (hd0 hd)
          · exact hd.resolve_left hleft
        refine ⟨⟨d, hright⟩, ?_⟩
        exact howner.trans (window.eventOwner_binaryRight hd0 hleft hright)

end EventOwnedFrames

/-- Prefix indices and open-frame owners are the same finite ledger, up to traversal order. -/
public structure PrefixFrameLedger
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) : Prop where
  owners_perm :
    (cursor.left.filterMap ScheduleAtom.indexOwner?).Perm cursor.frameOwners

namespace PrefixFrameLedger

/-- A cursor with no prefix indices and no open frames has an empty ledger. -/
public def of_empty
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input}
    (hleft : cursor.left.filterMap ScheduleAtom.indexOwner? = [])
    (hframes : cursor.frameOwners = []) : PrefixFrameLedger cursor where
  owners_perm := by simp [hleft, hframes]

/-- The ledger equates prefix-index count with open-frame count. -/
public theorem prefix_length_eq_frameCount
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : PrefixFrameLedger cursor) :
    (cursor.left.filterMap ScheduleAtom.indexOwner?).length = cursor.frameCount := by
  rw [ScheduleCursor.frameCount]
  exact ledger.owners_perm.length_eq

/-- Transport a prefix/frame ledger across arbitrary owner permutations. -/
public def transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input}
    (ledger : PrefixFrameLedger old)
    (hprefix : (new.left.filterMap ScheduleAtom.indexOwner?).Perm
      (old.left.filterMap ScheduleAtom.indexOwner?))
    (hframes : new.frameOwners.Perm old.frameOwners) :
    PrefixFrameLedger new where
  owners_perm := hprefix.trans (ledger.owners_perm.trans hframes.symm)

/-- Insert one matched prefix index and open frame.  The hypotheses are phrased as
permutations so runner-specific zipper rearrangements remain outside this generic API. -/
public def insert
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input}
    (ledger : PrefixFrameLedger old)
    (owner : Fin (10 * input.length))
    (hprefix : (new.left.filterMap ScheduleAtom.indexOwner?).Perm
      (owner :: old.left.filterMap ScheduleAtom.indexOwner?))
    (hframes : new.frameOwners.Perm (owner :: old.frameOwners)) :
    PrefixFrameLedger new where
  owners_perm := by
    apply hprefix.trans
    exact (List.Perm.cons owner ledger.owners_perm).trans hframes.symm

/-- Remove one matched prefix index and frame. -/
public def remove
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input}
    (ledger : PrefixFrameLedger old)
    (owner : Fin (10 * input.length))
    (hprefix : (old.left.filterMap ScheduleAtom.indexOwner?).Perm
      (owner :: new.left.filterMap ScheduleAtom.indexOwner?))
    (hframes : old.frameOwners.Perm (owner :: new.frameOwners)) :
    PrefixFrameLedger new where
  owners_perm := by
    have hcons : (owner :: new.left.filterMap ScheduleAtom.indexOwner?).Perm
        (owner :: new.frameOwners) := by
      exact hprefix.symm.trans (ledger.owners_perm.trans hframes)
    exact List.Perm.cons_inv hcons

/-- Complete cursor-level freshness from the three owner ledgers.  Prefix indices are open
frames, selected right-side indices are governed by the event layout, and every remaining
right-side index is explicitly outside the active productive window. -/
public theorem eventOwner_not_mem_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {cursor : ScheduleCursor g input}
    {blocks : List (List g.flag)}
    {owners outsideOwners : List (Fin (10 * input.length))}
    (prefixLedger : PrefixFrameLedger cursor)
    (layout : EventOwnedLayout parse window blocks owners)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hright : cursor.right.filterMap ScheduleAtom.indexOwner? =
      owners ++ outsideOwners)
    (houtside : ∀ owner ∈ outsideOwners,
      OutsideProductiveWindow window owner)
    {d : ℕ} (hd : d ∈ parse.eventDepths)
    (hframeFresh : window.eventOwner d hd ∉ cursor.frameOwners)
    (hdiff : ∀ i : Fin blocks.length, d ≠ blockEndpoint blocks i) :
    window.eventOwner d hd ∉ cursor.indexOwners := by
  intro hmem
  have heta : ScheduleCursor.mk cursor.left cursor.focus cursor.right = cursor := by
    cases cursor
    rfl
  have hsplit := ScheduleCursor.indexOwners_mk
    cursor.left cursor.focus cursor.right
  rw [heta] at hsplit
  rw [hsplit, hfocus] at hmem
  simp only [List.append_nil, List.mem_append] at hmem
  rcases hmem with hleft | hrightMem
  · have hframe : window.eventOwner d hd ∈ cursor.frameOwners :=
      prefixLedger.owners_perm.mem_iff.mp hleft
    exact hframeFresh hframe
  · rw [hright] at hrightMem
    rcases List.mem_append.mp hrightMem with hactive | houter
    · exact layout.eventOwner_not_mem_owners hd hdiff hactive
    · exact EventOwnedFrames.eventOwner_not_outside hd (houtside _ houter)

end PrefixFrameLedger

end Aho
end IndexedGrammar
