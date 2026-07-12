module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Ownership.EventLedger
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Ownership.Shadow

@[expose]
public section

/-!
# Fresh productive owners for unary pushes

A fresh singleton block introduced by a push is owned by the child's depth-one event.  This
file isolates the two facts needed to allocate that owner: it can coincide with a parent event
only at parent depth zero (and only when the child has no depth-zero event), and it is absent
from a fully accounted cursor whenever either that parent depth-zero frame is absent or the
child itself has a depth-zero event.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

namespace ProductiveOwnerWindow

/-- A child's depth-one event is inside the equal-count productive window of its push parent. -/
public theorem pushChild_eventOwner_one_not_outside
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) :
    ¬ OutsideProductiveWindow window
      (window.pushChild.eventOwner 1 hone) := by
  intro hout
  have hlt := rest.eventOwnerNat_lt_productiveCount hone
  simp only [OutsideProductiveWindow, ProductiveOwnerWindow.eventOwner_val,
    ProductiveOwnerWindow.pushChild_base] at hout
  rcases hout with hout | hout
  · omega
  · have hcount :
        (NFParse.push hr hlhs hc hrhs rest).productiveCount =
          rest.productiveCount := by
      simp [NFParse.productiveCount, NFParse.binaryCount, NFParse.terminalCount]
    rw [hcount] at hout
    omega

/-- Exact collision characterization for the depth-one push owner.  It aliases a parent event
precisely when that event is depth zero and the child has no event at depth zero. -/
public theorem pushChild_eventOwner_one_eq_parent_iff
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) {d : ℕ}
    (hd : d ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths) :
    window.pushChild.eventOwner 1 hone = window.eventOwner d hd ↔
      d = 0 ∧ 0 ∉ rest.eventDepths := by
  constructor
  · intro heq
    have hd0 : d = 0 := by
      by_contra hne
      exact window.eventOwner_one_ne_parent_positive hone
        (Nat.pos_of_ne_zero hne) hd heq
    subst d
    refine ⟨rfl, ?_⟩
    intro hzero
    have htransport := window.eventOwner_push hd
    have hpreimage : NFParse.pushEventPreimage rest.eventDepths 0 = 0 := by
      simp [NFParse.pushEventPreimage, hzero]
    have hcollision : window.pushChild.eventOwner 1 hone =
        window.pushChild.eventOwner 0 hzero := by
      rw [heq, htransport]
      simp [hpreimage]
    have := window.pushChild.eventOwner_injective hone hzero hcollision
    omega
  · rintro ⟨rfl, hzero⟩
    have hparent : 0 ∈
        (NFParse.push hr hlhs hc hrhs rest).eventDepths :=
      Finset.mem_image.mpr ⟨1, hone, by simp⟩
    have htransport := window.eventOwner_push hparent
    have hpreimage : NFParse.pushEventPreimage rest.eventDepths 0 = 1 := by
      simp [NFParse.pushEventPreimage, hzero]
    have hproof : hd = hparent := Subsingleton.elim _ _
    subst hproof
    rw [htransport]
    simp [hpreimage]

/-- The shadow-bank depth-one ticket has the same collision behavior as its primary mate. -/
public theorem pushChild_shadowEventOwner_one_eq_parent_iff
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) {d : ℕ}
    (hd : d ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths) :
    window.pushChild.shadowEventOwner 1 hone =
        window.shadowEventOwner d hd ↔
      d = 0 ∧ 0 ∉ rest.eventDepths := by
  have hprimary : window.pushChild.eventOwner 1 hone =
      window.eventOwner d hd ↔ d = 0 ∧ 0 ∉ rest.eventDepths :=
    window.pushChild_eventOwner_one_eq_parent_iff hone hd
  constructor
  · intro hshadow
    apply hprimary.mp
    apply Fin.ext
    have hval := congrArg Fin.val hshadow
    simp only [ProductiveOwnerWindow.shadowEventOwner_val] at hval
    simp only [ProductiveOwnerWindow.eventOwner_val]
    omega
  · intro hcollision
    exact window.shadowEventOwner_congr window.pushChild hd hone
      (hprimary.mpr hcollision).symm |>.symm

/-- The child depth-one shadow ticket remains inside the equal-count parent shadow window. -/
public theorem pushChild_shadowEventOwner_one_not_outside
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) :
    ¬ OutsideShadowWindow window
      (window.pushChild.shadowEventOwner 1 hone) := by
  intro hout
  apply OutsideShadowWindow.shadowEventOwner_not_outside
    window.pushChild hone
  simpa [ProductiveOwnerWindow.pushChild] using hout

end ProductiveOwnerWindow

namespace EventOwnedFrames

/-- If no parent depth-zero owner is held by a frame, the child's depth-one owner is fresh
from all frames.  Outside-window frames cannot collide because unary windows have equal extent. -/
public theorem pushChild_eventOwner_one_not_mem_of_no_parent_zero
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
      (NFParse.push hr hlhs hc hrhs rest) window owners)
    (hone : 1 ∈ rest.eventDepths)
    (hzeroFresh : ∀ hd : 0 ∈
      (NFParse.push hr hlhs hc hrhs rest).eventDepths,
      window.eventOwner 0 hd ∉ owners) :
    window.pushChild.eventOwner 1 hone ∉ owners := by
  intro hmem
  rcases frames.owner_at _ hmem with hout | hzero
  · exact window.pushChild_eventOwner_one_not_outside hone hout
  · rcases hzero with ⟨event, heq⟩
    rcases event with ⟨d, hd⟩
    have hcharacter :=
      (window.pushChild_eventOwner_one_eq_parent_iff hone hd).1 heq
    rcases hcharacter with ⟨hdepth, _⟩
    subst d
    exact hzeroFresh hd (heq ▸ hmem)

/-- If the child already has a depth-zero event, injectivity separates its depth-one owner
from every possible local depth-zero frame. -/
public theorem pushChild_eventOwner_one_not_mem_of_child_zero
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
      (NFParse.push hr hlhs hc hrhs rest) window owners)
    (hzero : 0 ∈ rest.eventDepths) (hone : 1 ∈ rest.eventDepths) :
    window.pushChild.eventOwner 1 hone ∉ owners := by
  intro hmem
  rcases frames.owner_at _ hmem with hout | hparentZero
  · exact window.pushChild_eventOwner_one_not_outside hone hout
  · rcases hparentZero with ⟨event, heq⟩
    have hcollision : window.pushChild.eventOwner 1 hone =
        window.eventOwner event.val event.property := heq
    have hcharacter :=
      (window.pushChild_eventOwner_one_eq_parent_iff hone event.property).1 hcollision
    exact hcharacter.2 hzero

end EventOwnedFrames

namespace PrefixFrameLedger

/-- Once frame freshness is known, the full cursor decomposition proves that the canonical
depth-one push owner is absent from every persistent index. -/
public theorem pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    {blocks : List (List g.flag)}
    {owners outsideOwners : List (Fin (10 * input.length))}
    (prefixLedger : PrefixFrameLedger cursor)
    (layout : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks owners)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hright : cursor.right.filterMap ScheduleAtom.indexOwner? =
      owners ++ outsideOwners)
    (houtside : ∀ owner ∈ outsideOwners,
      OutsideProductiveWindow window owner)
    (hone : 1 ∈ rest.eventDepths)
    (hframes : window.pushChild.eventOwner 1 hone ∉ cursor.frameOwners) :
    window.pushChild.eventOwner 1 hone ∉ cursor.indexOwners := by
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
  · exact hframes (prefixLedger.owners_perm.mem_iff.mp hleft)
  · rw [hright] at hrightMem
    rcases List.mem_append.mp hrightMem with hactive | houter
    · rcases List.mem_iff_getElem.mp hactive with ⟨i, hi, hget⟩
      have hi' : i < blocks.length := by
        rw [← layout.owners_length]
        exact hi
      let j : Fin blocks.length := ⟨i, hi'⟩
      have hat : blockOwnerAt owners layout.owners_length j =
          window.pushChild.eventOwner 1 hone := by
        simpa [blockOwnerAt, j] using hget
      rcases layout.owner_at j with hlocal | hout
      · rcases hlocal with ⟨hd, howner⟩
        have hdpos : 0 < blockEndpoint blocks j := layout.endpoint_pos j
        exact window.eventOwner_one_ne_parent_positive hone hdpos hd
          (hat.symm.trans howner)
      · exact window.pushChild_eventOwner_one_not_outside hone (hat ▸ hout)
    · exact window.pushChild_eventOwner_one_not_outside hone (houtside _ houter)

/-- Full-cursor push freshness when the parent depth-zero owner is not held by a frame. -/
public theorem pushChild_eventOwner_one_not_mem_indexOwners_of_no_parent_zero_frame
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    {blocks : List (List g.flag)}
    {owners outsideOwners : List (Fin (10 * input.length))}
    (prefixLedger : PrefixFrameLedger cursor)
    (frames : EventOwnedFrames
      (NFParse.push hr hlhs hc hrhs rest) window cursor.frameOwners)
    (layout : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks owners)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hright : cursor.right.filterMap ScheduleAtom.indexOwner? =
      owners ++ outsideOwners)
    (houtside : ∀ owner ∈ outsideOwners,
      OutsideProductiveWindow window owner)
    (hone : 1 ∈ rest.eventDepths)
    (hzeroFresh : ∀ hd : 0 ∈
      (NFParse.push hr hlhs hc hrhs rest).eventDepths,
      window.eventOwner 0 hd ∉ cursor.frameOwners) :
    window.pushChild.eventOwner 1 hone ∉ cursor.indexOwners :=
  prefixLedger.pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
    layout hfocus hright houtside hone
    (frames.pushChild_eventOwner_one_not_mem_of_no_parent_zero hone hzeroFresh)

/-- Full-cursor push freshness when child depths zero and one are both productive events. -/
public theorem pushChild_eventOwner_one_not_mem_indexOwners_of_child_zero
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    {blocks : List (List g.flag)}
    {owners outsideOwners : List (Fin (10 * input.length))}
    (prefixLedger : PrefixFrameLedger cursor)
    (frames : EventOwnedFrames
      (NFParse.push hr hlhs hc hrhs rest) window cursor.frameOwners)
    (layout : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks owners)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hright : cursor.right.filterMap ScheduleAtom.indexOwner? =
      owners ++ outsideOwners)
    (houtside : ∀ owner ∈ outsideOwners,
      OutsideProductiveWindow window owner)
    (hzero : 0 ∈ rest.eventDepths) (hone : 1 ∈ rest.eventDepths) :
    window.pushChild.eventOwner 1 hone ∉ cursor.indexOwners :=
  prefixLedger.pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
    layout hfocus hright houtside hone
    (frames.pushChild_eventOwner_one_not_mem_of_child_zero hzero hone)

end PrefixFrameLedger

namespace ScheduleOwnerLedger

/-- Schedule-ledger specialization of depth-one push freshness with an explicit frame premise. -/
public theorem pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    (ledger : ScheduleOwnerLedger
      (NFParse.push hr hlhs hc hrhs rest) window cursor)
    {blocks : List (List g.flag)}
    (activeLayout : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks ledger.active)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hone : 1 ∈ rest.eventDepths)
    (hframes : window.pushChild.eventOwner 1 hone ∉ cursor.frameOwners) :
    window.pushChild.eventOwner 1 hone ∉ cursor.indexOwners :=
  ledger.prefixLedger.pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
    activeLayout hfocus ledger.right_eq ledger.outside_at hone hframes

/-- Schedule-ledger push freshness when no parent depth-zero owner is framed. -/
public theorem pushChild_eventOwner_one_not_mem_indexOwners_of_no_parent_zero_frame
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    (ledger : ScheduleOwnerLedger
      (NFParse.push hr hlhs hc hrhs rest) window cursor)
    {blocks : List (List g.flag)}
    (activeLayout : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks ledger.active)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hone : 1 ∈ rest.eventDepths)
    (hzeroFresh : ∀ hd : 0 ∈
      (NFParse.push hr hlhs hc hrhs rest).eventDepths,
      window.eventOwner 0 hd ∉ cursor.frameOwners) :
    window.pushChild.eventOwner 1 hone ∉ cursor.indexOwners :=
  ledger.pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
    activeLayout hfocus hone
    (ledger.frames.pushChild_eventOwner_one_not_mem_of_no_parent_zero
      hone hzeroFresh)

/-- Schedule-ledger push freshness when child depths zero and one both carry events. -/
public theorem pushChild_eventOwner_one_not_mem_indexOwners_of_child_zero
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    (ledger : ScheduleOwnerLedger
      (NFParse.push hr hlhs hc hrhs rest) window cursor)
    {blocks : List (List g.flag)}
    (activeLayout : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks ledger.active)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hzero : 0 ∈ rest.eventDepths) (hone : 1 ∈ rest.eventDepths) :
    window.pushChild.eventOwner 1 hone ∉ cursor.indexOwners :=
  ledger.pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
    activeLayout hfocus hone
    (ledger.frames.pushChild_eventOwner_one_not_mem_of_child_zero hzero hone)

/-- If the canonical depth-one child owner is already persistent, the unique collision is an
open parent depth-zero frame.  In particular, the child cannot itself have a depth-zero event. -/
public theorem pushChild_eventOwner_one_mem_indexOwners_imp_parent_zero_frame
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    (ledger : ScheduleOwnerLedger
      (NFParse.push hr hlhs hc hrhs rest) window cursor)
    {blocks : List (List g.flag)}
    (activeLayout : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks ledger.active)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hone : 1 ∈ rest.eventDepths)
    (hmem : window.pushChild.eventOwner 1 hone ∈ cursor.indexOwners) :
    0 ∉ rest.eventDepths ∧
      ∃ hd : 0 ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths,
        window.eventOwner 0 hd ∈ cursor.frameOwners := by
  have hframe : window.pushChild.eventOwner 1 hone ∈ cursor.frameOwners := by
    by_contra hfresh
    exact (ledger.pushChild_eventOwner_one_not_mem_indexOwners_of_not_mem_frames
      activeLayout hfocus hone hfresh) hmem
  rcases ledger.frames.owner_at _ hframe with hout | hlocal
  · exact False.elim
      (window.pushChild_eventOwner_one_not_outside hone hout)
  · rcases hlocal with ⟨event, heq⟩
    rcases event with ⟨d, hd⟩
    have hcharacter :=
      (window.pushChild_eventOwner_one_eq_parent_iff hone hd).1 heq
    rcases hcharacter with ⟨hdepth, hzero⟩
    subst d
    exact ⟨hzero, ⟨hd, heq ▸ hframe⟩⟩

end ScheduleOwnerLedger

namespace ShadowOwnerLedger

/-- If child depths zero and one are both events, the depth-one shadow ticket is absent from
an entirely accounted parent semantic cursor.  It is neither a parent shadow event nor an
outside-window ticket. -/
public theorem pushChild_shadowEventOwner_one_not_mem_indexOwners_of_child_zero
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    {cursor : ScheduleCursor g input}
    (ledger : ShadowOwnerLedger
      (NFParse.push hr hlhs hc hrhs rest) window cursor)
    {blocks : List (List g.flag)}
    (layout : ShadowStartLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks ledger.active)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    (hzero : 0 ∈ rest.eventDepths) (hone : 1 ∈ rest.eventDepths) :
    window.pushChild.shadowEventOwner 1 hone ∉ cursor.indexOwners := by
  intro hmem
  have heta : ScheduleCursor.mk cursor.left cursor.focus cursor.right = cursor := by
    cases cursor
    rfl
  have hsplit := ScheduleCursor.indexOwners_mk
    cursor.left cursor.focus cursor.right
  rw [heta] at hsplit
  rw [hsplit, hfocus] at hmem
  simp only [List.append_nil, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · have hframe := ledger.prefixLedger.owners_perm.mem_iff.mp hleft
    exact window.pushChild_shadowEventOwner_one_not_outside hone
      (ledger.frames.owner_at _ hframe)
  · rw [ledger.right_eq] at hright
    rcases List.mem_append.mp hright with hactive | houtside
    · rcases List.mem_iff_getElem.mp hactive with ⟨i, hi, hget⟩
      have hi' : i < blocks.length := by
        rw [← layout.owners_length]
        exact hi
      let j : Fin blocks.length := ⟨i, hi'⟩
      have hat : blockOwnerAt ledger.active layout.owners_length j =
          window.pushChild.shadowEventOwner 1 hone := by
        simpa [blockOwnerAt, j] using hget
      rcases layout.owner_at j with hlocal | hout
      · rcases hlocal with ⟨hd, howner⟩
        have hcollision : window.pushChild.shadowEventOwner 1 hone =
            window.shadowEventOwner (blockStart blocks j) hd :=
          hat.symm.trans howner
        have hcharacter :=
          (window.pushChild_shadowEventOwner_one_eq_parent_iff hone hd).1
            hcollision
        exact hcharacter.2 hzero
      · exact window.pushChild_shadowEventOwner_one_not_outside hone
          (hat ▸ hout)
    · exact window.pushChild_shadowEventOwner_one_not_outside hone
        (ledger.outside_at _ houtside)

end ShadowOwnerLedger

end Aho
end IndexedGrammar
