module

public import Langlib.Grammars.Indexed.NormalForm.AhoEventOwnerFrames

@[expose]
public section

/-!
# Complete productive-owner ledgers for schedule layouts

`ScheduleBlockLayout` exposes a common suffix after its selected block owners.  This module
records that every owner in that suffix belongs outside the current productive subtree, then
packages the suffix, active-layout, and open-frame ledgers into a cursor-level invariant.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- The unselected index-owner suffix shared by the input and marked output of a block layout.
Every such owner belongs to a disjoint productive window. -/
public structure EventOwnedSuffix
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (owners : List (Fin (10 * input.length)))
    (word used : List (ScheduleAtom g input)) where
  suffix : List (Fin (10 * input.length))
  word_eq : word.filterMap ScheduleAtom.indexOwner? = owners ++ suffix
  used_eq : used.filterMap ScheduleAtom.indexOwner? = owners ++ suffix
  outside_at : ∀ owner ∈ suffix, OutsideProductiveWindow window owner

namespace EventOwnedSuffix

/-- Base layout: its arbitrary common tail is accepted once all tail owners are known outside. -/
public def nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    (tail : List (ScheduleAtom g input))
    (hout : ∀ owner ∈ tail.filterMap ScheduleAtom.indexOwner?,
      OutsideProductiveWindow window owner) :
    EventOwnedSuffix parse window [] tail tail where
  suffix := tail.filterMap ScheduleAtom.indexOwner?
  word_eq := by simp
  used_eq := by simp
  outside_at := hout

/-- Add one selected block.  Index-free gaps make no contribution to the common suffix. -/
public def cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners : List (Fin (10 * input.length))}
    {tail tail' : List (ScheduleAtom g input)}
    (ledger : EventOwnedSuffix parse window owners tail tail')
    (beta : List (ScheduleAtom g input)) (hbeta : ScheduleIndexFree beta)
    (idx : ScheduleIndex g input) :
    EventOwnedSuffix parse window (idx.owner :: owners)
      (beta ++ .index idx :: tail)
      (beta ++ .index idx.markUsed :: tail') where
  suffix := ledger.suffix
  word_eq := by
    simp [List.filterMap_append, hbeta.filterMap_indexOwner_eq_nil,
      ScheduleAtom.indexOwner?, ledger.word_eq]
  used_eq := by
    simp [List.filterMap_append, hbeta.filterMap_indexOwner_eq_nil,
      ScheduleAtom.indexOwner?, ledger.used_eq]
  outside_at := ledger.outside_at

/-- Re-selecting an already marked layout preserves its owner suffix. -/
public def marked
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (ledger : EventOwnedSuffix parse window owners word used) :
    EventOwnedSuffix parse window owners used used where
  suffix := ledger.suffix
  word_eq := ledger.used_eq
  used_eq := ledger.used_eq
  outside_at := ledger.outside_at

/-- Insert an index-free prefix before every selected block without changing the suffix. -/
public def prepend
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (ledger : EventOwnedSuffix parse window owners word used)
    (pref : List (ScheduleAtom g input)) (hfree : ScheduleIndexFree pref) :
    EventOwnedSuffix parse window owners (pref ++ word) (pref ++ used) where
  suffix := ledger.suffix
  word_eq := by
    simp [List.filterMap_append, hfree.filterMap_indexOwner_eq_nil,
      ledger.word_eq]
  used_eq := by
    simp [List.filterMap_append, hfree.filterMap_indexOwner_eq_nil,
      ledger.used_eq]
  outside_at := ledger.outside_at

/-- Equal-count unary transport preserves the outside-owner suffix. -/
public def transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (ledger : EventOwnedSuffix parse window owners word used)
    (hcount : residual.productiveCount = parse.productiveCount) :
    EventOwnedSuffix residual (window.transport hcount) owners word used where
  suffix := ledger.suffix
  word_eq := ledger.word_eq
  used_eq := ledger.used_eq
  outside_at owner hmem :=
    EventOwnedFrames.outside_transport window hcount (ledger.outside_at owner hmem)

/-- A parent suffix remains outside the left binary child window. -/
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
    {word used : List (ScheduleAtom g input)}
    (ledger : EventOwnedSuffix
      (NFParse.binary hr hlhs hc hrhs left right) window owners word used) :
    EventOwnedSuffix left window.binaryLeft owners word used where
  suffix := ledger.suffix
  word_eq := ledger.word_eq
  used_eq := ledger.used_eq
  outside_at owner hmem :=
    EventOwnedLayout.outside_binaryLeft window (ledger.outside_at owner hmem)

/-- A parent suffix remains outside the right binary child window. -/
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
    {word used : List (ScheduleAtom g input)}
    (ledger : EventOwnedSuffix
      (NFParse.binary hr hlhs hc hrhs left right) window owners word used) :
    EventOwnedSuffix right window.binaryRight owners word used where
  suffix := ledger.suffix
  word_eq := ledger.word_eq
  used_eq := ledger.used_eq
  outside_at owner hmem :=
    EventOwnedLayout.outside_binaryRight window (ledger.outside_at owner hmem)

end EventOwnedSuffix

/-- A scheduler block layout together with active-event and unselected-suffix provenance. -/
public structure EventOwnedScheduleLayout
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (flags : List g.flag) (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length)))
    (word used : List (ScheduleAtom g input)) where
  layout : ScheduleBlockLayout g input flags blocks owners word used
  active : EventOwnedLayout parse window blocks owners
  suffix : EventOwnedSuffix parse window owners word used

/-- Complete cursor-level owner ledger, independent of any particular block-layout syntax. -/
public structure ScheduleOwnerLedger
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (cursor : ScheduleCursor g input) where
  active : List (Fin (10 * input.length))
  outside : List (Fin (10 * input.length))
  right_eq : cursor.right.filterMap ScheduleAtom.indexOwner? = active ++ outside
  outside_at : ∀ owner ∈ outside, OutsideProductiveWindow window owner
  frames : EventOwnedFrames parse window cursor.frameOwners
  prefixLedger : PrefixFrameLedger cursor

namespace ScheduleOwnerLedger

/-- The canonical root cursor has no persistent, outside, or framed owners. -/
public def root
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (parse : NFParse g g.initial [] input) :
    ScheduleOwnerLedger parse (ProductiveOwnerWindow.root parse)
      (initialScheduleCursor parse) where
  active := []
  outside := []
  right_eq := by
    simp [initialScheduleCursor, ScheduleAtom.indexOwner?]
  outside_at _ hmem := by simp at hmem
  frames := EventOwnedFrames.nil
  prefixLedger := PrefixFrameLedger.of_empty (by
      simp [initialScheduleCursor, ScheduleAtom.indexOwner?]) (by
      simp [initialScheduleCursor, ScheduleCursor.frameOwners,
        ScheduleCursor.word, ScheduleAtom.closeOwner?])

/-- The complete schedule ledger specializes the generic whole-cursor freshness theorem. -/
public theorem eventOwner_not_mem_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {cursor : ScheduleCursor g input}
    (ledger : ScheduleOwnerLedger parse window cursor)
    {blocks : List (List g.flag)}
    (activeLayout : EventOwnedLayout parse window blocks ledger.active)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    {d : ℕ} (hd : d ∈ parse.eventDepths)
    (hframeFresh : window.eventOwner d hd ∉ cursor.frameOwners)
    (hdiff : ∀ i : Fin blocks.length, d ≠ blockEndpoint blocks i) :
    window.eventOwner d hd ∉ cursor.indexOwners :=
  ledger.prefixLedger.eventOwner_not_mem_indexOwners activeLayout hfocus
    ledger.right_eq ledger.outside_at hd hframeFresh hdiff

/-- Generic cursor reassembly after a parse/window transport. -/
public def transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {old new : ScheduleCursor g input}
    (ledger : ScheduleOwnerLedger parse window old)
    (residualWindow : ProductiveOwnerWindow (input := input) residual)
    (hright : new.right.filterMap ScheduleAtom.indexOwner? =
      ledger.active ++ ledger.outside)
    (houtside : ∀ owner ∈ ledger.outside,
      OutsideProductiveWindow residualWindow owner)
    (hframes : EventOwnedFrames residual residualWindow new.frameOwners)
    (hprefix : PrefixFrameLedger new) :
    ScheduleOwnerLedger residual residualWindow new where
  active := ledger.active
  outside := ledger.outside
  right_eq := hright
  outside_at := houtside
  frames := hframes
  prefixLedger := hprefix

end ScheduleOwnerLedger

end Aho
end IndexedGrammar
