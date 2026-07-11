module

public import Langlib.Grammars.Indexed.NormalForm.AhoEventOwnerFrames

@[expose]
public section

/-!
# Complete productive-owner ledgers for schedule cursors

This module packages active, outside-window, and open-frame owner provenance into a
cursor-level invariant.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

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
