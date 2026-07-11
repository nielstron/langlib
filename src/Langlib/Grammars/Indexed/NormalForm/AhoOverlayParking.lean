module

public import Langlib.Grammars.Indexed.NormalForm.AhoIndexTickets

@[expose]
public section

/-!
# Restorable parking for copy-on-write overlays

An overlay may leave the protected base block at the parking ticket of the current
productive window.  This is the one situation in which the ordinary strict
`IndexTicketLedger.ParkingBelow` invariant is deliberately weakened to
`ParkingAtOrBelow`.

`OverlayParking` records the exact extra information needed to undo that weakening: either
the strict bound already holds, or a specified live base owner carries the unique ticket at
the current base.  Reticketing that owner to a nonparking ticket then restores the strict
bound.  The development here is ghost-only and independent of the physical overlay layout.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

namespace IndexTicketLedger

/-- The parking invariant carried by overlay mode.

All live parking slots are at or below the current window base.  If the strict bound does not
already hold, `baseOwner` is live and identifies the owner of the canonical parking ticket at
that base.  Duplicate-freedom of the ticket ledger makes this owner unique. -/
public structure OverlayParking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    (ledger : IndexTicketLedger cursor)
    (window : ProductiveOwnerWindow (input := input) parse)
    (baseOwner : Fin (10 * input.length)) : Prop where
  atOrBelow : ledger.ParkingAtOrBelow window
  strict_or_parked :
    ledger.ParkingBelow window ∨
      (baseOwner ∈ cursor.indexOwners ∧
        ledger.ticketOf baseOwner = window.parkingTicket)

namespace OverlayParking

/-- Swapping two nonparking tickets preserves a restorable parking marker.  In the parked
branch the canonical parking ticket is fixed by the swap; in the strict branch this is the
ordinary strict parking preservation theorem. -/
public theorem swapTickets_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (left right : IndexTicket input)
    (hleft : ∀ hinput : 0 < input.length,
      left ≠ IndexTicket.scratch hinput)
    (hright : ∀ hinput : 0 < input.length,
      right ≠ IndexTicket.scratch hinput)
    (hleftNonparking : left.Nonparking)
    (hrightNonparking : right.Nonparking) :
    (ledger.swapTickets left right hleft hright).OverlayParking window baseOwner := by
  refine ⟨parking.atOrBelow.swapTickets_nonparking left right hleft hright
    hleftNonparking hrightNonparking, ?_⟩
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hbaseTicket⟩
  · exact Or.inl (hbelow.swapTickets_nonparking left right hleft hright
      hleftNonparking hrightNonparking)
  · refine Or.inr ⟨hlive, ?_⟩
    change Equiv.swap left right (ledger.ticketOf baseOwner) = window.parkingTicket
    rw [hbaseTicket]
    exact Equiv.swap_apply_of_ne_of_ne
      (hleftNonparking window.parkingSlot).symm
      (hrightNonparking window.parkingSlot).symm

/-- A strict parking bound is already a restorable overlay parking invariant. -/
public theorem ofBelow
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (baseOwner : Fin (10 * input.length))
    (hbelow : ledger.ParkingBelow window) :
    ledger.OverlayParking window baseOwner :=
  ⟨hbelow.toAtOrBelow, Or.inl hbelow⟩

/-- A live owner carrying the current canonical parking ticket supplies the parked branch of
the invariant, provided the non-strict global parking bound is known. -/
public theorem ofParked
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (hbound : ledger.ParkingAtOrBelow window)
    (hlive : baseOwner ∈ cursor.indexOwners)
    (hticket : ledger.ticketOf baseOwner = window.parkingTicket) :
    ledger.OverlayParking window baseOwner :=
  ⟨hbound, Or.inr ⟨hlive, hticket⟩⟩

/-- In the parked branch, the designated base owner is the unique live owner carrying the
current window parking ticket. -/
public theorem owner_eq_of_parked_ticket
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner candidate : Fin (10 * input.length)}
    (hlive : baseOwner ∈ cursor.indexOwners)
    (hbase : ledger.ticketOf baseOwner = window.parkingTicket)
    (hcandidate : candidate ∈ cursor.indexOwners)
    (hcandidateTicket : ledger.ticketOf candidate = window.parkingTicket) :
    candidate = baseOwner := by
  apply ledger.ticketOf_injectiveOn hcandidate hlive
  exact hcandidateTicket.trans hbase.symm

/-- Transporting the cursor through a physical-owner permutation preserves restorable
overlay parking. -/
public theorem transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (hindices : new.indexOwners.Perm old.indexOwners) :
    (ledger.transport hindices).OverlayParking window baseOwner := by
  refine ⟨parking.atOrBelow.transport hindices, ?_⟩
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hticket⟩
  · exact Or.inl (hbelow.transport hindices)
  · exact Or.inr ⟨hindices.mem_iff.mpr hlive, hticket⟩

/-- Transporting the physical cursor while weakly increasing the productive-window base
preserves restorable overlay parking.  A strict base increase absorbs a parked current-base
ticket into the ordinary strict bound; under equal bases the parked witness is unchanged. -/
public theorem transport_mono
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A₁ A₂ : g.nt} {stack₁ stack₂ : List g.flag} {w₁ w₂ : List T}
    {parse₁ : NFParse g A₁ stack₁ w₁}
    {parse₂ : NFParse g A₂ stack₂ w₂}
    {old new : ScheduleCursor g input} {ledger : IndexTicketLedger old}
    {oldWindow : ProductiveOwnerWindow (input := input) parse₁}
    {newWindow : ProductiveOwnerWindow (input := input) parse₂}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking oldWindow baseOwner)
    (hindices : new.indexOwners.Perm old.indexOwners)
    (hbase : oldWindow.base ≤ newWindow.base) :
    (ledger.transport hindices).OverlayParking newWindow baseOwner := by
  refine ⟨parking.atOrBelow.transport_mono hindices hbase, ?_⟩
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hticket⟩
  · exact Or.inl (hbelow.transport_mono hindices hbase)
  · rcases Nat.eq_or_lt_of_le hbase with hbaseEq | hbaseLt
    · refine Or.inr ⟨hindices.mem_iff.mpr hlive, ?_⟩
      change ledger.ticketOf baseOwner = newWindow.parkingTicket
      rw [hticket]
      apply Fin.ext
      simp only [ProductiveOwnerWindow.parkingTicket_val]
      omega
    · exact Or.inl
        (parking.atOrBelow.transport_toBelow_of_base_lt hindices hbaseLt)

/-- Replacing one live ticket by a nonparking ticket, while leaving every other live ticket
unchanged, preserves the non-strict parking bound. -/
public theorem _root_.IndexedGrammar.Aho.IndexTicketLedger.ParkingAtOrBelow.change_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger updated : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (parking : ledger.ParkingAtOrBelow window)
    (owner : Fin (10 * input.length))
    (hownerNonparking : (updated.ticketOf owner).Nonparking)
    (hunchanged : ∀ candidate ∈ cursor.indexOwners, candidate ≠ owner →
      updated.ticketOf candidate = ledger.ticketOf candidate) :
    updated.ParkingAtOrBelow window := by
  intro slot hslot
  rw [ScheduleCursor.indexTickets] at hslot
  rcases List.mem_map.mp hslot with ⟨candidate, hcandidate, hticket⟩
  by_cases hsame : candidate = owner
  · subst candidate
    exact False.elim (hownerNonparking slot hticket)
  · apply parking slot
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hcandidate,
      (hunchanged candidate hcandidate hsame).symm.trans hticket⟩

/-- Replacing one live ticket by a nonparking ticket, while leaving every other
live ticket unchanged, preserves a strict parking bound.  This abstract form is
useful for ticket normalizations whose implementation is not literally
`IndexTicketLedger.reticket`. -/
public theorem _root_.IndexedGrammar.Aho.IndexTicketLedger.ParkingBelow.change_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger updated : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (parking : ledger.ParkingBelow window)
    (owner : Fin (10 * input.length))
    (hownerNonparking : (updated.ticketOf owner).Nonparking)
    (hunchanged : ∀ candidate ∈ cursor.indexOwners, candidate ≠ owner →
      updated.ticketOf candidate = ledger.ticketOf candidate) :
    updated.ParkingBelow window := by
  intro slot hslot
  rw [ScheduleCursor.indexTickets] at hslot
  rcases List.mem_map.mp hslot with ⟨candidate, hcandidate, hticket⟩
  by_cases hsame : candidate = owner
  · subst candidate
    exact False.elim (hownerNonparking slot hticket)
  · apply parking slot
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hcandidate,
      (hunchanged candidate hcandidate hsame).symm.trans hticket⟩

/-- Replacing one live ticket by a nonparking ticket, while leaving every other
live ticket unchanged, preserves restorable overlay parking.  If the changed
owner was the parked base owner, the resulting invariant is strict; otherwise
the parked witness remains unchanged. -/
public theorem change_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger updated : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (owner : Fin (10 * input.length))
    (hownerNonparking : (updated.ticketOf owner).Nonparking)
    (hunchanged : ∀ candidate ∈ cursor.indexOwners, candidate ≠ owner →
      updated.ticketOf candidate = ledger.ticketOf candidate) :
    updated.OverlayParking window baseOwner := by
  have hbound : updated.ParkingAtOrBelow window :=
    parking.atOrBelow.change_nonparking owner hownerNonparking hunchanged
  refine ⟨hbound, ?_⟩
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hbaseTicket⟩
  · exact Or.inl
      (hbelow.change_nonparking owner hownerNonparking hunchanged)
  · by_cases hsame : owner = baseOwner
    · subst owner
      refine Or.inl ?_
      intro slot hslot
      have hle := hbound slot hslot
      by_contra hnlt
      have hslotBase : slot.val = window.base :=
        Nat.le_antisymm hle (Nat.le_of_not_gt hnlt)
      have hparkingEq : IndexTicket.parking slot = window.parkingTicket := by
        apply Fin.ext
        simp only [IndexTicket.parking_val,
          ProductiveOwnerWindow.parkingTicket_val]
        omega
      rw [ScheduleCursor.indexTickets] at hslot
      rcases List.mem_map.mp hslot with
        ⟨candidate, hcandidate, hcandidateTicket⟩
      by_cases hcandidateBase : candidate = baseOwner
      · subst candidate
        exact hownerNonparking slot hcandidateTicket
      · have holdCandidate :
            ledger.ticketOf candidate = window.parkingTicket := by
          calc
            ledger.ticketOf candidate = updated.ticketOf candidate :=
              (hunchanged candidate hcandidate hcandidateBase).symm
            _ = IndexTicket.parking slot := hcandidateTicket
            _ = window.parkingTicket := hparkingEq
        exact hcandidateBase (owner_eq_of_parked_ticket hlive hbaseTicket
          hcandidate holdCandidate)
    · refine Or.inr ⟨hlive, ?_⟩
      rw [hunchanged baseOwner hlive (Ne.symm hsame)]
      exact hbaseTicket

/-- Allocating a fresh owner at a nonparking ticket preserves restorable overlay parking.
The designated parked owner, when present, was already live and hence is not the allocated
owner. -/
public theorem allocate_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hnonparking : ticket.Nonparking) :
    (ledger.allocate owner ticket hownerFresh hticketFresh hticketNotScratch
      hindices).OverlayParking window baseOwner := by
  let updated := ledger.allocate owner ticket hownerFresh hticketFresh
    hticketNotScratch hindices
  refine ⟨parking.atOrBelow.allocate_nonparking owner ticket hownerFresh
    hticketFresh hticketNotScratch hindices hnonparking, ?_⟩
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hticket⟩
  · exact Or.inl (hbelow.allocate_nonparking owner ticket hownerFresh
      hticketFresh hticketNotScratch hindices hnonparking)
  · refine Or.inr ⟨hindices.mem_iff.mpr (List.mem_cons_of_mem owner hlive), ?_⟩
    change ledger.insertTicket owner ticket baseOwner = window.parkingTicket
    rw [ledger.insertTicket_eq_of_mem owner ticket hlive hownerFresh]
    exact hticket

/-- Abstract restoration lemma.  Suppose a parked base owner is reticketed to a
nonparking target and every other live ticket is unchanged.  Once the updated ledger still
satisfies `ParkingAtOrBelow`, its bound is automatically strict.

This formulation deliberately does not depend on the implementation of `reticket`; it is the
generic fact needed by any later overlay ticket surgery. -/
public theorem restore_of_base_reticket_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger updated : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (hbound : updated.ParkingAtOrBelow window)
    (hlive : baseOwner ∈ cursor.indexOwners)
    (holdBase : ledger.ticketOf baseOwner = window.parkingTicket)
    (hnewBase : (updated.ticketOf baseOwner).Nonparking)
    (hunchanged : ∀ candidate ∈ cursor.indexOwners, candidate ≠ baseOwner →
      updated.ticketOf candidate = ledger.ticketOf candidate) :
    updated.ParkingBelow window := by
  intro slot hslot
  have hle := hbound slot hslot
  by_contra hnlt
  have hslotBase : slot.val = window.base := Nat.le_antisymm hle (Nat.le_of_not_gt hnlt)
  have hparkingEq : IndexTicket.parking slot = window.parkingTicket := by
    apply Fin.ext
    simp only [IndexTicket.parking_val, ProductiveOwnerWindow.parkingTicket_val]
    omega
  rw [ScheduleCursor.indexTickets] at hslot
  rcases List.mem_map.mp hslot with ⟨candidate, hcandidate, hcandidateTicket⟩
  by_cases hcandidateBase : candidate = baseOwner
  · subst candidate
    exact hnewBase slot hcandidateTicket
  · have holdCandidate : ledger.ticketOf candidate = window.parkingTicket := by
      calc
        ledger.ticketOf candidate = updated.ticketOf candidate :=
          (hunchanged candidate hcandidate hcandidateBase).symm
        _ = IndexTicket.parking slot := hcandidateTicket
        _ = window.parkingTicket := hparkingEq
    exact hcandidateBase (owner_eq_of_parked_ticket hlive holdBase hcandidate
      holdCandidate)

/-- Reticketing the designated base owner to a fresh nonparking target restores the strict
parking bound.  `IndexTicketLedger.reticket` supplies the required unchanged-tail property. -/
public theorem reticket_base_nonparking_restores
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (hlive : baseOwner ∈ cursor.indexOwners)
    (target : IndexTicket input)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (hnonparking : target.Nonparking) :
    (ledger.reticket baseOwner target hlive htargetFresh
      htargetNotScratch).ParkingBelow window := by
  rcases parking.strict_or_parked with hbelow | ⟨_, hbaseTicket⟩
  · exact hbelow.reticket_nonparking baseOwner target hlive htargetFresh
      htargetNotScratch hnonparking
  · let updated := ledger.reticket baseOwner target hlive htargetFresh
      htargetNotScratch
    apply restore_of_base_reticket_nonparking
      (parking.atOrBelow.reticket_nonparking baseOwner target hlive htargetFresh
        htargetNotScratch hnonparking)
      hlive hbaseTicket
    · simpa [updated] using hnonparking
    · intro candidate hcandidate hne
      exact ledger.reticket_ticketOf_eq_of_mem_ne baseOwner target hlive
        htargetFresh htargetNotScratch hcandidate hne

/-- Core targets are nonparking, so reticketing the designated base owner to a fresh core
ticket restores the strict parking bound. -/
public theorem reticket_base_core_restores
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (hlive : baseOwner ∈ cursor.indexOwners)
    (target : IndexTicket input)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (hcore : target.val < 4 * input.length) :
    (ledger.reticket baseOwner target hlive htargetFresh
      htargetNotScratch).ParkingBelow window :=
  parking.reticket_base_nonparking_restores hlive target htargetFresh
    htargetNotScratch (IndexTicket.nonparking_of_core hcore)

/-- Reticketing any live owner to a fresh nonparking target preserves the restorable
invariant.  When the selected owner is the parked base owner, the result takes the strict
branch; otherwise the parked witness is unchanged. -/
public theorem reticket_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (hnonparking : target.Nonparking) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).OverlayParking window baseOwner := by
  refine ⟨parking.atOrBelow.reticket_nonparking owner target howner
    htargetFresh htargetNotScratch hnonparking, ?_⟩
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hbaseTicket⟩
  · exact Or.inl (hbelow.reticket_nonparking owner target howner
      htargetFresh htargetNotScratch hnonparking)
  · by_cases hsame : owner = baseOwner
    · subst owner
      exact Or.inl (parking.reticket_base_nonparking_restores hlive target
        htargetFresh htargetNotScratch hnonparking)
    · refine Or.inr ⟨hlive, ?_⟩
      rw [ledger.reticket_ticketOf_eq_of_mem_ne owner target howner
        htargetFresh htargetNotScratch hlive (Ne.symm hsame)]
      exact hbaseTicket

/-- Releasing an owner other than the designated base owner preserves restorable overlay
parking.  This is the operation used when an unrelated private overlay head is erased. -/
public theorem release_ne
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners))
    (hne : owner ≠ baseOwner) :
    (ledger.release owner hindices).OverlayParking window baseOwner := by
  refine ⟨parking.atOrBelow.release owner hindices, ?_⟩
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hbaseTicket⟩
  · exact Or.inl (hbelow.release owner hindices)
  · have hclass : baseOwner ∈ owner :: new.indexOwners :=
      hindices.mem_iff.mp hlive
    have hliveNew : baseOwner ∈ new.indexOwners := by
      rcases List.mem_cons.mp hclass with heq | hmem
      · exact False.elim (hne heq.symm)
      · exact hmem
    exact Or.inr ⟨hliveNew, hbaseTicket⟩

/-- Releasing the designated parked owner itself restores the strict parking bound.  The
released ticket is absent from the tail by duplicate-freedom, so no remaining owner can carry
the current canonical parking ticket. -/
public theorem release_base_restores
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (hindices : old.indexOwners.Perm (baseOwner :: new.indexOwners)) :
    (ledger.release baseOwner hindices).ParkingBelow window := by
  rcases parking.strict_or_parked with hbelow | ⟨hlive, hbaseTicket⟩
  · exact hbelow.release baseOwner hindices
  · have htailFresh : ledger.ticketOf baseOwner ∉
        new.indexOwners.map ledger.ticketOf := by
      have hperm := hindices.map ledger.ticketOf
      have hcons :
          (ledger.ticketOf baseOwner :: new.indexOwners.map ledger.ticketOf).Nodup :=
        hperm.nodup_iff.mp (by
          simpa [ScheduleCursor.indexTickets] using ledger.tickets_nodup)
      exact (List.nodup_cons.mp hcons).1
    intro slot hslot
    have hle := parking.atOrBelow.release baseOwner hindices slot hslot
    by_contra hnlt
    have hslotBase : slot.val = window.base :=
      Nat.le_antisymm hle (Nat.le_of_not_gt hnlt)
    have hticketEq : IndexTicket.parking slot = ledger.ticketOf baseOwner := by
      rw [hbaseTicket]
      apply Fin.ext
      simp only [IndexTicket.parking_val,
        ProductiveOwnerWindow.parkingTicket_val]
      omega
    apply htailFresh
    rw [ScheduleCursor.indexTickets] at hslot
    simpa [IndexTicketLedger.release_ticketOf, hticketEq] using hslot

/-- Releasing an arbitrary overlay owner preserves restorable parking.  If it is the
designated parked owner, the result moves to the strict branch; otherwise the witness remains
live. -/
public theorem release
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    {baseOwner : Fin (10 * input.length)}
    (parking : ledger.OverlayParking window baseOwner)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    (ledger.release owner hindices).OverlayParking window baseOwner := by
  by_cases hsame : owner = baseOwner
  · subst owner
    exact OverlayParking.ofBelow baseOwner
      (parking.release_base_restores hindices)
  · exact parking.release_ne owner hindices hsame

end OverlayParking
end IndexTicketLedger

end Aho
end IndexedGrammar
