module

public import Langlib.Grammars.Indexed.NormalForm.AhoIndexTickets

@[expose]
public section

/-!
# Core logical tickets

The first `4 * |input|` logical tickets contain the two productive-event banks and the two
temporary tickets.  The larger parking bank was introduced only for the old protected-push
scheduler.  A copy-on-write scheduler never moves a live ticket into that bank.

This file isolates the resulting strict cardinality bound.  If all live tickets are core
tickets, the permanently fresh scratch ticket can be prepended to their duplicate-free list.
Embedding that list into `Fin (4 * |input|)` proves that fewer than `4 * |input|` persistent
indices are live.  In particular the physical pool of `6 * |input|` owners cannot be empty.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

namespace IndexTicketLedger

/-- Every logical ticket currently attached to a persistent physical owner lies below the
parking bank. -/
public def Core
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) : Prop :=
  ∀ ticket ∈ cursor.indexTickets ledger.ticketOf,
    ticket.val < 4 * input.length

/-- The owner-free ticket ledger is core. -/
public theorem core_ofEmpty
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (hinput : 0 < input.length)
    (hempty : cursor.indexOwners = []) :
    (IndexTicketLedger.ofEmpty hinput hempty).Core := by
  intro ticket hticket
  simp [Core, ScheduleCursor.indexTickets, hempty] at hticket

/-- A core ledger has at most `4 * |input| - 1` live tickets, because scratch is core and is
permanently absent. -/
public theorem index_count_add_one_le_four_mul
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (hcore : ledger.Core) (hinput : 0 < input.length) :
    cursor.indexOwners.length + 1 ≤ 4 * input.length := by
  let tickets : List (IndexTicket input) :=
    IndexTicket.scratch hinput :: cursor.indexTickets ledger.ticketOf
  have hticketsNodup : tickets.Nodup := by
    exact List.nodup_cons.mpr
      ⟨ledger.scratch_fresh hinput, ledger.tickets_nodup⟩
  have hticketsCore : ∀ ticket ∈ tickets,
      ticket.val < 4 * input.length := by
    intro ticket hticket
    rcases List.mem_cons.mp hticket with hscratch | hlive
    · subst ticket
      simp only [IndexTicket.scratch_val]
      omega
    · exact hcore ticket hlive
  let encode : Fin tickets.length → Fin (4 * input.length) := fun i =>
    ⟨tickets[i], hticketsCore tickets[i] (List.getElem_mem i.isLt)⟩
  have hencode : Function.Injective encode := by
    intro i j hij
    apply Fin.ext
    apply hticketsNodup.getElem_inj_iff.mp
    apply Fin.ext
    have hvals := congrArg Fin.val hij
    change tickets[i].val = tickets[j].val at hvals
    exact hvals
  have hcard := Fintype.card_le_of_injective encode hencode
  simp only [Fintype.card_fin] at hcard
  simpa [tickets, ScheduleCursor.indexTickets] using hcard

/-- The core-ticket bound is strictly below the `6 * |input|` physical capacity. -/
public theorem index_count_lt_six_mul_of_core
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (hcore : ledger.Core) (hinput : 0 < input.length) :
    cursor.indexOwners.length < 6 * input.length := by
  have hsharp := ledger.index_count_add_one_le_four_mul hcore hinput
  omega

/-- Transport across a physical-owner permutation preserves core tickets. -/
public theorem Core.transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} {ledger : IndexTicketLedger old}
    (hcore : ledger.Core) (hindices : new.indexOwners.Perm old.indexOwners) :
    (ledger.transport hindices).Core := by
  intro ticket hticket
  rw [ScheduleCursor.indexTickets] at hticket
  rcases List.mem_map.mp hticket with ⟨owner, howner, rfl⟩
  apply hcore (ledger.ticketOf owner)
  rw [ScheduleCursor.indexTickets]
  exact List.mem_map.mpr ⟨owner, hindices.mem_iff.mp howner, rfl⟩

/-- Releasing one physical owner preserves core tickets. -/
public theorem Core.release
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} {ledger : IndexTicketLedger old}
    (hcore : ledger.Core) (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    (ledger.release owner hindices).Core := by
  intro ticket hticket
  rw [ScheduleCursor.indexTickets] at hticket
  rcases List.mem_map.mp hticket with ⟨candidate, hcandidate, rfl⟩
  apply hcore (ledger.ticketOf candidate)
  rw [ScheduleCursor.indexTickets]
  exact List.mem_map.mpr ⟨candidate,
    hindices.mem_iff.mpr (List.mem_cons_of_mem owner hcandidate), rfl⟩

/-- Allocating a fresh core target preserves the core-ticket invariant. -/
public theorem Core.allocate
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} {ledger : IndexTicketLedger old}
    (hcore : ledger.Core)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hticketCore : ticket.val < 4 * input.length) :
    (ledger.allocate owner ticket hownerFresh hticketFresh hticketNotScratch
      hindices).Core := by
  intro candidateTicket hcandidateTicket
  rw [ScheduleCursor.indexTickets] at hcandidateTicket
  rcases List.mem_map.mp hcandidateTicket with
    ⟨candidate, hcandidate, rfl⟩
  have hmember := hindices.mem_iff.mp hcandidate
  rcases List.mem_cons.mp hmember with hnew | hold
  · subst candidate
    simpa using hticketCore
  · have hcandidateNe : candidate ≠ owner := by
      intro heq
      subst candidate
      exact hownerFresh hold
    change (ledger.insertTicket owner ticket candidate).val < 4 * input.length
    rw [ledger.insertTicket_eq_of_mem owner ticket hold hownerFresh]
    apply hcore (ledger.ticketOf candidate)
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hold, rfl⟩

/-- Reticketing one live owner to a fresh core target preserves the core-ticket invariant. -/
public theorem Core.reticket
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} {ledger : IndexTicketLedger cursor}
    (hcore : ledger.Core)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (htargetCore : target.val < 4 * input.length) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).Core := by
  intro candidateTicket hcandidateTicket
  rw [ScheduleCursor.indexTickets] at hcandidateTicket
  rcases List.mem_map.mp hcandidateTicket with
    ⟨candidate, hcandidate, rfl⟩
  by_cases hcandidateOwner : candidate = owner
  · subst candidate
    rw [ledger.reticket_ticketOf_owner owner target howner htargetFresh
      htargetNotScratch]
    exact htargetCore
  · rw [ledger.reticket_ticketOf_eq_of_mem_ne owner target howner
      htargetFresh htargetNotScratch hcandidate hcandidateOwner]
    apply hcore (ledger.ticketOf candidate)
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩

end IndexTicketLedger

end Aho
end IndexedGrammar

end
