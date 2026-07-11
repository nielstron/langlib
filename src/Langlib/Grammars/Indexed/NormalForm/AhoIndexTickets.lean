module

public import Langlib.Grammars.Indexed.NormalForm.AhoShadowOwners
public import Mathlib.Data.List.Nodup

@[expose]
public section

/-!
# Logical tickets for persistent compressed indices

Physical index owners are drawn from the reusable generic bank.  A second, ghost-only ticket
ledger gives every live physical owner a distinct element of `Fin (6 * |input|)`.  Keeping the
association in a function, rather than in `ScheduleIndex`, lets the scheduler change physical
owners without changing the finite machine alphabet or the block-layout API.

The important distinction is that the ticket ledger is inductive: allocation extends the
association at one fresh physical owner and demands a genuinely fresh logical ticket.  Thus the
cardinality bound below cannot be manufactured merely by assuming a scalar inequality.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- The logical ticket carrier. Primary productive tickets occupy the first `2|input|-1`
values, shadow tickets the next `2|input|-1`, the next two values are emergency scratch and
transient tickets, and the upper `2|input|` values form an outside-window parking bank.

The parking bank is as large as the complete physical owner pool.  Consequently a live core
ticket and the global `6|input|` index bound certify that some parking ticket is absent, even
while parking tickets belonging to nested protected calls remain live. -/
public abbrev IndexTicket (input : List T) := Fin (6 * input.length)

namespace IndexTicket

/-- The one-step emergency logical scratch ticket. -/
public def scratch {input : List T} (hinput : 0 < input.length) :
    IndexTicket input :=
  ⟨4 * input.length - 2, by omega⟩

@[simp] public theorem scratch_val {input : List T}
    (hinput : 0 < input.length) :
    (scratch hinput : IndexTicket input).val = 4 * input.length - 2 := rfl

/-- The distinguished last logical transient ticket. -/
public def transient {input : List T} (hinput : 0 < input.length) :
    IndexTicket input :=
  ⟨4 * input.length - 1, by omega⟩

@[simp] public theorem transient_val {input : List T}
    (hinput : 0 < input.length) :
    (transient hinput : IndexTicket input).val = 4 * input.length - 1 := rfl

/-- One logical parking ticket. Parking tickets lie above both productive semantic banks. -/
public def parking {input : List T} (slot : Fin (2 * input.length)) :
    IndexTicket input :=
  ⟨4 * input.length + slot.val, by
    have := slot.isLt
    omega⟩

@[simp] public theorem parking_val {input : List T}
    (slot : Fin (2 * input.length)) :
    (parking slot : IndexTicket input).val = 4 * input.length + slot.val := rfl

/-- The complete finite parking bank. -/
public def parkingRange (input : List T) : List (IndexTicket input) :=
  List.ofFn (fun slot : Fin (2 * input.length) => parking slot)

@[simp] public theorem parkingRange_length (input : List T) :
    (parkingRange input).length = 2 * input.length := by
  simp [parkingRange]

public theorem parking_injective {input : List T} :
    Function.Injective (parking (input := input)) := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp only [parking_val] at hval
  omega

public theorem parkingRange_nodup (input : List T) :
    (parkingRange input).Nodup :=
  List.nodup_ofFn.mpr parking_injective

public theorem parking_ne_scratch {input : List T}
    (slot : Fin (2 * input.length)) (hinput : 0 < input.length) :
    parking slot ≠ scratch hinput := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [parking_val, scratch_val] at hval
  omega

public theorem parking_ne_transient {input : List T}
    (slot : Fin (2 * input.length)) (hinput : 0 < input.length) :
    parking slot ≠ transient hinput := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [parking_val, transient_val] at hval
  omega

/-- A ticket is nonparking when it is distinct from every member of the upper parking bank. -/
public def Nonparking {input : List T} (ticket : IndexTicket input) : Prop :=
  ∀ slot : Fin (2 * input.length), ticket ≠ parking slot

/-- Every core ticket lies strictly below, and hence outside, the parking bank. -/
public theorem nonparking_of_core {input : List T} {ticket : IndexTicket input}
    (hcore : ticket.val < 4 * input.length) : ticket.Nonparking := by
  intro slot heq
  have hval := congrArg Fin.val heq
  simp only [parking_val] at hval
  omega

/-- The reserved scratch ticket is nonparking. -/
public theorem scratch_nonparking {input : List T} (hinput : 0 < input.length) :
    (scratch hinput).Nonparking :=
  nonparking_of_core (by simp only [scratch_val]; omega)

/-- The distinguished transient ticket is nonparking. -/
public theorem transient_nonparking {input : List T} (hinput : 0 < input.length) :
    (transient hinput).Nonparking :=
  nonparking_of_core (by simp only [transient_val]; omega)

/-- Interpret a logical ticket in the semantic-owner carrier.  All ticket values, including
the complete parking bank, are retained by the embedding. -/
public def semanticOwner
    {g : IndexedGrammar T} {input : List T}
    (ticket : IndexTicket input) : Fin (10 * input.length) :=
  ⟨ticket.val, by
    have := ticket.isLt
    omega⟩

/-- The semantic interpretation of logical tickets is injective. -/
public theorem semanticOwner_injective
    {g : IndexedGrammar T} {input : List T} :
    Function.Injective (semanticOwner (g := g) (input := input)) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun owner : Fin (10 * input.length) => owner.val) hij

/-- Turn a semantic productive owner into its corresponding logical ticket. -/
public def ofProductiveOwner
    {input : List T}
    (owner : Fin (10 * input.length))
    (hprimary : owner.val < 2 * input.length - 1) : IndexTicket input :=
  ⟨owner.val, by omega⟩

/-- Any semantic primary-or-shadow owner below the two temporary slots is a logical ticket. -/
public def ofSemanticOwner
    {input : List T}
    (owner : Fin (10 * input.length))
    (hbank : owner.val < 4 * input.length - 2) : IndexTicket input :=
  ⟨owner.val, by omega⟩

/-- Every primary productive-owner ticket is nonparking. -/
public theorem ofProductiveOwner_nonparking
    {input : List T} (owner : Fin (10 * input.length))
    (hprimary : owner.val < 2 * input.length - 1) :
    (ofProductiveOwner owner hprimary).Nonparking :=
  nonparking_of_core (by
    change owner.val < 4 * input.length
    omega)

/-- Every primary-or-shadow semantic-owner ticket is nonparking. -/
public theorem ofSemanticOwner_nonparking
    {input : List T} (owner : Fin (10 * input.length))
    (hbank : owner.val < 4 * input.length - 2) :
    (ofSemanticOwner owner hbank).Nonparking :=
  nonparking_of_core (by
    change owner.val < 4 * input.length
    omega)

@[simp] public theorem semanticOwner_ofProductiveOwner
    {g : IndexedGrammar T} {input : List T}
    (owner : Fin (10 * input.length))
    (hprimary : owner.val < 2 * input.length - 1) :
    semanticOwner (g := g) (ofProductiveOwner owner hprimary) = owner := by
  apply Fin.ext
  rfl

@[simp] public theorem semanticOwner_ofSemanticOwner
    {g : IndexedGrammar T} {input : List T}
    (owner : Fin (10 * input.length))
    (hbank : owner.val < 4 * input.length - 2) :
    semanticOwner (g := g) (ofSemanticOwner owner hbank) = owner := by
  apply Fin.ext
  rfl

@[simp] public theorem semanticOwner_scratch
    {g : IndexedGrammar T} {input : List T} (hinput : 0 < input.length) :
    semanticOwner (g := g) (scratch hinput) =
      ProductiveOwnerWindow.scratchOwner (g := g) hinput := by
  apply Fin.ext
  rfl

@[simp] public theorem semanticOwner_transient
    {g : IndexedGrammar T} {input : List T} (hinput : 0 < input.length) :
    semanticOwner (g := g) (transient hinput) =
      ProductiveOwnerWindow.transientOwner (g := g) hinput := by
  apply Fin.ext
  rfl

@[simp] public theorem semanticOwner_transient_val
    {g : IndexedGrammar T} {input : List T} (hinput : 0 < input.length) :
    (semanticOwner (g := g) (transient hinput)).val =
      4 * input.length - 1 := rfl

end IndexTicket

namespace ProductiveOwnerWindow

/-- The logical ticket of the child depth-one event exposed by a unary push. -/
public def pushChildEventTicketOne
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) : IndexTicket input :=
  IndexTicket.ofProductiveOwner (window.pushChild.eventOwner 1 hone) (by
    have hlocal := rest.eventOwnerNat_lt_productiveCount hone
    have hend := window.end_le
    simp only [ProductiveOwnerWindow.eventOwner_val,
      ProductiveOwnerWindow.pushChild_base]
    simp only [NFParse.productiveCount, NFParse.binaryCount,
      NFParse.terminalCount] at hlocal hend
    omega)

@[simp] public theorem semanticOwner_pushChildEventTicketOne
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) :
    IndexTicket.semanticOwner (g := g) (window.pushChildEventTicketOne hone) =
      window.pushChild.eventOwner 1 hone := by
  simp [pushChildEventTicketOne]

/-- The child depth-one productive-event ticket lies below the parking bank. -/
public theorem pushChildEventTicketOne_nonparking
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) :
    (window.pushChildEventTicketOne hone).Nonparking := by
  apply IndexTicket.nonparking_of_core
  have hlocal := rest.eventOwnerNat_lt_productiveCount hone
  have hend := window.end_le
  simp only [pushChildEventTicketOne, IndexTicket.ofProductiveOwner,
    ProductiveOwnerWindow.eventOwner_val,
    ProductiveOwnerWindow.pushChild_base]
  simp only [NFParse.productiveCount, NFParse.binaryCount,
    NFParse.terminalCount] at hlocal hend
  omega

/-- The logical shadow ticket attached to one productive event. -/
public def shadowEventTicket
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (d : ℕ) (hd : d ∈ parse.eventDepths) : IndexTicket input :=
  IndexTicket.ofSemanticOwner (window.shadowEventOwner d hd) (by
    have hlocal := parse.eventOwnerNat_lt_productiveCount hd
    have hend := window.end_le
    simp only [ProductiveOwnerWindow.shadowEventOwner_val, shadowOwnerOffset]
    omega)

@[simp] public theorem semanticOwner_shadowEventTicket
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (d : ℕ) (hd : d ∈ parse.eventDepths) :
    IndexTicket.semanticOwner (g := g) (window.shadowEventTicket d hd) =
      window.shadowEventOwner d hd := by
  simp [shadowEventTicket]

/-- Every shadow-event ticket lies below the parking bank. -/
public theorem shadowEventTicket_nonparking
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (d : ℕ) (hd : d ∈ parse.eventDepths) :
    (window.shadowEventTicket d hd).Nonparking := by
  apply IndexTicket.nonparking_of_core
  have hlocal := parse.eventOwnerNat_lt_productiveCount hd
  have hend := window.end_le
  simp only [shadowEventTicket, IndexTicket.ofSemanticOwner,
    ProductiveOwnerWindow.shadowEventOwner_val, shadowOwnerOffset]
  omega

/-- The canonical parking slot of a productive window is its root-relative base. -/
public def parkingSlot
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse) :
    Fin (2 * input.length) :=
  ⟨window.base, by
    have hend := window.end_le
    have hyield := parse.yield_length_pos
    rw [parse.productiveCount_eq_twice_yield_length_sub_one] at hend
    omega⟩

@[simp] public theorem parkingSlot_val
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse) :
    window.parkingSlot.val = window.base := rfl

/-- The canonical logical parking ticket associated with a productive window. -/
public def parkingTicket
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse) : IndexTicket input :=
  IndexTicket.parking window.parkingSlot

@[simp] public theorem parkingTicket_val
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse) :
    window.parkingTicket.val = 4 * input.length + window.base := rfl

end ProductiveOwnerWindow

/-- Logical tickets currently present on the work tape, read through an owner-to-ticket
association. -/
public def ScheduleCursor.indexTickets
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (ticketOf : Fin (10 * input.length) → IndexTicket input) :
    List (IndexTicket input) :=
  cursor.indexOwners.map ticketOf

@[simp] public theorem ScheduleCursor.indexTickets_length
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (ticketOf : Fin (10 * input.length) → IndexTicket input) :
    (cursor.indexTickets ticketOf).length = cursor.indexOwners.length := by
  simp [ScheduleCursor.indexTickets]

/-! ### Ghost-only semantic projection -/

/-- Replace only the owner annotation of a compressed index.  This local copy deliberately
does not import the later physical-owner relabelling module, so ticket resources remain usable
by `AhoScheduleResources` without an import cycle. -/
public def ScheduleIndex.withTicketOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    ScheduleIndex g input where
  flags := idx.flags
  relation := idx.relation
  mark := idx.mark
  denotes := idx.denotes
  owner := owner

@[simp] public theorem ScheduleIndex.withTicketOwner_owner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (idx : ScheduleIndex g input) (owner : Fin (10 * input.length)) :
    (idx.withTicketOwner owner).owner = owner := rfl

/-- Relabel index and matching frame annotations for the semantic ticket view. -/
public def ScheduleAtom.relabelTicketOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    ScheduleAtom g input → ScheduleAtom g input
  | .index idx => .index (idx.withTicketOwner (f idx.owner))
  | .close owner => .close (f owner)
  | atom => atom

@[simp] public theorem ScheduleAtom.indexOwner?_relabelTicketOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.relabelTicketOwner f).indexOwner? = atom.indexOwner?.map f := by
  cases atom <;> rfl

@[simp] public theorem ScheduleAtom.closeOwner?_relabelTicketOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (atom : ScheduleAtom g input) :
    (atom.relabelTicketOwner f).closeOwner? = atom.closeOwner?.map f := by
  cases atom <;> rfl

@[simp] public theorem ScheduleAtom.filterMap_indexOwner_relabelTicketOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (word : List (ScheduleAtom g input)) :
    (word.map (ScheduleAtom.relabelTicketOwner f)).filterMap
        ScheduleAtom.indexOwner? =
      (word.filterMap ScheduleAtom.indexOwner?).map f := by
  induction word with
  | nil => rfl
  | cons atom word ih =>
      rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, ih]
      cases atom <;>
        simp [ScheduleAtom.relabelTicketOwner, ScheduleAtom.indexOwner?]

@[simp] public theorem ScheduleAtom.filterMap_closeOwner_relabelTicketOwner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (f : Fin (10 * input.length) → Fin (10 * input.length))
    (word : List (ScheduleAtom g input)) :
    (word.map (ScheduleAtom.relabelTicketOwner f)).filterMap
        ScheduleAtom.closeOwner? =
      (word.filterMap ScheduleAtom.closeOwner?).map f := by
  induction word with
  | nil => rfl
  | cons atom word ih =>
      rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, ih]
      cases atom <;>
        simp [ScheduleAtom.relabelTicketOwner, ScheduleAtom.closeOwner?]

/-- A virtual cursor whose owner annotations are the semantic images of logical tickets. -/
public def ScheduleCursor.relabelTicketOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    ScheduleCursor g input :=
  ⟨cursor.left.map (ScheduleAtom.relabelTicketOwner f),
    cursor.focus.relabelTicketOwner f,
    cursor.right.map (ScheduleAtom.relabelTicketOwner f)⟩

@[simp] public theorem ScheduleCursor.relabelTicketOwners_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelTicketOwners f).indexOwners = cursor.indexOwners.map f := by
  simp only [ScheduleCursor.indexOwners, ScheduleCursor.word,
    ScheduleCursor.relabelTicketOwners, List.map_append, List.map_cons,
    List.filterMap_append, ScheduleAtom.filterMap_indexOwner_relabelTicketOwner,
    List.filterMap_cons, List.filterMap_nil,
    ScheduleAtom.indexOwner?_relabelTicketOwner]
  cases cursor.focus <;> simp [ScheduleAtom.relabelTicketOwner,
    ScheduleAtom.indexOwner?]

@[simp] public theorem ScheduleCursor.relabelTicketOwners_frameOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input)
    (f : Fin (10 * input.length) → Fin (10 * input.length)) :
    (cursor.relabelTicketOwners f).frameOwners = cursor.frameOwners.map f := by
  simp only [ScheduleCursor.frameOwners, ScheduleCursor.word,
    ScheduleCursor.relabelTicketOwners, List.map_append, List.map_cons,
    List.filterMap_append, ScheduleAtom.filterMap_closeOwner_relabelTicketOwner,
    List.filterMap_cons, List.filterMap_nil,
    ScheduleAtom.closeOwner?_relabelTicketOwner]
  cases cursor.focus <;> simp [ScheduleAtom.relabelTicketOwner,
    ScheduleAtom.closeOwner?]

/-- An injective logical-ticket assignment for all persistent physical owners in a cursor. -/
public structure IndexTicketLedger
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) where
  ticketOf : Fin (10 * input.length) → IndexTicket input
  tickets_nodup : (cursor.indexTickets ticketOf).Nodup
  scratch_fresh : ∀ hinput : 0 < input.length,
    IndexTicket.scratch hinput ∉ cursor.indexTickets ticketOf

namespace IndexTicketLedger

/-- Apply one logical-ticket transposition to every persistent index.  This is a ghost-only
operation: injectivity is preserved by the permutation, and the explicit side conditions say
that the reserved scratch ticket is fixed. -/
public def swapTickets
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (left right : IndexTicket input)
    (hleft : ∀ hinput : 0 < input.length,
      left ≠ IndexTicket.scratch hinput)
    (hright : ∀ hinput : 0 < input.length,
      right ≠ IndexTicket.scratch hinput) :
    IndexTicketLedger cursor where
  ticketOf := fun owner => Equiv.swap left right (ledger.ticketOf owner)
  tickets_nodup := by
    simpa [ScheduleCursor.indexTickets, List.map_map, Function.comp_def] using
      ledger.tickets_nodup.map (Equiv.swap left right).injective
  scratch_fresh := by
    intro hinput hmem
    rw [ScheduleCursor.indexTickets] at hmem
    change IndexTicket.scratch hinput ∈ cursor.indexOwners.map
      (fun owner => Equiv.swap left right (ledger.ticketOf owner)) at hmem
    rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
    rw [Equiv.swap_apply_eq_iff] at heq
    have hfix : Equiv.swap left right (IndexTicket.scratch hinput) =
        IndexTicket.scratch hinput :=
      Equiv.swap_apply_of_ne_of_ne (hleft hinput).symm (hright hinput).symm
    rw [hfix] at heq
    apply ledger.scratch_fresh hinput
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨owner, howner, heq⟩

@[simp] public theorem swapTickets_ticketOf
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (left right : IndexTicket input)
    (hleft : ∀ hinput : 0 < input.length,
      left ≠ IndexTicket.scratch hinput)
    (hright : ∀ hinput : 0 < input.length,
      right ≠ IndexTicket.scratch hinput)
    (owner : Fin (10 * input.length)) :
    (ledger.swapTickets left right hleft hright).ticketOf owner =
      Equiv.swap left right (ledger.ticketOf owner) := rfl

/-- Every live parking ticket has a slot strictly below the active productive-window base. -/
public def ParkingBelow
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    (ledger : IndexTicketLedger cursor)
    (window : ProductiveOwnerWindow (input := input) parse) : Prop :=
  ∀ slot : Fin (2 * input.length),
    IndexTicket.parking slot ∈ cursor.indexTickets ledger.ticketOf →
      slot.val < window.base

/-- Every live parking ticket has a slot at or below the active productive-window base. -/
public def ParkingAtOrBelow
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    (ledger : IndexTicketLedger cursor)
    (window : ProductiveOwnerWindow (input := input) parse) : Prop :=
  ∀ slot : Fin (2 * input.length),
    IndexTicket.parking slot ∈ cursor.indexTickets ledger.ticketOf →
      slot.val ≤ window.base

/-- A strict parking bound also supplies the corresponding non-strict bound. -/
public theorem ParkingBelow.toAtOrBelow
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbelow : ledger.ParkingBelow window) : ledger.ParkingAtOrBelow window := by
  intro slot hslot
  exact Nat.le_of_lt (hbelow slot hslot)

/-- The canonical window-base parking ticket is fresh under a strict parking bound. -/
public theorem ParkingBelow.parkingTicket_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbelow : ledger.ParkingBelow window) :
    window.parkingTicket ∉ cursor.indexTickets ledger.ticketOf := by
  intro hmem
  have hlt := hbelow window.parkingSlot (by
    simpa [ProductiveOwnerWindow.parkingTicket] using hmem)
  simpa using hlt

/-- Increasing the productive-window base preserves a strict parking bound. -/
public theorem ParkingBelow.mono
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A₁ A₂ : g.nt} {stack₁ stack₂ : List g.flag} {w₁ w₂ : List T}
    {parse₁ : NFParse g A₁ stack₁ w₁}
    {parse₂ : NFParse g A₂ stack₂ w₂}
    {cursor : ScheduleCursor g input} {ledger : IndexTicketLedger cursor}
    {oldWindow : ProductiveOwnerWindow (input := input) parse₁}
    {newWindow : ProductiveOwnerWindow (input := input) parse₂}
    (hbelow : ledger.ParkingBelow oldWindow)
    (hbase : oldWindow.base ≤ newWindow.base) :
    ledger.ParkingBelow newWindow := by
  intro slot hslot
  exact lt_of_lt_of_le (hbelow slot hslot) hbase

/-- Increasing the productive-window base preserves a non-strict parking bound. -/
public theorem ParkingAtOrBelow.mono
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A₁ A₂ : g.nt} {stack₁ stack₂ : List g.flag} {w₁ w₂ : List T}
    {parse₁ : NFParse g A₁ stack₁ w₁}
    {parse₂ : NFParse g A₂ stack₂ w₂}
    {cursor : ScheduleCursor g input} {ledger : IndexTicketLedger cursor}
    {oldWindow : ProductiveOwnerWindow (input := input) parse₁}
    {newWindow : ProductiveOwnerWindow (input := input) parse₂}
    (hbound : ledger.ParkingAtOrBelow oldWindow)
    (hbase : oldWindow.base ≤ newWindow.base) :
    ledger.ParkingAtOrBelow newWindow := by
  intro slot hslot
  exact le_trans (hbound slot hslot) hbase

/-- A strict increase of the productive-window base turns `AtOrBelow` back into `Below`. -/
public theorem ParkingAtOrBelow.toBelow_of_base_lt
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A₁ A₂ : g.nt} {stack₁ stack₂ : List g.flag} {w₁ w₂ : List T}
    {parse₁ : NFParse g A₁ stack₁ w₁}
    {parse₂ : NFParse g A₂ stack₂ w₂}
    {cursor : ScheduleCursor g input} {ledger : IndexTicketLedger cursor}
    {oldWindow : ProductiveOwnerWindow (input := input) parse₁}
    {newWindow : ProductiveOwnerWindow (input := input) parse₂}
    (hbound : ledger.ParkingAtOrBelow oldWindow)
    (hbase : oldWindow.base < newWindow.base) :
    ledger.ParkingBelow newWindow := by
  intro slot hslot
  exact lt_of_le_of_lt (hbound slot hslot) hbase

/-- The unique useful ticket state for an owner-free cursor.  The association away from live
owners is deliberately arbitrary; choosing the transient ticket makes the root construction
uniform. -/
public def ofEmpty
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (hinput : 0 < input.length)
    (hempty : cursor.indexOwners = []) : IndexTicketLedger cursor where
  ticketOf := fun _ => IndexTicket.transient hinput
  tickets_nodup := by
    simp [ScheduleCursor.indexTickets, hempty]
  scratch_fresh := by
    intro _
    simp [ScheduleCursor.indexTickets, hempty]

/-- The owner-free ledger satisfies every strict window-relative parking bound. -/
public theorem parkingBelow_ofEmpty
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    (hinput : 0 < input.length) (hempty : cursor.indexOwners = [])
    (window : ProductiveOwnerWindow (input := input) parse) :
    (IndexTicketLedger.ofEmpty hinput hempty).ParkingBelow window := by
  intro slot hmem
  simp [ScheduleCursor.indexTickets, hempty] at hmem

/-- Live physical owners inherit injectivity from the duplicate-free ticket image. -/
public theorem ticketOf_injectiveOn
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    {left right : Fin (10 * input.length)}
    (hleft : left ∈ cursor.indexOwners) (hright : right ∈ cursor.indexOwners)
    (heq : ledger.ticketOf left = ledger.ticketOf right) : left = right := by
  have hnodup : (cursor.indexOwners.map ledger.ticketOf).Nodup := by
    simpa [ScheduleCursor.indexTickets] using ledger.tickets_nodup
  exact List.inj_on_of_nodup_map hnodup hleft hright heq

/-- Interpret one physical owner through the ledger's logical ticket. -/
public def semanticOwnerOf
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) : Fin (10 * input.length) :=
  IndexTicket.semanticOwner (g := g) (ledger.ticketOf owner)

/-- The virtual cursor on which the existing productive-owner ledger can be reused unchanged.
Both compressed indices and their matching frame closes are projected. -/
public def semanticCursor
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    ScheduleCursor g input :=
  cursor.relabelTicketOwners ledger.semanticOwnerOf

@[simp] public theorem semanticCursor_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    ledger.semanticCursor.indexOwners =
      (cursor.indexTickets ledger.ticketOf).map
        (IndexTicket.semanticOwner (g := g)) := by
  simp [semanticCursor, semanticOwnerOf, ScheduleCursor.indexTickets,
    Function.comp_def]

@[simp] public theorem semanticCursor_frameOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    ledger.semanticCursor.frameOwners =
      cursor.frameOwners.map ledger.semanticOwnerOf := by
  simp [semanticCursor]

@[simp] public theorem semanticCursor_right
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    ledger.semanticCursor.right =
      cursor.right.map (ScheduleAtom.relabelTicketOwner ledger.semanticOwnerOf) := rfl

@[simp] public theorem semanticCursor_left
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    ledger.semanticCursor.left =
      cursor.left.map (ScheduleAtom.relabelTicketOwner ledger.semanticOwnerOf) := rfl

@[simp] public theorem semanticCursor_right_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    ledger.semanticCursor.right.filterMap ScheduleAtom.indexOwner? =
      (cursor.right.filterMap ScheduleAtom.indexOwner?).map
        ledger.semanticOwnerOf := by
  change
    (cursor.right.map
      (ScheduleAtom.relabelTicketOwner ledger.semanticOwnerOf)).filterMap
        ScheduleAtom.indexOwner? = _
  exact ScheduleAtom.filterMap_indexOwner_relabelTicketOwner
    ledger.semanticOwnerOf cursor.right

@[simp] public theorem semanticCursor_focus_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    [ledger.semanticCursor.focus].filterMap ScheduleAtom.indexOwner? =
      ([cursor.focus].filterMap ScheduleAtom.indexOwner?).map
        ledger.semanticOwnerOf := by
  change
    [cursor.focus.relabelTicketOwner ledger.semanticOwnerOf].filterMap
      ScheduleAtom.indexOwner? = _
  cases cursor.focus <;>
    simp [ScheduleAtom.relabelTicketOwner, ScheduleAtom.indexOwner?]

/-- Membership in the virtual semantic cursor is exactly membership of the corresponding
logical ticket in the physical cursor. -/
public theorem semanticOwner_mem_indexOwners_iff
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (ticket : IndexTicket input) :
    IndexTicket.semanticOwner (g := g) ticket ∈ ledger.semanticCursor.indexOwners ↔
      ticket ∈ cursor.indexTickets ledger.ticketOf := by
  rw [ledger.semanticCursor_indexOwners]
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
    have hticket : candidate = ticket :=
      IndexTicket.semanticOwner_injective heq
    simpa [hticket] using hcandidate
  · intro hmem
    exact List.mem_map.mpr ⟨ticket, hmem, rfl⟩

/-- Negative form used directly after an existing productive-owner freshness theorem. -/
public theorem ticket_not_mem_of_semanticOwner_not_mem
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    {ticket : IndexTicket input}
    (hfresh : IndexTicket.semanticOwner (g := g) ticket ∉
      ledger.semanticCursor.indexOwners) :
    ticket ∉ cursor.indexTickets ledger.ticketOf := by
  simpa only [ledger.semanticOwner_mem_indexOwners_iff ticket] using hfresh

/-- Map an aligned physical-owner list into its productive-owner ticket view. -/
public def semanticOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owners : List (Fin (10 * input.length))) : List (Fin (10 * input.length)) :=
  owners.map ledger.semanticOwnerOf

/-- Reuse the existing event-owned block layout on the semantic ticket projection. -/
public abbrev EventTicketLayout
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length))) : Type :=
  EventOwnedLayout parse window blocks (ledger.semanticOwners owners)

/-- Reuse the existing shadow-start layout on the semantic ticket projection. -/
public abbrev ShadowTicketLayout
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length))) : Prop :=
  ShadowStartLayout parse window blocks (ledger.semanticOwners owners)

/-- Reuse the complete cursor-level productive-owner ledger on the semantic ticket cursor. -/
public abbrev SemanticScheduleOwnerLedger
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) : Type :=
  ScheduleOwnerLedger parse window ledger.semanticCursor

/-- Reuse the complete cursor-level shadow ledger on the semantic ticket cursor. -/
public abbrev SemanticShadowOwnerLedger
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) : Type :=
  ShadowOwnerLedger parse window ledger.semanticCursor

/-- The owner-to-ticket association used after allocating one physical owner. -/
public def insertTicket
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input) :
    Fin (10 * input.length) → IndexTicket input :=
  fun candidate => if candidate = owner then ticket else ledger.ticketOf candidate

@[simp] public theorem insertTicket_self
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input) :
    ledger.insertTicket owner ticket owner = ticket := by
  simp [insertTicket]

public theorem insertTicket_eq_of_mem
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    {candidate : Fin (10 * input.length)}
    (hcandidate : candidate ∈ cursor.indexOwners)
    (hfresh : owner ∉ cursor.indexOwners) :
    ledger.insertTicket owner ticket candidate = ledger.ticketOf candidate := by
  have hne : candidate ≠ owner := by
    intro heq
    exact hfresh (heq ▸ hcandidate)
  simp [insertTicket, hne]

/-- Allocate a fresh physical owner and attach a fresh logical ticket to it. -/
public def allocate
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    IndexTicketLedger new where
  ticketOf := ledger.insertTicket owner ticket
  tickets_nodup := by
    have holdMap : old.indexOwners.map (ledger.insertTicket owner ticket) =
        old.indexOwners.map ledger.ticketOf := by
      apply List.map_congr_left
      intro candidate hcandidate
      exact ledger.insertTicket_eq_of_mem owner ticket hcandidate hownerFresh
    have hperm := hindices.map (ledger.insertTicket owner ticket)
    have hperm' :
        (new.indexOwners.map (ledger.insertTicket owner ticket)).Perm
          (ticket :: old.indexOwners.map ledger.ticketOf) := by
      simpa [holdMap] using hperm
    apply hperm'.nodup_iff.mpr
    exact List.nodup_cons.mpr ⟨hticketFresh, ledger.tickets_nodup⟩
  scratch_fresh := by
    intro hinput hmem
    have holdMap : old.indexOwners.map (ledger.insertTicket owner ticket) =
        old.indexOwners.map ledger.ticketOf := by
      apply List.map_congr_left
      intro candidate hcandidate
      exact ledger.insertTicket_eq_of_mem owner ticket hcandidate hownerFresh
    have hperm := hindices.map (ledger.insertTicket owner ticket)
    have hperm' :
        (new.indexOwners.map (ledger.insertTicket owner ticket)).Perm
          (ticket :: old.indexOwners.map ledger.ticketOf) := by
      simpa [holdMap] using hperm
    have hclass := hperm'.mem_iff.mp (by
      simpa [ScheduleCursor.indexTickets] using hmem)
    rcases List.mem_cons.mp hclass with heq | hold
    · exact hticketNotScratch hinput heq.symm
    · exact ledger.scratch_fresh hinput (by
        simpa [ScheduleCursor.indexTickets] using hold)

@[simp] public theorem allocate_ticketOf_self
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners)) :
    (ledger.allocate owner ticket hownerFresh hticketFresh hticketNotScratch
      hindices).ticketOf owner =
      ticket := by
  simp [allocate]

/-- If a ticket absent from the old cursor appears after one fresh-owner allocation, it must
be the ticket assigned to the new owner. -/
public theorem allocate_ticket_eq_of_mem_of_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length)) (ticket fresh : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hfresh : fresh ∉ old.indexTickets ledger.ticketOf)
    (hmem : fresh ∈ new.indexTickets
      (ledger.allocate owner ticket hownerFresh hticketFresh
        hticketNotScratch hindices).ticketOf) :
    ticket = fresh := by
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  rcases List.mem_cons.mp (hindices.mem_iff.mp hcandidate) with hnew | hold
  · subst candidate
    simpa using heq
  · have hsame :
        (ledger.allocate owner ticket hownerFresh hticketFresh
          hticketNotScratch hindices).ticketOf candidate =
          ledger.ticketOf candidate := by
      simpa [allocate] using
        ledger.insertTicket_eq_of_mem owner ticket hold hownerFresh
    apply False.elim
    apply hfresh
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hold, hsame.symm.trans heq⟩

/-- Allocating a different ticket preserves freshness of every ticket absent from the old
cursor. -/
public theorem allocate_preserves_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length)) (ticket fresh : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hfresh : fresh ∉ old.indexTickets ledger.ticketOf)
    (hne : fresh ≠ ticket) :
    fresh ∉ new.indexTickets
      (ledger.allocate owner ticket hownerFresh hticketFresh
        hticketNotScratch hindices).ticketOf := by
  intro hmem
  exact hne (ledger.allocate_ticket_eq_of_mem_of_fresh owner ticket fresh
    hownerFresh hticketFresh hticketNotScratch hindices hfresh hmem).symm

/-- Transport tickets across a cursor change which preserves physical owners up to
permutation. -/
public def transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (hindices : new.indexOwners.Perm old.indexOwners) :
    IndexTicketLedger new where
  ticketOf := ledger.ticketOf
  tickets_nodup :=
    (hindices.map ledger.ticketOf).nodup_iff.mpr ledger.tickets_nodup
  scratch_fresh := by
    intro hinput hmem
    apply ledger.scratch_fresh hinput
    have hperm := hindices.map ledger.ticketOf
    exact hperm.mem_iff.mp (by
      simpa [ScheduleCursor.indexTickets] using hmem)

/-- Releasing one physical owner preserves injectivity on the remaining owners. -/
public def release
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    IndexTicketLedger new where
  ticketOf := ledger.ticketOf
  tickets_nodup := by
    have hperm := hindices.map ledger.ticketOf
    have hcons :
        (ledger.ticketOf owner :: new.indexOwners.map ledger.ticketOf).Nodup :=
      hperm.nodup_iff.mp ledger.tickets_nodup
    exact (List.nodup_cons.mp hcons).2
  scratch_fresh := by
    intro hinput hmem
    apply ledger.scratch_fresh hinput
    have hperm := hindices.map ledger.ticketOf
    have htail : IndexTicket.scratch hinput ∈
        new.indexOwners.map ledger.ticketOf := by
      simpa [ScheduleCursor.indexTickets] using hmem
    exact hperm.mem_iff.mpr (List.mem_cons_of_mem _ htail)

@[simp] public theorem release_ticketOf
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    (ledger.release owner hindices).ticketOf = ledger.ticketOf := rfl

@[simp] public theorem release_semanticOwnerOf
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (ledger : IndexTicketLedger old)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners))
    (candidate : Fin (10 * input.length)) :
    (ledger.release owner hindices).semanticOwnerOf candidate =
      ledger.semanticOwnerOf candidate := rfl

/-- Reticket one live physical owner by swapping its old logical ticket with a fresh target.
Because live tickets are duplicate-free and the target is absent, only that owner changes on
the projected cursor; applying the same map to frame closes keeps owner matching coherent. -/
public def reticket
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput) :
    IndexTicketLedger cursor where
  ticketOf := fun candidate =>
    Equiv.swap (ledger.ticketOf owner) target (ledger.ticketOf candidate)
  tickets_nodup := by
    have hinjective : Function.Injective
        (Equiv.swap (ledger.ticketOf owner) target) :=
      (Equiv.swap (ledger.ticketOf owner) target).injective
    simpa [ScheduleCursor.indexTickets, List.map_map, Function.comp_def] using
      ledger.tickets_nodup.map hinjective
  scratch_fresh := by
    intro hinput hmem
    have holdTicket : ledger.ticketOf owner ∈
        cursor.indexTickets ledger.ticketOf := by
      exact List.mem_map.mpr ⟨owner, howner, rfl⟩
    have holdNeScratch : ledger.ticketOf owner ≠ IndexTicket.scratch hinput := by
      intro heq
      exact ledger.scratch_fresh hinput (heq ▸ holdTicket)
    have htargetNeScratch := htargetNotScratch hinput
    have hswapScratch :
        Equiv.swap (ledger.ticketOf owner) target (IndexTicket.scratch hinput) =
          IndexTicket.scratch hinput := by
      exact Equiv.swap_apply_of_ne_of_ne holdNeScratch.symm htargetNeScratch.symm
    rw [ScheduleCursor.indexTickets] at hmem
    simp only [List.mem_map] at hmem
    rcases hmem with ⟨candidate, hcandidate, heq⟩
    have heq' := congrArg (Equiv.swap (ledger.ticketOf owner) target) heq
    simp only [Equiv.swap_apply_self, hswapScratch] at heq'
    exact ledger.scratch_fresh hinput (by
      rw [ScheduleCursor.indexTickets]
      exact List.mem_map.mpr ⟨candidate, hcandidate, heq'⟩)

@[simp] public theorem reticket_ticketOf_owner
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).ticketOf owner = target := by
  simp [reticket]

/-- Reticketing one live owner leaves every other live owner association unchanged. -/
public theorem reticket_ticketOf_eq_of_mem_ne
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    {candidate : Fin (10 * input.length)}
    (hcandidate : candidate ∈ cursor.indexOwners) (hne : candidate ≠ owner) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).ticketOf candidate =
      ledger.ticketOf candidate := by
  have holdNe : ledger.ticketOf candidate ≠ ledger.ticketOf owner := by
    intro heq
    exact hne (ledger.ticketOf_injectiveOn hcandidate howner heq)
  have htargetNe : ledger.ticketOf candidate ≠ target := by
    intro heq
    apply htargetFresh
    exact List.mem_map.mpr ⟨candidate, hcandidate, heq⟩
  exact Equiv.swap_apply_of_ne_of_ne holdNe htargetNe

/-- After reticketing to a fresh target, the old ticket is absent from the live cursor. -/
public theorem reticket_old_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput) :
    ledger.ticketOf owner ∉ cursor.indexTickets
      (ledger.reticket owner target howner htargetFresh
        htargetNotScratch).ticketOf := by
  intro hmem
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  have heq' := congrArg (Equiv.swap (ledger.ticketOf owner) target) heq
  simp only [reticket, Equiv.swap_apply_self, Equiv.swap_apply_left] at heq'
  apply htargetFresh
  rw [ScheduleCursor.indexTickets]
  exact List.mem_map.mpr ⟨candidate, hcandidate, heq'⟩

/-! ### Preservation of window-relative parking bounds -/

/-- Swapping two nonparking tickets preserves a strict parking bound. -/
public theorem ParkingBelow.swapTickets_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (left right : IndexTicket input)
    (hleft : ∀ hinput : 0 < input.length,
      left ≠ IndexTicket.scratch hinput)
    (hright : ∀ hinput : 0 < input.length,
      right ≠ IndexTicket.scratch hinput)
    (hleftNonparking : left.Nonparking)
    (hrightNonparking : right.Nonparking) :
    (ledger.swapTickets left right hleft hright).ParkingBelow window := by
  intro slot hmem
  apply hbound slot
  rw [ScheduleCursor.indexTickets] at hmem ⊢
  rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
  have heq' := congrArg (Equiv.swap left right) heq
  have hfix : Equiv.swap left right (IndexTicket.parking slot) =
      IndexTicket.parking slot :=
    Equiv.swap_apply_of_ne_of_ne
      (hleftNonparking slot).symm (hrightNonparking slot).symm
  simp only [swapTickets_ticketOf, Equiv.swap_apply_self, hfix] at heq'
  exact List.mem_map.mpr ⟨owner, howner, heq'⟩

/-- Swapping two nonparking tickets preserves a non-strict parking bound. -/
public theorem ParkingAtOrBelow.swapTickets_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingAtOrBelow window)
    (left right : IndexTicket input)
    (hleft : ∀ hinput : 0 < input.length,
      left ≠ IndexTicket.scratch hinput)
    (hright : ∀ hinput : 0 < input.length,
      right ≠ IndexTicket.scratch hinput)
    (hleftNonparking : left.Nonparking)
    (hrightNonparking : right.Nonparking) :
    (ledger.swapTickets left right hleft hright).ParkingAtOrBelow window := by
  intro slot hmem
  apply hbound slot
  rw [ScheduleCursor.indexTickets] at hmem ⊢
  rcases List.mem_map.mp hmem with ⟨owner, howner, heq⟩
  have heq' := congrArg (Equiv.swap left right) heq
  have hfix : Equiv.swap left right (IndexTicket.parking slot) =
      IndexTicket.parking slot :=
    Equiv.swap_apply_of_ne_of_ne
      (hleftNonparking slot).symm (hrightNonparking slot).symm
  simp only [swapTickets_ticketOf, Equiv.swap_apply_self, hfix] at heq'
  exact List.mem_map.mpr ⟨owner, howner, heq'⟩

/-- Transport across a physical-owner permutation preserves strict parking bounds. -/
public theorem ParkingBelow.transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (hindices : new.indexOwners.Perm old.indexOwners) :
    (ledger.transport hindices).ParkingBelow window := by
  intro slot hmem
  apply hbound slot
  have hnew : IndexTicket.parking slot ∈
      new.indexOwners.map ledger.ticketOf := by
    simpa [ScheduleCursor.indexTickets, IndexTicketLedger.transport] using hmem
  have hold := (hindices.map ledger.ticketOf).mem_iff.mp hnew
  simpa [ScheduleCursor.indexTickets] using hold

/-- Transport across a physical-owner permutation preserves non-strict parking bounds. -/
public theorem ParkingAtOrBelow.transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingAtOrBelow window)
    (hindices : new.indexOwners.Perm old.indexOwners) :
    (ledger.transport hindices).ParkingAtOrBelow window := by
  intro slot hmem
  apply hbound slot
  have hnew : IndexTicket.parking slot ∈
      new.indexOwners.map ledger.ticketOf := by
    simpa [ScheduleCursor.indexTickets, IndexTicketLedger.transport] using hmem
  have hold := (hindices.map ledger.ticketOf).mem_iff.mp hnew
  simpa [ScheduleCursor.indexTickets] using hold

/-- Transport followed by a weak base increase preserves a strict parking bound. -/
public theorem ParkingBelow.transport_mono
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A₁ A₂ : g.nt} {stack₁ stack₂ : List g.flag} {w₁ w₂ : List T}
    {parse₁ : NFParse g A₁ stack₁ w₁}
    {parse₂ : NFParse g A₂ stack₂ w₂}
    {old new : ScheduleCursor g input} {ledger : IndexTicketLedger old}
    {oldWindow : ProductiveOwnerWindow (input := input) parse₁}
    {newWindow : ProductiveOwnerWindow (input := input) parse₂}
    (hbound : ledger.ParkingBelow oldWindow)
    (hindices : new.indexOwners.Perm old.indexOwners)
    (hbase : oldWindow.base ≤ newWindow.base) :
    (ledger.transport hindices).ParkingBelow newWindow :=
  (hbound.transport hindices).mono hbase

/-- Transport followed by a weak base increase preserves a non-strict parking bound. -/
public theorem ParkingAtOrBelow.transport_mono
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A₁ A₂ : g.nt} {stack₁ stack₂ : List g.flag} {w₁ w₂ : List T}
    {parse₁ : NFParse g A₁ stack₁ w₁}
    {parse₂ : NFParse g A₂ stack₂ w₂}
    {old new : ScheduleCursor g input} {ledger : IndexTicketLedger old}
    {oldWindow : ProductiveOwnerWindow (input := input) parse₁}
    {newWindow : ProductiveOwnerWindow (input := input) parse₂}
    (hbound : ledger.ParkingAtOrBelow oldWindow)
    (hindices : new.indexOwners.Perm old.indexOwners)
    (hbase : oldWindow.base ≤ newWindow.base) :
    (ledger.transport hindices).ParkingAtOrBelow newWindow :=
  (hbound.transport hindices).mono hbase

/-- A strict base increase after transport restores a strict bound from `AtOrBelow`. -/
public theorem ParkingAtOrBelow.transport_toBelow_of_base_lt
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A₁ A₂ : g.nt} {stack₁ stack₂ : List g.flag} {w₁ w₂ : List T}
    {parse₁ : NFParse g A₁ stack₁ w₁}
    {parse₂ : NFParse g A₂ stack₂ w₂}
    {old new : ScheduleCursor g input} {ledger : IndexTicketLedger old}
    {oldWindow : ProductiveOwnerWindow (input := input) parse₁}
    {newWindow : ProductiveOwnerWindow (input := input) parse₂}
    (hbound : ledger.ParkingAtOrBelow oldWindow)
    (hindices : new.indexOwners.Perm old.indexOwners)
    (hbase : oldWindow.base < newWindow.base) :
    (ledger.transport hindices).ParkingBelow newWindow :=
  (hbound.transport hindices).toBelow_of_base_lt hbase

/-- Releasing one physical owner preserves strict parking bounds. -/
public theorem ParkingBelow.release
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    (ledger.release owner hindices).ParkingBelow window := by
  intro slot hmem
  apply hbound slot
  have hnew : IndexTicket.parking slot ∈
      new.indexOwners.map ledger.ticketOf := by
    simpa [ScheduleCursor.indexTickets, IndexTicketLedger.release] using hmem
  have hold := (hindices.map ledger.ticketOf).mem_iff.mpr
    (List.mem_cons_of_mem (ledger.ticketOf owner) hnew)
  simpa [ScheduleCursor.indexTickets] using hold

/-- Releasing one physical owner preserves non-strict parking bounds. -/
public theorem ParkingAtOrBelow.release
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingAtOrBelow window)
    (owner : Fin (10 * input.length))
    (hindices : old.indexOwners.Perm (owner :: new.indexOwners)) :
    (ledger.release owner hindices).ParkingAtOrBelow window := by
  intro slot hmem
  apply hbound slot
  have hnew : IndexTicket.parking slot ∈
      new.indexOwners.map ledger.ticketOf := by
    simpa [ScheduleCursor.indexTickets, IndexTicketLedger.release] using hmem
  have hold := (hindices.map ledger.ticketOf).mem_iff.mpr
    (List.mem_cons_of_mem (ledger.ticketOf owner) hnew)
  simpa [ScheduleCursor.indexTickets] using hold

/-- Allocating a nonparking ticket preserves a strict parking bound. -/
public theorem ParkingBelow.allocate_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hnonparking : ticket.Nonparking) :
    (ledger.allocate owner ticket hownerFresh hticketFresh hticketNotScratch
      hindices).ParkingBelow window := by
  intro slot hmem
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  have hclass := hindices.mem_iff.mp hcandidate
  rcases List.mem_cons.mp hclass with hself | hold
  · subst candidate
    have hticket : ticket = IndexTicket.parking slot := by
      simpa [IndexTicketLedger.allocate] using heq
    exact False.elim (hnonparking slot hticket)
  · apply hbound slot
    rw [ScheduleCursor.indexTickets]
    apply List.mem_map.mpr
    refine ⟨candidate, hold, ?_⟩
    change ledger.insertTicket owner ticket candidate = IndexTicket.parking slot at heq
    rw [ledger.insertTicket_eq_of_mem owner ticket hold hownerFresh] at heq
    exact heq

/-- Allocating a nonparking ticket preserves a non-strict parking bound. -/
public theorem ParkingAtOrBelow.allocate_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingAtOrBelow window)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hnonparking : ticket.Nonparking) :
    (ledger.allocate owner ticket hownerFresh hticketFresh hticketNotScratch
      hindices).ParkingAtOrBelow window := by
  intro slot hmem
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  have hclass := hindices.mem_iff.mp hcandidate
  rcases List.mem_cons.mp hclass with hself | hold
  · subst candidate
    have hticket : ticket = IndexTicket.parking slot := by
      simpa [IndexTicketLedger.allocate] using heq
    exact False.elim (hnonparking slot hticket)
  · apply hbound slot
    rw [ScheduleCursor.indexTickets]
    apply List.mem_map.mpr
    refine ⟨candidate, hold, ?_⟩
    change ledger.insertTicket owner ticket candidate = IndexTicket.parking slot at heq
    rw [ledger.insertTicket_eq_of_mem owner ticket hold hownerFresh] at heq
    exact heq

/-- Allocating a core ticket preserves a strict parking bound. -/
public theorem ParkingBelow.allocate_core
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hcore : ticket.val < 4 * input.length) :
    (ledger.allocate owner ticket hownerFresh hticketFresh hticketNotScratch
      hindices).ParkingBelow window :=
  hbound.allocate_nonparking owner ticket hownerFresh hticketFresh
    hticketNotScratch hindices (IndexTicket.nonparking_of_core hcore)

/-- Allocating a core ticket preserves a non-strict parking bound. -/
public theorem ParkingAtOrBelow.allocate_core
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {old new : ScheduleCursor g input}
    {ledger : IndexTicketLedger old}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingAtOrBelow window)
    (owner : Fin (10 * input.length)) (ticket : IndexTicket input)
    (hownerFresh : owner ∉ old.indexOwners)
    (hticketFresh : ticket ∉ old.indexTickets ledger.ticketOf)
    (hticketNotScratch : ∀ hinput : 0 < input.length,
      ticket ≠ IndexTicket.scratch hinput)
    (hindices : new.indexOwners.Perm (owner :: old.indexOwners))
    (hcore : ticket.val < 4 * input.length) :
    (ledger.allocate owner ticket hownerFresh hticketFresh hticketNotScratch
      hindices).ParkingAtOrBelow window :=
  hbound.allocate_nonparking owner ticket hownerFresh hticketFresh
    hticketNotScratch hindices (IndexTicket.nonparking_of_core hcore)

/-- Reticketing one owner to a fresh nonparking target preserves a strict parking bound. -/
public theorem ParkingBelow.reticket_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (hnonparking : target.Nonparking) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).ParkingBelow window := by
  intro slot hmem
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  by_cases hself : candidate = owner
  · subst candidate
    rw [ledger.reticket_ticketOf_owner owner target howner htargetFresh
      htargetNotScratch] at heq
    exact False.elim (hnonparking slot heq)
  · rw [ledger.reticket_ticketOf_eq_of_mem_ne owner target howner
      htargetFresh htargetNotScratch hcandidate hself] at heq
    apply hbound slot
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hcandidate, heq⟩

/-- Reticketing one owner to a fresh nonparking target preserves a non-strict bound. -/
public theorem ParkingAtOrBelow.reticket_nonparking
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingAtOrBelow window)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (hnonparking : target.Nonparking) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).ParkingAtOrBelow window := by
  intro slot hmem
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  by_cases hself : candidate = owner
  · subst candidate
    rw [ledger.reticket_ticketOf_owner owner target howner htargetFresh
      htargetNotScratch] at heq
    exact False.elim (hnonparking slot heq)
  · rw [ledger.reticket_ticketOf_eq_of_mem_ne owner target howner
      htargetFresh htargetNotScratch hcandidate hself] at heq
    apply hbound slot
    rw [ScheduleCursor.indexTickets]
    exact List.mem_map.mpr ⟨candidate, hcandidate, heq⟩

/-- Reticketing one owner to a fresh core target preserves a strict parking bound. -/
public theorem ParkingBelow.reticket_core
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (hcore : target.val < 4 * input.length) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).ParkingBelow window :=
  hbound.reticket_nonparking owner target howner htargetFresh htargetNotScratch
    (IndexTicket.nonparking_of_core hcore)

/-- Reticketing one owner to a fresh core target preserves a non-strict parking bound. -/
public theorem ParkingAtOrBelow.reticket_core
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingAtOrBelow window)
    (owner : Fin (10 * input.length)) (target : IndexTicket input)
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : target ∉ cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      target ≠ IndexTicket.scratch hinput)
    (hcore : target.val < 4 * input.length) :
    (ledger.reticket owner target howner htargetFresh
      htargetNotScratch).ParkingAtOrBelow window :=
  hbound.reticket_nonparking owner target howner htargetFresh htargetNotScratch
    (IndexTicket.nonparking_of_core hcore)

/-- Parking one owner at the canonical window-base ticket weakens `Below` only to
`AtOrBelow`. -/
public theorem ParkingBelow.reticket_parkingTicket
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {cursor : ScheduleCursor g input}
    {ledger : IndexTicketLedger cursor}
    {window : ProductiveOwnerWindow (input := input) parse}
    (hbound : ledger.ParkingBelow window)
    (owner : Fin (10 * input.length))
    (howner : owner ∈ cursor.indexOwners)
    (htargetFresh : window.parkingTicket ∉
      cursor.indexTickets ledger.ticketOf)
    (htargetNotScratch : ∀ hinput : 0 < input.length,
      window.parkingTicket ≠ IndexTicket.scratch hinput) :
    (ledger.reticket owner window.parkingTicket howner htargetFresh
      htargetNotScratch).ParkingAtOrBelow window := by
  intro slot hmem
  rw [ScheduleCursor.indexTickets] at hmem
  rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
  by_cases hself : candidate = owner
  · subst candidate
    rw [ledger.reticket_ticketOf_owner owner window.parkingTicket howner
      htargetFresh htargetNotScratch] at heq
    have hval := congrArg Fin.val heq
    simp only [ProductiveOwnerWindow.parkingTicket_val,
      IndexTicket.parking_val] at hval
    omega
  · rw [ledger.reticket_ticketOf_eq_of_mem_ne owner window.parkingTicket
      howner htargetFresh htargetNotScratch hcandidate hself] at heq
    exact Nat.le_of_lt (hbound slot (by
      rw [ScheduleCursor.indexTickets]
      exact List.mem_map.mpr ⟨candidate, hcandidate, heq⟩))

/-- Logical ticket injectivity bounds physical persistent indices by the complete
`6|input|` logical carrier. -/
public theorem index_count_le
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    cursor.indexOwners.length ≤ 6 * input.length := by
  have hcard := ledger.tickets_nodup.length_le_card
  simpa [ScheduleCursor.indexTickets] using hcard

/-- The permanently reserved scratch ticket leaves strict room in the complete logical
carrier.  This is deliberately not a bound for the smaller physical owner pool. -/
public theorem index_count_lt
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (hinput : 0 < input.length) :
    cursor.indexOwners.length < 6 * input.length := by
  have hnodup :
      (IndexTicket.scratch hinput :: cursor.indexTickets ledger.ticketOf).Nodup :=
    List.nodup_cons.mpr ⟨ledger.scratch_fresh hinput, ledger.tickets_nodup⟩
  have hcard := hnodup.length_le_card
  simp only [List.length_cons, ScheduleCursor.indexTickets_length,
    Fintype.card_fin] at hcard
  omega

/-- An explicit strict physical-capacity bound implies that the physical owner pool is
nonempty.  Logical-ticket cardinality alone does not imply this after adding parking tickets. -/
public theorem pool_free_ne_nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor)
    (pool : IndexOwnerPool cursor)
    (hcapacity : cursor.indexOwners.length < 6 * input.length) :
    pool.free ≠ [] := by
  intro hnil
  have hconserve := pool.index_count_add_free_length
  simp only [hnil, List.length_nil, Nat.add_zero] at hconserve
  omega

/-- Semantic-owner images of live tickets are also duplicate-free. -/
public theorem semanticOwners_nodup
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (ledger : IndexTicketLedger cursor) :
    (cursor.indexTickets ledger.ticketOf).map
      (IndexTicket.semanticOwner (g := g)) |>.Nodup :=
  ledger.tickets_nodup.map IndexTicket.semanticOwner_injective

end IndexTicketLedger

end Aho
end IndexedGrammar
