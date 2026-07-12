module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Ownership.EventLedger

@[expose]
public section

/-!
# Ticketed shadow owners for Aho's compressed scheduler

The primary owner bank records productive events at block endpoints.  A temporarily unaligned
head cannot use that bank, since it need not end at an event.  Before such a head is buried
under another block, it is sealed into a disjoint shadow bank.  Its ticket is the productive
event at the *start* of the block.

For an input of length `n`, productive owners occupy `[0, 2n - 1)`, their shadows occupy
`[2n - 1, 4n - 2)`, and the last two slots are the temporary scratch and transient owners.
This file contains only the owner arithmetic and semantic ledgers.  It does not perform any
machine move.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- First physical slot of the bank of productive-event shadows. -/
public def shadowOwnerOffset (input : List T) : ℕ :=
  2 * input.length - 1

namespace ProductiveOwnerWindow

/-- The shadow of a canonical event owner.  The shadow has the same root-relative productive
ticket, translated into the disjoint second bank. -/
public def shadowEventOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (d : ℕ) (hd : d ∈ parse.eventDepths) : Fin (10 * input.length) :=
  ⟨shadowOwnerOffset input + (window.eventOwner d hd).val, by
    have hlocal := parse.eventOwnerNat_lt_productiveCount hd
    have hend := window.end_le
    simp only [eventOwner_val, shadowOwnerOffset]
    omega⟩

@[simp] public theorem shadowEventOwner_val
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (d : ℕ) (hd : d ∈ parse.eventDepths) :
    (window.shadowEventOwner d hd).val =
      shadowOwnerOffset input + window.base + parse.eventOwnerNat d := by
  change shadowOwnerOffset input + (window.eventOwner d hd).val = _
  rw [eventOwner_val]
  omega

/-- Shadowing preserves injectivity of productive event tickets. -/
public theorem shadowEventOwner_injective
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse) :
    ∀ {d e : ℕ} (hd : d ∈ parse.eventDepths) (he : e ∈ parse.eventDepths),
      window.shadowEventOwner d hd = window.shadowEventOwner e he → d = e := by
  intro d e hd he howner
  apply window.eventOwner_injective hd he
  apply Fin.ext
  have hval := congrArg Fin.val howner
  change shadowOwnerOffset input + (window.eventOwner d hd).val =
    shadowOwnerOffset input + (window.eventOwner e he).val at hval
  exact Nat.add_left_cancel hval

/-- Any equality of primary event owners lifts to the corresponding equality in the shadow
bank.  This is the generic bridge used by unary and binary parse transports. -/
public theorem shadowEventOwner_congr
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {parse' : NFParse g B stack' w'}
    (window : ProductiveOwnerWindow (input := input) parse)
    (window' : ProductiveOwnerWindow (input := input) parse')
    {d e : ℕ} (hd : d ∈ parse.eventDepths) (he : e ∈ parse'.eventDepths)
    (howner : window.eventOwner d hd = window'.eventOwner e he) :
    window.shadowEventOwner d hd = window'.shadowEventOwner e he := by
  apply Fin.ext
  have hval := congrArg Fin.val howner
  change shadowOwnerOffset input + (window.eventOwner d hd).val =
    shadowOwnerOffset input + (window'.eventOwner e he).val
  omega

/-- Shadow owners commute with the one-position event shift of a pop. -/
public theorem shadowEventOwner_pop_succ
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
    {rest : NFParse g B stack w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.pop hr hlhs hc hrhs rest))
    {d : ℕ} (hd : d ∈ rest.eventDepths) :
    window.shadowEventOwner (d + 1)
        (Finset.mem_image.mpr ⟨d, hd, by omega⟩) =
      window.popChild.shadowEventOwner d hd :=
  window.shadowEventOwner_congr window.popChild _ _
    (window.eventOwner_pop_succ hd)

/-- Shadow owners commute with the canonical preimage of a push event. -/
public theorem shadowEventOwner_push
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    {d : ℕ} (hd : d ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths) :
    window.shadowEventOwner d hd =
      window.pushChild.shadowEventOwner
        (NFParse.pushEventPreimage rest.eventDepths d)
        (NFParse.pushEventPreimage_mem hd) :=
  window.shadowEventOwner_congr window.pushChild _ _
    (window.eventOwner_push hd)

/-- Positive push events and their one-deeper child events have the same shadow owner. -/
public theorem shadowEventOwner_push_pos
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    {d : ℕ} (hdpos : 0 < d) (hd : d + 1 ∈ rest.eventDepths) :
    window.shadowEventOwner d
        (Finset.mem_image.mpr ⟨d + 1, hd, by simp⟩) =
      window.pushChild.shadowEventOwner (d + 1) hd :=
  window.shadowEventOwner_congr window.pushChild _ _
    (window.eventOwner_push_pos hdpos hd)

/-- Primary and shadow banks are physically disjoint. -/
public theorem eventOwner_ne_shadowEventOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    {d e : ℕ} (hd : d ∈ parse.eventDepths) (he : e ∈ parse.eventDepths) :
    window.eventOwner d hd ≠ window.shadowEventOwner e he := by
  intro howner
  have hdlt := parse.eventOwnerNat_lt_productiveCount hd
  have hend := window.end_le
  have hval := congrArg Fin.val howner
  simp only [eventOwner_val, shadowEventOwner_val, shadowOwnerOffset] at hval
  omega

/-- A shadow owner is never the temporary scratch slot. -/
public theorem shadowEventOwner_ne_scratchOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    {d : ℕ} (hd : d ∈ parse.eventDepths) (hinput : 0 < input.length) :
    window.shadowEventOwner d hd ≠ scratchOwner (g := g) hinput := by
  intro howner
  have hlocal := parse.eventOwnerNat_lt_productiveCount hd
  have hend := window.end_le
  have hval := congrArg Fin.val howner
  simp only [shadowEventOwner_val, scratchOwner_val, shadowOwnerOffset] at hval
  omega

/-- A shadow owner is never the temporary collision slot. -/
public theorem shadowEventOwner_ne_transientOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    {d : ℕ} (hd : d ∈ parse.eventDepths) (hinput : 0 < input.length) :
    window.shadowEventOwner d hd ≠ transientOwner (g := g) hinput := by
  intro howner
  have hlocal := parse.eventOwnerNat_lt_productiveCount hd
  have hend := window.end_le
  have hval := congrArg Fin.val howner
  simp only [shadowEventOwner_val, transientOwner_val, shadowOwnerOffset] at hval
  omega

end ProductiveOwnerWindow

/-- An owner does not use a shadow ticket belonging to the active productive window.  Primary
owners and the two temporary owners satisfy this automatically. -/
public def OutsideShadowWindow
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (owner : Fin (10 * input.length)) : Prop :=
  owner.val < shadowOwnerOffset input + window.base ∨
    shadowOwnerOffset input + window.base + parse.productiveCount ≤ owner.val

namespace OutsideShadowWindow

/-- A local shadow event lies strictly inside its shadow-ticket window. -/
public theorem shadowEventOwner_not_outside
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    {d : ℕ} (hd : d ∈ parse.eventDepths) :
    ¬ OutsideShadowWindow window (window.shadowEventOwner d hd) := by
  intro hout
  have hlt := parse.eventOwnerNat_lt_productiveCount hd
  simp only [OutsideShadowWindow, ProductiveOwnerWindow.shadowEventOwner_val] at hout
  rcases hout with hout | hout <;> omega

/-- Every primary productive owner lies before the shadow bank. -/
public theorem eventOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    {d : ℕ} (hd : d ∈ parse.eventDepths) :
    OutsideShadowWindow window (window.eventOwner d hd) := by
  left
  have hlt := parse.eventOwnerNat_lt_productiveCount hd
  have hend := window.end_le
  simp only [ProductiveOwnerWindow.eventOwner_val,
    shadowOwnerOffset]
  omega

/-- The temporary scratch slot lies after every shadow window. -/
public theorem scratchOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hinput : 0 < input.length) :
    OutsideShadowWindow window
      (ProductiveOwnerWindow.scratchOwner (g := g) hinput) := by
  right
  have hend := window.end_le
  simp only [ProductiveOwnerWindow.scratchOwner_val,
    shadowOwnerOffset]
  omega

/-- The temporary collision slot lies after every shadow window. -/
public theorem transientOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hinput : 0 < input.length) :
    OutsideShadowWindow window
      (ProductiveOwnerWindow.transientOwner (g := g) hinput) := by
  right
  have hend := window.end_le
  simp only [ProductiveOwnerWindow.transientOwner_val,
    shadowOwnerOffset]
  omega

/-- Every reusable generic label lies beyond every shadow-owner window. -/
public theorem genericOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    {owner : Fin (10 * input.length)}
    (howner : owner ∈ genericOwnerRange g input) :
    OutsideShadowWindow window owner := by
  right
  have hend := window.end_le
  have hge := genericOwnerRange_val_ge howner
  simp only [genericOwnerOffset, shadowOwnerOffset] at hge ⊢
  omega

/-- Equal-count transports preserve shadow-window exclusion. -/
public theorem transport
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hcount : residual.productiveCount = parse.productiveCount)
    {owner : Fin (10 * input.length)}
    (hout : OutsideShadowWindow window owner) :
    OutsideShadowWindow (window.transport hcount) owner := by
  simpa [OutsideShadowWindow, ProductiveOwnerWindow.transport, hcount] using hout

/-- Shadow tickets outside a binary parent window remain outside its left child. -/
public theorem binaryLeft
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    {owner : Fin (10 * input.length)}
    (hout : OutsideShadowWindow window owner) :
    OutsideShadowWindow window.binaryLeft owner := by
  rcases hout with hout | hout
  · exact Or.inl (by
      simp only [ProductiveOwnerWindow.binaryLeft_base]
      omega)
  · right
    rw [NFParse.productiveCount_binary hr hlhs hc hrhs left right] at hout
    simp only [ProductiveOwnerWindow.binaryLeft_base]
    omega

/-- Shadow tickets outside a binary parent window remain outside its right child. -/
public theorem binaryRight
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    {owner : Fin (10 * input.length)}
    (hout : OutsideShadowWindow window owner) :
    OutsideShadowWindow window.binaryRight owner := by
  rcases hout with hout | hout
  · exact Or.inl (by
      simp only [ProductiveOwnerWindow.binaryRight_base]
      omega)
  · right
    rw [NFParse.productiveCount_binary hr hlhs hc hrhs left right] at hout
    simp only [ProductiveOwnerWindow.binaryRight_base]
    omega

/-- The binary root ticket is already outside the left child's shadow window. -/
public theorem binaryZero_left
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    (hzero : 0 ∈ (NFParse.binary hr hlhs hc hrhs left right).eventDepths) :
    OutsideShadowWindow window.binaryLeft
      (window.shadowEventOwner 0 hzero) := by
  left
  have hprimary := window.eventOwner_binary_zero_val
  have hshadow : (window.shadowEventOwner 0 hzero).val =
      shadowOwnerOffset input + window.base := by
    change shadowOwnerOffset input + (window.eventOwner 0 hzero).val = _
    rw [hprimary]
  simp only [ProductiveOwnerWindow.binaryLeft_base]
  omega

/-- The binary root ticket is already outside the right child's shadow window. -/
public theorem binaryZero_right
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    (hzero : 0 ∈ (NFParse.binary hr hlhs hc hrhs left right).eventDepths) :
    OutsideShadowWindow window.binaryRight
      (window.shadowEventOwner 0 hzero) := by
  left
  have hprimary := window.eventOwner_binary_zero_val
  have hshadow : (window.shadowEventOwner 0 hzero).val =
      shadowOwnerOffset input + window.base := by
    change shadowOwnerOffset input + (window.eventOwner 0 hzero).val = _
    rw [hprimary]
  simp only [ProductiveOwnerWindow.binaryRight_base]
  omega

end OutsideShadowWindow

/-- Concrete start position of block `i`.  Unlike `blockEndpoint`, this excludes block `i`
itself. -/
public def blockStart {g : IndexedGrammar T}
    (blocks : List (List g.flag)) (i : Fin blocks.length) : ℕ :=
  (blocks.take i.val).flatten.length

@[simp] public theorem blockStart_cons_zero
    {g : IndexedGrammar T} (block : List g.flag) (blocks : List (List g.flag)) :
    blockStart (block :: blocks) ⟨0, by simp⟩ = 0 := by
  simp [blockStart]

@[simp] public theorem blockStart_cons_succ
    {g : IndexedGrammar T} (block : List g.flag) (blocks : List (List g.flag))
    (i : Fin blocks.length) :
    blockStart (block :: blocks) (Fin.succ i) =
      block.length + blockStart blocks i := by
  simp [blockStart, List.take_succ_cons]

/-- Productive provenance for shadow-bank owners aligned with block starts.  Non-shadow owners
fall into the outside alternative automatically. -/
public structure ShadowStartLayout
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length))) where
  owners_length : owners.length = blocks.length
  block_nonempty : ∀ block ∈ blocks, block ≠ []
  owner_at : ∀ i : Fin blocks.length,
    (∃ hd : blockStart blocks i ∈ parse.eventDepths,
      blockOwnerAt owners owners_length i =
        window.shadowEventOwner (blockStart blocks i) hd) ∨
    OutsideShadowWindow window (blockOwnerAt owners owners_length i)

namespace ShadowStartLayout

/-- The empty block partition has the empty shadow ledger. -/
public def nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse} :
    ShadowStartLayout parse window [] [] where
  owners_length := rfl
  block_nonempty _ hmem := by simp at hmem
  owner_at i := Fin.elim0 i

/-- A layout all of whose owners are outside the active shadow window. -/
public def ofOutside
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {blocks : List (List g.flag)} {owners : List (Fin (10 * input.length))}
    (hlen : owners.length = blocks.length)
    (hne : ∀ block ∈ blocks, block ≠ [])
    (hout : ∀ i : Fin blocks.length,
      OutsideShadowWindow window (blockOwnerAt owners hlen i)) :
    ShadowStartLayout parse window blocks owners where
  owners_length := hlen
  block_nonempty := hne
  owner_at i := Or.inr (hout i)

/-- Generic parse/window transport.  Local shadow tickets are transported explicitly; owners
already outside the old window must remain outside the new one. -/
public def transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {residualWindow : ProductiveOwnerWindow (input := input) residual}
    {blocks : List (List g.flag)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window blocks owners)
    (outside : ∀ owner, OutsideShadowWindow window owner →
      OutsideShadowWindow residualWindow owner)
    (ticket_shift : ∀ (i : Fin blocks.length)
      (hd : blockStart blocks i ∈ parse.eventDepths),
      ∃ hd' : blockStart blocks i ∈ residual.eventDepths,
        window.shadowEventOwner (blockStart blocks i) hd =
          residualWindow.shadowEventOwner (blockStart blocks i) hd') :
    ShadowStartLayout residual residualWindow blocks owners where
  owners_length := layout.owners_length
  block_nonempty := layout.block_nonempty
  owner_at i := by
    rcases layout.owner_at i with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      rcases ticket_shift i hd with ⟨hd', hshift⟩
      exact Or.inl ⟨hd', howner.trans hshift⟩
    · exact Or.inr (outside _ hout)

/-- Prepend one block, shifting every old block start by its length. -/
public def cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {nextParse : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {nextWindow : ProductiveOwnerWindow (input := input) nextParse}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window blocks owners)
    (block_ne : block ≠ [])
    (head_owner :
      (∃ hd : 0 ∈ nextParse.eventDepths,
        owner = nextWindow.shadowEventOwner 0 hd) ∨
      OutsideShadowWindow nextWindow owner)
    (outside : ∀ candidate, OutsideShadowWindow window candidate →
      OutsideShadowWindow nextWindow candidate)
    (ticket_shift : ∀ (i : Fin blocks.length)
      (hd : blockStart blocks i ∈ parse.eventDepths),
      ∃ hd' : block.length + blockStart blocks i ∈ nextParse.eventDepths,
        window.shadowEventOwner (blockStart blocks i) hd =
          nextWindow.shadowEventOwner
            (block.length + blockStart blocks i) hd') :
    ShadowStartLayout nextParse nextWindow (block :: blocks) (owner :: owners) where
  owners_length := by simp [layout.owners_length]
  block_nonempty candidate hmem := by
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact block_ne
    · exact layout.block_nonempty candidate htail
  owner_at i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [blockOwnerAt] using head_owner
    · rcases layout.owner_at j with hlocal | hout
      · rcases hlocal with ⟨hd, howner⟩
        rcases ticket_shift j hd with ⟨hd', hshift⟩
        apply Or.inl
        refine ⟨by simpa using hd', ?_⟩
        simpa [blockOwnerAt] using howner.trans hshift
      · apply Or.inr
        simpa [blockOwnerAt] using outside _ hout

/-- Remove the first block, shifting every remaining start back by its length. -/
public def tail
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {residualWindow : ProductiveOwnerWindow (input := input) residual}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window (block :: blocks) (owner :: owners))
    (outside : ∀ candidate, OutsideShadowWindow window candidate →
      OutsideShadowWindow residualWindow candidate)
    (ticket_shift : ∀ (i : Fin blocks.length)
      (hd : block.length + blockStart blocks i ∈ parse.eventDepths),
      ∃ hd' : blockStart blocks i ∈ residual.eventDepths,
        window.shadowEventOwner (block.length + blockStart blocks i) hd =
          residualWindow.shadowEventOwner (blockStart blocks i) hd') :
    ShadowStartLayout residual residualWindow blocks owners where
  owners_length := by simpa using layout.owners_length
  block_nonempty candidate hmem :=
    layout.block_nonempty candidate (List.mem_cons_of_mem block hmem)
  owner_at i := by
    let parentIndex : Fin (block :: blocks).length := Fin.succ i
    rcases layout.owner_at parentIndex with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      have hd' : block.length + blockStart blocks i ∈ parse.eventDepths := by
        simpa [parentIndex] using hd
      rcases ticket_shift i hd' with ⟨hresidual, hshift⟩
      apply Or.inl
      refine ⟨hresidual, ?_⟩
      have howner' :
          blockOwnerAt owners (by simpa using layout.owners_length) i =
            window.shadowEventOwner
              (block.length + blockStart blocks i) hd' := by
        simpa [parentIndex, blockOwnerAt] using howner
      exact howner'.trans hshift
    · apply Or.inr
      apply outside
      simpa [parentIndex, blockOwnerAt] using hout

/-- Restrict a shadow-start layout to the left binary child.  A ticket belonging to the binary
root or the right subtree becomes outside the child's shadow window. -/
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
    {blocks : List (List g.flag)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout
      (NFParse.binary hr hlhs hc hrhs left right) window blocks owners) :
    ShadowStartLayout left window.binaryLeft blocks owners where
  owners_length := layout.owners_length
  block_nonempty := layout.block_nonempty
  owner_at i := by
    rcases layout.owner_at i with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      by_cases hd0 : blockStart blocks i = 0
      · apply Or.inr
        rw [howner]
        simpa [hd0] using OutsideShadowWindow.binaryZero_left window
          (by simpa [hd0] using hd)
      · by_cases hleft : blockStart blocks i ∈ left.eventDepths
        · apply Or.inl
          refine ⟨hleft, howner.trans ?_⟩
          exact window.shadowEventOwner_congr window.binaryLeft _ _
            (window.eventOwner_binaryLeft hd0 hleft)
        · apply Or.inr
          have hright : blockStart blocks i ∈ right.eventDepths := by
            simp only [NFParse.eventDepths, Finset.mem_insert,
              Finset.mem_union] at hd
            rcases hd with hd | hd
            · exact False.elim (hd0 hd)
            · exact hd.resolve_left hleft
          have heq : window.shadowEventOwner (blockStart blocks i) hd =
              window.binaryRight.shadowEventOwner (blockStart blocks i) hright :=
            window.shadowEventOwner_congr window.binaryRight _ _
              (window.eventOwner_binaryRight hd0 hleft hright)
          right
          have hval := congrArg Fin.val (howner.trans heq)
          simp only [ProductiveOwnerWindow.shadowEventOwner_val,
            ProductiveOwnerWindow.binaryLeft_base,
            ProductiveOwnerWindow.binaryRight_base] at hval ⊢
          omega
    · exact Or.inr (OutsideShadowWindow.binaryLeft window hout)

/-- Restrict a shadow-start layout to the right binary child.  A ticket belonging to the
binary root or the left subtree becomes outside the child's shadow window. -/
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
    {blocks : List (List g.flag)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout
      (NFParse.binary hr hlhs hc hrhs left right) window blocks owners) :
    ShadowStartLayout right window.binaryRight blocks owners where
  owners_length := layout.owners_length
  block_nonempty := layout.block_nonempty
  owner_at i := by
    rcases layout.owner_at i with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      by_cases hd0 : blockStart blocks i = 0
      · apply Or.inr
        rw [howner]
        simpa [hd0] using OutsideShadowWindow.binaryZero_right window
          (by simpa [hd0] using hd)
      · by_cases hleft : blockStart blocks i ∈ left.eventDepths
        · apply Or.inr
          have heq : window.shadowEventOwner (blockStart blocks i) hd =
              window.binaryLeft.shadowEventOwner (blockStart blocks i) hleft :=
            window.shadowEventOwner_congr window.binaryLeft _ _
              (window.eventOwner_binaryLeft hd0 hleft)
          left
          have hval := congrArg Fin.val (howner.trans heq)
          have hlt := left.eventOwnerNat_lt_productiveCount hleft
          simp only [ProductiveOwnerWindow.shadowEventOwner_val,
            ProductiveOwnerWindow.binaryLeft_base,
            ProductiveOwnerWindow.binaryRight_base] at hval ⊢
          omega
        · apply Or.inl
          have hright : blockStart blocks i ∈ right.eventDepths := by
            simp only [NFParse.eventDepths, Finset.mem_insert,
              Finset.mem_union] at hd
            rcases hd with hd | hd
            · exact False.elim (hd0 hd)
            · exact hd.resolve_left hleft
          refine ⟨hright, howner.trans ?_⟩
          exact window.shadowEventOwner_congr window.binaryRight _ _
            (window.eventOwner_binaryRight hd0 hleft hright)
    · exact Or.inr (OutsideShadowWindow.binaryRight window hout)

/-- Replace the owner of the first block while keeping all shadow-start classifications below
it unchanged. -/
public def reownerHead
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {block : List g.flag} {blocks : List (List g.flag)}
    {oldOwner newOwner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window
      (block :: blocks) (oldOwner :: owners))
    (head_owner :
      (∃ hd : 0 ∈ parse.eventDepths,
        newOwner = window.shadowEventOwner 0 hd) ∨
      OutsideShadowWindow window newOwner) :
    ShadowStartLayout parse window (block :: blocks) (newOwner :: owners) where
  owners_length := by simpa using layout.owners_length
  block_nonempty := layout.block_nonempty
  owner_at i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [blockOwnerAt] using head_owner
    · simpa [blockOwnerAt] using layout.owner_at (Fin.succ j)

/-- A local shadow event absent from every represented block start is absent from all selected
owners. -/
public theorem shadowEventOwner_not_mem_owners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {blocks : List (List g.flag)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window blocks owners)
    {d : ℕ} (hd : d ∈ parse.eventDepths)
    (hdiff : ∀ i : Fin blocks.length, d ≠ blockStart blocks i) :
    window.shadowEventOwner d hd ∉ owners := by
  intro hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hget⟩
  have hi' : i < blocks.length := by
    rw [← layout.owners_length]
    exact hi
  let j : Fin blocks.length := ⟨i, hi'⟩
  have hat : blockOwnerAt owners layout.owners_length j =
      window.shadowEventOwner d hd := by
    simpa [blockOwnerAt, j] using hget
  rcases layout.owner_at j with hlocal | hout
  · rcases hlocal with ⟨hstart, howner⟩
    have heq : d = blockStart blocks j :=
      window.shadowEventOwner_injective hd hstart (hat.symm.trans howner)
    exact hdiff j heq
  · exact OutsideShadowWindow.shadowEventOwner_not_outside window hd (hat ▸ hout)

/-- The shadow ticket at the start of the first block is fresh from every lower block owner.
This is the active-layout fact used when a scratch head is sealed at a binary event. -/
public theorem shadowEventOwner_zero_not_mem_tail
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window
      (block :: blocks) (owner :: owners))
    (hzero : 0 ∈ parse.eventDepths) :
    window.shadowEventOwner 0 hzero ∉ owners := by
  intro hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hget⟩
  have hlength : owners.length = blocks.length := by
    simpa using layout.owners_length
  have hi' : i < blocks.length := by simpa [hlength] using hi
  let j : Fin blocks.length := ⟨i, hi'⟩
  let parentIndex : Fin (block :: blocks).length := Fin.succ j
  have hat : blockOwnerAt (owner :: owners) layout.owners_length parentIndex =
      window.shadowEventOwner 0 hzero := by
    simpa [parentIndex, blockOwnerAt, j] using hget
  rcases layout.owner_at parentIndex with hlocal | hout
  · rcases hlocal with ⟨hstart, howner⟩
    have heq : 0 = blockStart (block :: blocks) parentIndex :=
      window.shadowEventOwner_injective hzero hstart (hat.symm.trans howner)
    have hblock : 0 < block.length :=
      List.length_pos_of_ne_nil
        (layout.block_nonempty block (by simp))
    simp only [parentIndex, blockStart_cons_succ] at heq
    omega
  · exact OutsideShadowWindow.shadowEventOwner_not_outside window hzero
      (hat ▸ hout)

/-- Replacing a non-shadow head by its depth-zero shadow yields a physically fresh owner as
soon as the old head is known distinct from that shadow. -/
public theorem shadowEventOwner_zero_fresh_of_head_ne
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)} {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window
      (block :: blocks) (owner :: owners))
    (hzero : 0 ∈ parse.eventDepths)
    (hhead : window.shadowEventOwner 0 hzero ≠ owner) :
    window.shadowEventOwner 0 hzero ∉ owner :: owners := by
  simp only [List.mem_cons, not_or]
  exact ⟨hhead, layout.shadowEventOwner_zero_not_mem_tail hzero⟩

/-- When the second block is sealed at the end of a newly prepended first block, its shadow
ticket is fresh from the new head and from every block below it. -/
public theorem shadowEventOwner_second_fresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {first second : List g.flag} {blocks : List (List g.flag)}
    {firstOwner secondOwner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    (layout : ShadowStartLayout parse window
      (first :: second :: blocks) (firstOwner :: secondOwner :: owners))
    (hstart : first.length ∈ parse.eventDepths)
    (hfirst : window.shadowEventOwner first.length hstart ≠ firstOwner) :
    window.shadowEventOwner first.length hstart ∉ firstOwner :: owners := by
  simp only [List.mem_cons, not_or]
  refine ⟨hfirst, ?_⟩
  intro hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hget⟩
  have hlength : owners.length = blocks.length := by
    simpa using layout.owners_length
  have hi' : i < blocks.length := by simpa [hlength] using hi
  let j : Fin blocks.length := ⟨i, hi'⟩
  let parentIndex : Fin (first :: second :: blocks).length := Fin.succ (Fin.succ j)
  have hat :
      blockOwnerAt (firstOwner :: secondOwner :: owners)
          layout.owners_length parentIndex =
        window.shadowEventOwner first.length hstart := by
    simpa [parentIndex, blockOwnerAt, j] using hget
  rcases layout.owner_at parentIndex with hlocal | hout
  · rcases hlocal with ⟨hticket, howner⟩
    have heq : first.length =
        blockStart (first :: second :: blocks) parentIndex :=
      window.shadowEventOwner_injective hstart hticket (hat.symm.trans howner)
    have hsecond : 0 < second.length :=
      List.length_pos_of_ne_nil
        (layout.block_nonempty second (by simp))
    simp only [parentIndex, blockStart_cons_succ] at heq
    omega
  · exact OutsideShadowWindow.shadowEventOwner_not_outside window hstart
      (hat ▸ hout)

end ShadowStartLayout

/-- Every open-frame owner has no ticket in the active shadow window.  Primary owners satisfy
this automatically.  A local shadow-start owner can enter an open frame only after descent
through the productive event at its start, at which point that ticket belongs to an ancestor
window and is outside the active child window. -/
public def ShadowOwnedFrame
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (owner : Fin (10 * input.length)) : Prop :=
  OutsideShadowWindow window owner

/-- Shadow-ticket provenance for every open frame. -/
public structure ShadowOwnedFrames
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (owners : List (Fin (10 * input.length))) : Prop where
  owner_at : ∀ owner ∈ owners, ShadowOwnedFrame parse window owner

namespace ShadowOwnedFrames

public def nil
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse} :
    ShadowOwnedFrames parse window [] where
  owner_at _ hmem := by simp at hmem

public def cons
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owner : Fin (10 * input.length)} {owners : List (Fin (10 * input.length))}
    (head : ShadowOwnedFrame parse window owner)
    (tail : ShadowOwnedFrames parse window owners) :
    ShadowOwnedFrames parse window (owner :: owners) where
  owner_at candidate hmem := by
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact head
    · exact tail.owner_at candidate htail

public def transport
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {residualWindow : ProductiveOwnerWindow (input := input) residual}
    {owners : List (Fin (10 * input.length))}
    (frames : ShadowOwnedFrames parse window owners)
    (shift : ∀ owner, ShadowOwnedFrame parse window owner →
      ShadowOwnedFrame residual residualWindow owner) :
    ShadowOwnedFrames residual residualWindow owners where
  owner_at owner hmem := shift owner (frames.owner_at owner hmem)

/-- Equal-count window transport preserves the outside-only frame invariant. -/
public def transportEqual
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners : List (Fin (10 * input.length))}
    (frames : ShadowOwnedFrames parse window owners)
    (hcount : residual.productiveCount = parse.productiveCount) :
    ShadowOwnedFrames residual (window.transport hcount) owners :=
  frames.transport (fun _ hout => OutsideShadowWindow.transport window hcount hout)

/-- Parent frame tickets remain outside the left binary child shadow window. -/
public def binaryLeft
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)}
    {owners : List (Fin (10 * input.length))}
    (frames : ShadowOwnedFrames
      (NFParse.binary hr hlhs hc hrhs left right) window owners) :
    ShadowOwnedFrames left window.binaryLeft owners :=
  frames.transport (fun _ hout => OutsideShadowWindow.binaryLeft window hout)

/-- Parent frame tickets remain outside the right binary child shadow window. -/
public def binaryRight
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)}
    {owners : List (Fin (10 * input.length))}
    (frames : ShadowOwnedFrames
      (NFParse.binary hr hlhs hc hrhs left right) window owners) :
    ShadowOwnedFrames right window.binaryRight owners :=
  frames.transport (fun _ hout => OutsideShadowWindow.binaryRight window hout)

public def perm
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners owners' : List (Fin (10 * input.length))}
    (frames : ShadowOwnedFrames parse window owners)
    (hperm : owners'.Perm owners) :
    ShadowOwnedFrames parse window owners' where
  owner_at owner hmem := frames.owner_at owner (hperm.mem_iff.mp hmem)

/-- No local shadow event can be held by an open frame. -/
public theorem shadowEventOwner_not_mem
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {owners : List (Fin (10 * input.length))}
    (frames : ShadowOwnedFrames parse window owners)
    {d : ℕ} (hd : d ∈ parse.eventDepths) :
    window.shadowEventOwner d hd ∉ owners := by
  intro hmem
  exact OutsideShadowWindow.shadowEventOwner_not_outside window hd
    (frames.owner_at _ hmem)

end ShadowOwnedFrames

/-- Cursor-level decomposition of shadow tickets.  The active start layout is supplied by the
runner because its block list is mode-specific. -/
public structure ShadowOwnerLedger
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (cursor : ScheduleCursor g input) where
  active : List (Fin (10 * input.length))
  outside : List (Fin (10 * input.length))
  right_eq : cursor.right.filterMap ScheduleAtom.indexOwner? = active ++ outside
  outside_at : ∀ owner ∈ outside, OutsideShadowWindow window owner
  frames : ShadowOwnedFrames parse window cursor.frameOwners
  prefixLedger : PrefixFrameLedger cursor

namespace ShadowOwnerLedger

/-- The canonical root cursor has an empty shadow ledger. -/
public def root
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (parse : NFParse g g.initial [] input) :
    ShadowOwnerLedger parse (ProductiveOwnerWindow.root parse)
      (initialScheduleCursor parse) where
  active := []
  outside := []
  right_eq := by simp [initialScheduleCursor, ScheduleAtom.indexOwner?]
  outside_at _ hmem := by simp at hmem
  frames := ShadowOwnedFrames.nil
  prefixLedger := PrefixFrameLedger.of_empty
    (by simp [initialScheduleCursor, ScheduleAtom.indexOwner?])
    (by simp [initialScheduleCursor, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?])

/-- Whole-cursor shadow freshness.  Active right-side owners are excluded by their block starts,
the common suffix is outside the shadow window, and prefix indices are reduced to the explicit
frame-freshness premise. -/
public theorem shadowEventOwner_not_mem_indexOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {cursor : ScheduleCursor g input}
    (ledger : ShadowOwnerLedger parse window cursor)
    {blocks : List (List g.flag)}
    (layout : ShadowStartLayout parse window blocks ledger.active)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    {d : ℕ} (hd : d ∈ parse.eventDepths)
    (hdiff : ∀ i : Fin blocks.length, d ≠ blockStart blocks i) :
    window.shadowEventOwner d hd ∉ cursor.indexOwners := by
  intro hmem
  have heta : ScheduleCursor.mk cursor.left cursor.focus cursor.right = cursor := by
    cases cursor
    rfl
  have hsplit := ScheduleCursor.indexOwners_mk cursor.left cursor.focus cursor.right
  rw [heta] at hsplit
  rw [hsplit, hfocus] at hmem
  simp only [List.append_nil, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact ledger.frames.shadowEventOwner_not_mem hd
      (ledger.prefixLedger.owners_perm.mem_iff.mp hleft)
  · rw [ledger.right_eq] at hright
    rcases List.mem_append.mp hright with hactive | houtside
    · exact layout.shadowEventOwner_not_mem_owners hd hdiff hactive
    · exact OutsideShadowWindow.shadowEventOwner_not_outside window hd
        (ledger.outside_at _ houtside)

/-- Whole-cursor shadow freshness from an explicit active-list freshness fact.  Prefix frames
and the unselected right suffix are discharged entirely by the shadow ledger. -/
public theorem shadowEventOwner_not_mem_indexOwners_of_active
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {cursor : ScheduleCursor g input}
    (ledger : ShadowOwnerLedger parse window cursor)
    (hfocus : [cursor.focus].filterMap ScheduleAtom.indexOwner? = [])
    {d : ℕ} (hd : d ∈ parse.eventDepths)
    (hactiveFresh : window.shadowEventOwner d hd ∉ ledger.active) :
    window.shadowEventOwner d hd ∉ cursor.indexOwners := by
  intro hmem
  have heta : ScheduleCursor.mk cursor.left cursor.focus cursor.right = cursor := by
    cases cursor
    rfl
  have hsplit := ScheduleCursor.indexOwners_mk cursor.left cursor.focus cursor.right
  rw [heta] at hsplit
  rw [hsplit, hfocus] at hmem
  simp only [List.append_nil, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact ledger.frames.shadowEventOwner_not_mem hd
      (ledger.prefixLedger.owners_perm.mem_iff.mp hleft)
  · rw [ledger.right_eq] at hright
    rcases List.mem_append.mp hright with hactive | houtside
    · exact hactiveFresh hactive
    · exact OutsideShadowWindow.shadowEventOwner_not_outside window hd
        (ledger.outside_at _ houtside)

/-- Generic cursor reassembly after transporting the active parse/window. -/
public def transport
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w'}
    {window : ProductiveOwnerWindow (input := input) parse}
    {old new : ScheduleCursor g input}
    (ledger : ShadowOwnerLedger parse window old)
    (residualWindow : ProductiveOwnerWindow (input := input) residual)
    (hright : new.right.filterMap ScheduleAtom.indexOwner? =
      ledger.active ++ ledger.outside)
    (houtside : ∀ owner ∈ ledger.outside,
      OutsideShadowWindow residualWindow owner)
    (hframes : ShadowOwnedFrames residual residualWindow new.frameOwners)
    (hprefix : PrefixFrameLedger new) :
    ShadowOwnerLedger residual residualWindow new where
  active := ledger.active
  outside := ledger.outside
  right_eq := hright
  outside_at := houtside
  frames := hframes
  prefixLedger := hprefix

end ShadowOwnerLedger

end Aho
end IndexedGrammar
