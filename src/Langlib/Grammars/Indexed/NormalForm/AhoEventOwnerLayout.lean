module

public import Langlib.Grammars.Indexed.NormalForm.AhoEventCompatibility

@[expose]
public section

/-!
# Productive-owner provenance for compressed layouts

`EventCompatible` records only that every event depth is a physical block boundary.  It does
not say which productive node owns a selected block, and a binary child can inherit a parent
block whose endpoint belongs only to its sibling.  `EventOwnedLayout` adds exactly that local
provenance: every owner is either the canonical owner of its cumulative endpoint in the current
parse, or lies outside the current parse's productive-owner window.  The latter alternative is
what makes the ledger stable under binary descent.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Cumulative concrete endpoint of block `i`. -/
public def blockEndpoint {g : IndexedGrammar T}
    (blocks : List (List g.flag)) (i : Fin blocks.length) : ℕ :=
  (blocks.take (i.val + 1)).flatten.length

/-- Read the owner aligned with a block index. -/
public def blockOwnerAt {g : IndexedGrammar T} {input : List T}
    {blocks : List (List g.flag)} (owners : List (Fin (10 * input.length)))
    (hlen : owners.length = blocks.length) (i : Fin blocks.length) :
    Fin (10 * input.length) :=
  owners.get ⟨i.val, by rw [hlen]; exact i.isLt⟩

/-- Cumulative endpoints are positive when every represented block is nonempty. -/
public theorem blockEndpoint_pos_of_blocks_nonempty
    {g : IndexedGrammar T} {blocks : List (List g.flag)}
    (hne : ∀ block ∈ blocks, block ≠ [])
    (i : Fin blocks.length) : 0 < blockEndpoint blocks i := by
  cases blocks with
  | nil => exact Fin.elim0 i
  | cons block blocks =>
      have hblock : 0 < block.length := List.length_pos_of_ne_nil (hne block (by simp))
      simp only [blockEndpoint, List.take_succ_cons, List.flatten_cons,
        List.length_append]
      omega

/-- An inherited owner belongs to a disjoint productive subtree when it lies outside the
current parse's contiguous owner window. -/
public def OutsideProductiveWindow
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (owner : Fin (10 * input.length)) : Prop :=
  owner.val < window.base ∨
    window.base + parse.productiveCount ≤ owner.val

/-- The distinguished persistent scratch owner is outside every productive window. -/
public theorem ProductiveOwnerWindow.scratchOwner_outside
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hinput : 0 < input.length) :
    OutsideProductiveWindow window
      (ProductiveOwnerWindow.scratchOwner (g := g) hinput) := by
  right
  have hend := window.end_le
  simp only [ProductiveOwnerWindow.scratchOwner_val]
  omega

/-- The distinguished collision owner is outside every productive window. -/
public theorem ProductiveOwnerWindow.transientOwner_outside
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hinput : 0 < input.length) :
    OutsideProductiveWindow window
      (ProductiveOwnerWindow.transientOwner (g := g) hinput) := by
  right
  have hend := window.end_le
  simp only [ProductiveOwnerWindow.transientOwner_val]
  omega

/-- Every reusable generic label lies beyond every primary productive-owner window. -/
public theorem ProductiveOwnerWindow.genericOwner_outside
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (window : ProductiveOwnerWindow (input := input) parse)
    {owner : Fin (10 * input.length)}
    (howner : owner ∈ genericOwnerRange g input) :
    OutsideProductiveWindow window owner := by
  right
  have hend := window.end_le
  have hge := genericOwnerRange_val_ge howner
  simp only [genericOwnerOffset] at hge
  omega

/-- Semantic owner refinement of `EventCompatible`.

At every nonempty physical block endpoint, either the aligned owner is the canonical current
event owner, or it is inherited from a disjoint productive window.  Binary children use the
second case for cuts contributed only by their sibling. -/
public structure EventOwnedLayout
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (window : ProductiveOwnerWindow (input := input) parse)
    (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length))) where
  compatible : EventCompatible parse blocks
  owners_length : owners.length = blocks.length
  endpoint_pos : ∀ i : Fin blocks.length, 0 < blockEndpoint blocks i
  owner_at : ∀ i : Fin blocks.length,
    (∃ hd : blockEndpoint blocks i ∈ parse.eventDepths,
      blockOwnerAt owners owners_length i =
        window.eventOwner (blockEndpoint blocks i) hd) ∨
    OutsideProductiveWindow window (blockOwnerAt owners owners_length i)

namespace EventOwnedLayout

@[simp] public theorem blockEndpoint_cons_succ
    {g : IndexedGrammar T} (block : List g.flag)
    (blocks : List (List g.flag)) (i : Fin blocks.length) :
    blockEndpoint (block :: blocks)
      ⟨i.val + 1, by
        simp only [List.length_cons]
        omega⟩ =
      block.length + blockEndpoint blocks i := by
  simp [blockEndpoint, List.take_succ_cons, Nat.add_assoc]

@[simp] public theorem blockOwnerAt_cons_succ
    {g : IndexedGrammar T} {input : List T}
    {block : List g.flag} {blocks : List (List g.flag)}
    (owner : Fin (10 * input.length))
    (owners : List (Fin (10 * input.length)))
    (hlen : (owner :: owners).length = (block :: blocks).length)
    (i : Fin blocks.length) :
    blockOwnerAt (owner :: owners) hlen
      ⟨i.val + 1, by
        simp only [List.length_cons]
        omega⟩ =
      blockOwnerAt owners (by simpa using hlen) i := by
  simp [blockOwnerAt]

@[simp] public theorem blockEndpoint_cons_zero
    {g : IndexedGrammar T} (block : List g.flag)
    (blocks : List (List g.flag)) :
    blockEndpoint (block :: blocks) ⟨0, by simp⟩ = block.length := by
  simp [blockEndpoint]

@[simp] public theorem blockOwnerAt_cons_zero
    {g : IndexedGrammar T} {input : List T}
    {block : List g.flag} {blocks : List (List g.flag)}
    (owner : Fin (10 * input.length))
    (owners : List (Fin (10 * input.length)))
    (hlen : (owner :: owners).length = (block :: blocks).length) :
    blockOwnerAt (owner :: owners) hlen ⟨0, by simp⟩ = owner := by
  simp [blockOwnerAt]

/-- Remove the first block while transporting endpoint-event ownership through a unary or
atomic-pop continuation.  The caller supplies precisely the semantic shift of endpoint owners;
the concrete list alignment is handled here. -/
public def tail
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    {window : ProductiveOwnerWindow (input := input) parse}
    {residualWindow : ProductiveOwnerWindow (input := input) residual}
    (ledger : EventOwnedLayout parse window (block :: blocks) (owner :: owners))
    (compatible : EventCompatible residual blocks)
    (endpoint_pos : ∀ i : Fin blocks.length, 0 < blockEndpoint blocks i)
    (outside : ∀ o, OutsideProductiveWindow window o →
      OutsideProductiveWindow residualWindow o)
    (owner_shift : ∀ (i : Fin blocks.length)
      (hd : block.length + blockEndpoint blocks i ∈ parse.eventDepths),
      ∃ hd' : blockEndpoint blocks i ∈ residual.eventDepths,
        window.eventOwner (block.length + blockEndpoint blocks i) hd =
          residualWindow.eventOwner (blockEndpoint blocks i) hd') :
    EventOwnedLayout residual residualWindow blocks owners where
  compatible := compatible
  owners_length := by simpa using ledger.owners_length
  endpoint_pos := endpoint_pos
  owner_at i := by
    let parentIndex : Fin (block :: blocks).length :=
      ⟨i.val + 1, by
        simp only [List.length_cons]
        omega⟩
    rcases ledger.owner_at parentIndex with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      have hdShift : block.length + blockEndpoint blocks i ∈ parse.eventDepths := by
        simpa [parentIndex] using hd
      rcases owner_shift i hdShift with ⟨hd', hshift⟩
      left
      refine ⟨hd', ?_⟩
      have howner' :
          blockOwnerAt owners (by simpa using ledger.owners_length) i =
            window.eventOwner (block.length + blockEndpoint blocks i) hdShift := by
        simpa [parentIndex] using howner
      exact howner'.trans hshift
    · right
      apply outside
      simpa [parentIndex] using hout

/-- Prepend a new physical block while transporting every old endpoint by the new block's
length.  The head's provenance is explicit, so this constructor supports both a canonical fresh
event owner and an owner inherited from outside the new window. -/
public def cons
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {nextParse : NFParse g B stack' w}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    {window : ProductiveOwnerWindow (input := input) parse}
    {nextWindow : ProductiveOwnerWindow (input := input) nextParse}
    (ledger : EventOwnedLayout parse window blocks owners)
    (compatible : EventCompatible nextParse (block :: blocks))
    (block_pos : 0 < block.length)
    (head_owner :
      (∃ hd : block.length ∈ nextParse.eventDepths,
        owner = nextWindow.eventOwner block.length hd) ∨
      OutsideProductiveWindow nextWindow owner)
    (outside : ∀ o, OutsideProductiveWindow window o →
      OutsideProductiveWindow nextWindow o)
    (owner_shift : ∀ (i : Fin blocks.length)
      (hd : blockEndpoint blocks i ∈ parse.eventDepths),
      ∃ hd' : block.length + blockEndpoint blocks i ∈ nextParse.eventDepths,
        window.eventOwner (blockEndpoint blocks i) hd =
          nextWindow.eventOwner (block.length + blockEndpoint blocks i) hd') :
    EventOwnedLayout nextParse nextWindow (block :: blocks) (owner :: owners) where
  compatible := compatible
  owners_length := by simp [ledger.owners_length]
  endpoint_pos := by
    intro i
    refine Fin.cases (by simpa [blockEndpoint] using block_pos) (fun j => ?_) i
    have heq : blockEndpoint (block :: blocks) (Fin.succ j) =
        block.length + blockEndpoint blocks j := by
      simp [blockEndpoint, List.take_succ_cons, Nat.add_assoc]
    rw [heq]
    omega
  owner_at := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [blockEndpoint, blockOwnerAt] using head_owner
    · have heq : blockEndpoint (block :: blocks) (Fin.succ j) =
          block.length + blockEndpoint blocks j := by
        simp [blockEndpoint, List.take_succ_cons, Nat.add_assoc]
      rw [heq]
      rcases ledger.owner_at j with hlocal | hout
      · rcases hlocal with ⟨hd, howner⟩
        rcases owner_shift j hd with ⟨hd', hshift⟩
        left
        refine ⟨hd', ?_⟩
        simpa [blockOwnerAt] using howner.trans hshift
      · right
        apply outside
        simpa [blockOwnerAt] using hout

/-- Adding one flag to the first block shifts every cumulative endpoint by one. -/
public theorem blockEndpoint_extendHead
    {g : IndexedGrammar T} (f : g.flag) (block : List g.flag)
    (blocks : List (List g.flag))
    (i : Fin (block :: blocks).length) :
    blockEndpoint ((f :: block) :: blocks) i =
      blockEndpoint (block :: blocks) i + 1 := by
  unfold blockEndpoint
  have hi : i.val + 1 = Nat.succ i.val := by omega
  rw [hi]
  simp only [List.take_succ_cons, List.flatten_cons, List.length_append,
    List.length_cons]
  omega

/-- Unary push windows have the same interval as their parents. -/
public theorem outside_pushChild
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    {owner : Fin (10 * input.length)}
    (hout : OutsideProductiveWindow window owner) :
    OutsideProductiveWindow window.pushChild owner := by
  simpa [OutsideProductiveWindow] using hout

/-- Specialized fresh-block transport for a unary push.  The new head may be either a canonical
depth-one event block or an inherited owner outside the child window. -/
public def pushFresh
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {newOwner : Fin (10 * input.length)}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    (ledger : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window blocks owners)
    (head_owner :
      (∃ h₁ : 1 ∈ rest.eventDepths,
        newOwner = window.pushChild.eventOwner 1 h₁) ∨
      OutsideProductiveWindow window.pushChild newOwner) :
    EventOwnedLayout rest window.pushChild ([f] :: blocks)
      (newOwner :: owners) := by
  apply ledger.cons (compatible := EventCompatible.pushFresh ledger.compatible)
    (block_pos := by simp) head_owner
  · intro owner hout
    exact outside_pushChild window hout
  · intro i hd
    have hdpos : 0 < blockEndpoint blocks i := ledger.endpoint_pos i
    have hchild : blockEndpoint blocks i + 1 ∈ rest.eventDepths :=
      window.exists_child_eventDepth_of_push_parent_pos hdpos hd
    refine ⟨by simpa [Nat.add_comm] using hchild, ?_⟩
    simpa [Nat.add_comm] using window.eventOwner_push_pos hdpos hchild

/-- Specialized fused-head transport for a unary push.  No owner is allocated: all old positive
endpoints and their owners shift together by one. -/
public def pushCompress
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)}
    (hdepthOne : 1 ∉ rest.eventDepths)
    (ledger : EventOwnedLayout
      (NFParse.push hr hlhs hc hrhs rest) window (block :: blocks) owners) :
    EventOwnedLayout rest window.pushChild ((f :: block) :: blocks) owners where
  compatible := EventCompatible.pushExtendHead hdepthOne ledger.compatible
  owners_length := by simpa using ledger.owners_length
  endpoint_pos := by
    intro i
    rw [blockEndpoint_extendHead]
    have := ledger.endpoint_pos i
    omega
  owner_at i := by
    have heq := blockEndpoint_extendHead f block blocks i
    rcases ledger.owner_at i with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      have hdpos := ledger.endpoint_pos i
      have hchild : blockEndpoint (block :: blocks) i + 1 ∈ rest.eventDepths :=
        window.exists_child_eventDepth_of_push_parent_pos hdpos hd
      left
      have hchild' : blockEndpoint ((f :: block) :: blocks) i ∈
          rest.eventDepths := by simpa [heq] using hchild
      refine ⟨hchild', ?_⟩
      have htransport := window.eventOwner_push_pos hdpos hchild
      have howners : blockOwnerAt owners (by simpa using ledger.owners_length) i =
          window.pushChild.eventOwner
            (blockEndpoint (block :: blocks) i + 1) hchild :=
        howner.trans htransport
      simpa [heq, blockOwnerAt] using howners
    · right
      apply outside_pushChild window
      simpa [blockOwnerAt] using hout

/-- Transport a tail ledger through an atomic whole-block pop.  This consumes exactly the owner
shift furnished by `exists_popContinuation_of_eventFree_block_with_owners`. -/
public def atomicPopTail
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {residual : NFParse g B stack' w}
    {block : List g.flag} {blocks : List (List g.flag)}
    {owner : Fin (10 * input.length)}
    {owners : List (Fin (10 * input.length))}
    {window : ProductiveOwnerWindow (input := input) parse}
    (ledger : EventOwnedLayout parse window (block :: blocks) (owner :: owners))
    (compatible : EventCompatible residual blocks)
    (endpoint_pos : ∀ i : Fin blocks.length, 0 < blockEndpoint blocks i)
    (hproductive : residual.productiveCount = parse.productiveCount)
    (hevents : ∀ d, d ∈ residual.eventDepths ↔
      block.length + d ∈ parse.eventDepths)
    (howners : ∀ d, residual.eventOwnerNat d =
      parse.eventOwnerNat (block.length + d)) :
    EventOwnedLayout residual (window.transport hproductive) blocks owners := by
  apply ledger.tail compatible endpoint_pos
  · intro o hout
    simpa [OutsideProductiveWindow, hproductive] using hout
  · intro i hd
    have hd' : blockEndpoint blocks i ∈ residual.eventDepths :=
      (hevents _).2 hd
    refine ⟨hd', ?_⟩
    apply Fin.ext
    simp only [ProductiveOwnerWindow.eventOwner_val,
      ProductiveOwnerWindow.transport_base]
    rw [howners]

/-- A canonical event owner whose depth differs from every represented endpoint is absent from
the layout's complete owner list.  Outside-window inherited owners cannot collide with it. -/
public theorem eventOwner_not_mem_owners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (ledger : EventOwnedLayout parse window blocks owners)
    {d : ℕ} (hd : d ∈ parse.eventDepths)
    (hdiff : ∀ i : Fin blocks.length, d ≠ blockEndpoint blocks i) :
    window.eventOwner d hd ∉ owners := by
  intro hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hget⟩
  have hi' : i < blocks.length := by
    rw [← ledger.owners_length]
    exact hi
  let j : Fin blocks.length := ⟨i, hi'⟩
  have hat : blockOwnerAt owners ledger.owners_length j =
      window.eventOwner d hd := by
    simpa [blockOwnerAt, j] using hget
  rcases ledger.owner_at j with hlocal | hout
  · rcases hlocal with ⟨he, howner⟩
    have heq : window.eventOwner (blockEndpoint blocks j) he =
        window.eventOwner d hd := howner.symm.trans hat
    have hdepth := window.eventOwner_injective he hd heq
    exact hdiff j hdepth.symm
  · have hval := congrArg Fin.val hat
    have hlt := parse.eventOwnerNat_lt_productiveCount hd
    simp only [ProductiveOwnerWindow.eventOwner_val] at hval
    rcases hout with hout | hout <;> omega

/-- Owners outside a parent window are outside its left binary subwindow. -/
public theorem outside_binaryLeft
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    {owner : Fin (10 * input.length)}
    (hout : OutsideProductiveWindow window owner) :
    OutsideProductiveWindow window.binaryLeft owner := by
  rcases hout with hout | hout
  · exact Or.inl (by
      simp only [ProductiveOwnerWindow.binaryLeft_base]
      omega)
  · right
    rw [NFParse.productiveCount_binary hr hlhs hc hrhs left right] at hout
    simp only [ProductiveOwnerWindow.binaryLeft_base]
    omega

/-- Owners outside a parent window are outside its right binary subwindow. -/
public theorem outside_binaryRight
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    {owner : Fin (10 * input.length)}
    (hout : OutsideProductiveWindow window owner) :
    OutsideProductiveWindow window.binaryRight owner := by
  rcases hout with hout | hout
  · exact Or.inl (by
      simp only [ProductiveOwnerWindow.binaryRight_base]
      omega)
  · right
    rw [NFParse.productiveCount_binary hr hlhs hc hrhs left right] at hout
    simp only [ProductiveOwnerWindow.binaryRight_base]
    omega

/-- Restrict an owner ledger to the left binary child.  Parent endpoints belonging only to the
right child become inherited owners outside the left productive window. -/
public def binaryLeft
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)}
    (ledger : EventOwnedLayout
      (NFParse.binary hr hlhs hc hrhs left right) window blocks owners) :
    EventOwnedLayout left window.binaryLeft blocks owners where
  compatible := ledger.compatible.binaryLeft
  owners_length := ledger.owners_length
  endpoint_pos := ledger.endpoint_pos
  owner_at i := by
    rcases ledger.owner_at i with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      have hd0 : blockEndpoint blocks i ≠ 0 :=
        Nat.ne_of_gt (ledger.endpoint_pos i)
      by_cases hleft : blockEndpoint blocks i ∈ left.eventDepths
      · left
        exact ⟨hleft, howner.trans
          (window.eventOwner_binaryLeft hd0 hleft)⟩
      · right
        have hright : blockEndpoint blocks i ∈ right.eventDepths := by
          simp only [NFParse.eventDepths, Finset.mem_insert,
            Finset.mem_union] at hd
          rcases hd with hd | hd
          · exact False.elim (hd0 hd)
          · exact hd.resolve_left hleft
        have heq := window.eventOwner_binaryRight hd0 hleft hright
        right
        have hval := congrArg Fin.val (howner.trans heq)
        simp only [ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.binaryLeft_base,
          ProductiveOwnerWindow.binaryRight_base] at hval ⊢
        omega
    · exact Or.inr (outside_binaryLeft window hout)

/-- Restrict an owner ledger to the right binary child.  Parent endpoints selected from the left
child become inherited owners outside the right productive window. -/
public def binaryRight
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)}
    (ledger : EventOwnedLayout
      (NFParse.binary hr hlhs hc hrhs left right) window blocks owners) :
    EventOwnedLayout right window.binaryRight blocks owners where
  compatible := ledger.compatible.binaryRight
  owners_length := ledger.owners_length
  endpoint_pos := ledger.endpoint_pos
  owner_at i := by
    rcases ledger.owner_at i with hlocal | hout
    · rcases hlocal with ⟨hd, howner⟩
      have hd0 : blockEndpoint blocks i ≠ 0 :=
        Nat.ne_of_gt (ledger.endpoint_pos i)
      by_cases hleft : blockEndpoint blocks i ∈ left.eventDepths
      · right
        have hleftOwner := window.eventOwner_binaryLeft hd0 hleft
        left
        have hval := congrArg Fin.val (howner.trans hleftOwner)
        have hlt := left.eventOwnerNat_lt_productiveCount hleft
        simp only [ProductiveOwnerWindow.eventOwner_val,
          ProductiveOwnerWindow.binaryLeft_base,
          ProductiveOwnerWindow.binaryRight_base] at hval ⊢
        omega
      · left
        have hright : blockEndpoint blocks i ∈ right.eventDepths := by
          simp only [NFParse.eventDepths, Finset.mem_insert,
            Finset.mem_union] at hd
          rcases hd with hd | hd
          · exact False.elim (hd0 hd)
          · exact hd.resolve_left hleft
        exact ⟨hright, howner.trans
          (window.eventOwner_binaryRight hd0 hleft hright)⟩
    · exact Or.inr (outside_binaryRight window hout)

end EventOwnedLayout
end Aho
end IndexedGrammar
