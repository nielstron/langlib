module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.CompressedState

@[expose]
public section

/-!
# Transporting canonical event boundaries through parse constructors

These lemmas isolate the block-boundary bookkeeping used by the compressed runner.  They do
not construct machine steps: they only transport `EventCompatible` across binary children and
the singleton/fused block layouts created by pop and push moves.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace EventCompatible

/-- A binary parent's compatible partition is compatible with its left child. -/
public def binaryLeft
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {blocks : List (List g.flag)}
    (compatible : EventCompatible
      (NFParse.binary hr hlhs hc hrhs left right) blocks) :
    EventCompatible left blocks where
  boundary d hd := compatible.boundary d (by
    simp only [NFParse.eventDepths, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl hd))

/-- A binary parent's compatible partition is compatible with its right child. -/
public def binaryRight
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {blocks : List (List g.flag)}
    (compatible : EventCompatible
      (NFParse.binary hr hlhs hc hrhs left right) blocks) :
    EventCompatible right blocks where
  boundary d hd := compatible.boundary d (by
    simp only [NFParse.eventDepths, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr hd))

/-- Compatible binary children combine into a compatible parent. -/
public def binary
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    {blocks : List (List g.flag)}
    (leftCompatible : EventCompatible left blocks)
    (rightCompatible : EventCompatible right blocks) :
    EventCompatible (NFParse.binary hr hlhs hc hrhs left right) blocks where
  boundary d hd := by
    if hd0 : d = 0 then
      exact hd0 ▸ BlockLayout.Boundary.start blocks
    else if hleft : d ∈ left.eventDepths then
      exact leftCompatible.boundary d hleft
    else
      have hright : d ∈ right.eventDepths := by
        simp only [NFParse.eventDepths, Finset.mem_insert, Finset.mem_union] at hd
        rcases hd with hd | hd
        · exact False.elim (hd0 hd)
        · exact hd.resolve_left hleft
      exact rightCompatible.boundary d hright

/-- Generic whole-block pop transport.  A caller only has to show that every residual event
depth shifts upward by the concrete length of the removed first block. -/
public def tailOfShift
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {parentStack residualStack : List g.flag}
    {parentYield residualYield : List T}
    {parent : NFParse g A parentStack parentYield}
    {residual : NFParse g B residualStack residualYield}
    {block : List g.flag} {blocks : List (List g.flag)}
    (hblock : block ≠ [])
    (compatible : EventCompatible parent (block :: blocks))
    (shift : ∀ d ∈ residual.eventDepths,
      block.length + d ∈ parent.eventDepths) :
    EventCompatible residual blocks where
  boundary d hd :=
    BlockLayout.Boundary.tail_of_cons hblock
      (compatible.boundary (block.length + d) (shift d hd))

/-- A structural pop removes its singleton first block and exposes a compatible residual parse. -/
public def popTail
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
    {rest : NFParse g B stack w} {blocks : List (List g.flag)}
    (compatible : EventCompatible (NFParse.pop hr hlhs hc hrhs rest)
      ([f] :: blocks)) :
    EventCompatible rest blocks where
  boundary d hd := by
    have parentBoundary := compatible.boundary (d + 1)
      (Finset.mem_image.mpr ⟨d, hd, by omega⟩)
    simpa [Nat.add_comm] using
      BlockLayout.Boundary.tail_of_cons (by simp : ([f] : List g.flag) ≠ [])
        (by simpa [Nat.add_comm] using parentBoundary)

/-- Conversely, prefixing the popped flag as a singleton block makes the pop parent compatible. -/
public def popCons
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
    {rest : NFParse g B stack w} {blocks : List (List g.flag)}
    (compatible : EventCompatible rest blocks) :
    EventCompatible (NFParse.pop hr hlhs hc hrhs rest) ([f] :: blocks) where
  boundary d hd := by
    have hdpos : 0 < d := by
      rcases Finset.mem_image.mp hd with ⟨e, _he, hed⟩
      omega
    have hrest : d - 1 ∈ rest.eventDepths := by
      rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
      have : d - 1 = e := by omega
      simpa [this] using he
    have heq : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
    exact heq ▸
      BlockLayout.Boundary.singletonCons f (compatible.boundary (d - 1) hrest)

/-- A fresh singleton block above the old partition is compatible with the pushed child. -/
public def pushFresh
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w} {blocks : List (List g.flag)}
    (compatible : EventCompatible (NFParse.push hr hlhs hc hrhs rest) blocks) :
    EventCompatible rest ([f] :: blocks) where
  boundary d hd := by
    cases d with
    | zero => exact BlockLayout.Boundary.start ([f] :: blocks)
    | succ d =>
        have parentEvent : d ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths :=
          Finset.mem_image.mpr ⟨d + 1, hd, by simp⟩
        exact BlockLayout.Boundary.singletonCons f
          (compatible.boundary d parentEvent)

/-- If the pushed child has no event at depth one, the new flag may be fused into the existing
first block while preserving all event boundaries. -/
public def pushExtendHead
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    {block : List g.flag} {blocks : List (List g.flag)}
    (hdepthOne : 1 ∉ rest.eventDepths)
    (compatible : EventCompatible (NFParse.push hr hlhs hc hrhs rest)
      (block :: blocks)) :
    EventCompatible rest ((f :: block) :: blocks) where
  boundary d hd := by
    cases d with
    | zero => exact BlockLayout.Boundary.start ((f :: block) :: blocks)
    | succ d =>
        cases d with
        | zero => exact False.elim (hdepthOne hd)
        | succ d =>
            have parentEvent : d + 1 ∈
                (NFParse.push hr hlhs hc hrhs rest).eventDepths :=
              Finset.mem_image.mpr ⟨d + 2, hd, by simp⟩
            exact BlockLayout.Boundary.extendHead_of_pos f (by omega)
              (compatible.boundary (d + 1) parentEvent)

end EventCompatible
end Aho
end IndexedGrammar
