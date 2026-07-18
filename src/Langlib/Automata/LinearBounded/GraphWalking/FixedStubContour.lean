module

public import Langlib.Automata.LinearBounded.FunctionalGraphReversibleTraversal
import Mathlib.Tactic

@[expose]
public section

/-!
# Euler contours with local fixed stubs

The canonical semantic port system has one fixed anchor per vertex.  A uniform
finite-control presentation naturally has additional ports for transition
candidates that are absent at a particular configuration.  Those ports are
fixed by edge-end swapping.  This module proves that such fixed stubs do not
break the standard ranked-tree contour induction.
-/

namespace FunctionalGraphReversibleTraversal

open Classical Relation

universe u v

namespace PortSystem

variable {V : Type u} {edge : V → V → Prop} (ports : PortSystem edge)

local instance : Fintype ports.Port := ports.portFintype
local instance : DecidableEq ports.Port := ports.portDecidableEq

/-- A ranked rooted component in which any number of non-edge ports may be
fixed by `swap`.  The other ports are the unique parent edge end or the far
end of a strictly lower-ranked child's parent port. -/
public structure FixedStubRankedTree where
  member : V → Prop
  rank : V → ℕ
  parentPort : V → Option ports.Port
  parent_endpoint : ∀ {vertex port}, parentPort vertex = some port →
    ports.endpoint port = vertex
  classify : ∀ (vertex : V) (port : ports.Port),
    member vertex → ports.endpoint port = vertex →
      ports.swap port = port ∨
      (∃ parent, parentPort vertex = some parent ∧ port = parent) ∨
      ∃ child childParent,
        member child ∧ rank child < rank vertex ∧
        parentPort child = some childParent ∧
        ports.swap childParent = port
  edge_parent : ∀ {source target}, member source → edge source target →
    ∃ parent, parentPort source = some parent ∧
      ports.endpoint (ports.swap parent) = target
  forward_closed : ∀ {source target}, member source → edge source target →
    member target

namespace FixedStubRankedTree

variable (tree : ports.FixedStubRankedTree)

/-- The inverse local rotation remains incident with the same vertex. -/
private theorem endpoint_rotate_symm (port : ports.Port) :
    ports.endpoint (ports.rotate⁻¹ port) = ports.endpoint port := by
  have h := ports.rotate_endpoint (ports.rotate⁻¹ port)
  simpa using h.symm

/-- The ranked-tree Euler contour remains complete when a vertex has any
number of additional fixed stubs.  Rotating onto such a stub immediately
continues at that same port. -/
public theorem eulerReaches_swap_parent
    {vertex : V} {parent port : ports.Port}
    (hmember : tree.member vertex)
    (hparent : tree.parentPort vertex = some parent)
    (hport : ports.endpoint port = vertex) :
    ReflTransGen ports.EulerEdge port (ports.swap parent) := by
  suffices houter : ∀ fuel vertex, tree.rank vertex = fuel →
      ∀ {parent port : ports.Port},
        tree.member vertex →
        tree.parentPort vertex = some parent →
        ports.endpoint port = vertex →
        ReflTransGen ports.EulerEdge port (ports.swap parent) by
    exact houter (tree.rank vertex) vertex rfl hmember hparent hport
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel outer =>
      intro vertex hrank parent port hmember hparent hport
      let trigger : ports.Port := ports.rotate⁻¹ parent
      have htrigger : ports.endpoint trigger = vertex := by
        rw [endpoint_rotate_symm (ports := ports)]
        exact tree.parent_endpoint hparent
      suffices hinner : ∀ distance port, ports.endpoint port = vertex →
          ports.rotationDistance port trigger = distance →
          ReflTransGen ports.EulerEdge port (ports.swap parent) by
        exact hinner (ports.rotationDistance port trigger) port hport rfl
      intro distance
      induction distance using Nat.strong_induction_on with
      | h distance inner =>
          intro port hport hdistance
          by_cases hatTrigger : port = trigger
          · subst port
            apply ReflTransGen.single
            change ports.swap (ports.rotate trigger) = ports.swap parent
            simp [trigger]
          · let next : ports.Port := ports.rotate port
            have hnext : ports.endpoint next = vertex := by
              rw [ports.rotate_endpoint, hport]
            have hsmaller : ports.rotationDistance next trigger < distance := by
              rw [← hdistance]
              exact ports.rotationDistance_rotate_lt
                (hport.trans htrigger.symm) hatTrigger
            have hcontinue :
                ReflTransGen ports.EulerEdge next (ports.swap parent) :=
              inner (ports.rotationDistance next trigger) hsmaller next hnext rfl
            rcases tree.classify vertex next hmember hnext with
              hfixed | hparentPort |
                ⟨child, childParent, hchildMember, hchildRank,
                  hchildParent, hchildSwap⟩
            · have hstep : ports.EulerEdge port next := by
                change ports.swap next = next
                exact hfixed
              exact hcontinue.head hstep
            · obtain ⟨otherParent, hotherParent, hnextParent⟩ := hparentPort
              have hparents : otherParent = parent := by
                rw [hparent] at hotherParent
                exact (Option.some.inj hotherParent).symm
              have hrotate : ports.rotate port = parent := by
                simpa [next, hparents] using hnextParent
              have : port = trigger := by
                dsimp only [trigger]
                apply ports.rotate.injective
                simpa using hrotate
              exact (hatTrigger this).elim
            · have hchildFuel : tree.rank child < fuel := by
                simpa [hrank] using hchildRank
              have hchildEndpoint : ports.endpoint childParent = child :=
                tree.parent_endpoint hchildParent
              have hchildTour : ReflTransGen ports.EulerEdge
                  childParent (ports.swap childParent) :=
                outer (tree.rank child) hchildFuel child rfl
                  hchildMember hchildParent hchildEndpoint
              have hswapNext : ports.swap next = childParent := by
                rw [← hchildSwap]
                exact ports.swap_involution childParent
              have hdescend : ports.EulerEdge port childParent := by
                change ports.swap (ports.rotate port) = childParent
                exact hswapNext
              have hreturn : ReflTransGen ports.EulerEdge childParent next := by
                simpa [hchildSwap] using hchildTour
              exact (hreturn.head hdescend).trans hcontinue

/-- A source directed path is contained in the local Euler contour of a
fixed-stub ranked tree. -/
public theorem eulerReaches_endpoint_of_reaches
    {source target : V} {start : ports.Port}
    (hmember : tree.member source)
    (hstart : ports.endpoint start = source)
    (hreach : ReflTransGen edge source target) :
    ∃ finish, ReflTransGen ports.EulerEdge start finish ∧
      ports.endpoint finish = target := by
  induction hreach using Relation.ReflTransGen.head_induction_on generalizing start with
  | refl => exact ⟨start, .refl, hstart⟩
  | @head source middle hstep _ ih =>
      obtain ⟨parent, hparent, htarget⟩ := tree.edge_parent hmember hstep
      have hcross := eulerReaches_swap_parent (ports := ports) tree
        hmember hparent hstart
      have hmiddleMember := tree.forward_closed hmember hstep
      obtain ⟨finish, hfinish, hfinishEndpoint⟩ :=
        ih hmiddleMember htarget
      exact ⟨finish, hcross.trans hfinish, hfinishEndpoint⟩

/-- Anchor-start form of fixed-stub contour completeness. -/
public theorem eulerReaches_accept_of_reaches
    {source accept : V} (hmember : tree.member source)
    (hreach : ReflTransGen edge source accept) :
    ∃ finish,
      ReflTransGen ports.EulerEdge (ports.anchor source) finish ∧
      ports.endpoint finish = accept :=
  eulerReaches_endpoint_of_reaches (ports := ports) tree
    hmember (ports.endpoint_anchor source) hreach

end FixedStubRankedTree

end PortSystem

end FunctionalGraphReversibleTraversal

end
