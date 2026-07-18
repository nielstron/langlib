module

public import Langlib.Automata.LinearBounded.FiniteAcyclicRank
public import Langlib.Automata.LinearBounded.PermutationReachability
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

@[expose]
public section

/-!
# Finite reversible traversal of a functional graph

This module isolates the finite-graph semantic core of the
Lange--McKenzie--Tapp traversal.  A port system supplies two reversible local
operations on a finite graph:

* `rotate` cyclically enumerates all edge ends incident with the current
  vertex;
* `swap` crosses an edge from one end to the other.

For arbitrary port systems the single permutation `rotate * swap` need not
have one orbit, so the module first gives a finite exhaustive fallback
schedule.  For the canonical edge-end system on the backward basin of a
terminal vertex, however, functionality makes the component a ranked rooted
tree.  The standard contour induction then proves that `rotate * swap` itself
has one orbit on every port of that basin.

For a functional directed graph and a terminal accepting vertex, weak
connectivity to that vertex is equivalent to directed reachability.  Combining
this fact with both traversal constructions proves exact acceptance
equivalence.  The local Euler orbit has a witness bounded by the finite order
of its permutation, so a controller can inspect one cycle and halt even if the
represented source computation lies in a nonterminating directed cycle.

The construction here is deliberately semantic.  Its witness schedule uses
finite choice, and this module does not implement the port operations or the
phase schedule on an LBA tape.
-/

namespace FunctionalGraphReversibleTraversal

open Classical Relation

universe u v

/-! ## Functional components and terminal sinks -/

/-- The undirected adjacency relation underlying a directed relation. -/
@[expose]
public def WeakStep {V : Type u} (edge : V → V → Prop) : V → V → Prop :=
  fun left right => edge left right ∨ edge right left

/-- Undirected adjacency is symmetric. -/
public theorem weakStep_symmetric {V : Type u} (edge : V → V → Prop) :
    Symmetric (WeakStep edge) := by
  intro left right hstep
  exact hstep.symm

/-- Along one functional edge, the two endpoints either both reach a fixed
terminal vertex or neither does. -/
private theorem reaches_sink_iff_of_edge
    {V : Type u} {edge : V → V → Prop}
    (functional : Relator.RightUnique edge) {sink source target : V}
    (sink_terminal : ∀ next, ¬ edge sink next)
    (hstep : edge source target) :
    ReflTransGen edge source sink ↔ ReflTransGen edge target sink := by
  constructor
  · intro hreach
    rcases hreach.cases_head with heq | ⟨next, hfirst, hrest⟩
    · subst source
      exact (sink_terminal target hstep).elim
    · have htarget : target = next := functional hstep hfirst
      simpa [htarget] using hrest
  · intro hreach
    exact hreach.head hstep

/-- Reachability of a terminal sink is invariant across one weak edge of a
functional graph. -/
private theorem reaches_sink_iff_of_weakStep
    {V : Type u} {edge : V → V → Prop}
    (functional : Relator.RightUnique edge) {sink source target : V}
    (sink_terminal : ∀ next, ¬ edge sink next)
    (hstep : WeakStep edge source target) :
    ReflTransGen edge source sink ↔ ReflTransGen edge target sink := by
  rcases hstep with hforward | hbackward
  · exact reaches_sink_iff_of_edge functional sink_terminal hforward
  · exact (reaches_sink_iff_of_edge functional sink_terminal hbackward).symm

/-- In a functional graph, a vertex is weakly connected to a terminal sink
exactly when its unique forward computation reaches that sink.

No acyclicity promise is needed.  A component containing a directed cycle and
no terminal vertex simply lies outside the sink's weak component. -/
public theorem weakReaches_sink_iff_reaches
    {V : Type u} {edge : V → V → Prop}
    (functional : Relator.RightUnique edge) {source sink : V}
    (sink_terminal : ∀ next, ¬ edge sink next) :
    ReflTransGen (WeakStep edge) source sink ↔
      ReflTransGen edge source sink := by
  constructor
  · intro hweak
    have hreverse : ReflTransGen (WeakStep edge) sink source :=
      hweak.symmetric (weakStep_symmetric edge)
    have hpropagate :
        ReflTransGen edge sink sink → ReflTransGen edge source sink := by
      refine ReflTransGen.trans_induction_on
        (motive := fun {left right} _ =>
          ReflTransGen edge left sink → ReflTransGen edge right sink)
        hreverse ?_ ?_ ?_
      · intro vertex hreach
        exact hreach
      · intro left right hstep hreach
        exact (reaches_sink_iff_of_weakStep functional sink_terminal hstep).mp hreach
      · intro left middle right _ _ hleft hright hreach
        exact hright (hleft hreach)
    exact hpropagate .refl
  · intro hreach
    exact hreach.lift id (fun _ _ hstep => Or.inl hstep)

/-! ### Finite path lengths inside a terminating basin -/

/-- A directed path carrying its exact number of edges. -/
public inductive ReachesIn {V : Type u} (edge : V → V → Prop) :
    ℕ → V → V → Prop
  | zero (vertex) : ReachesIn edge 0 vertex vertex
  | succ {source middle target length} :
      edge source middle → ReachesIn edge length middle target →
        ReachesIn edge (length + 1) source target

/-- Forgetting the length gives ordinary reflexive-transitive reachability. -/
public theorem ReachesIn.reflTransGen
    {V : Type u} {edge : V → V → Prop}
    {length : ℕ} {source target : V}
    (path : ReachesIn edge length source target) :
    ReflTransGen edge source target := by
  induction path with
  | zero => exact .refl
  | succ hstep _ ih => exact ih.head hstep

/-- Every finite reflexive-transitive path has an exact natural length. -/
public theorem reaches_iff_exists_reachesIn
    {V : Type u} {edge : V → V → Prop} {source target : V} :
    ReflTransGen edge source target ↔
      ∃ length, ReachesIn edge length source target := by
  constructor
  · intro hreach
    induction hreach using ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .zero _⟩
    | head hstep _ ih =>
        obtain ⟨length, hlength⟩ := ih
        exact ⟨length + 1, .succ hstep hlength⟩
  · rintro ⟨_, path⟩
    exact path.reflTransGen

/-- Least directed-path length to a target, with zero as an irrelevant default
outside the target's backward basin. -/
noncomputable def distanceTo
    {V : Type u} (edge : V → V → Prop) (target source : V) : ℕ :=
  if h : ∃ length, ReachesIn edge length source target then Nat.find h else 0

/-- The least distance realizes a path whenever the target is reachable. -/
public theorem reachesIn_distanceTo
    {V : Type u} {edge : V → V → Prop} {source target : V}
    (hreach : ReflTransGen edge source target) :
    ReachesIn edge (distanceTo edge target source) source target := by
  have hexists := reaches_iff_exists_reachesIn.mp hreach
  rw [distanceTo, dif_pos hexists]
  exact Nat.find_spec hexists

/-- Along a functional edge inside the basin of a terminal target, least
distance to the target strictly decreases. -/
public theorem distanceTo_lt_of_edge
    {V : Type u} {edge : V → V → Prop}
    (functional : Relator.RightUnique edge) {source next target : V}
    (target_terminal : ∀ after, ¬ edge target after)
    (hstep : edge source next)
    (hreach : ReflTransGen edge source target) :
    distanceTo edge target next < distanceTo edge target source := by
  have hpath := reachesIn_distanceTo hreach
  generalize hdistance : distanceTo edge target source = distance at hpath
  cases hpath with
  | zero => exact (target_terminal next hstep).elim
  | @succ _ middle _ length hfirst hrest =>
      have hnext : next = middle := functional hstep hfirst
      subst next
      have hnextReach := hrest.reflTransGen
      have hexists := reaches_iff_exists_reachesIn.mp hnextReach
      have hle : distanceTo edge target middle ≤ length := by
        rw [distanceTo, dif_pos hexists]
        exact Nat.find_min' hexists hrest
      exact hle.trans_lt (Nat.lt_succ_self length)

/-- The backward basin of one designated target. -/
public abbrev Basin {V : Type u} (edge : V → V → Prop) (target : V) :=
  { vertex : V // ReflTransGen edge vertex target }

/-- The source relation restricted to a target's backward basin. -/
@[expose]
public def BasinEdge {V : Type u} (edge : V → V → Prop) (target : V) :
    Basin edge target → Basin edge target → Prop :=
  fun source next => edge source.val next.val

/-- A functional relation restricted to the basin of a terminal target is
acyclic.  Least distance to the target strictly decreases around every source
edge, so a nonempty directed cycle would give a strict self-inequality. -/
public theorem basinEdge_acyclic
    {V : Type u} {edge : V → V → Prop}
    (functional : Relator.RightUnique edge) {target : V}
    (target_terminal : ∀ next, ¬ edge target next) :
    ∀ vertex : Basin edge target,
      ¬ TransGen (BasinEdge edge target) vertex vertex := by
  have hdecrease : ∀ {source next : Basin edge target},
      BasinEdge edge target source next →
        distanceTo edge target next.val < distanceTo edge target source.val := by
    intro source next hstep
    exact distanceTo_lt_of_edge functional target_terminal hstep source.property
  have hpath : ∀ {source next : Basin edge target},
      TransGen (BasinEdge edge target) source next →
        distanceTo edge target next.val < distanceTo edge target source.val := by
    intro source next path
    induction path with
    | single hstep => exact hdecrease hstep
    | tail _ hstep ih => exact (hdecrease hstep).trans ih
  intro vertex hcycle
  exact (Nat.lt_irrefl _) (hpath hcycle)

/-- Ancestor-count rank inside the terminating basin, extended by zero outside
that basin. -/
noncomputable def basinRank
    {V : Type u} [Fintype V] (edge : V → V → Prop) (target vertex : V) : ℕ :=
  if hmember : ReflTransGen edge vertex target then
    letI : Fintype (Basin edge target) := Fintype.ofFinite _
    FiniteAcyclicRank.rank (BasinEdge edge target) ⟨vertex, hmember⟩
  else
    0

/-- Basin ancestor rank strictly increases along every functional edge toward
the terminal target. -/
public theorem basinRank_lt_of_edge
    {V : Type u} [Fintype V] {edge : V → V → Prop}
    (functional : Relator.RightUnique edge) {target source next : V}
    (target_terminal : ∀ after, ¬ edge target after)
    (hsource : ReflTransGen edge source target)
    (hstep : edge source next) :
    basinRank edge target source < basinRank edge target next := by
  have hnext : ReflTransGen edge next target :=
    (reaches_sink_iff_of_edge functional target_terminal hstep).mp hsource
  letI : Fintype (Basin edge target) := Fintype.ofFinite _
  have hrank := FiniteAcyclicRank.rank_lt_of_edge
    (basinEdge_acyclic functional target_terminal)
    (source := (⟨source, hsource⟩ : Basin edge target))
    (target := (⟨next, hnext⟩ : Basin edge target)) hstep
  simpa [basinRank, hsource, hnext] using hrank

/-! ## Abstract port systems -/

/-- Rotate an arbitrary finite type through the order supplied by its canonical
equivalence with `Fin`. -/
noncomputable def cyclicPerm (A : Type*) [Fintype A] : Equiv.Perm A :=
  (Fintype.equivFin A).trans (finRotate (Fintype.card A)) |>.trans
    (Fintype.equivFin A).symm

/-- A positive finite rotation reaches every element from every other element. -/
private theorem finRotate_reaches_everywhere
    {n : ℕ} [NeZero n] (source target : Fin n) :
    ReflTransGen (PermutationReachability.PowerEdge (finRotate n)) source target := by
  by_cases hone : n = 1
  · subst n
    have heq : source = target := Subsingleton.elim _ _
    subst target
    exact .refl
  · have hn : 2 ≤ n := by
      have hpos : 0 < n := NeZero.pos n
      omega
    have hsource : finRotate n source ≠ source := by
      rw [← Equiv.Perm.mem_support]
      simp [support_finRotate_of_le hn]
    have htarget : finRotate n target ≠ target := by
      rw [← Equiv.Perm.mem_support]
      simp [support_finRotate_of_le hn]
    have hsame : (finRotate n).SameCycle source target :=
      (isCycle_finRotate_of_le hn).sameCycle hsource htarget
    obtain ⟨power, hpower⟩ := hsame.exists_nat_pow_eq
    simpa [hpower] using
      PermutationReachability.reaches_pow (finRotate n) source power

/-- The canonical cyclic permutation of a nonempty finite type has a single
reachability orbit. -/
theorem cyclicPerm_reaches_everywhere
    {A : Type*} [Fintype A] [Nonempty A] (source target : A) :
    ReflTransGen (PermutationReachability.PowerEdge (cyclicPerm A)) source target := by
  let equivalence := Fintype.equivFin A
  letI : NeZero (Fintype.card A) :=
    ⟨Fintype.card_ne_zero⟩
  have hfinite := finRotate_reaches_everywhere (equivalence source) (equivalence target)
  have hlift : ReflTransGen
      (PermutationReachability.PowerEdge (cyclicPerm A)) source target :=
    by
      simpa [equivalence] using
        (ReflTransGen.lift
          (p := PermutationReachability.PowerEdge (cyclicPerm A))
          equivalence.symm (fun left right hstep => by
            change cyclicPerm A (equivalence.symm left) = equivalence.symm right
            change (finRotate (Fintype.card A)) left = right at hstep
            simp only [cyclicPerm, equivalence, Equiv.trans_apply,
              Equiv.apply_symm_apply, hstep]) hfinite)
  simpa [equivalence] using hlift

/-- Reachability under one permutation is exactly equality with a nonnegative
power of that permutation. -/
public theorem powerEdge_reaches_iff_exists_pow
    {A : Type*} (permutation : Equiv.Perm A) {source target : A} :
    ReflTransGen (PermutationReachability.PowerEdge permutation) source target ↔
      ∃ power : ℕ, (permutation ^ power) source = target := by
  constructor
  · intro hreach
    induction hreach with
    | refl => exact ⟨0, rfl⟩
    | tail _ hstep ih =>
        obtain ⟨power, hpower⟩ := ih
        refine ⟨power + 1, ?_⟩
        change permutation _ = _ at hstep
        simpa [pow_succ', Equiv.Perm.mul_apply, hpower] using hstep
  · rintro ⟨power, rfl⟩
    exact PermutationReachability.reaches_pow permutation source power

/-- Reversible local access to the edge ends of a finite directed graph.

The `anchor` gives a distinguished port at every vertex, including isolated
vertices.  `rotate_complete` says that forward rotations enumerate the entire
fiber of ports at one vertex.  `swap` is an involution; it crosses every graph
edge by `edge_port`, and `swap_sound` prevents it from crossing between
unrelated weak components. -/
public structure PortSystem {V : Type u} (edge : V → V → Prop) where
  Port : Type v
  portFintype : Fintype Port
  portDecidableEq : DecidableEq Port
  endpoint : Port → V
  anchor : V → Port
  endpoint_anchor : ∀ vertex, endpoint (anchor vertex) = vertex
  rotate : Equiv.Perm Port
  rotate_endpoint : ∀ port, endpoint (rotate port) = endpoint port
  rotate_complete : ∀ left right, endpoint left = endpoint right →
    ReflTransGen (PermutationReachability.PowerEdge rotate) left right
  swap : Equiv.Perm Port
  swap_involution : ∀ port, swap (swap port) = port
  swap_sound : ∀ port,
    ReflTransGen (WeakStep edge) (endpoint port) (endpoint (swap port))
  edge_port : ∀ {source target}, edge source target →
    ∃ port, endpoint port = source ∧ endpoint (swap port) = target

namespace PortSystem

variable {V : Type u} {edge : V → V → Prop} (ports : PortSystem edge)

local instance : Fintype ports.Port := ports.portFintype
local instance : DecidableEq ports.Port := ports.portDecidableEq

/-! ### The local Euler permutation -/

/-- One standard Euler step: rotate to the next port at the current vertex,
then swap to the other end of the selected edge. -/
@[expose]
public def euler : Equiv.Perm ports.Port :=
  ports.rotate.trans ports.swap

/-- The one-step relation of the local Euler permutation. -/
@[expose]
public def EulerEdge : ports.Port → ports.Port → Prop :=
  PermutationReachability.PowerEdge ports.euler

/-- A local Euler step is a partial bijection (in fact, a total permutation). -/
public theorem eulerEdge_biUnique : Relator.BiUnique ports.EulerEdge := by
  constructor
  · intro left right target hleft hright
    exact ports.euler.injective (hleft.trans hright.symm)
  · intro source left right hleft hright
    exact hleft.symm.trans hright

/-- On finite ports, reachability under the Euler permutation is symmetric.
Equivalently, every Euler orbit is a directed cycle rather than a one-way
path. -/
public theorem eulerReaches_symmetric :
    Symmetric (ReflTransGen ports.EulerEdge) := by
  exact PermutationReachability.reflTransGen_symmetric_of_reverse_steps
    (fun hstep => PermutationReachability.reverse_powerEdge_reaches
      ports.euler hstep)

/-- Every reachable Euler port is reached before the order of the finite
Euler permutation.  Thus a controller can inspect one bounded cycle and then
halt, even when the represented functional computation itself enters a
directed cycle. -/
public theorem eulerReaches_iff_exists_lt_orderOf
    {source target : ports.Port} :
    ReflTransGen ports.EulerEdge source target ↔
      ∃ steps < orderOf ports.euler,
        (ports.euler ^ steps) source = target := by
  constructor
  · intro hreach
    obtain ⟨steps, hsteps⟩ :=
      (powerEdge_reaches_iff_exists_pow ports.euler).mp hreach
    refine ⟨steps % orderOf ports.euler,
      Nat.mod_lt _ (orderOf_pos ports.euler), ?_⟩
    rw [pow_mod_orderOf]
    exact hsteps
  · rintro ⟨steps, _, hsteps⟩
    exact (powerEdge_reaches_iff_exists_pow ports.euler).mpr ⟨steps, hsteps⟩

/-- After its finite group order, the Euler permutation returns every port to
itself. -/
public theorem euler_pow_orderOf (port : ports.Port) :
    (ports.euler ^ orderOf ports.euler) port = port := by
  rw [pow_orderOf_eq_one]
  rfl

/-- A local Euler run accepts when it reaches any port incident with the
designated accepting vertex. -/
@[expose]
public def EulerAccepts (source accept : V) : Prop :=
  ∃ finish, ReflTransGen ports.EulerEdge (ports.anchor source) finish ∧
    ports.endpoint finish = accept

/-- One Euler step stays within the weak component of its source endpoint. -/
private theorem weakReaches_endpoint_eulerStep
    (port : ports.Port) :
    ReflTransGen (WeakStep edge) (ports.endpoint port)
      (ports.endpoint (ports.euler port)) := by
  have hswap := ports.swap_sound (ports.rotate port)
  change ReflTransGen (WeakStep edge) (ports.endpoint port)
    (ports.endpoint (ports.swap (ports.rotate port)))
  simpa [ports.rotate_endpoint] using hswap

/-- Every local Euler orbit is sound for weak connectivity of represented
vertices. -/
public theorem weakReaches_endpoint_of_eulerReaches
    {source target : ports.Port}
    (hreach : ReflTransGen ports.EulerEdge source target) :
    ReflTransGen (WeakStep edge) (ports.endpoint source) (ports.endpoint target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      change ports.euler _ = _ at hstep
      subst_vars
      exact ih.trans (ports.weakReaches_endpoint_eulerStep _)

/-- Euler acceptance implies weak connectivity to the accepting vertex. -/
public theorem weakReaches_of_eulerAccepts {source accept : V}
    (haccept : ports.EulerAccepts source accept) :
    ReflTransGen (WeakStep edge) source accept := by
  obtain ⟨finish, hreach, hfinish⟩ := haccept
  have hweak := ports.weakReaches_endpoint_of_eulerReaches hreach
  simpa [ports.endpoint_anchor, hfinish] using hweak

/-- The chosen least number of local rotations carrying one port to another;
zero is used only when the endpoints differ. -/
noncomputable def rotationDistance (source target : ports.Port) : ℕ :=
  if h : ∃ power : ℕ, (ports.rotate ^ power) source = target then
    Nat.find h
  else
    0

/-- Ports at one vertex are related by the power selected by
`rotationDistance`. -/
public theorem rotate_pow_rotationDistance
    {source target : ports.Port}
    (hsame : ports.endpoint source = ports.endpoint target) :
    (ports.rotate ^ ports.rotationDistance source target) source = target := by
  have hexists : ∃ power : ℕ, (ports.rotate ^ power) source = target :=
    (powerEdge_reaches_iff_exists_pow ports.rotate).mp
      (ports.rotate_complete source target hsame)
  rw [rotationDistance, dif_pos hexists]
  exact Nat.find_spec hexists

/-- Unless the target has already been reached, rotating once strictly
decreases the chosen rotation distance. -/
public theorem rotationDistance_rotate_lt
    {source target : ports.Port}
    (hsame : ports.endpoint source = ports.endpoint target)
    (hne : source ≠ target) :
    ports.rotationDistance (ports.rotate source) target <
      ports.rotationDistance source target := by
  have hspec := ports.rotate_pow_rotationDistance hsame
  have hpositive : 0 < ports.rotationDistance source target := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, pow_zero] at hspec
    exact hne hspec
  obtain ⟨distance, hdistance⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  have hwitness : (ports.rotate ^ distance) (ports.rotate source) = target := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ]
    simpa [hdistance, Nat.succ_eq_add_one] using hspec
  have hexists : ∃ power : ℕ,
      (ports.rotate ^ power) (ports.rotate source) = target := ⟨distance, hwitness⟩
  rw [rotationDistance, dif_pos hexists, hdistance]
  exact Nat.find_min' hexists hwitness |>.trans_lt (Nat.lt_succ_self distance)

/-! ### Ranked rooted components -/

/-- The additional data needed to view one port system as a finite rooted
forest.  A non-root vertex has one `parentPort`; every other non-anchor port is
the far end of the parent port of a strictly lower-ranked child.  Thus the rank
orients the forest toward its roots without assuming any particular cyclic
ordering of sibling ports. -/
public structure RankedTree where
  member : V → Prop
  rank : V → ℕ
  parentPort : V → Option ports.Port
  parent_endpoint : ∀ {vertex port}, parentPort vertex = some port →
    ports.endpoint port = vertex
  anchor_fixed : ∀ vertex, ports.swap (ports.anchor vertex) = ports.anchor vertex
  classify : ∀ (vertex : V) (port : ports.Port),
    member vertex → ports.endpoint port = vertex →
      port = ports.anchor vertex ∨
      (∃ parent, parentPort vertex = some parent ∧ port = parent) ∨
      ∃ child childParent,
        member child ∧ rank child < rank vertex ∧
        parentPort child = some childParent ∧
        ports.swap childParent = port
  edge_parent : ∀ {source target}, member source → edge source target →
    ∃ parent, parentPort source = some parent ∧
      ports.endpoint (ports.swap parent) = target
  forward_closed : ∀ {source target}, member source → edge source target → member target

namespace RankedTree

variable (tree : ports.RankedTree)

/-- The inverse rotation of a port is incident with the same vertex. -/
private theorem endpoint_rotate_symm (port : ports.Port) :
    ports.endpoint (ports.rotate⁻¹ port) = ports.endpoint port := by
  have h := ports.rotate_endpoint (ports.rotate⁻¹ port)
  simpa using h.symm

/-- **Local Euler-tour theorem.**  At a non-root vertex of a ranked rooted
component, iterating the single local permutation `swap ∘ rotate` from any
incident port eventually crosses the vertex's parent edge.

The proof is the standard contour induction.  Rotate toward the port just
before the parent port.  Passing an anchor is immediate because anchors are
fixed by swap.  Passing a child port descends to the child's parent port; the
strictly smaller child rank completes that subtree excursion and returns to
the same child port. -/
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
              exact ports.rotationDistance_rotate_lt (hport.trans htrigger.symm) hatTrigger
            have hcontinue :
                ReflTransGen ports.EulerEdge next (ports.swap parent) :=
              inner (ports.rotationDistance next trigger) hsmaller next hnext rfl
            rcases tree.classify vertex next hmember hnext with
              hanchor | hparentPort | ⟨child, childParent, hchildMember,
                hchildRank, hchildParent, hchildSwap⟩
            · have hstep : ports.EulerEdge port next := by
                change ports.swap next = next
                rw [hanchor, tree.anchor_fixed]
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

/-- Following any original directed path can be simulated by the local Euler
permutation, ending at a port incident with the same target vertex. -/
public theorem eulerReaches_endpoint_of_reaches
    (tree : ports.RankedTree)
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
      obtain ⟨finish, hfinish, hfinishEndpoint⟩ := ih hmiddleMember htarget
      exact ⟨finish, hcross.trans hfinish, hfinishEndpoint⟩

/-- In particular, the local Euler permutation reaches every terminal vertex
that the original functional computation reaches. -/
public theorem eulerReaches_accept_of_reaches
    (tree : ports.RankedTree)
    {source accept : V} (hmember : tree.member source)
    (hreach : ReflTransGen edge source accept) :
    ∃ finish,
      ReflTransGen ports.EulerEdge (ports.anchor source) finish ∧
      ports.endpoint finish = accept :=
  eulerReaches_endpoint_of_reaches (ports := ports) tree
    hmember (ports.endpoint_anchor source) hreach

end RankedTree

/-- The three reversible primitive actions used by the exhaustive traversal. -/
public inductive Action where
  | rotate
  | unrotate
  | swap
  deriving DecidableEq, Fintype

/-- The port permutation performed by one primitive action. -/
@[expose]
public def actionPerm : Action → Equiv.Perm ports.Port
  | .rotate => ports.rotate
  | .unrotate => ports.rotate⁻¹
  | .swap => ports.swap

/-- The syntactic inverse of a primitive action. -/
@[expose]
public def inverseAction : Action → Action
  | .rotate => .unrotate
  | .unrotate => .rotate
  | .swap => .swap

@[simp]
public theorem inverseAction_inverseAction (action : Action) :
    inverseAction (inverseAction action) = action := by
  cases action <;> rfl

/-- Applying an action followed by its syntactic inverse restores the port. -/
@[simp]
public theorem actionPerm_inverseAction_apply
    (action : Action) (port : ports.Port) :
    ports.actionPerm (inverseAction action)
        (ports.actionPerm action port) = port := by
  cases action
  · exact ports.rotate.symm_apply_apply port
  · exact ports.rotate.apply_symm_apply port
  · exact ports.swap_involution port

/-- Execute a word of primitive reversible actions from left to right. -/
@[expose]
public def execute : List Action → ports.Port → ports.Port
  | [], port => port
  | action :: actions, port =>
      execute actions (ports.actionPerm action port)

@[simp]
public theorem execute_nil (port : ports.Port) : ports.execute [] port = port := rfl

@[simp]
public theorem execute_cons (action : Action) (actions : List Action)
    (port : ports.Port) :
    ports.execute (action :: actions) port =
      ports.execute actions (ports.actionPerm action port) := rfl

/-- Executing an appended word executes its left part first. -/
public theorem execute_append (first second : List Action) (port : ports.Port) :
    ports.execute (first ++ second) port =
      ports.execute second (ports.execute first port) := by
  induction first generalizing port with
  | nil => rfl
  | cons action first ih =>
      simp only [List.cons_append, execute_cons]
      exact ih (ports.actionPerm action port)

/-- Reverse a word and invert every action. -/
@[expose]
public def inverseWord (actions : List Action) : List Action :=
  actions.reverse.map inverseAction

/-- Every action word is undone exactly by its inverse word. -/
@[simp]
public theorem execute_inverseWord (actions : List Action) (port : ports.Port) :
    ports.execute (inverseWord actions) (ports.execute actions port) = port := by
  induction actions generalizing port with
  | nil => rfl
  | cons action actions ih =>
      rw [execute_cons]
      rw [show inverseWord (action :: actions) =
          inverseWord actions ++ [inverseAction action] by
        simp [inverseWord]]
      rw [execute_append, ih]
      exact ports.actionPerm_inverseAction_apply action port

/-- One edge in the graph generated by the reversible primitive actions. -/
@[expose]
public def ActionEdge (source target : ports.Port) : Prop :=
  ∃ action, ports.actionPerm action source = target

/-- Every action edge can be reversed by one action edge. -/
public theorem actionEdge_symmetric : Symmetric ports.ActionEdge := by
  intro source target hstep
  rcases hstep with ⟨action, rfl⟩
  refine ⟨inverseAction action, ?_⟩
  exact ports.actionPerm_inverseAction_apply action source

/-- Action reachability is symmetric. -/
public theorem actionReaches_symmetric :
    Symmetric (ReflTransGen ports.ActionEdge) :=
  ReflTransGen.symmetric ports.actionEdge_symmetric

/-- Every forward rotation path is an action path. -/
private theorem rotateReaches_actionReaches {source target : ports.Port}
    (hreach : ReflTransGen
      (PermutationReachability.PowerEdge ports.rotate) source target) :
    ReflTransGen ports.ActionEdge source target := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail ⟨Action.rotate, hstep⟩

/-- A directed graph edge can be crossed between the anchor ports of its
endpoints using rotations, one swap, and rotations. -/
public theorem actionReaches_anchor_of_edge
    {source target : V} (hstep : edge source target) :
    ReflTransGen ports.ActionEdge (ports.anchor source) (ports.anchor target) := by
  obtain ⟨port, hsource, htarget⟩ := ports.edge_port hstep
  have htoPort : ReflTransGen ports.ActionEdge (ports.anchor source) port :=
    ports.rotateReaches_actionReaches
      (ports.rotate_complete _ _ ((ports.endpoint_anchor source).trans hsource.symm))
  have hswap : ports.ActionEdge port (ports.swap port) := ⟨Action.swap, rfl⟩
  have htoAnchor : ReflTransGen ports.ActionEdge
      (ports.swap port) (ports.anchor target) :=
    ports.rotateReaches_actionReaches
      (ports.rotate_complete _ _ (htarget.trans (ports.endpoint_anchor target).symm))
  exact (htoPort.tail hswap).trans htoAnchor

/-- One weak graph edge can be traversed between anchor ports. -/
private theorem actionReaches_anchor_of_weakStep
    {source target : V} (hstep : WeakStep edge source target) :
    ReflTransGen ports.ActionEdge (ports.anchor source) (ports.anchor target) := by
  rcases hstep with hforward | hbackward
  · exact ports.actionReaches_anchor_of_edge hforward
  · exact ports.actionReaches_symmetric
      (ports.actionReaches_anchor_of_edge hbackward)

/-- Weak connectivity of graph vertices is complete for reachability between
their anchor ports. -/
public theorem actionReaches_anchor_of_weakReaches
    {source target : V}
    (hreach : ReflTransGen (WeakStep edge) source target) :
    ReflTransGen ports.ActionEdge (ports.anchor source) (ports.anchor target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.trans (ports.actionReaches_anchor_of_weakStep hstep)

/-- A primitive action never leaves the weak component of its endpoint. -/
private theorem weakReaches_endpoint_action
    (action : Action) (port : ports.Port) :
    ReflTransGen (WeakStep edge) (ports.endpoint port)
      (ports.endpoint (ports.actionPerm action port)) := by
  cases action with
  | rotate =>
      change ReflTransGen (WeakStep edge) (ports.endpoint port)
        (ports.endpoint (ports.rotate port))
      rw [ports.rotate_endpoint]
  | unrotate =>
      change ReflTransGen (WeakStep edge) (ports.endpoint port)
        (ports.endpoint (ports.rotate⁻¹ port))
      have heq : ports.endpoint port = ports.endpoint (ports.rotate⁻¹ port) := by
        simpa using ports.rotate_endpoint (ports.rotate⁻¹ port)
      rw [heq]
  | swap =>
      exact ports.swap_sound port

/-- Action reachability is sound for weak graph connectivity of endpoints. -/
public theorem weakReaches_endpoint_of_actionReaches
    {source target : ports.Port}
    (hreach : ReflTransGen ports.ActionEdge source target) :
    ReflTransGen (WeakStep edge) (ports.endpoint source) (ports.endpoint target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases hstep with ⟨action, rfl⟩
      exact ih.trans (ports.weakReaches_endpoint_action action _)

/-- Every action word gives a path to its execution result. -/
public theorem actionReaches_execute (actions : List Action) (port : ports.Port) :
    ReflTransGen ports.ActionEdge port (ports.execute actions port) := by
  induction actions generalizing port with
  | nil => exact .refl
  | cons action actions ih =>
      exact (ih (ports.actionPerm action port)).head ⟨action, rfl⟩

/-- Action reachability is exactly execution of some finite action word. -/
public theorem actionReaches_iff_exists_word {source target : ports.Port} :
    ReflTransGen ports.ActionEdge source target ↔
      ∃ actions, ports.execute actions source = target := by
  constructor
  · intro hreach
    induction hreach with
    | refl => exact ⟨[], rfl⟩
    | tail _ hstep ih =>
        obtain ⟨actions, hactions⟩ := ih
        obtain ⟨action, haction⟩ := hstep
        refine ⟨actions ++ [action], ?_⟩
        rw [execute_append, hactions]
        simpa [execute] using haction
  · rintro ⟨actions, rfl⟩
    exact ports.actionReaches_execute actions source

/-! ## A finite exhaustive reversible schedule -/

/-- A chosen action word from `source` to `target`, or the empty word when
`target` is outside the generated component. -/
noncomputable def witnessWord (source target : ports.Port) : List Action :=
  if h : ReflTransGen ports.ActionEdge source target then
    Classical.choose (ports.actionReaches_iff_exists_word.mp h)
  else
    []

/-- A chosen witness word reaches every target in the generated component. -/
public theorem execute_witnessWord_of_reaches
    {source target : ports.Port}
    (hreach : ReflTransGen ports.ActionEdge source target) :
    ports.execute (ports.witnessWord source target) source = target := by
  rw [witnessWord, dif_pos hreach]
  exact Classical.choose_spec (ports.actionReaches_iff_exists_word.mp hreach)

/-- Visit one target and then reversibly return to the source. -/
noncomputable def excursion (source target : ports.Port) : List Action :=
  ports.witnessWord source target ++
    inverseWord (ports.witnessWord source target)

/-- Every excursion returns to its source, whether or not its target was
reachable. -/
@[simp]
public theorem execute_excursion (source target : ports.Port) :
    ports.execute (ports.excursion source target) source = source := by
  rw [excursion, execute_append]
  exact ports.execute_inverseWord (ports.witnessWord source target) source

/-- Concatenate one return excursion for every finite port. -/
noncomputable def exhaustiveSchedule (source : ports.Port) : List Action :=
  Finset.univ.toList.flatMap (ports.excursion source)

/-- Any list of complete excursions returns to the common source. -/
private theorem execute_flatMap_excursions
    (source : ports.Port) (targets : List ports.Port) :
    ports.execute (targets.flatMap (ports.excursion source)) source = source := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      rw [List.flatMap_cons, execute_append, execute_excursion, ih]

/-- A word visits a target when some prefix executes to that target. -/
@[expose]
public def Visits (actions : List Action) (source target : ports.Port) : Prop :=
  ∃ pre suf, actions = pre ++ suf ∧
    ports.execute pre source = target

/-- The exhaustive schedule visits every port in the action component of its
source. -/
public theorem exhaustiveSchedule_visits_of_actionReaches
    {source target : ports.Port}
    (hreach : ReflTransGen ports.ActionEdge source target) :
    ports.Visits (ports.exhaustiveSchedule source) source target := by
  have hmem : target ∈ (Finset.univ.toList : List ports.Port) := by simp
  obtain ⟨before, after, hparts⟩ := List.mem_iff_append.mp hmem
  let witness := ports.witnessWord source target
  refine ⟨before.flatMap (ports.excursion source) ++ witness,
    inverseWord witness ++ after.flatMap (ports.excursion source), ?_, ?_⟩
  · simp only [exhaustiveSchedule, hparts, List.flatMap_append,
      List.flatMap_cons, excursion, witness]
    simp only [List.append_assoc]
  · rw [execute_append, ports.execute_flatMap_excursions]
    exact ports.execute_witnessWord_of_reaches hreach

/-! ## The reversible phase line -/

/-- Phases before, between, and after the actions of a schedule. -/
public abbrev Phase (actions : List Action) := Fin (actions.length + 1)

/-- The port represented at one phase of a scheduled run. -/
@[expose]
public def portAt (actions : List Action) (source : ports.Port)
    (phase : Phase actions) : ports.Port :=
  ports.execute (actions.take phase.val) source

/-- Moving to the next phase executes exactly the action at the old phase. -/
public theorem portAt_succ
    (actions : List Action) (source : ports.Port)
    (phase : Phase actions) (hphase : phase.val < actions.length) :
    ports.portAt actions source ⟨phase.val + 1, by omega⟩ =
      ports.actionPerm actions[phase.val] (ports.portAt actions source phase) := by
  simp only [portAt]
  rw [List.take_succ_eq_append_getElem hphase, execute_append]
  rfl

/-- The phase-line step relation.  It is intentionally partial at the final
phase. -/
@[expose]
public def PhaseStep (actions : List Action) :
    Phase actions → Phase actions → Prop :=
  fun source target => target.val = source.val + 1

/-- The phase line is both functional and cofunctional. -/
public theorem phaseStep_biUnique (actions : List Action) :
    Relator.BiUnique (PhaseStep actions) := by
  constructor
  · intro left right target hleft hright
    apply Fin.ext
    simp only [PhaseStep] at hleft hright
    omega
  · intro source left right hleft hright
    apply Fin.ext
    simp only [PhaseStep] at hleft hright
    omega

/-- Phase strictly increases at every scheduled step. -/
public theorem phaseStep_rank
    (actions : List Action) {source target : Phase actions}
    (hstep : PhaseStep actions source target) :
    source.val < target.val := by
  simp only [PhaseStep] at hstep
  omega

/-- The reversible scheduled run contains no directed cycle. -/
public theorem phaseStep_acyclic (actions : List Action) :
    ∀ phase, ¬ TransGen (PhaseStep actions) phase phase := by
  apply FiniteAcyclicRank.acyclic_of_strictRank
    (rank := fun phase : Phase actions => phase.val)
  intro source target hstep
  exact phaseStep_rank actions hstep

/-- Every phase is reached from phase zero. -/
public theorem zero_reaches_phase (actions : List Action) (phase : Phase actions) :
    ReflTransGen (PhaseStep actions) 0 phase := by
  induction phase using Fin.induction with
  | zero => exact .refl
  | succ phase ih =>
      exact ih.tail (by simp [PhaseStep])

/-- The last phase has no successor. -/
public theorem last_terminal (actions : List Action) :
    ∀ next, ¬ PhaseStep actions (Fin.last actions.length) next := by
  intro next hstep
  simp only [PhaseStep, Fin.val_last] at hstep
  omega

/-- The scheduled traversal always reaches its terminal phase, independently
of cycles in the source graph. -/
public theorem zero_reaches_last (actions : List Action) :
    ReflTransGen (PhaseStep actions) 0 (Fin.last actions.length) :=
  zero_reaches_phase actions (Fin.last actions.length)

/-- A visited port appears at the corresponding reachable phase. -/
private theorem exists_phase_of_visits
    {actions : List Action} {source target : ports.Port}
    (hvisit : ports.Visits actions source target) :
    ∃ phase, ReflTransGen (PhaseStep actions) 0 phase ∧
      ports.portAt actions source phase = target := by
  obtain ⟨pre, suf, hactions, hexecute⟩ := hvisit
  let phase : Phase actions :=
    ⟨pre.length, by simp [hactions]⟩
  refine ⟨phase, zero_reaches_phase actions phase, ?_⟩
  simpa [portAt, phase, hactions] using hexecute

/-! ## Exact acceptance equivalence -/

/-- The finite reversible traversal accepts when a reachable scheduled phase
has a port at the designated accepting vertex. -/
@[expose]
public def Accepts (source accept : V) : Prop :=
  let actions := ports.exhaustiveSchedule (ports.anchor source)
  ∃ phase, ReflTransGen (PhaseStep actions) 0 phase ∧
    ports.endpoint (ports.portAt actions (ports.anchor source) phase) = accept

/-- The finite reversible port traversal decides reachability of a designated
terminal sink in a functional graph. -/
public theorem accepts_iff_reaches
    (functional : Relator.RightUnique edge) {source accept : V}
    (accept_terminal : ∀ next, ¬ edge accept next) :
    ports.Accepts source accept ↔ ReflTransGen edge source accept := by
  constructor
  · rintro ⟨phase, _, haccept⟩
    have haction := ports.actionReaches_execute
      ((ports.exhaustiveSchedule (ports.anchor source)).take phase.val)
      (ports.anchor source)
    have hweak := ports.weakReaches_endpoint_of_actionReaches haction
    rw [ports.endpoint_anchor source] at hweak
    change ports.endpoint
      (ports.execute
        ((ports.exhaustiveSchedule (ports.anchor source)).take phase.val)
        (ports.anchor source)) = accept at haccept
    rw [haccept] at hweak
    exact (weakReaches_sink_iff_reaches functional accept_terminal).mp hweak
  · intro hreach
    have hweak : ReflTransGen (WeakStep edge) source accept :=
      hreach.lift id (fun _ _ hstep => Or.inl hstep)
    have haction : ReflTransGen ports.ActionEdge
        (ports.anchor source) (ports.anchor accept) :=
      ports.actionReaches_anchor_of_weakReaches hweak
    have hvisit := ports.exhaustiveSchedule_visits_of_actionReaches haction
    obtain ⟨phase, hphase, hport⟩ := ports.exists_phase_of_visits hvisit
    refine ⟨phase, hphase, ?_⟩
    rw [hport, ports.endpoint_anchor]

/-- If the functional source computation does not reach the accepting sink,
the finite reversible schedule terminates without accepting.  This includes
nonhalting source components whose eventual behavior is a directed cycle. -/
public theorem not_accepts_of_not_reaches
    (functional : Relator.RightUnique edge) {source accept : V}
    (accept_terminal : ∀ next, ¬ edge accept next)
    (hnot : ¬ ReflTransGen edge source accept) :
    ¬ ports.Accepts source accept := by
  rwa [ports.accepts_iff_reaches functional accept_terminal]

end PortSystem

/-! ## Canonical edge-end ports for every finite graph -/

namespace CanonicalPortSystem

variable {V : Type u} [Fintype V] [DecidableEq V]
  (edge : V → V → Prop) [DecidableRel edge]

/-- A directed edge, carrying its proof of membership in the graph. -/
public abbrev DirectedEdge := { endpoints : V × V // edge endpoints.1 endpoints.2 }

/-- One permanent anchor at every vertex, plus the two ends of every directed
edge.  `false` is the source end and `true` is the target end. -/
public abbrev Port := V ⊕ (DirectedEdge edge × Bool)

/-- The vertex incident with a canonical port. -/
@[expose]
public def endpoint : Port edge → V
  | .inl vertex => vertex
  | .inr (directed, false) => directed.val.1
  | .inr (directed, true) => directed.val.2

/-- The permanent anchor port of a vertex. -/
@[expose]
public def anchor (vertex : V) : Port edge := .inl vertex

omit [Fintype V] [DecidableEq V] [DecidableRel edge] in
@[simp]
public theorem endpoint_anchor (vertex : V) :
    endpoint edge (anchor edge vertex) = vertex := rfl

/-- Flip the two ends of an edge and fix every anchor. -/
@[expose]
public def swap : Equiv.Perm (Port edge) where
  toFun
    | .inl vertex => .inl vertex
    | .inr (directed, side) => .inr (directed, !side)
  invFun
    | .inl vertex => .inl vertex
    | .inr (directed, side) => .inr (directed, !side)
  left_inv := by
    intro port
    rcases port with vertex | ⟨directed, side⟩
    · rfl
    · cases side <;> rfl
  right_inv := by
    intro port
    rcases port with vertex | ⟨directed, side⟩
    · rfl
    · cases side <;> rfl

omit [Fintype V] [DecidableEq V] [DecidableRel edge] in
@[simp]
public theorem swap_involution (port : Port edge) :
    swap edge (swap edge port) = port := by
  rcases port with vertex | ⟨directed, side⟩
  · rfl
  · cases side <;> rfl

/-- Ports incident with one fixed vertex. -/
public abbrev Fiber (vertex : V) :=
  { port : Port edge // endpoint edge port = vertex }

private instance fiberNonempty (vertex : V) : Nonempty (Fiber edge vertex) :=
  ⟨⟨anchor edge vertex, endpoint_anchor edge vertex⟩⟩

/-- Rotate each vertex fiber independently through its canonical finite cyclic
order. -/
noncomputable def rotate : Equiv.Perm (Port edge) :=
  Equiv.ofFiberEquiv (fun vertex => cyclicPerm (Fiber edge vertex))

/-- Rotation never changes the incident vertex. -/
@[simp]
public theorem endpoint_rotate (port : Port edge) :
    endpoint edge (rotate edge port) = endpoint edge port := by
  exact Equiv.ofFiberEquiv_map
    (fun vertex => cyclicPerm (Fiber edge vertex)) port

/-- Applying the global rotation to a port in a named fiber is exactly the
canonical cyclic permutation of that fiber. -/
private theorem rotate_coe_fiber (vertex : V) (port : Fiber edge vertex) :
    rotate edge port.val = (cyclicPerm (Fiber edge vertex) port).val := by
  rcases port with ⟨port, hport⟩
  subst vertex
  simp [rotate, Equiv.ofFiberEquiv_apply, Equiv.sigmaFiberEquiv]

/-- Forward rotation enumerates every port incident with one vertex. -/
public theorem rotate_complete (left right : Port edge)
    (hsame : endpoint edge left = endpoint edge right) :
    ReflTransGen (PermutationReachability.PowerEdge (rotate edge)) left right := by
  let vertex := endpoint edge left
  let leftFiber : Fiber edge vertex := ⟨left, rfl⟩
  let rightFiber : Fiber edge vertex := ⟨right, hsame.symm⟩
  have hlocal := cyclicPerm_reaches_everywhere leftFiber rightFiber
  have hlift : ReflTransGen
      (PermutationReachability.PowerEdge (rotate edge)) left right := by
    simpa [leftFiber, rightFiber] using
      (ReflTransGen.lift
        (p := PermutationReachability.PowerEdge (rotate edge))
        (fun port : Fiber edge vertex => port.val)
        (fun source target hstep => by
          change rotate edge source.val = target.val
          rw [rotate_coe_fiber edge vertex source]
          exact congrArg Subtype.val hstep) hlocal)
  exact hlift

omit [Fintype V] [DecidableEq V] [DecidableRel edge] in
/-- Swapping a canonical port crosses at most one underlying weak edge. -/
public theorem swap_sound (port : Port edge) :
    ReflTransGen (WeakStep edge) (endpoint edge port)
      (endpoint edge (swap edge port)) := by
  rcases port with vertex | ⟨directed, side⟩
  · exact .refl
  · rcases directed with ⟨⟨source, target⟩, hstep⟩
    cases side
    · exact .single (Or.inl hstep)
    · exact .single (Or.inr hstep)

omit [Fintype V] [DecidableEq V] [DecidableRel edge] in
/-- Every directed edge is represented by its source edge end and is crossed
by `swap` to its target edge end. -/
public theorem edge_port {source target : V} (hstep : edge source target) :
    ∃ port : Port edge,
      endpoint edge port = source ∧ endpoint edge (swap edge port) = target := by
  let directed : DirectedEdge edge := ⟨(source, target), hstep⟩
  exact ⟨.inr (directed, false), rfl, rfl⟩

/-- Every finite decidable directed graph has a canonical reversible edge-end
port system. -/
noncomputable def ofFinite : PortSystem edge where
  Port := Port edge
  portFintype := inferInstance
  portDecidableEq := inferInstance
  endpoint := endpoint edge
  anchor := anchor edge
  endpoint_anchor := endpoint_anchor edge
  rotate := rotate edge
  rotate_endpoint := endpoint_rotate edge
  rotate_complete := rotate_complete edge
  swap := swap edge
  swap_involution := swap_involution edge
  swap_sound := swap_sound edge
  edge_port := edge_port edge

/-! ### The terminating basin as a ranked rooted component -/

/-- The selected outgoing edge of a vertex, when one exists. -/
noncomputable def selectedEdge (vertex : V) : Option { target : V // edge vertex target } :=
  if h : ∃ target, edge vertex target then
    some ⟨Classical.choose h, Classical.choose_spec h⟩
  else
    none

omit [DecidableEq V] in
/-- Functionality makes the selected outgoing edge equal to every supplied
outgoing edge. -/
public theorem selectedEdge_eq_some_of_edge
    (functional : Relator.RightUnique edge) {source target : V}
    (hstep : edge source target) :
    selectedEdge edge source = some ⟨target, hstep⟩ := by
  rw [selectedEdge, dif_pos ⟨target, hstep⟩]
  congr 2
  exact functional (Classical.choose_spec ⟨target, hstep⟩) hstep

/-- The source end of one represented directed edge. -/
@[expose]
public def sourcePort {source target : V} (hstep : edge source target) : Port edge :=
  .inr (⟨(source, target), hstep⟩, false)

/-- The canonical parent port is the source end of the selected outgoing
edge. -/
noncomputable def parentPort (vertex : V) : Option (Port edge) :=
  (selectedEdge edge vertex).map fun target => sourcePort edge target.property

omit [DecidableEq V] in
/-- Every supplied functional edge determines the canonical parent port. -/
public theorem parentPort_eq_some_of_edge
    (functional : Relator.RightUnique edge) {source target : V}
    (hstep : edge source target) :
    parentPort edge source = some (sourcePort edge hstep) := by
  rw [parentPort, selectedEdge_eq_some_of_edge edge functional hstep]
  rfl

omit [DecidableEq V] in
/-- A canonical parent port is incident with its source vertex. -/
public theorem endpoint_parentPort
    {vertex : V} {port : Port edge}
    (hport : parentPort edge vertex = some port) :
    endpoint edge port = vertex := by
  unfold parentPort at hport
  cases hselected : selectedEdge edge vertex with
  | none => simp [hselected] at hport
  | some target =>
      simp only [hselected, Option.map_some, Option.some.injEq] at hport
      subst port
      rfl

/-- Parent ports for the basin contour.  The terminal root uses its fixed
anchor as a virtual parent port.  This closes the contour into one cycle and
also handles a completely isolated root. -/
noncomputable def basinParentPort (target vertex : V) : Option (Port edge) :=
  if vertex = target then some (anchor edge target) else parentPort edge vertex

/-- The terminal root's virtual parent port is its anchor. -/
@[simp]
public theorem basinParentPort_target (target : V) :
    basinParentPort edge target target = some (anchor edge target) := by
  simp [basinParentPort]

/-- Away from the terminal root, a functional edge determines the basin
parent port. -/
public theorem basinParentPort_eq_some_of_edge
    (functional : Relator.RightUnique edge) {target source next : V}
    (target_terminal : ∀ after, ¬ edge target after)
    (hstep : edge source next) :
    basinParentPort edge target source = some (sourcePort edge hstep) := by
  have hne : source ≠ target := by
    intro heq
    subst source
    exact target_terminal next hstep
  simp only [basinParentPort, if_neg hne]
  exact parentPort_eq_some_of_edge edge functional hstep

/-- Every basin parent port, including the virtual root anchor, is incident
with its named vertex. -/
public theorem endpoint_basinParentPort
    {target vertex : V} {port : Port edge}
    (hport : basinParentPort edge target vertex = some port) :
    endpoint edge port = vertex := by
  by_cases heq : vertex = target
  · subst vertex
    simp only [basinParentPort_target, Option.some.injEq] at hport
    subst port
    rfl
  · rw [basinParentPort, if_neg heq] at hport
    exact endpoint_parentPort edge hport

/-- The backward basin of a terminal vertex, equipped with canonical parent
ports and the strict ancestor-count rank. -/
noncomputable def rankedBasin
    (functional : Relator.RightUnique edge) (target : V)
    (target_terminal : ∀ next, ¬ edge target next) :
    (ofFinite edge).RankedTree where
  member := fun vertex => ReflTransGen edge vertex target
  rank := basinRank edge target
  parentPort := basinParentPort edge target
  parent_endpoint := endpoint_basinParentPort edge
  anchor_fixed := by
    intro vertex
    rfl
  classify := by
    intro vertex port hmember hendpoint
    rcases port with portVertex | ⟨directed, side⟩
    · simp only [ofFinite, endpoint] at hendpoint
      subst portVertex
      exact Or.inl rfl
    · rcases directed with ⟨⟨source, edgeTarget⟩, hstep⟩
      cases side
      · simp only [ofFinite, endpoint] at hendpoint
        subst source
        exact Or.inr (Or.inl
          ⟨sourcePort edge hstep,
            basinParentPort_eq_some_of_edge edge functional target_terminal hstep, rfl⟩)
      · simp only [ofFinite, endpoint] at hendpoint
        subst edgeTarget
        have hchildMember : ReflTransGen edge source target :=
          hmember.head hstep
        have hrank : basinRank edge target source < basinRank edge target vertex :=
          basinRank_lt_of_edge functional target_terminal hchildMember hstep
        exact Or.inr (Or.inr
          ⟨source, sourcePort edge hstep, hchildMember, hrank,
            basinParentPort_eq_some_of_edge edge functional target_terminal hstep, rfl⟩)
  edge_parent := by
    intro source edgeTarget hmember hstep
    exact ⟨sourcePort edge hstep,
      basinParentPort_eq_some_of_edge edge functional target_terminal hstep, rfl⟩
  forward_closed := by
    intro source next hsource hstep
    exact (reaches_sink_iff_of_edge functional target_terminal hstep).mp hsource

/-- Every port incident with the terminal basin eventually reaches the
terminal root's anchor under the single local Euler permutation. -/
public theorem eulerReaches_sink_anchor
    (functional : Relator.RightUnique edge) {accept : V}
    (accept_terminal : ∀ next, ¬ edge accept next)
    {start : Port edge}
    (hmember : ReflTransGen edge (endpoint edge start) accept) :
    ReflTransGen (ofFinite edge).EulerEdge start
      ((ofFinite edge).anchor accept) := by
  let tree := rankedBasin edge functional accept accept_terminal
  obtain ⟨finish, hfinish, hfinishEndpoint⟩ :=
    PortSystem.RankedTree.eulerReaches_endpoint_of_reaches
      (ports := ofFinite edge) tree hmember rfl hmember
  have hrootMember : tree.member accept := by
    exact ReflTransGen.refl
  have hrootParent :
      tree.parentPort accept = some ((ofFinite edge).anchor accept) := by
    exact basinParentPort_target edge accept
  have hrootTour := PortSystem.RankedTree.eulerReaches_swap_parent
    (ports := ofFinite edge) tree hrootMember hrootParent hfinishEndpoint
  have hanchorFixed :
      (ofFinite edge).swap ((ofFinite edge).anchor accept) =
        (ofFinite edge).anchor accept := tree.anchor_fixed accept
  rw [hanchorFixed] at hrootTour
  exact hfinish.trans hrootTour

/-- **Single-orbit basin theorem.**  All canonical edge ends incident with the
backward basin of a terminal vertex belong to one orbit of `swap ∘ rotate`.
This is the finite functional-tree form of the Euler-tour lemma used by the
Lange--McKenzie--Tapp traversal. -/
public theorem euler_singleOrbit_on_basin
    (functional : Relator.RightUnique edge) {accept : V}
    (accept_terminal : ∀ next, ¬ edge accept next)
    {left right : Port edge}
    (hleft : ReflTransGen edge (endpoint edge left) accept)
    (hright : ReflTransGen edge (endpoint edge right) accept) :
    ReflTransGen (ofFinite edge).EulerEdge left right := by
  have hleftAnchor := eulerReaches_sink_anchor edge functional accept_terminal hleft
  have hrightAnchor := eulerReaches_sink_anchor edge functional accept_terminal hright
  exact hleftAnchor.trans ((ofFinite edge).eulerReaches_symmetric hrightAnchor)

/-- **Finite LMT Euler theorem.**  For any finite functional graph and terminal
accepting vertex, the single canonical local permutation `swap ∘ rotate`
accepts from a source exactly when the original directed computation reaches
the accepting vertex.

Completeness uses the ranked-tree contour theorem on the accepting sink's
backward basin.  Soundness uses only weak-component preservation and the fact
that weak connectivity to a terminal sink agrees with forward reachability.
The total Euler permutation may cycle forever on a nonterminating source
component, but it cannot accept there. -/
public theorem eulerAccepts_iff_reaches
    (functional : Relator.RightUnique edge) {source accept : V}
    (accept_terminal : ∀ next, ¬ edge accept next) :
    (ofFinite edge).EulerAccepts source accept ↔
      ReflTransGen edge source accept := by
  constructor
  · intro haccept
    have hweak := (ofFinite edge).weakReaches_of_eulerAccepts haccept
    exact (weakReaches_sink_iff_reaches functional accept_terminal).mp hweak
  · intro hreach
    exact PortSystem.RankedTree.eulerReaches_accept_of_reaches
      (ports := ofFinite edge) (rankedBasin edge functional accept accept_terminal)
      hreach hreach

/-- **Accepting-set form.**  If every accepting vertex is terminal, the Euler
orbit from the source visits an accepting endpoint exactly when the original
functional source orbit reaches some accepting vertex.  The accepting target
is existential on both sides; no distinguished final configuration is
required. -/
public theorem exists_eulerReaches_accepting_iff_exists_reaches
    (functional : Relator.RightUnique edge)
    (accepting : V → Prop)
    (accept_terminal : ∀ accept, accepting accept →
      ∀ next, ¬ edge accept next)
    (source : V) :
    (∃ finish,
      ReflTransGen (ofFinite edge).EulerEdge
        ((ofFinite edge).anchor source) finish ∧
      accepting ((ofFinite edge).endpoint finish)) ↔
      ∃ accept, accepting accept ∧ ReflTransGen edge source accept := by
  constructor
  · rintro ⟨finish, hfinish, haccept⟩
    let accept := (ofFinite edge).endpoint finish
    have heuler : (ofFinite edge).EulerAccepts source accept :=
      ⟨finish, hfinish, rfl⟩
    exact ⟨accept, haccept,
      (eulerAccepts_iff_reaches edge functional
        (accept_terminal accept haccept)).mp heuler⟩
  · rintro ⟨accept, haccept, hreach⟩
    obtain ⟨finish, hfinish, hendpoint⟩ :=
      (eulerAccepts_iff_reaches edge functional
        (accept_terminal accept haccept)).mpr hreach
    exact ⟨finish, hfinish, hendpoint ▸ haccept⟩

end CanonicalPortSystem

end FunctionalGraphReversibleTraversal

end
