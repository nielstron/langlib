module

public import Langlib.Automata.LinearBounded.TwoLayerReachability

@[expose]
public section

/-!
# The ordered-fork reachability barrier

This module isolates a general obstruction to resolving nondeterministic forks by choosing the
first child that can still reach acceptance.

For an arbitrary relation `edge` with distinguished vertices `source` and `target`, adjoin a fresh
root with two ordered children.  Its first child is a copy of `source`; its second child is a fresh,
immediately accepting fallback.  The first child is the first successful child exactly when
`target` is reachable from `source`, while the fallback is first successful exactly when `target`
is not reachable.  Consequently, the identity of the first successful child semantically
characterizes both reachability and nonreachability.  This is a barrier theorem: it does not
construct, or assume the existence of, a computable first-successful-child selector.

The construction does not require finiteness, decidable adjacency, or degree assumptions.  It also
preserves acyclicity: the fresh root has no incoming edge, the fallback has no outgoing edge, and
all edges between old vertices are inherited from the original relation.
-/

namespace ForkReachabilityBarrier

open Relation

universe u

/-- Vertices of the ordered-fork extension of a relation.

`root` is fresh, `old vertex` embeds an original vertex, and `fallback` is the fresh accepting
second child. -/
public inductive ForkNode (α : Type u) where
  | root
  | old (vertex : α)
  | fallback
deriving DecidableEq

/-- The ordered-fork extension of `edge` rooted at `source`.

The root has the old source as its left child and the accepting fallback as its right child.  The
only remaining edges are embedded original edges. -/
public inductive ForkEdge {α : Type u} (edge : α → α → Prop) (source : α) :
    ForkNode α → ForkNode α → Prop where
  | left : ForkEdge edge source .root (.old source)
  | right : ForkEdge edge source .root .fallback
  | old {a b : α} : edge a b → ForkEdge edge source (.old a) (.old b)

/-- The two-color extension of an old edge coloring to the ordered fork.

Old edges retain their colors.  The fresh left edge has color `0`, and the fresh fallback edge
has color `1`. -/
public inductive ForkLayer {α : Type u} (layer : Fin 2 → α → α → Prop) (source : α) :
    Fin 2 → ForkNode α → ForkNode α → Prop where
  | left : ForkLayer layer source 0 .root (.old source)
  | right : ForkLayer layer source 1 .root .fallback
  | old {color : Fin 2} {a b : α} :
      layer color a b → ForkLayer layer source color (.old a) (.old b)

/-! ## Preservation of an exact two-partial-bijection presentation -/

/-- Every colored fork edge is an uncolored fork edge when every old colored edge is an old
edge. -/
public theorem forkLayer_sub_forkEdge {α : Type u} {edge : α → α → Prop}
    {layer : Fin 2 → α → α → Prop} {source : α}
    (hsub : ∀ color a b, layer color a b → edge a b) :
    ∀ {color start finish},
      ForkLayer layer source color start finish → ForkEdge edge source start finish := by
  intro color start finish hlayer
  cases hlayer with
  | left => exact .left
  | right => exact .right
  | old hold => exact .old (hsub _ _ _ hold)

/-- An exact two-color partition of the old relation extends to an exact two-color partition of
the fork relation. -/
public theorem forkLayer_exact {α : Type u} {edge : α → α → Prop}
    {layer : Fin 2 → α → α → Prop} {source : α}
    (hexact : ∀ a b, edge a b ↔ (∃! color, layer color a b))
    (hsub : ∀ color a b, layer color a b → edge a b) :
    ∀ start finish, ForkEdge edge source start finish ↔
      (∃! color, ForkLayer layer source color start finish) := by
  intro start finish
  constructor
  · intro hedge
    cases hedge with
    | left =>
        refine ⟨0, .left, ?_⟩
        intro color hcolor
        cases hcolor with
        | left => rfl
    | right =>
        refine ⟨1, .right, ?_⟩
        intro color hcolor
        cases hcolor with
        | right => rfl
    | @old a b hab =>
        obtain ⟨color, hcolor, hunique⟩ := (hexact a b).mp hab
        refine ⟨color, .old hcolor, ?_⟩
        intro other hother
        cases hother with
        | old hold => exact hunique _ hold
  · rintro ⟨_, hcolor, _⟩
    exact forkLayer_sub_forkEdge hsub hcolor

/-- If the old layers are partial bijections and the distinguished source has no old incoming
edge, then each extended fork layer is again a partial bijection.

The no-incoming hypothesis supplies the free incoming port needed for the new left edge.  Without
it, adjoining that edge can destroy left-uniqueness. -/
public theorem forkLayer_biUnique {α : Type u} {edge : α → α → Prop}
    {layer : Fin 2 → α → α → Prop} {source : α}
    (hsub : ∀ color a b, layer color a b → edge a b)
    (hbiUnique : ∀ color, Relator.BiUnique (layer color))
    (hnoIncoming : ∀ a, ¬ edge a source) :
    ∀ color, Relator.BiUnique (ForkLayer layer source color) := by
  intro color
  constructor
  · intro first second finish hfirst hsecond
    cases hfirst with
    | left =>
        cases hsecond with
        | left => rfl
        | old hold => exact False.elim (hnoIncoming _ (hsub _ _ _ hold))
    | right =>
        cases hsecond with
        | right => rfl
    | old holdFirst =>
        cases hsecond with
        | left => exact False.elim (hnoIncoming _ (hsub _ _ _ holdFirst))
        | old holdSecond =>
            exact congrArg ForkNode.old ((hbiUnique _).1 holdFirst holdSecond)
  · intro start first second hfirst hsecond
    cases hfirst with
    | left =>
        cases hsecond with
        | left => rfl
    | right =>
        cases hsecond with
        | right => rfl
    | old holdFirst =>
        cases hsecond with
        | old holdSecond =>
            exact congrArg ForkNode.old ((hbiUnique _).2 holdFirst holdSecond)

/-- Accepting vertices of the fork extension.

An old vertex accepts precisely when it is the distinguished target, and the fallback always
accepts.  The root never accepts. -/
@[expose]
public def Accepting {α : Type u} (target : α) : ForkNode α → Prop
  | .root => False
  | .old vertex => vertex = target
  | .fallback => True

/-- A fork vertex is successful when it can reach an accepting vertex, allowing a zero-step
path. -/
@[expose]
public def Successful {α : Type u} (edge : α → α → Prop) (source target : α)
    (node : ForkNode α) : Prop :=
  ∃ final, ReflTransGen (ForkEdge edge source) node final ∧ Accepting target final

/-- The two children of the fresh root, indexed in their search order.

`false` denotes the old source and `true` denotes the accepting fallback. -/
@[expose]
public def OrderedChild {α : Type u} (source : α) : Bool → ForkNode α
  | false => .old source
  | true => .fallback

/-- Strict order on the two child indices: the left child `false` precedes the fallback `true`. -/
@[expose]
public def Earlier : Bool → Bool → Prop
  | false, true => True
  | _, _ => False

/-- A child is first successful when it is successful and every earlier child is unsuccessful. -/
@[expose]
public def IsFirstSuccessful {α : Type u} (edge : α → α → Prop) (source target : α)
    (child : Bool) : Prop :=
  Successful edge source target (OrderedChild source child) ∧
    ∀ earlier, Earlier earlier child →
      ¬Successful edge source target (OrderedChild source earlier)

/-- Original reflexive-transitive reachability lifts to reachability between embedded old
vertices. -/
public theorem lift_reaches {α : Type u} {edge : α → α → Prop} {source a b : α}
    (h : ReflTransGen edge a b) :
    ReflTransGen (ForkEdge edge source) (.old a) (.old b) :=
  h.lift ForkNode.old (fun _ _ oldEdge => .old oldEdge)

/-- Every path starting at an old vertex stays among old vertices and projects to an original
path. -/
public theorem old_reaches_only_old {α : Type u} {edge : α → α → Prop} {source a : α}
    {node : ForkNode α}
    (h : ReflTransGen (ForkEdge edge source) (.old a) node) :
    ∃ b, node = .old b ∧ ReflTransGen edge a b := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | tail h nextEdge ih =>
      obtain ⟨b, rfl, hab⟩ := ih
      cases nextEdge with
      | old oldEdge => exact ⟨_, rfl, hab.tail oldEdge⟩

/-- The left child succeeds exactly when the original target is reachable from the original
source. -/
public theorem successful_left_iff {α : Type u} (edge : α → α → Prop)
    (source target : α) :
    Successful edge source target (.old source) ↔ ReflTransGen edge source target := by
  constructor
  · rintro ⟨final, hreach, hfinal⟩
    obtain ⟨b, rfl, hsb⟩ := old_reaches_only_old hreach
    change b = target at hfinal
    subst b
    exact hsb
  · intro h
    exact ⟨.old target, lift_reaches h, rfl⟩

/-- The fallback is always successful because it accepts immediately. -/
public theorem successful_fallback {α : Type u} (edge : α → α → Prop)
    (source target : α) :
    Successful edge source target .fallback :=
  ⟨.fallback, .refl, trivial⟩

/-- The left child is first successful exactly on positive reachability instances. -/
public theorem left_is_first_successful_iff {α : Type u}
    (edge : α → α → Prop) (source target : α) :
    IsFirstSuccessful edge source target false ↔ ReflTransGen edge source target := by
  simp [IsFirstSuccessful, OrderedChild, Earlier, successful_left_iff]

/-- The fallback is first successful exactly on negative reachability instances. -/
public theorem fallback_is_first_successful_iff {α : Type u}
    (edge : α → α → Prop) (source target : α) :
    IsFirstSuccessful edge source target true ↔ ¬ReflTransGen edge source target := by
  simp [IsFirstSuccessful, OrderedChild, Earlier, successful_left_iff,
    successful_fallback]

/-- First-successful-child selection simultaneously characterizes reachability and its
complement for an arbitrary relation. -/
public theorem first_successful_child_decides {α : Type u}
    (edge : α → α → Prop) (source target : α) :
    (IsFirstSuccessful edge source target false ↔ ReflTransGen edge source target) ∧
      (IsFirstSuccessful edge source target true ↔ ¬ReflTransGen edge source target) :=
  ⟨left_is_first_successful_iff edge source target,
    fallback_is_first_successful_iff edge source target⟩

/-! ## Acyclicity preservation -/

/-- A relation is acyclic when no vertex reaches itself by a nonempty path. -/
@[expose]
public def Acyclic {α : Type u} (edge : α → α → Prop) : Prop :=
  ∀ vertex, ¬TransGen edge vertex vertex

/-- A nonempty fork path starting at an old vertex stays among old vertices and projects to a
nonempty original path. -/
public theorem old_trans_reaches_only_old {α : Type u} {edge : α → α → Prop} {source a : α}
    {node : ForkNode α}
    (h : TransGen (ForkEdge edge source) (.old a) node) :
    ∃ b, node = .old b ∧ TransGen edge a b := by
  induction h with
  | single nextEdge =>
      cases nextEdge with
      | old oldEdge => exact ⟨_, rfl, .single oldEdge⟩
  | tail h nextEdge ih =>
      obtain ⟨b, rfl, hab⟩ := ih
      cases nextEdge with
      | old oldEdge => exact ⟨_, rfl, hab.tail oldEdge⟩

/-- No nonempty fork path can end at the fresh root. -/
public theorem no_trans_path_to_root {α : Type u} {edge : α → α → Prop} {source : α}
    {node : ForkNode α} :
    ¬TransGen (ForkEdge edge source) node .root := by
  intro h
  cases h with
  | single nextEdge => cases nextEdge
  | tail _ nextEdge => cases nextEdge

/-- Every nonempty transitive path has a first edge. -/
public theorem transGen_has_first {α : Type u} {relation : α → α → Prop} {a b : α}
    (h : TransGen relation a b) : ∃ next, relation a next := by
  induction h using TransGen.head_induction_on with
  | single firstEdge => exact ⟨_, firstEdge⟩
  | head firstEdge _ _ => exact ⟨_, firstEdge⟩

/-- No nonempty fork path can start at the fallback. -/
public theorem no_trans_path_from_fallback {α : Type u} {edge : α → α → Prop} {source : α}
    {node : ForkNode α} :
    ¬TransGen (ForkEdge edge source) .fallback node := by
  intro h
  obtain ⟨_, firstEdge⟩ := transGen_has_first h
  cases firstEdge

/-- Adding the ordered fork and accepting fallback preserves acyclicity. -/
public theorem forkEdge_acyclic {α : Type u} {edge : α → α → Prop} {source : α}
    (hEdge : Acyclic edge) : Acyclic (ForkEdge edge source) := by
  intro node cycle
  cases node with
  | root => exact no_trans_path_to_root cycle
  | fallback => exact no_trans_path_from_fallback cycle
  | old a =>
      obtain ⟨b, hEq, hab⟩ := old_trans_reaches_only_old cycle
      cases hEq
      exact hEdge a hab

/-- The preserved exact two-biunique presentation makes both directed degrees of the fork at
most two.  The no-incoming hypothesis is needed only for the new predecessor of `old source`. -/
public theorem forkEdge_directedDegreeAtMostTwo {α : Type u}
    {edge : α → α → Prop} {layer : Fin 2 → α → α → Prop} {source : α}
    (hexact : ∀ a b, edge a b ↔ (∃! color, layer color a b))
    (hsub : ∀ color a b, layer color a b → edge a b)
    (hbiUnique : ∀ color, Relator.BiUnique (layer color))
    (hnoIncoming : ∀ a, ¬ edge a source) :
    (∀ start, Set.encard {finish | ForkEdge edge source start finish} ≤ 2) ∧
      ∀ finish, Set.encard {start | ForkEdge edge source start finish} ≤ 2 := by
  let partition :
      TwoLayerReachability.TwoPartialFunctionPartition
        (ForkEdge edge source) (ForkLayer layer source) :=
    TwoLayerReachability.TwoPartialFunctionPartition.of_existsUnique_biUnique
      (forkLayer_exact hexact hsub)
      (fun _ _ _ hlayer => forkLayer_sub_forkEdge hsub hlayer)
      (forkLayer_biUnique hsub hbiUnique hnoIncoming)
  exact partition.directedDegreeAtMostTwo_of_biUnique
    (forkLayer_biUnique hsub hbiUnique hnoIncoming)

/-- The ordered fork stays inside the acyclic, exactly two-layer, partial-bijection setting when
the old source has no incoming edge.

This theorem is purely structural.  Together with `first_successful_child_decides`, it places the
semantic first-successful-child barrier inside that restricted graph class; it does not provide a
computable selector.  The explicit directed degree bounds are exposed separately by
`forkEdge_directedDegreeAtMostTwo`. -/
public theorem fork_preserves_acyclic_two_biUnique {α : Type u}
    {edge : α → α → Prop} {layer : Fin 2 → α → α → Prop} {source : α}
    (hexact : ∀ a b, edge a b ↔ (∃! color, layer color a b))
    (hsub : ∀ color a b, layer color a b → edge a b)
    (hbiUnique : ∀ color, Relator.BiUnique (layer color))
    (hnoIncoming : ∀ a, ¬ edge a source)
    (hacyclic : Acyclic edge) :
    (∀ start finish, ForkEdge edge source start finish ↔
      (∃! color, ForkLayer layer source color start finish)) ∧
      (∀ color start finish,
        ForkLayer layer source color start finish → ForkEdge edge source start finish) ∧
      (∀ color, Relator.BiUnique (ForkLayer layer source color)) ∧
      Acyclic (ForkEdge edge source) :=
  ⟨forkLayer_exact hexact hsub,
    fun _ _ _ => forkLayer_sub_forkEdge hsub,
    forkLayer_biUnique hsub hbiUnique hnoIncoming,
    forkEdge_acyclic hacyclic⟩

end ForkReachabilityBarrier
