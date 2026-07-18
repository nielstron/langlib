module

public import Langlib.Automata.LinearBounded.ThreeMatchingReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# An all-pairs embedding barrier between three and two matchings

An exact union of two directed matchings can branch at a source, but it cannot branch after an
incoming edge.  This file strengthens the one-step result in
`ThreeMatchingReachability.successor_eq_of_incoming`: once a vertex has an incoming edge, every
two descendants of that vertex are comparable by reachability.

Consequently, a graph containing an incoming fork with two incomparable descendants cannot be
embedded vertexwise into an exact union of two directed matchings while both preserving and
reflecting reachability for every pair of represented vertices.  A concrete four-vertex fork is
also exhibited as an exact union of three directed matchings.

This is a barrier only to this strong, all-pairs, vertexwise form of reduction.  A language
reduction may depend on its designated initial vertex, introduce query-specific representations,
or preserve only reachability of an accepting set.  Therefore the results below do not separate
`LBA` from `DLBA` and do not rule out a language-level reduction from three matchings to two.
-/

open Relation

namespace ThreeMatchingReachability

universe u

variable {V : Type u}

/-- Once a vertex has an incoming edge in an exact union of two directed matchings, every two
vertices reachable from it are reachability-comparable.

No finiteness, decidable equality, degree hypothesis beyond the matching presentation, or
acyclicity is required. -/
public theorem reaches_comparable_of_incoming
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {predecessor source left right : V}
    (hincoming : edge predecessor source)
    (hleft : ReflTransGen edge source left)
    (hright : ReflTransGen edge source right) :
    ReflTransGen edge left right ∨ ReflTransGen edge right left := by
  induction hleft using ReflTransGen.head_induction_on generalizing predecessor right with
  | refl => exact Or.inl hright
  | @head source middle hstep _ ih =>
      rcases ReflTransGen.cases_head hright with heq | ⟨other, hother, htail⟩
      · subst right
        exact Or.inr (ReflTransGen.head hstep ‹ReflTransGen edge middle left›)
      · have hmiddle : middle = other :=
          successor_eq_of_incoming cover biUnique short hincoming hstep hother
        subst other
        exact ih hstep htail

end ThreeMatchingReachability

namespace TwoMatchingEmbeddingBarrier

universe u v

variable {V : Type u} {W : Type v}

/-- A vertex map preserves and reflects reflexive-transitive reachability for every ordered pair
of source vertices. -/
@[expose]
public def PreservesAndReflectsAllReachability
    (sourceEdge : V → V → Prop) (targetEdge : W → W → Prop)
    (encode : V → W) : Prop :=
  ∀ source target,
    ReflTransGen sourceEdge source target ↔
      ReflTransGen targetEdge (encode source) (encode target)

/-- An incoming fork consists of a proper predecessor edge into a junction and two descendants
of that junction which are incomparable by reachability. -/
@[expose]
public def HasIncomingIncomparableFork (edge : V → V → Prop) : Prop :=
  ∃ predecessor junction left right,
    predecessor ≠ junction ∧
      edge predecessor junction ∧
      ReflTransGen edge junction left ∧
      ReflTransGen edge junction right ∧
      ¬ReflTransGen edge left right ∧
      ¬ReflTransGen edge right left

/-- A vertexwise injective, all-pairs reachability-preserving-and-reflecting encoding cannot map
an incoming incomparable fork into an exact union of two directed matchings.

The target may have arbitrary type and may contain arbitrary vertices outside the image of
`encode`; in particular, auxiliary paths are allowed. -/
public theorem false_of_injective_allPairs_encoding_of_incomingFork
    {sourceEdge : V → V → Prop}
    {targetEdge : W → W → Prop}
    {targetLayer : Fin 2 → W → W → Prop}
    (targetCover : ∀ source target, targetEdge source target ↔
      ∃! color, targetLayer color source target)
    (targetBiUnique : ∀ color, Relator.BiUnique (targetLayer color))
    (targetShort : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (targetLayer color))
    {predecessor junction left right : V}
    (hne : predecessor ≠ junction)
    (hincoming : sourceEdge predecessor junction)
    (hleft : ReflTransGen sourceEdge junction left)
    (hright : ReflTransGen sourceEdge junction right)
    (hincomparable :
      ¬ReflTransGen sourceEdge left right ∧
        ¬ReflTransGen sourceEdge right left)
    (encode : V → W) (hinjective : Function.Injective encode)
    (hexact : PreservesAndReflectsAllReachability sourceEdge targetEdge encode) :
    False := by
  have hpredecessorJunction :
      ReflTransGen targetEdge (encode predecessor) (encode junction) :=
    (hexact predecessor junction).mp (ReflTransGen.single hincoming)
  have hjunctionIncoming : ∃ targetPredecessor,
      targetEdge targetPredecessor (encode junction) := by
    rcases ReflTransGen.cases_tail hpredecessorJunction with heq |
        ⟨targetPredecessor, _, hlast⟩
    · exact False.elim (hne (hinjective heq.symm))
    · exact ⟨targetPredecessor, hlast⟩
  obtain ⟨targetPredecessor, htargetIncoming⟩ := hjunctionIncoming
  have htargetLeft :
      ReflTransGen targetEdge (encode junction) (encode left) :=
    (hexact junction left).mp hleft
  have htargetRight :
      ReflTransGen targetEdge (encode junction) (encode right) :=
    (hexact junction right).mp hright
  rcases ThreeMatchingReachability.reaches_comparable_of_incoming
      targetCover targetBiUnique targetShort htargetIncoming htargetLeft htargetRight with
    hleftRight | hrightLeft
  · exact hincomparable.1 ((hexact left right).mpr hleftRight)
  · exact hincomparable.2 ((hexact right left).mpr hrightLeft)

/-- Existential form of the all-pairs embedding barrier. -/
public theorem no_injective_allPairs_encoding_of_incomingFork
    {sourceEdge : V → V → Prop}
    {targetEdge : W → W → Prop}
    {targetLayer : Fin 2 → W → W → Prop}
    (targetCover : ∀ source target, targetEdge source target ↔
      ∃! color, targetLayer color source target)
    (targetBiUnique : ∀ color, Relator.BiUnique (targetLayer color))
    (targetShort : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (targetLayer color))
    (hfork : HasIncomingIncomparableFork sourceEdge) :
    ¬∃ encode : V → W,
      Function.Injective encode ∧
        PreservesAndReflectsAllReachability sourceEdge targetEdge encode := by
  rintro ⟨encode, hinjective, hexact⟩
  obtain ⟨predecessor, junction, left, right, hne, hincoming,
    hleft, hright, hincomparable⟩ := hfork
  exact false_of_injective_allPairs_encoding_of_incomingFork
    targetCover targetBiUnique targetShort hne hincoming hleft hright
    hincomparable encode hinjective hexact

/-! ## The concrete exact-three-matching fork -/

/-- Four vertices exhibiting the minimal incoming binary fork. -/
public inductive ThreeForkVertex where
  | predecessor
  | junction
  | left
  | right
deriving DecidableEq, Fintype

/-- The predecessor enters the junction, which has two distinct terminal children. -/
public inductive ThreeForkEdge : ThreeForkVertex → ThreeForkVertex → Prop where
  | incoming : ThreeForkEdge .predecessor .junction
  | left : ThreeForkEdge .junction .left
  | right : ThreeForkEdge .junction .right

/-- Give each of the three fork edges its own directed-matching color. -/
public inductive ThreeForkLayer : Fin 3 → ThreeForkVertex → ThreeForkVertex → Prop where
  | incoming : ThreeForkLayer 0 .predecessor .junction
  | left : ThreeForkLayer 1 .junction .left
  | right : ThreeForkLayer 2 .junction .right

/-- The concrete fork relation is covered exactly once by its three layers. -/
public theorem threeForkEdge_iff_existsUnique_layer
    (source target : ThreeForkVertex) :
    ThreeForkEdge source target ↔
      ∃! color, ThreeForkLayer color source target := by
  constructor
  · intro hedge
    cases hedge with
    | incoming =>
        refine ⟨0, .incoming, ?_⟩
        intro color hcolor
        cases hcolor
        rfl
    | left =>
        refine ⟨1, .left, ?_⟩
        intro color hcolor
        cases hcolor
        rfl
    | right =>
        refine ⟨2, .right, ?_⟩
        intro color hcolor
        cases hcolor
        rfl
  · rintro ⟨color, hcolor, _⟩
    cases hcolor with
    | incoming => exact .incoming
    | left => exact .left
    | right => exact .right

/-- A colored concrete-fork edge is an edge of the uncolored fork relation. -/
public theorem threeForkLayer_sub_edge {color : Fin 3} {source target : ThreeForkVertex}
    (hlayer : ThreeForkLayer color source target) :
    ThreeForkEdge source target := by
  cases hlayer with
  | incoming => exact .incoming
  | left => exact .left
  | right => exact .right

/-- Every concrete fork layer is a partial bijection. -/
public theorem threeForkLayer_biUnique (color : Fin 3) :
    Relator.BiUnique (ThreeForkLayer color) := by
  constructor
  · intro first second target hfirst hsecond
    cases hfirst <;> cases hsecond <;> rfl
  · intro source first second hfirst hsecond
    cases hfirst <;> cases hsecond <;> rfl

/-- Every concrete fork layer has paths of length at most one. -/
public theorem threeForkLayer_pathLengthAtMostOne (color : Fin 3) :
    LinearTwoDiforestReachability.PathLengthAtMostOne (ThreeForkLayer color) := by
  intro first middle last hfirst hlast
  cases hfirst <;> cases hlast

/-- Packaged structural statement that the concrete fork is an exact union of three directed
matchings. -/
public theorem threeFork_exact_threeMatching_partition :
    (∀ source target, ThreeForkEdge source target ↔
      ∃! color, ThreeForkLayer color source target) ∧
      (∀ color source target,
        ThreeForkLayer color source target → ThreeForkEdge source target) ∧
      (∀ color, Relator.BiUnique (ThreeForkLayer color)) ∧
      ∀ color,
        LinearTwoDiforestReachability.PathLengthAtMostOne (ThreeForkLayer color) :=
  ⟨threeForkEdge_iff_existsUnique_layer,
    fun _ _ _ ↦ threeForkLayer_sub_edge,
    threeForkLayer_biUnique,
    threeForkLayer_pathLengthAtMostOne⟩

/-- A path starting at the left child is necessarily reflexive. -/
public theorem reaches_from_threeFork_left_eq {target : ThreeForkVertex}
    (hreach : ReflTransGen ThreeForkEdge .left target) :
    target = .left := by
  rcases ReflTransGen.cases_head hreach with heq | ⟨next, hstep, _⟩
  · exact heq.symm
  · cases hstep

/-- A path starting at the right child is necessarily reflexive. -/
public theorem reaches_from_threeFork_right_eq {target : ThreeForkVertex}
    (hreach : ReflTransGen ThreeForkEdge .right target) :
    target = .right := by
  rcases ReflTransGen.cases_head hreach with heq | ⟨next, hstep, _⟩
  · exact heq.symm
  · cases hstep

/-- The concrete exact-three-matching graph contains an incoming fork with incomparable
descendants. -/
public theorem threeFork_hasIncomingIncomparableFork :
    HasIncomingIncomparableFork ThreeForkEdge := by
  refine ⟨.predecessor, .junction, .left, .right, ?_, .incoming,
    ReflTransGen.single .left, ReflTransGen.single .right, ?_, ?_⟩
  · intro heq
    cases heq
  · intro hreach
    have heq := reaches_from_threeFork_left_eq hreach
    cases heq
  · intro hreach
    have heq := reaches_from_threeFork_right_eq hreach
    cases heq

/-- The explicit exact union of three directed matchings has no injective vertexwise encoding
into the target exact union of two directed matchings that preserves and reflects all-pairs
reachability.  The target type is arbitrary and may contain auxiliary vertices. -/
public theorem threeFork_no_injective_allPairs_encoding_into_twoMatchings
    {targetEdge : W → W → Prop}
    {targetLayer : Fin 2 → W → W → Prop}
    (targetCover : ∀ source target, targetEdge source target ↔
      ∃! color, targetLayer color source target)
    (targetBiUnique : ∀ color, Relator.BiUnique (targetLayer color))
    (targetShort : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (targetLayer color)) :
    ¬∃ encode : ThreeForkVertex → W,
      Function.Injective encode ∧
        PreservesAndReflectsAllReachability ThreeForkEdge targetEdge encode :=
  no_injective_allPairs_encoding_of_incomingFork
    targetCover targetBiUnique targetShort threeFork_hasIncomingIncomparableFork

end TwoMatchingEmbeddingBarrier

end
