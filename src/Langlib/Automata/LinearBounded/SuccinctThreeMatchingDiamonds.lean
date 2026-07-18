module

public import Langlib.Automata.LinearBounded.ThreeMatchingDiamondBranches
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

@[expose]
public section

/-!
# Succinct names for exponentially long three-matching diamond chains

At row width `w`, instantiate the split diamond construction with `k = 2 ^ w` diamonds.  Its
`6 * k + 2` vertices fit injectively in a state consisting of constant finite control `Fin 8`
and one `w`-bit row.  At the same time, the graph has exactly `2 ^ w` source-to-target-relevant
branch vertices and remains an acyclic exact union of three directed matchings.

The encoding below is explicit and does not select an arbitrary finite-type numbering.  It
enumerates finite sums, products, and bit rows, embeds the resulting bounded numeral into the
larger state numeral, and decodes it again.
In particular, no positive-width premise is needed, so all statements include `w = 0`.

This is only a structural succinct-naming result.  It does not provide a local implementation
of the encoded edge relation or layers, an effective reduction between machine descriptions,
or an LBA compiler.  Cardinal capacity for vertex names alone does not settle any of those
uniformity and locality obligations.
-/

namespace SuccinctThreeMatchingDiamonds

open Relation

/-! ## Explicit bounded-numeral encodings -/

/-- One width-`w` binary work row. -/
public abbrev BitRow (w : ℕ) := Fin w → Bool

/-- Constant eight-way finite control together with one width-`w` binary row. -/
public abbrev State (w : ℕ) := Fin 8 × BitRow w

/-- Explicitly enumerate binary rows by the numeral whose base-two digits they contain. -/
@[expose]
public def bitRowEquivFin (w : ℕ) : BitRow w ≃ Fin (2 ^ w) :=
  (Equiv.arrowCongr (Equiv.refl (Fin w)) finTwoEquiv.symm).trans
    finFunctionFinEquiv

/-- Explicitly enumerate the two branch vertices at each old diamond index. -/
@[expose]
public def oldBranchEquivFin (k : ℕ) :
    (Fin k × Bool) ≃ Fin (Nat.mul k 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin k)) finTwoEquiv.symm).trans
    finProdFinEquiv

/-- Explicitly enumerate the `k + 1` junctions followed by the `2 * k` branch vertices. -/
@[expose]
public def oldVertexEquivFin (k : ℕ) :
    DiamondPaths.Vertex k ≃ Fin ((k + 1) + Nat.mul k 2) :=
  (Equiv.sumCongr (Equiv.refl (Fin (k + 1))) (oldBranchEquivFin k)).trans
    finSumFinEquiv

/-- Identify input/output copies with a sum of two copies of the old vertex type. -/
@[expose]
public def splitVertexEquivSum (V : Type*) :
    ThreeMatchingReachability.Vertex V ≃ V ⊕ V where
  toFun
    | .input vertex => .inl vertex
    | .output vertex => .inr vertex
  invFun
    | .inl vertex => .input vertex
    | .inr vertex => .output vertex
  left_inv := by intro vertex; cases vertex <;> rfl
  right_inv := by intro vertex; cases vertex <;> rfl

/-- Explicit bounded-numeral enumeration of every split diamond vertex. -/
@[expose]
public def splitDiamondVertexEquivFin (k : ℕ) :
    ThreeMatchingDiamondBranches.Vertex k ≃
      Fin (((k + 1) + Nat.mul k 2) + ((k + 1) + Nat.mul k 2)) :=
  (splitVertexEquivSum (DiamondPaths.Vertex k)).trans
    ((Equiv.sumCongr (oldVertexEquivFin k) (oldVertexEquivFin k)).trans
      finSumFinEquiv)

/-- Explicit bounded-numeral enumeration of constant control and one binary row. -/
@[expose]
public def stateEquivFin (w : ℕ) : State w ≃ Fin (Nat.mul 8 (2 ^ w)) :=
  (Equiv.prodCongr (Equiv.refl (Fin 8)) (bitRowEquivFin w)).trans
    finProdFinEquiv

private theorem six_mul_add_two_le_eight_mul (k : ℕ) (hk : 0 < k) :
    Nat.mul 6 k + 2 ≤ Nat.mul 8 k := by
  have hkone : 1 ≤ k := by omega
  have htwo : 2 ≤ Nat.mul 2 k := by
    calc
      2 = Nat.mul 2 1 := by decide
      _ ≤ Nat.mul 2 k := Nat.mul_le_mul_left 2 hkone
  calc
    Nat.mul 6 k + 2 ≤ Nat.mul 6 k + Nat.mul 2 k :=
      Nat.add_le_add_left htwo _
    _ = Nat.mul 8 k := by
      change 6 * k + 2 * k = 8 * k
      rw [← Nat.add_mul]

private theorem splitDiamondIndex_eq_six_mul_add_two (k : ℕ) :
    ((k + 1) + Nat.mul k 2) + ((k + 1) + Nat.mul k 2) =
      Nat.mul 6 k + 2 := by
  have htwoComm : Nat.mul k 2 = Nat.mul 2 k := Nat.mul_comm k 2
  have htwo : Nat.mul 2 k = k + k := by
    change 2 * k = k + k
    exact Nat.two_mul k
  have hsix :
      Nat.mul 6 k =
        (Nat.mul 2 k + Nat.mul 2 k) + Nat.mul 2 k := by
    calc
      Nat.mul 6 k = Nat.mul (2 + 2 + 2) k := by norm_num
      _ = Nat.mul (2 + 2) k + Nat.mul 2 k := Nat.add_mul (2 + 2) 2 k
      _ = (Nat.mul 2 k + Nat.mul 2 k) + Nat.mul 2 k := by
        change (2 + 2) * k + 2 * k = (2 * k + 2 * k) + 2 * k
        rw [Nat.add_mul]
  omega

/-- The split `2 ^ w`-diamond vertex numeral fits in the numeral space represented by eight
control values and one width-`w` bit row.  Positivity comes from `2 ^ w`, including at `w = 0`;
it is not imposed as an extra premise. -/
public theorem splitDiamondIndex_le_stateIndex (w : ℕ) :
    let k := 2 ^ w
    ((k + 1) + Nat.mul k 2) + ((k + 1) + Nat.mul k 2) ≤
      Nat.mul 8 k := by
  dsimp only
  have hk : 0 < 2 ^ w := Nat.pow_pos (by omega)
  rw [splitDiamondIndex_eq_six_mul_add_two]
  exact six_mul_add_two_le_eight_mul (2 ^ w) hk

/-- Canonical explicit encoding of every split vertex of a `2 ^ w`-diamond chain using constant
eight-way control and one width-`w` binary row. -/
@[expose]
public def encodeVertex (w : ℕ) :
    ThreeMatchingDiamondBranches.Vertex (2 ^ w) → State w :=
  fun vertex ↦
    (stateEquivFin w).symm
      (Fin.castLE (splitDiamondIndex_le_stateIndex w)
        (splitDiamondVertexEquivFin (2 ^ w) vertex))

/-- The explicit constant-control-plus-row encoding loses no split vertex information. -/
public theorem encodeVertex_injective (w : ℕ) :
    Function.Injective (encodeVertex w) := by
  exact (stateEquivFin w).symm.injective.comp
    ((Fin.castLE_injective (splitDiamondIndex_le_stateIndex w)).comp
      (splitDiamondVertexEquivFin (2 ^ w)).injective)

/-! ## Exact capacities and encoded relevant branches -/

/-- The constant-control-plus-row state type has exactly `8 * 2 ^ w` elements. -/
public theorem card_state (w : ℕ) :
    Fintype.card (State w) = Nat.mul 8 (2 ^ w) := by
  rw [Fintype.card_congr (stateEquivFin w)]
  simp

/-- The `6 * 2 ^ w + 2` split vertices fit under the exact state capacity. -/
public theorem card_splitVertices_le_card_state (w : ℕ) :
    Fintype.card (ThreeMatchingDiamondBranches.Vertex (2 ^ w)) ≤
      Fintype.card (State w) := by
  exact Fintype.card_le_of_injective (encodeVertex w)
    (encodeVertex_injective w)

/-- Direct arithmetic form of the same capacity comparison. -/
public theorem six_twoPow_add_two_le_eight_twoPow (w : ℕ) :
    Nat.mul 6 (2 ^ w) + 2 ≤ Nat.mul 8 (2 ^ w) := by
  have hk : 0 < 2 ^ w := Nat.pow_pos (by omega)
  exact six_mul_add_two_le_eight_mul (2 ^ w) hk

/-- The canonical relevant branch vertices remain pairwise distinct after succinct encoding. -/
public theorem encodedBranchJunction_injective (w : ℕ) :
    Function.Injective
      (encodeVertex w ∘
        (@ThreeMatchingDiamondBranches.branchJunction (2 ^ w))) :=
  (encodeVertex_injective w).comp
    (ThreeMatchingDiamondBranches.branchJunction_injective (2 ^ w))

/-- There are `2 ^ w` injectively and succinctly named genuine branches between the designated
source and target.  The branches occur in their natural reachability order. -/
public theorem exists_twoPow_relevantBranches_with_succinct_names (w : ℕ) :
    ∃ branches : Fin (2 ^ w) →
        ThreeMatchingDiamondBranches.Vertex (2 ^ w),
      Function.Injective branches ∧
        Function.Injective (encodeVertex w ∘ branches) ∧
        (∀ i,
          ReflTransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w))
              (ThreeMatchingDiamondBranches.source (2 ^ w)) (branches i) ∧
            ThreeMatchingReachability.Branches
              (ThreeMatchingDiamondBranches.Edge (2 ^ w)) (branches i) ∧
            ReflTransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w))
              (branches i) (ThreeMatchingDiamondBranches.target (2 ^ w))) ∧
        ∀ i j, i.val ≤ j.val →
          ReflTransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w))
            (branches i) (branches j) := by
  refine ⟨ThreeMatchingDiamondBranches.branchJunction,
    ThreeMatchingDiamondBranches.branchJunction_injective (2 ^ w),
    encodedBranchJunction_injective w, ?_, ?_⟩
  · intro i
    exact ⟨ThreeMatchingDiamondBranches.source_reaches_branchJunction i,
      ThreeMatchingDiamondBranches.branches_branchJunction i,
      ThreeMatchingDiamondBranches.branchJunction_reaches_target i⟩
  · intro i j hle
    exact ThreeMatchingDiamondBranches.branchJunction_reaches_branchJunction_of_le
      i j hle

/-! ## Packaged succinct exact-three-matching obstruction -/

/-- For every row width, including zero, an exponentially long split diamond DAG has succinct
vertex names in constant finite control plus one binary row.  It is an acyclic exact union of
three directed matchings and has exactly `2 ^ w` relevant branches between its designated
source and target.

The final branch family is also injective after `encodeVertex`; this remains a naming theorem,
not an encoded transition implementation or a same-width automaton compiler. -/
public theorem succinct_exactThreeMatching_relevantBranch_obstruction (w : ℕ) :
    Fintype.card (State w) = Nat.mul 8 (2 ^ w) ∧
      Function.Injective (encodeVertex w) ∧
      Fintype.card (ThreeMatchingDiamondBranches.Vertex (2 ^ w)) =
        Nat.mul 6 (2 ^ w) + 2 ∧
      Set.ncard
          {vertex : ThreeMatchingDiamondBranches.Vertex (2 ^ w) |
            ThreeMatchingReachability.Branches
              (ThreeMatchingDiamondBranches.Edge (2 ^ w)) vertex} =
        2 ^ w ∧
      (∀ vertex,
        ¬ TransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w)) vertex vertex) ∧
      (∀ old new,
        ThreeMatchingDiamondBranches.Edge (2 ^ w) old new ↔
          ∃! color, ThreeMatchingDiamondBranches.Layer (2 ^ w) color old new) ∧
      (∀ color old new,
        ThreeMatchingDiamondBranches.Layer (2 ^ w) color old new →
          ThreeMatchingDiamondBranches.Edge (2 ^ w) old new) ∧
      (∀ color,
        Relator.BiUnique (ThreeMatchingDiamondBranches.Layer (2 ^ w) color)) ∧
      (∀ color,
        LinearTwoDiforestReachability.PathLengthAtMostOne
          (ThreeMatchingDiamondBranches.Layer (2 ^ w) color)) ∧
      ReflTransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w))
        (ThreeMatchingDiamondBranches.source (2 ^ w))
        (ThreeMatchingDiamondBranches.target (2 ^ w)) ∧
      ∃ branches : Fin (2 ^ w) →
          ThreeMatchingDiamondBranches.Vertex (2 ^ w),
        Function.Injective branches ∧
          Function.Injective (encodeVertex w ∘ branches) ∧
          (∀ i,
            ReflTransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w))
                (ThreeMatchingDiamondBranches.source (2 ^ w)) (branches i) ∧
              ThreeMatchingReachability.Branches
                (ThreeMatchingDiamondBranches.Edge (2 ^ w)) (branches i) ∧
              ReflTransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w))
                (branches i) (ThreeMatchingDiamondBranches.target (2 ^ w))) ∧
          ∀ i j, i.val ≤ j.val →
            ReflTransGen (ThreeMatchingDiamondBranches.Edge (2 ^ w))
              (branches i) (branches j) := by
  have hdiamond :=
    ThreeMatchingDiamondBranches.exactThreeMatching_relevantBranch_obstruction
      (2 ^ w)
  refine ⟨card_state w, encodeVertex_injective w, hdiamond.1, hdiamond.2.1,
    hdiamond.2.2.1, hdiamond.2.2.2.1, hdiamond.2.2.2.2.1,
    hdiamond.2.2.2.2.2.1, hdiamond.2.2.2.2.2.2.1,
    hdiamond.2.2.2.2.2.2.2.1, ?_⟩
  exact exists_twoPow_relevantBranches_with_succinct_names w

end SuccinctThreeMatchingDiamonds

end
