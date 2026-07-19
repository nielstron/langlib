module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.ClassEquivalence
public import Langlib.Automata.LinearBounded.Cofunctional.Triviality

@[expose]
public section

/-!
# The hierarchy by number of directed-matching layers

This module packages the exact two- and three-matching predicates into one natural-number
parameter.  A `k`-matching presentation supplies, uniformly at every tape width, an exact
`Fin k`-coloring of the complete raw step relation.  Every color is a directed matching: it is
both left- and right-unique, and it contains no composable pair of edges.

The existing endpoint results and the complete-raw cofunctionality obstruction give the whole
hierarchy: levels zero and one contain exactly the empty and universal languages, level two is
`DLBA`, and every level at least three is `LBA`.  Adding unused colors is monotone.  Consequently
the first LBA problem is exactly the question whether levels three and two collapse.  None of
these statements asserts that they do.
-/

namespace LBA

open Relation

variable {Gamma State : Type*}

/-- A width-uniform exact `k`-color partition of the complete raw configuration relation into
directed matchings. -/
public def Machine.HasKMatchingStepPartition
    (M : Machine Gamma State) (k : Nat) : Prop :=
  ∃ layer : (n : Nat) → Fin k →
      DLBA.Cfg Gamma State n → DLBA.Cfg Gamma State n → Prop,
    (∀ n source target,
      Step M source target ↔ ∃! color, layer n color source target) ∧
      (∀ n color source target,
        layer n color source target → Step M source target) ∧
      (∀ n color, Relator.BiUnique (layer n color)) ∧
      ∀ n color,
        LinearTwoDiforestReachability.PathLengthAtMostOne (layer n color)

/-- The generic predicate at two colors is exactly the existing two-matching predicate. -/
@[simp]
public theorem Machine.hasKMatchingStepPartition_two_iff (M : Machine Gamma State) :
    M.HasKMatchingStepPartition 2 ↔ M.HasTwoMatchingStepPartition := by
  rfl

/-- The generic predicate at three colors is exactly the existing three-matching predicate. -/
@[simp]
public theorem Machine.hasKMatchingStepPartition_three_iff (M : Machine Gamma State) :
    M.HasKMatchingStepPartition 3 ↔ M.HasThreeMatchingStepPartition := by
  rfl

/-- Adding unused colors preserves an exact matching partition. -/
public theorem Machine.hasKMatchingStepPartition_mono
    (M : Machine Gamma State) {small large : Nat} (hcolors : small ≤ large)
    (hlayers : M.HasKMatchingStepPartition small) :
    M.HasKMatchingStepPartition large := by
  rcases hlayers with
    ⟨layer, cover, layerSubStep, layerBiUnique, layerShort⟩
  let includeColor : Fin small → Fin large := Fin.castLE hcolors
  have includeColor_injective : Function.Injective includeColor := by
    intro left right heq
    apply Fin.ext
    exact congrArg (fun color : Fin large => color.val) heq
  let enlargedLayer : (n : Nat) → Fin large →
      DLBA.Cfg Gamma State n → DLBA.Cfg Gamma State n → Prop :=
    fun n color source target =>
      ∃ oldColor, includeColor oldColor = color ∧
        layer n oldColor source target
  refine ⟨enlargedLayer, ?_, ?_, ?_, ?_⟩
  . intro n source target
    constructor
    . intro hstep
      obtain ⟨oldColor, hold, hunique⟩ := (cover n source target).mp hstep
      refine ⟨includeColor oldColor, ⟨oldColor, rfl, hold⟩, ?_⟩
      intro color hcolor
      obtain ⟨otherColor, hinclude, hother⟩ := hcolor
      have heq : otherColor = oldColor := hunique otherColor hother
      subst otherColor
      exact hinclude.symm
    . rintro ⟨color, ⟨oldColor, _hinclude, hold⟩, _hunique⟩
      exact layerSubStep n oldColor source target hold
  . intro n color source target
    rintro ⟨oldColor, _hinclude, hold⟩
    exact layerSubStep n oldColor source target hold
  . intro n color
    constructor
    . intro left right target hleft hright
      obtain ⟨leftColor, hleftColor, hleft⟩ := hleft
      obtain ⟨rightColor, hrightColor, hright⟩ := hright
      have hcolor : leftColor = rightColor :=
        includeColor_injective (hleftColor.trans hrightColor.symm)
      subst rightColor
      exact (layerBiUnique n leftColor).1 hleft hright
    . intro source left right hleft hright
      obtain ⟨leftColor, hleftColor, hleft⟩ := hleft
      obtain ⟨rightColor, hrightColor, hright⟩ := hright
      have hcolor : leftColor = rightColor :=
        includeColor_injective (hleftColor.trans hrightColor.symm)
      subst rightColor
      exact (layerBiUnique n leftColor).2 hleft hright
  . intro n color first middle last hfirst hlast
    obtain ⟨firstColor, hfirstColor, hfirst⟩ := hfirst
    obtain ⟨lastColor, hlastColor, hlast⟩ := hlast
    have hcolor : firstColor = lastColor :=
      includeColor_injective (hfirstColor.trans hlastColor.symm)
    subst lastColor
    exact layerShort n firstColor hfirst hlast

/-- A transition-free machine has an exact matching partition with any number of colors: every
color layer is empty. -/
public theorem Machine.trivialCofunctional_hasKMatchingStepPartition
    (Gamma : Type*) (accepts : Bool) (k : Nat) :
    (Machine.trivialCofunctional Gamma accepts).HasKMatchingStepPartition k := by
  refine ⟨fun _n _color _source _target => False, ?_, ?_, ?_, ?_⟩
  . intro n source target
    constructor
    . rintro ⟨next, written, direction, henabled, _hmove⟩
      simp [Machine.trivialCofunctional] at henabled
    . rintro ⟨color, hfalse, _hunique⟩
      exact hfalse.elim
  . intro n color source target hfalse
    exact hfalse.elim
  . intro n color
    constructor
    . intro left right target hfalse _hright
      exact hfalse.elim
    . intro source left right hfalse _hright
      exact hfalse.elim
  . intro n color first middle last hfalse _hlast
    exact hfalse.elim

/-- With only one matching color, the complete raw step relation is globally cofunctional. -/
public theorem Machine.cofunctional_of_hasKMatchingStepPartition_one
    (M : Machine Gamma State) (hlayers : M.HasKMatchingStepPartition 1) :
    M.Cofunctional := by
  rcases hlayers with
    ⟨layer, cover, _layerSubStep, layerBiUnique, _layerShort⟩
  intro n left right target hleft hright
  obtain ⟨leftColor, hleftLayer, _hleftUnique⟩ :=
    (cover n left target).mp hleft
  obtain ⟨rightColor, hrightLayer, _hrightUnique⟩ :=
    (cover n right target).mp hright
  have hcolor : leftColor = rightColor := Subsingleton.elim _ _
  subst rightColor
  exact (layerBiUnique n leftColor).1 hleftLayer hrightLayer

end LBA

/-! ## Language classes -/

/-- A language with a canonical endmarker LBA presentation whose complete raw step relation is
an exact union of `k` directed matchings at every tape width. -/
@[expose]
public def is_KMatchingLBA
    (k : Nat) {T : Type} [Fintype T] [DecidableEq T]
    (L : Language T) : Prop :=
  ∃ (Gamma State : Type) (_ : Fintype Gamma) (_ : Fintype State)
    (_ : DecidableEq Gamma) (_ : DecidableEq State)
    (M : LBA.Machine (LBA.EndAlpha T Gamma) State),
    M.HasKMatchingStepPartition k ∧ LBA.LanguageEnd M = L

/-- The class of languages with exact `k`-matching LBA presentations. -/
@[expose]
public def KMatchingLBA
    (k : Nat) {T : Type} [Fintype T] [DecidableEq T] :
    Set (Language T) :=
  setOf (is_KMatchingLBA k)

/-- The generic two-color language predicate is exactly the existing two-matching predicate. -/
@[simp]
public theorem is_KMatchingLBA_two_iff_is_TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_KMatchingLBA 2 L ↔ is_TwoMatchingLBA L := by
  rfl

/-- The generic two-color language class is the existing two-matching class. -/
public theorem KMatchingLBA_two_eq_TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA 2 : Set (Language T)) = TwoMatchingLBA := by
  rfl

/-- Forgetting the matching layers gives an ordinary canonical endmarker LBA presentation. -/
public theorem is_LBA_of_is_KMatchingLBA
    {k : Nat} {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_KMatchingLBA k L) : is_LBA L := by
  rcases hL with
    ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
      M, _hlayers, hlanguage⟩
  exact ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState, M, hlanguage⟩

/-- Every level of the matching-layer hierarchy is contained in `LBA`. -/
public theorem KMatchingLBA_subset_LBA
    (k : Nat) {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA k : Set (Language T)) ⊆ LBA :=
  fun _ hL => is_LBA_of_is_KMatchingLBA hL

/-- Adding unused matching colors preserves a language presentation. -/
public theorem is_KMatchingLBA_mono
    {small large : Nat} (hcolors : small ≤ large)
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_KMatchingLBA small L) : is_KMatchingLBA large L := by
  rcases hL with
    ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
      M, hlayers, hlanguage⟩
  refine ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState, M, ?_, hlanguage⟩
  exact M.hasKMatchingStepPartition_mono hcolors hlayers

/-- The matching-layer language classes are monotone in the number of available colors. -/
public theorem KMatchingLBA_mono
    {small large : Nat} (hcolors : small ≤ large)
    {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA small : Set (Language T)) ⊆ KMatchingLBA large :=
  fun _ hL => is_KMatchingLBA_mono hcolors hL

/-! ## The exact low levels -/

/-- A one-color matching presentation is globally cofunctional. -/
public theorem is_CofunctionalLBA_of_is_KMatchingLBA_one
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_KMatchingLBA 1 L) : is_CofunctionalLBA L := by
  rcases hL with
    ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
      M, hlayers, hlanguage⟩
  exact ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
    M, M.cofunctional_of_hasKMatchingStepPartition_one hlayers, hlanguage⟩

/-- The empty language has a transition-free `k`-matching presentation for every `k`. -/
public theorem is_KMatchingLBA_empty
    (k : Nat) {T : Type} [Fintype T] [DecidableEq T] :
    is_KMatchingLBA k (∅ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    LBA.Machine.trivialCofunctional (LBA.EndAlpha T Unit) false,
    LBA.Machine.trivialCofunctional_hasKMatchingStepPartition _ _ k, ?_⟩
  exact LBA.Machine.languageEnd_trivialCofunctional_false

/-- The universal language has a transition-free `k`-matching presentation for every `k`. -/
public theorem is_KMatchingLBA_univ
    (k : Nat) {T : Type} [Fintype T] [DecidableEq T] :
    is_KMatchingLBA k (Set.univ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    LBA.Machine.trivialCofunctional (LBA.EndAlpha T Unit) true,
    LBA.Machine.trivialCofunctional_hasKMatchingStepPartition _ _ k, ?_⟩
  exact LBA.Machine.languageEnd_trivialCofunctional_true

/-- Every hierarchy level with at most one color consists exactly of the empty and universal
languages.  This is uniform over all finite terminal types, including the empty type. -/
public theorem KMatchingLBA_eq_trivial_languages_of_le_one
    {k : Nat} (hk : k ≤ 1)
    {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA k : Set (Language T)) =
      ({(∅ : Set (List T)), (Set.univ : Set (List T))} : Set (Language T)) := by
  ext L
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  change is_KMatchingLBA k L ↔ _
  constructor
  . intro hL
    have hOne : is_KMatchingLBA 1 L := is_KMatchingLBA_mono hk hL
    exact is_CofunctionalLBA_iff_eq_empty_or_univ.mp
      (is_CofunctionalLBA_of_is_KMatchingLBA_one hOne)
  . rintro (rfl | rfl)
    . exact is_KMatchingLBA_empty k
    . exact is_KMatchingLBA_univ k

/-- In particular, the one-color matching class is exactly the two trivial languages. -/
public theorem KMatchingLBA_one_eq_trivial_languages
    {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA 1 : Set (Language T)) =
      ({(∅ : Set (List T)), (Set.univ : Set (List T))} : Set (Language T)) :=
  KMatchingLBA_eq_trivial_languages_of_le_one (le_refl 1)

/-! ## The exact two- and three-color levels -/

/-- Two exact directed-matching colors characterize deterministic linear space. -/
public theorem KMatchingLBA_two_eq_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA 2 : Set (Language T)) = DLBA := by
  rw [KMatchingLBA_two_eq_TwoMatchingLBA, TwoMatchingLBA_eq_DLBA]

/-- The acyclic degree-two three-matching normal form embeds into the generic three-color
class after forgetting its additional structural promises. -/
public theorem is_KMatchingLBA_three_of_is_AcyclicDegreeTwoThreeMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicDegreeTwoThreeMatchingLBA L) : is_KMatchingLBA 3 L := by
  rcases hL with
    ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
      M, _hacyclic, _hdegree, hlayers, hlanguage⟩
  exact ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
    M, (M.hasKMatchingStepPartition_three_iff).mpr hlayers, hlanguage⟩

/-- Three exact directed-matching colors already present every LBA language. -/
public theorem KMatchingLBA_three_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA 3 : Set (Language T)) = LBA := by
  apply Set.Subset.antisymm (KMatchingLBA_subset_LBA 3)
  intro L hL
  exact is_KMatchingLBA_three_of_is_AcyclicDegreeTwoThreeMatchingLBA
    (is_AcyclicDegreeTwoThreeMatchingLBA_of_is_LBA hL)

/-- Every hierarchy level with at least three colors is exactly `LBA`. -/
public theorem KMatchingLBA_eq_LBA_of_three_le
    {k : Nat} (hk : 3 ≤ k)
    {T : Type} [Fintype T] [DecidableEq T] :
    (KMatchingLBA k : Set (Language T)) = LBA := by
  apply Set.Subset.antisymm (KMatchingLBA_subset_LBA k)
  rw [← KMatchingLBA_three_eq_LBA]
  exact KMatchingLBA_mono hk

/-- Every hierarchy level with at least two colors contains deterministic linear space. -/
public theorem DLBA_subset_KMatchingLBA_of_two_le
    {k : Nat} (hk : 2 ≤ k)
    {T : Type} [Fintype T] [DecidableEq T] :
    (DLBA : Set (Language T)) ⊆ KMatchingLBA k := by
  rw [← KMatchingLBA_two_eq_DLBA]
  exact KMatchingLBA_mono hk

/-! ## The first-LBA-problem frontier -/

/-- The first LBA problem is exactly whether the three- and two-matching levels coincide. -/
public theorem lba_eq_dlba_iff_KMatchingLBA_three_eq_two
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((KMatchingLBA 3 : Set (Language T)) = KMatchingLBA 2) := by
  rw [KMatchingLBA_three_eq_LBA, KMatchingLBA_two_eq_DLBA]

/-- Equivalently, determinizing every three-matching language is the full first LBA problem. -/
public theorem lba_eq_dlba_iff_KMatchingLBA_three_subset_two
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((KMatchingLBA 3 : Set (Language T)) ⊆ KMatchingLBA 2) := by
  rw [KMatchingLBA_three_eq_LBA, KMatchingLBA_two_eq_DLBA]
  constructor
  . intro heq
    rw [heq]
  . intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

end
