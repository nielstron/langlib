module

public import Langlib.Automata.LinearBounded.ScheduleCapacity
public import Langlib.Automata.LinearBounded.SuccinctThreeMatchingDiamonds
public import Langlib.Automata.LinearBounded.ThreeMatchingDiamondChoiceLowerBound
import Mathlib.Tactic

@[expose]
public section

/-!
# Capacity of complete schedules for succinct diamond chains

A width-`w` succinct diamond chain has `2 ^ w` successive binary branches and therefore exactly
`2 ^ (2 ^ w)` complete branch vectors and source-to-target paths.  In the finite-choice
presentation, every target-reaching branch or replay trace still consumes exactly `2 ^ w`
choice names.  Its distinct target-reaching choice lists and its actual bounded schedule
records are both counted exactly by the same double exponential.

For every finite row alphabet `A` and every fixed linear width factor `factor`, this file gives
an explicit width at which rows of width `factor * w` cannot injectively hold all complete path
vectors, all explicit diamond paths, or all bounded schedules.  The witness is
`w = 2 * (|A| * factor)`.  It works without hypotheses on `A` or `factor`, including an empty or
singleton alphabet and factor zero.

These are cardinal obstructions to **literal simultaneous materialization or enumeration** of
complete schedules.  They are not deterministic-LBA space lower bounds: a simulator can
recompute branch information, reuse cells, select schedules without storing them injectively,
or exploit a different presentation.
-/

namespace SuccinctDiamondScheduleCapacity

open ThreeMatchingDiamondChoiceLowerBound
open ThreeMatchingDiamondBranches
open Relation

/-! ## Exact double-exponential families -/

/-- A complete schedule selects one Boolean branch at every one of the `2 ^ w` diamonds. -/
public abbrev CompletePathSchedule (w : ℕ) := Fin (2 ^ w) → Bool

/-- There are exactly `2 ^ (2 ^ w)` complete branch schedules. -/
public theorem card_completePathSchedules (w : ℕ) :
    Fintype.card (CompletePathSchedule w) = 2 ^ (2 ^ w) := by
  simp [CompletePathSchedule]

/-- The explicit source-to-target paths through the succinct diamond chain have the same exact
double-exponential cardinality. -/
public theorem card_succinctDiamondPaths (w : ℕ) :
    Nat.card (DiamondPaths.STPath (2 ^ w)) = 2 ^ (2 ^ w) := by
  simpa using DiamondPaths.card_stPaths (2 ^ w)

/-- Complete schedules and explicit source-to-target paths are canonically equivalent. -/
@[expose]
public noncomputable def completeSchedulesEquivPaths (w : ℕ) :
    CompletePathSchedule w ≃ DiamondPaths.STPath (2 ^ w) :=
  DiamondPaths.bitVectorsEquivPaths (2 ^ w)

/-! ## Complete schedules in the finite-choice presentation -/

/-- The matching color which selects one Boolean child at a split-diamond branch. -/
@[expose]
public def branchColor (bit : Bool) : Fin 3 :=
  ThreeMatchingReachability.oldColor (finTwoEquiv.symm bit)

/-- Boolean branch tags give distinct finite-choice names. -/
public theorem branchColor_injective : Function.Injective branchColor := by
  intro left right heq
  apply finTwoEquiv.symm.injective
  exact ThreeMatchingReachability.oldColor_injective heq

/-- The Boolean color lookup selects the corresponding branch child. -/
public theorem choiceGraph_next_branchColor
    {k : ℕ} (i : Fin k) (bit : Bool) :
    (choiceGraph k).next (branchJunction i) (branchColor bit) =
      some (branchChild i bit) := by
  rw [choiceGraph_next_eq_some_iff]
  apply ThreeMatchingReachability.layer_external
  change DiamondPaths.edgeLayer k
    (finTwoEquiv (finTwoEquiv.symm bit))
      (DiamondPaths.junction i.castSucc) (DiamondPaths.branch i bit)
  simp [DiamondPaths.edgeLayer, DiamondPaths.Edge,
    DiamondPaths.edgeColor, DiamondPaths.junction, DiamondPaths.branch]

/-- The complete finite-choice list obtained from a Boolean path vector. -/
@[expose]
public def completeChoiceList {k : ℕ} (bits : Fin k → Bool) : List (Fin 3) :=
  List.ofFn (branchColor ∘ bits)

@[simp]
public theorem completeChoiceList_length {k : ℕ} (bits : Fin k → Bool) :
    (completeChoiceList bits).length = k := by
  simp [completeChoiceList]

/-- Distinct Boolean path vectors give distinct complete finite-choice lists. -/
public theorem completeChoiceList_injective (k : ℕ) :
    Function.Injective (@completeChoiceList k) := by
  intro left right heq
  have hfunctions : branchColor ∘ left = branchColor ∘ right :=
    List.ofFn_injective heq
  funext i
  exact branchColor_injective (congrFun hfunctions i)

private theorem not_branching_input
    {k : ℕ} (vertex : DiamondPaths.Vertex k) :
    ¬ (choiceGraph k).Branching
      (ThreeMatchingReachability.Vertex.input vertex) := by
  rw [choiceGraph_branching_iff_exists_branchJunction]
  rintro ⟨i, heq⟩
  cases heq

private theorem not_branching_branchOutput
    {k : ℕ} (i : Fin k) (bit : Bool) :
    ¬ (choiceGraph k).Branching
      (ThreeMatchingReachability.Vertex.output (DiamondPaths.branch i bit)) := by
  rw [choiceGraph_branching_iff_exists_branchJunction]
  rintro ⟨j, heq⟩
  have hold := congrArg ThreeMatchingReachability.project heq
  simp [branchJunction, DiamondPaths.branch, DiamondPaths.junction,
    ThreeMatchingReachability.project] at hold

private theorem internal_deterministicStep
    {k : ℕ} (vertex : DiamondPaths.Vertex k) :
    (choiceGraph k).DeterministicStep
      (.input vertex) (.output vertex) := by
  refine ⟨(choiceGraph_edge_iff k _ _).mpr
    (ThreeMatchingReachability.edge_internal (DiamondPaths.Edge k) vertex),
    not_branching_input vertex⟩

private theorem branchLeave_deterministicStep
    {k : ℕ} (i : Fin k) (bit : Bool) :
    (choiceGraph k).DeterministicStep
      (.output (DiamondPaths.branch i bit))
      (.input (DiamondPaths.junction i.succ)) := by
  refine ⟨(choiceGraph_edge_iff k _ _).mpr
    (ThreeMatchingReachability.edge_external ?_),
    not_branching_branchOutput i bit⟩
  simp [DiamondPaths.Edge, DiamondPaths.branch, DiamondPaths.junction]

private theorem branchTrace_head_deterministic
    {V Choice : Type*} (G : FiniteChoiceGraph V Choice)
    {choices : List Choice} {first source target : V}
    (prelude : ReflTransGen G.DeterministicStep first source)
    (trace : G.BranchTrace choices source target) :
    G.BranchTrace choices first target := by
  induction trace with
  | finish suffix => exact .finish (prelude.trans suffix)
  | branch suffix isBranch take rest _ =>
      exact .branch (prelude.trans suffix) isBranch take rest

private theorem branchTrace_completeChoiceList_from_junction
    {k : ℕ} (bits : Fin k → Bool) (i : Fin (k + 1)) :
    (choiceGraph k).BranchTrace
      ((completeChoiceList bits).drop i.val)
      (.input (DiamondPaths.junction i)) (target k) := by
  induction i using Fin.reverseInduction with
  | last =>
      have hdrop : (completeChoiceList bits).drop k = [] := by
        exact List.drop_eq_nil_of_le (by simp)
      change (choiceGraph k).BranchTrace
        ((completeChoiceList bits).drop k)
        (.input (DiamondPaths.junction (Fin.last k))) (target k)
      rw [hdrop]
      apply FiniteChoiceGraph.BranchTrace.finish
      simpa [target, DiamondPaths.target] using
        (ReflTransGen.single
          (internal_deterministicStep (DiamondPaths.junction (Fin.last k))))
  | cast i ih =>
      have hindex : i.val < (completeChoiceList bits).length := by
        simp
      have hdrop :
          (completeChoiceList bits).drop i.val =
            branchColor (bits i) ::
              (completeChoiceList bits).drop i.succ.val := by
        rw [List.drop_eq_getElem_cons hindex]
        simp [completeChoiceList]
      change (choiceGraph k).BranchTrace
        ((completeChoiceList bits).drop i.val)
        (.input (DiamondPaths.junction i.castSucc)) (target k)
      rw [hdrop]
      apply FiniteChoiceGraph.BranchTrace.branch
        (ReflTransGen.single
          (internal_deterministicStep (DiamondPaths.junction i.castSucc)))
        (choiceGraph_branching_iff_exists_branchJunction.mpr ⟨i, rfl⟩)
        (choiceGraph_next_branchColor i (bits i))
      apply branchTrace_head_deterministic (G := choiceGraph k)
        ((ReflTransGen.single
            (internal_deterministicStep (DiamondPaths.branch i (bits i)))).tail
          (branchLeave_deterministicStep i (bits i)))
      simpa using ih

/-- Every Boolean path vector is an actual target-reaching branch schedule in the finite-choice
presentation. -/
public theorem branchTrace_completeChoiceList {k : ℕ} (bits : Fin k → Bool) :
    (choiceGraph k).BranchTrace (completeChoiceList bits) (source k) (target k) := by
  simpa [source, DiamondPaths.source] using
    branchTrace_completeChoiceList_from_junction bits (0 : Fin (k + 1))

/-- Every Boolean path vector also has a bounded replay trace with the same complete list. -/
public theorem replayTrace_completeChoiceList {k : ℕ} (bits : Fin k → Bool) :
    (choiceGraph k).ReplayTrace (completeChoiceList bits) (source k) (target k) := by
  exact (choiceGraph k).replayTrace_of_branchTrace
    (branchTrace_completeChoiceList bits)

/-- Every choice name actually taken at a genuine split-diamond branch is one of the two
Boolean branch colors. -/
public theorem exists_bit_of_next_of_branching
    {k : ℕ} {vertex next : Vertex k} {color : Fin 3}
    (hbranch : (choiceGraph k).Branching vertex)
    (hnext : (choiceGraph k).next vertex color = some next) :
    ∃ bit : Bool, branchColor bit = color := by
  obtain ⟨i, rfl⟩ :=
    choiceGraph_branching_iff_exists_branchJunction.mp hbranch
  have hlayer := choiceGraph_next_eq_some_iff.mp hnext
  rcases next with next | next
  · change ∃ old : Fin 2,
      OldLayer k old (DiamondPaths.junction i.castSucc) next ∧
        ThreeMatchingReachability.oldColor old = color at hlayer
    obtain ⟨old, _, hold⟩ := hlayer
    refine ⟨finTwoEquiv old, ?_⟩
    simpa [branchColor] using hold
  · exact False.elim hlayer

/-- Every entry of a target-reaching branch trace is a Boolean branch color. -/
public theorem BranchTrace.forall_mem_exists_bit
    {k : ℕ} {choices : List (Fin 3)} {first last : Vertex k}
    (trace : (choiceGraph k).BranchTrace choices first last) :
    ∀ color ∈ choices, ∃ bit : Bool, branchColor bit = color := by
  induction trace with
  | finish _ => simp
  | branch _ isBranch take _ ih =>
      intro color hmem
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact exists_bit_of_next_of_branching isBranch take
      · exact ih color hrest

/-- A target-reaching branch schedule is a choice list equipped with evidence that it leads
from the designated source to the target.  Proof irrelevance means only the distinct lists are
counted. -/
public abbrev TargetBranchSchedule (k : ℕ) :=
  { choices : List (Fin 3) //
    Nonempty ((choiceGraph k).BranchTrace choices (source k) (target k)) }

/-- Regard a complete Boolean vector as its actual target-reaching finite-choice schedule. -/
@[expose]
public def completeTargetBranchSchedule {k : ℕ} (bits : Fin k → Bool) :
    TargetBranchSchedule k :=
  ⟨completeChoiceList bits, ⟨branchTrace_completeChoiceList bits⟩⟩

/-- Complete Boolean vectors inject into actual target-reaching finite-choice schedules. -/
public theorem completeTargetBranchSchedule_injective (k : ℕ) :
    Function.Injective (@completeTargetBranchSchedule k) := by
  intro left right heq
  apply completeChoiceList_injective k
  exact congrArg Subtype.val heq

/-- Every target-reaching choice list is the complete Boolean-color list of a unique path
vector. -/
public theorem completeTargetBranchSchedule_surjective (k : ℕ) :
    Function.Surjective (@completeTargetBranchSchedule k) := by
  rintro ⟨choices, ⟨trace⟩⟩
  have hlength : choices.length = k := branchTrace_length_eq trace
  have hall := BranchTrace.forall_mem_exists_bit trace
  let bits : Fin k → Bool := fun i ↦
    Classical.choose
      (hall (choices.get ⟨i.val, by omega⟩)
        (List.get_mem choices _))
  have hbits (i : Fin k) :
      branchColor (bits i) =
        choices.get ⟨i.val, by omega⟩ := by
    exact Classical.choose_spec
      (hall (choices.get ⟨i.val, by omega⟩)
        (List.get_mem choices _))
  refine ⟨bits, Subtype.ext ?_⟩
  change List.ofFn (branchColor ∘ bits) = choices
  apply List.ext_get
  · simp [hlength]
  · intro index hleft hright
    rw [List.get_ofFn]
    simp only [List.length_ofFn] at hleft
    exact hbits ⟨index, hleft⟩

/-- Complete Boolean vectors are equivalent to the actual target-reaching branch-choice
lists. -/
@[expose]
public noncomputable def completeSchedulesEquivTargetBranchSchedules (k : ℕ) :
    (Fin k → Bool) ≃ TargetBranchSchedule k :=
  Equiv.ofBijective completeTargetBranchSchedule
    ⟨completeTargetBranchSchedule_injective k,
      completeTargetBranchSchedule_surjective k⟩

/-- The actual target-reaching choice lists of the succinct finite-choice graph number exactly
`2 ^ (2 ^ w)`. -/
public theorem card_targetBranchSchedules (w : ℕ) :
    Nat.card (TargetBranchSchedule (2 ^ w)) = 2 ^ (2 ^ w) := by
  rw [Nat.card_congr (completeSchedulesEquivTargetBranchSchedules (2 ^ w)).symm]
  simp

/-- The analogous type whose evidence is a bounded replay trace. -/
public abbrev TargetReplaySchedule (k : ℕ) :=
  { choices : List (Fin 3) //
    Nonempty ((choiceGraph k).ReplayTrace choices (source k) (target k)) }

/-- Branch-trace and bounded-replay presentations have exactly the same target-reaching choice
lists. -/
@[expose]
public noncomputable def targetBranchSchedulesEquivReplaySchedules (k : ℕ) :
    TargetBranchSchedule k ≃ TargetReplaySchedule k where
  toFun schedule :=
    ⟨schedule.1, ⟨(choiceGraph k).replayTrace_of_branchTrace schedule.2.some⟩⟩
  invFun schedule :=
    ⟨schedule.1, ⟨(choiceGraph k).branchTrace_of_replayTrace schedule.2.some⟩⟩
  left_inv := by intro schedule; exact Subtype.ext rfl
  right_inv := by intro schedule; exact Subtype.ext rfl

/-- The actual target-reaching bounded-replay choice lists also number exactly
`2 ^ (2 ^ w)`. -/
public theorem card_targetReplaySchedules (w : ℕ) :
    Nat.card (TargetReplaySchedule (2 ^ w)) = 2 ^ (2 ^ w) := by
  rw [Nat.card_congr (targetBranchSchedulesEquivReplaySchedules (2 ^ w)).symm]
  exact card_targetBranchSchedules w

/-- Regard a complete Boolean vector as an actual target-reaching replay schedule. -/
@[expose]
public def completeTargetReplaySchedule {k : ℕ} (bits : Fin k → Bool) :
    TargetReplaySchedule k :=
  ⟨completeChoiceList bits, ⟨replayTrace_completeChoiceList bits⟩⟩

/-- Complete Boolean vectors inject into actual target-reaching replay schedules. -/
public theorem completeTargetReplaySchedule_injective (k : ℕ) :
    Function.Injective (@completeTargetReplaySchedule k) := by
  intro left right heq
  apply completeChoiceList_injective k
  exact congrArg Subtype.val heq

/-- A bounded schedule is determined by its list of entries. -/
public theorem scheduleToList_injective
    {Choice : Type*} {budget : ℕ} :
    Function.Injective
      (FiniteChoiceGraph.Schedule.toList :
        FiniteChoiceGraph.Schedule Choice budget → List Choice) := by
  rintro ⟨leftLength, left⟩ ⟨rightLength, right⟩ heq
  have hlength : leftLength = rightLength := by
    apply Fin.ext
    simpa using congrArg List.length heq
  subst rightLength
  have hvalues : left = right := by
    apply List.ofFn_injective
    exact heq
  subst right
  rfl

/-- Actual bounded schedules of budget `k` whose replay reaches the designated target. -/
public abbrev TargetBoundedReplaySchedule (k : ℕ) :=
  { schedule : FiniteChoiceGraph.Schedule (Fin 3) k //
    Nonempty ((choiceGraph k).ReplayTrace schedule.toList (source k) (target k)) }

/-- Pack a target-reaching replay list into the bounded schedule type with budget `k`. -/
@[expose]
public noncomputable def targetReplayToBoundedSchedule {k : ℕ}
    (schedule : TargetReplaySchedule k) : TargetBoundedReplaySchedule k := by
  have hlength : schedule.1.length ≤ k :=
    (replayTrace_length_eq schedule.2.some).le
  let bounded := FiniteChoiceGraph.Schedule.ofList schedule.1 hlength
  refine ⟨bounded, ⟨?_⟩⟩
  simpa only [bounded, FiniteChoiceGraph.Schedule.toList_ofList] using
    schedule.2.some

/-- Packing and then reading a target replay schedule recovers its list. -/
@[simp]
public theorem targetReplayToBoundedSchedule_toList
    {k : ℕ} (schedule : TargetReplaySchedule k) :
    (targetReplayToBoundedSchedule schedule).1.toList = schedule.1 := by
  simp [targetReplayToBoundedSchedule]

/-- Forget the bounded-record wrapper while retaining its replay evidence. -/
@[expose]
public def targetBoundedScheduleToReplay {k : ℕ}
    (schedule : TargetBoundedReplaySchedule k) : TargetReplaySchedule k :=
  ⟨schedule.1.toList, schedule.2⟩

/-- Target-reaching replay lists and target-reaching bounded schedule records are equivalent.
Every such list has length exactly `k`, so conversion to the budget-`k` record loses nothing. -/
@[expose]
public noncomputable def targetReplaySchedulesEquivBoundedSchedules (k : ℕ) :
    TargetReplaySchedule k ≃ TargetBoundedReplaySchedule k where
  toFun := targetReplayToBoundedSchedule
  invFun := targetBoundedScheduleToReplay
  left_inv := by
    intro schedule
    apply Subtype.ext
    exact targetReplayToBoundedSchedule_toList schedule
  right_inv := by
    intro schedule
    apply Subtype.ext
    apply scheduleToList_injective
    exact targetReplayToBoundedSchedule_toList
      (targetBoundedScheduleToReplay schedule)

/-- The actual target-reaching bounded schedule records number exactly `2 ^ (2 ^ w)`. -/
public theorem card_targetBoundedReplaySchedules (w : ℕ) :
    Nat.card (TargetBoundedReplaySchedule (2 ^ w)) = 2 ^ (2 ^ w) := by
  rw [Nat.card_congr
    (targetReplaySchedulesEquivBoundedSchedules (2 ^ w)).symm]
  exact card_targetReplaySchedules w

/-- A complete Boolean vector as an actual budget-exact target-reaching schedule record. -/
@[expose]
public noncomputable def completeTargetBoundedReplaySchedule
    {k : ℕ} (bits : Fin k → Bool) :
    TargetBoundedReplaySchedule k :=
  targetReplayToBoundedSchedule (completeTargetReplaySchedule bits)

/-- Complete Boolean vectors inject into actual target-reaching bounded schedule records. -/
public theorem completeTargetBoundedReplaySchedule_injective (k : ℕ) :
    Function.Injective (@completeTargetBoundedReplaySchedule k) := by
  intro left right heq
  apply completeTargetReplaySchedule_injective k
  exact (targetReplaySchedulesEquivBoundedSchedules k).injective heq

/-! ## Exact target-reaching choice length -/

/-- Every target-reaching branch trace in the succinct finite-choice presentation contains
exactly `2 ^ w` genuine branch choices. -/
public theorem branchTrace_length_eq_twoPow
    {w : ℕ} {choices : List (Fin 3)}
    (trace : (choiceGraph (2 ^ w)).BranchTrace choices
      (ThreeMatchingDiamondBranches.source (2 ^ w))
      (ThreeMatchingDiamondBranches.target (2 ^ w))) :
    choices.length = 2 ^ w := by
  exact branchTrace_length_eq trace

/-- Every target-reaching bounded replay trace in the succinct finite-choice presentation also
contains exactly `2 ^ w` genuine branch choices. -/
public theorem replayTrace_length_eq_twoPow
    {w : ℕ} {choices : List (Fin 3)}
    (trace : (choiceGraph (2 ^ w)).ReplayTrace choices
      (ThreeMatchingDiamondBranches.source (2 ^ w))
      (ThreeMatchingDiamondBranches.target (2 ^ w))) :
    choices.length = 2 ^ w := by
  exact replayTrace_length_eq trace

/-! ## An explicit eventual-capacity witness -/

/-- Twice the product of the row-alphabet cardinality and the fixed linear factor is a width at
which the double-exponential schedule family exceeds the row capacity. -/
@[expose]
public def obstructionWidth (A : Type*) [Fintype A] (factor : ℕ) : ℕ :=
  Nat.mul 2 (Nat.mul (Fintype.card A) factor)

private theorem linear_exponent_lt_twoPow (coefficient : ℕ) :
    coefficient * (2 * coefficient) < 2 ^ (2 * coefficient) := by
  have hsquare : coefficient * (2 * coefficient) = 2 * coefficient ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hsquare]
  have hbound := Nat.two_mul_sq_add_one_le_two_pow_two_mul coefficient
  omega

/-- At the explicit obstruction width, the exact row capacity is strictly smaller than the
number of complete path schedules.  No nonemptiness or positive-factor premise is needed. -/
public theorem rowCapacity_lt_completePathSchedules
    (A : Type*) [Fintype A] (factor : ℕ) :
    Fintype.card A ^ (factor * obstructionWidth A factor) <
      2 ^ (2 ^ obstructionWidth A factor) := by
  let coefficient := Fintype.card A * factor
  have hbase : Fintype.card A ≤ 2 ^ Fintype.card A :=
    (Nat.lt_two_pow_self (n := Fintype.card A)).le
  have hlinear : coefficient * (2 * coefficient) < 2 ^ (2 * coefficient) :=
    linear_exponent_lt_twoPow coefficient
  calc
    Fintype.card A ^ (factor * obstructionWidth A factor) ≤
        (2 ^ Fintype.card A) ^ (factor * obstructionWidth A factor) :=
      Nat.pow_le_pow_left hbase _
    _ = 2 ^ (Fintype.card A * (factor * obstructionWidth A factor)) :=
      (pow_mul 2 (Fintype.card A) (factor * obstructionWidth A factor)).symm
    _ = 2 ^ (coefficient * (2 * coefficient)) := by
      apply congrArg (fun exponent : ℕ ↦ 2 ^ exponent)
      dsimp only [obstructionWidth, coefficient]
      exact (Nat.mul_assoc _ _ _).symm
    _ < 2 ^ (2 ^ (2 * coefficient)) :=
      Nat.pow_lt_pow_right (by omega) hlinear
    _ = 2 ^ (2 ^ obstructionWidth A factor) := by
      apply congrArg (fun width ↦ 2 ^ (2 ^ width))
      change Nat.mul 2 (Nat.mul (Fintype.card A) factor) =
        Nat.mul 2 (Nat.mul (Fintype.card A) factor)
      rfl

/-- For every finite row alphabet and fixed linear factor, some width has too few rows to
injectively materialize every complete path vector. -/
public theorem exists_no_injective_completePathSchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ) :
    ∃ w : ℕ, ∀ encode : CompletePathSchedule w →
        Fin (factor * w) → A,
      ¬ Function.Injective encode := by
  refine ⟨obstructionWidth A factor, ?_⟩
  intro encode
  exact ScheduleCapacity.not_injective_bitVectors_of_capacity_lt
    (rowCapacity_lt_completePathSchedules A factor) encode

/-- The same explicit width cannot injectively materialize all source-to-target path records. -/
public theorem exists_no_injective_succinctDiamondPaths_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ) :
    ∃ w : ℕ, ∀ encode : DiamondPaths.STPath (2 ^ w) →
        Fin (factor * w) → A,
      ¬ Function.Injective encode := by
  refine ⟨obstructionWidth A factor, ?_⟩
  intro encode
  exact ScheduleCapacity.not_injective_diamondPaths_of_capacity_lt
    (rowCapacity_lt_completePathSchedules A factor) encode

/-- At the same explicit width, the actual target-reaching branch-choice lists cannot all be
injectively materialized in a fixed-linear row. -/
public theorem exists_no_injective_targetBranchSchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ) :
    ∃ w : ℕ, ∀ encode : TargetBranchSchedule (2 ^ w) →
        Fin (factor * w) → A,
      ¬ Function.Injective encode := by
  refine ⟨obstructionWidth A factor, ?_⟩
  intro encode hinjective
  exact ScheduleCapacity.not_injective_bitVectors_of_capacity_lt
    (rowCapacity_lt_completePathSchedules A factor)
    (encode ∘ completeTargetBranchSchedule)
    (hinjective.comp
      (completeTargetBranchSchedule_injective
        (2 ^ obstructionWidth A factor)))

/-- The same literal-capacity obstruction applies when target-reaching schedules carry bounded
replay evidence instead of branch-trace evidence. -/
public theorem exists_no_injective_targetReplaySchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ) :
    ∃ w : ℕ, ∀ encode : TargetReplaySchedule (2 ^ w) →
        Fin (factor * w) → A,
      ¬ Function.Injective encode := by
  refine ⟨obstructionWidth A factor, ?_⟩
  intro encode hinjective
  exact ScheduleCapacity.not_injective_bitVectors_of_capacity_lt
    (rowCapacity_lt_completePathSchedules A factor)
    (encode ∘ completeTargetReplaySchedule)
    (hinjective.comp
      (completeTargetReplaySchedule_injective
        (2 ^ obstructionWidth A factor)))

/-- In particular, even the actual target-reaching records in the repository's bounded
schedule type cannot all be injectively materialized in a fixed-linear row. -/
public theorem exists_no_injective_targetBoundedReplaySchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ) :
    ∃ w : ℕ, ∀ encode : TargetBoundedReplaySchedule (2 ^ w) →
        Fin (factor * w) → A,
      ¬ Function.Injective encode := by
  refine ⟨obstructionWidth A factor, ?_⟩
  intro encode hinjective
  exact ScheduleCapacity.not_injective_bitVectors_of_capacity_lt
    (rowCapacity_lt_completePathSchedules A factor)
    (encode ∘ completeTargetBoundedReplaySchedule)
    (hinjective.comp
      (completeTargetBoundedReplaySchedule_injective
        (2 ^ obstructionWidth A factor)))

/-- Even the larger type of all Boolean schedules of length at most `2 ^ w` cannot be
injectively materialized in fixed-linearly many row cells at the explicit witness width. -/
public theorem exists_no_injective_boundedSchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ) :
    ∃ w : ℕ, ∀ encode :
        FiniteChoiceGraph.Schedule Bool (2 ^ w) → Fin (factor * w) → A,
      ¬ Function.Injective encode := by
  refine ⟨obstructionWidth A factor, ?_⟩
  intro encode
  exact ScheduleCapacity.not_injective_schedules_of_capacity_lt
    (by simpa using rowCapacity_lt_completePathSchedules A factor) encode

/-- The actual three-color finite-choice schedule type is also too large to inject into the
same fixed-linear row family.  This statement counts all bounded schedules, not only valid
target-reaching schedules. -/
public theorem exists_no_injective_threeColorSchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ) :
    ∃ w : ℕ, ∀ encode :
        FiniteChoiceGraph.Schedule (Fin 3) (2 ^ w) → Fin (factor * w) → A,
      ¬ Function.Injective encode := by
  refine ⟨obstructionWidth A factor, ?_⟩
  intro encode
  apply ScheduleCapacity.not_injective_schedules_of_capacity_lt (encode := encode)
  exact (rowCapacity_lt_completePathSchedules A factor).trans_le
    (Nat.pow_le_pow_left (by simp) (2 ^ obstructionWidth A factor))

end SuccinctDiamondScheduleCapacity

end
