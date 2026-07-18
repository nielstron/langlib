module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.LanguageEquivalence
public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.TwoMatching
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.Determinize
public import Langlib.Automata.LinearBounded.MachineThreeMatchings.NormalForm

@[expose]
public section

/-!
# Deterministic linear space as exact two-matching linear space

The marked Euler probe compiles an arbitrary deterministic marker-free LBA
presentation into a canonical endmarker LBA whose complete raw configuration
relation is an exact union of two directed matchings.  The language theorem is
uniform over every word, including the empty word, while the matching theorem
quantifies over every tape width and every malformed raw configuration.

Together with the existing determinization of exact two-matching
presentations, this identifies `DLBA` with `TwoMatchingLBA`.  Combining that
identity with the universal three-matching normal form isolates the first LBA
problem as precisely the remaining language-class inclusion from the
three-matching class into the two-matching class.  No equality between `LBA`
and `DLBA` is asserted here.
-/

open GraphWalking
open GraphWalking.MarkedEulerProbe

/-- Every deterministic-LBA language has a canonical raw presentation whose
complete fixed-width step relations are exact unions of two directed
matchings.  This is uniform over arbitrary finite terminal, work, and state
types; no nontrivial-cardinality premise is needed. -/
public theorem is_TwoMatchingLBA_of_is_DLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_DLBA L) : is_TwoMatchingLBA L := by
  rcases hL with
    ⟨Gamma, Q, hGamma, hQ, hdecGamma, hdecQ, acceptEmpty, machine, hmachine⟩
  letI := hGamma
  letI := hQ
  letI := hdecGamma
  letI := hdecQ
  let simulator :=
    EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty
  rw [← hmachine]
  refine
    ⟨WorkSymbol T Gamma (LBA.SimState (Option Q)),
      State T Gamma (LBA.SimState (Option Q)),
      inferInstance, inferInstance, inferInstance, inferInstance,
      rawMachine simulator, rawMachine_hasTwoMatchingStepPartition simulator,
      ?_⟩
  exact languageEnd_rawMachine_deterministicSimMachine_eq machine acceptEmpty

/-- Deterministic linear space is contained in the exact-two-matching LBA
class, over every finite terminal alphabet. -/
public theorem DLBA_subset_twoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (DLBA : Set (Language T)) ⊆ TwoMatchingLBA :=
  fun _ hL ↦ is_TwoMatchingLBA_of_is_DLBA hL

/-- Exact two directed-matching layers characterize deterministic linear
space. -/
public theorem TwoMatchingLBA_eq_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (TwoMatchingLBA : Set (Language T)) = DLBA :=
  Set.Subset.antisymm twoMatchingLBA_subset_DLBA
    DLBA_subset_twoMatchingLBA

/-- The first LBA problem is equivalent to asking whether every LBA language
has an exact-two-matching presentation. -/
public theorem lba_eq_dlba_iff_lba_subset_twoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((LBA : Set (Language T)) ⊆ TwoMatchingLBA) := by
  rw [TwoMatchingLBA_eq_DLBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

/-- Since three exact matching layers already present every LBA language, the
unrestricted LBA-versus-DLBA question is exactly the remaining inclusion from
the acyclic degree-two three-matching normal form into the two-matching
class. -/
public theorem
    lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_subset_twoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((AcyclicDegreeTwoThreeMatchingLBA : Set (Language T)) ⊆
        TwoMatchingLBA) := by
  rw [AcyclicDegreeTwoThreeMatchingLBA_eq_LBA,
    TwoMatchingLBA_eq_DLBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

/-- Equivalently, the first LBA problem asks whether the universal
three-matching normal-form class and the exact-two-matching class are equal. -/
public theorem
    lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_eq_twoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((AcyclicDegreeTwoThreeMatchingLBA : Set (Language T)) =
        TwoMatchingLBA) := by
  rw [AcyclicDegreeTwoThreeMatchingLBA_eq_LBA,
    TwoMatchingLBA_eq_DLBA]

end
