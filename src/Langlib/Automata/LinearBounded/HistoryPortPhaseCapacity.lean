module

public import Langlib.Automata.LinearBounded.HistoryDiamondCapacity
public import Langlib.Automata.LinearBounded.HistoryPortCompilation
import Mathlib.Tactic

@[expose]
public section

/-!
# Capacity of the exhaustive history-port phase line

The exhaustive port schedule used by `HistoryPortCompilation` visits a port incident with every
rooted history.  Choosing one such visit for each history is injective, because the represented
port's endpoint recovers the history.  Thus the phase line has at least as many phases as the
complete rooted-history type.

For the chain of `k` diamonds, the earlier injection of all `2 ^ k` explicit paths into rooted
histories therefore gives a lower bound of `2 ^ k` on the *actual phase type* of the exhaustive
two-matching presentation.  This result concerns that particular nonuniform history traversal.
It is not a size lower bound for other source-sensitive reductions or deterministic simulations,
which may recompute context or avoid materializing the complete history unfolding.
-/

namespace HistoryPortPhaseCapacity

open Relation
open FunctionalGraphReversibleTraversal
open HistoryUnfolding

universe u

variable {V : Type u} [Fintype V]

/-- The action list used by the exhaustive port traversal of all simple histories rooted at
`source`. -/
public noncomputable def historyActions (edge : V → V → Prop) (source : V) :
    List PortSystem.Action :=
  let ports := HistoryPortCompilation.historyPorts edge source
  ports.exhaustiveSchedule (ports.anchor (History.root edge source))

/-- The rooted history represented at one phase of the exhaustive schedule. -/
@[expose]
public noncomputable def representedHistory
    (edge : V → V → Prop) (source : V)
    (phase : PortSystem.Phase (historyActions edge source)) : History edge source :=
  let ports := HistoryPortCompilation.historyPorts edge source
  ports.endpoint
    (ports.portAt (historyActions edge source)
      (ports.anchor (History.root edge source)) phase)

/-- Every rooted history occurs at some phase of the exhaustive history-port schedule. -/
public theorem exists_phase_representing
    (edge : V → V → Prop) (source : V) (history : History edge source) :
    ∃ phase : PortSystem.Phase (historyActions edge source),
      representedHistory edge source phase = history := by
  let ports := HistoryPortCompilation.historyPorts edge source
  have haccepts :
      HistoryPortCompilation.AcceptsWhere ports (History.root edge source)
        (fun candidate : History edge source ↦ candidate = history) :=
    (HistoryPortCompilation.acceptsWhere_iff_exists_reaches_of_cofunctional_root
      ports History.extension_leftUnique
      (History.root_no_predecessor edge source)
      (fun candidate : History edge source ↦ candidate = history)).2
        ⟨history, rfl, history.root_reaches⟩
  obtain ⟨phase, _, hphase⟩ := haccepts
  exact ⟨phase, hphase⟩

/-- Choose the first-class phase witness supplied by exhaustive traversal.  No effectiveness is
claimed: both the schedule and this selection use finite classical choice. -/
public noncomputable def phaseOfHistory
    (edge : V → V → Prop) (source : V) (history : History edge source) :
    PortSystem.Phase (historyActions edge source) :=
  Classical.choose (exists_phase_representing edge source history)

/-- The chosen phase represents the history from which it was selected. -/
public theorem representedHistory_phaseOfHistory
    (edge : V → V → Prop) (source : V) (history : History edge source) :
    representedHistory edge source (phaseOfHistory edge source history) = history :=
  Classical.choose_spec (exists_phase_representing edge source history)

/-- Distinct rooted histories require distinct phases in the actual exhaustive schedule. -/
public theorem phaseOfHistory_injective
    (edge : V → V → Prop) (source : V) :
    Function.Injective (phaseOfHistory edge source) := by
  intro left right heq
  calc
    left = representedHistory edge source (phaseOfHistory edge source left) :=
      (representedHistory_phaseOfHistory edge source left).symm
    _ = representedHistory edge source (phaseOfHistory edge source right) := by rw [heq]
    _ = right := representedHistory_phaseOfHistory edge source right

/-- The number of phases in the exhaustive history-port line is at least the number of rooted
histories.  The theorem has no lower-cardinality premise on the finite base type. -/
public theorem card_history_le_card_phase
    (edge : V → V → Prop) (source : V) :
    Fintype.card (History edge source) ≤
      Fintype.card (PortSystem.Phase (historyActions edge source)) := by
  exact Fintype.card_le_of_injective (phaseOfHistory edge source)
    (phaseOfHistory_injective edge source)

/-- List-length form of the same bound: there is one more phase than scheduled action. -/
public theorem card_history_le_actions_length_add_one
    (edge : V → V → Prop) (source : V) :
    Fintype.card (History edge source) ≤ (historyActions edge source).length + 1 := by
  simpa only [Fintype.card_fin] using card_history_le_card_phase edge source

/-! ## Diamond-chain consequence -/

/-- On the `k`-diamond chain, the actual phase type of the exhaustive history traversal has at
least `2 ^ k` elements.  This includes `k = 0`. -/
public theorem twoPow_le_card_historyPhase (k : ℕ) :
    2 ^ k ≤ Fintype.card
      (PortSystem.Phase
        (historyActions (DiamondPaths.Edge k) (DiamondPaths.source k))) := by
  exact (HistoryDiamondCapacity.twoPow_le_card_history k).trans
    (card_history_le_card_phase (DiamondPaths.Edge k) (DiamondPaths.source k))

/-- Equivalently, the exhaustive history-port action list for a `k`-diamond chain has at least
`2 ^ k - 1` actions. -/
public theorem twoPow_le_historyActions_length_add_one (k : ℕ) :
    2 ^ k ≤
      (historyActions (DiamondPaths.Edge k) (DiamondPaths.source k)).length + 1 := by
  simpa only [Fintype.card_fin] using twoPow_le_card_historyPhase k

/-- Direct action-count form of the exponential lower bound. -/
public theorem twoPow_sub_one_le_historyActions_length (k : ℕ) :
    2 ^ k - 1 ≤
      (historyActions (DiamondPaths.Edge k) (DiamondPaths.source k)).length := by
  have h := twoPow_le_historyActions_length_add_one k
  omega

/-- Injectively representing every phase of the actual diamond-history schedule in one
width-`width` row requires capacity for all `2 ^ k` retained path contexts.  The finite row
alphabet and both natural parameters are arbitrary. -/
public theorem historyPhases_le_rowCapacity_of_injective
    {A : Type*} [Fintype A] {k width : ℕ}
    (encode :
      PortSystem.Phase
          (historyActions (DiamondPaths.Edge k) (DiamondPaths.source k)) →
        Fin width → A)
    (hinjective : Function.Injective encode) :
    2 ^ k ≤ Fintype.card A ^ width := by
  calc
    2 ^ k ≤ Fintype.card
        (PortSystem.Phase
          (historyActions (DiamondPaths.Edge k) (DiamondPaths.source k))) :=
      twoPow_le_card_historyPhase k
    _ ≤ Fintype.card (Fin width → A) :=
      Fintype.card_le_of_injective encode hinjective
    _ = Fintype.card A ^ width := Fintype.card_pi_const A width

/-- Below the `2 ^ k` threshold, the complete phase set of this particular exhaustive
presentation cannot be injected into one width-`width` row. -/
public theorem not_injective_historyPhases_of_capacity_lt
    {A : Type*} [Fintype A] {k width : ℕ}
    (hcapacity : Fintype.card A ^ width < 2 ^ k)
    (encode :
      PortSystem.Phase
          (historyActions (DiamondPaths.Edge k) (DiamondPaths.source k)) →
        Fin width → A) :
    ¬ Function.Injective encode := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (historyPhases_le_rowCapacity_of_injective encode hinjective)) hcapacity

end HistoryPortPhaseCapacity

end
