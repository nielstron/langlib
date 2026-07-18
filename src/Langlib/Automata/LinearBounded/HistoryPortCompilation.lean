module

public import Langlib.Automata.LinearBounded.CofunctionalRootReachability
public import Langlib.Automata.LinearBounded.HistoryUnfoldingReachability
public import Langlib.Automata.LinearBounded.LinearTwoDiforestReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# A finite reversible port traversal of bounded histories

This module composes the finite bounded-history unfolding of an arbitrary finite directed graph
with the exhaustive reversible port traversal.  The history-extension relation is cofunctional
and its empty history has no predecessor.  Consequently, traversing the weak component of that
root visits exactly the histories extending it, and hence exactly the original vertices reachable
from the designated source.

The resulting finite phase line is partitioned by source-phase parity into two directed
matchings.  This is a semantic finite-instance construction only.  In particular, the exhaustive
schedule uses finite choice, its phase type depends on the whole input instance, and no effective
or space-bounded encoding of phases is supplied here.
-/

namespace HistoryPortCompilation

open Relation
open FunctionalGraphReversibleTraversal

universe u

/-! ## Accepting sets for the exhaustive port schedule -/

/-- The exhaustive port schedule accepts a predicate when some reachable phase represents a
vertex satisfying that predicate. -/
@[expose]
public def AcceptsWhere {V : Type u} {edge : V → V → Prop}
    (ports : PortSystem edge) (source : V) (accepting : V → Prop) : Prop :=
  let actions := ports.exhaustiveSchedule (ports.anchor source)
  ∃ phase, ReflTransGen (PortSystem.PhaseStep actions) 0 phase ∧
    accepting (ports.endpoint
      (ports.portAt actions (ports.anchor source) phase))

/-- On a cofunctional graph, the exhaustive port schedule from a predecessor-free root accepts
a vertex predicate exactly when a satisfying vertex is forward-reachable from the root. -/
public theorem acceptsWhere_iff_exists_reaches_of_cofunctional_root
    {V : Type u} {edge : V → V → Prop}
    (ports : PortSystem edge)
    (cofunctional : Relator.LeftUnique edge) {root : V}
    (root_initial : ∀ predecessor, ¬ edge predecessor root)
    (accepting : V → Prop) :
    AcceptsWhere ports root accepting ↔
      ∃ target, accepting target ∧ ReflTransGen edge root target := by
  constructor
  · rintro ⟨phase, hphase, haccept⟩
    let actions := ports.exhaustiveSchedule (ports.anchor root)
    let target := ports.endpoint
      (ports.portAt actions (ports.anchor root) phase)
    have htarget : ports.Accepts root target := ⟨phase, hphase, rfl⟩
    exact ⟨target, haccept,
      (ports.accepts_iff_reaches_of_cofunctional_root
        cofunctional root_initial).mp htarget⟩
  · rintro ⟨target, haccept, hreach⟩
    obtain ⟨phase, hphase, htarget⟩ :=
      (ports.accepts_iff_reaches_of_cofunctional_root
        cofunctional root_initial).mpr hreach
    exact ⟨phase, hphase, htarget ▸ haccept⟩

/-! ## Alternating matching layers on a finite phase line -/

/-- Color each edge of a finite phase line by the parity of its source phase. -/
@[expose]
public def PhaseLayer (actions : List PortSystem.Action) (color : Fin 2) :
    PortSystem.Phase actions → PortSystem.Phase actions → Prop :=
  fun source target =>
    PortSystem.PhaseStep actions source target ∧ source.val % 2 = color.val

/-- Every phase edge has exactly one parity color. -/
public theorem phaseStep_iff_existsUnique_phaseLayer
    (actions : List PortSystem.Action) (source target : PortSystem.Phase actions) :
    PortSystem.PhaseStep actions source target ↔
      ∃! color, PhaseLayer actions color source target := by
  constructor
  · intro hstep
    let color : Fin 2 := ⟨source.val % 2, Nat.mod_lt _ (by omega)⟩
    refine ⟨color, ⟨hstep, rfl⟩, ?_⟩
    intro other hother
    apply Fin.ext
    exact hother.2.symm
  · rintro ⟨color, hcolor, _⟩
    exact hcolor.1

/-- A parity layer contains no edge outside the phase line. -/
public theorem phaseLayer_sub_phaseStep
    (actions : List PortSystem.Action) (color : Fin 2)
    {source target : PortSystem.Phase actions}
    (hstep : PhaseLayer actions color source target) :
    PortSystem.PhaseStep actions source target :=
  hstep.1

/-- Each parity layer is a partial bijection. -/
public theorem phaseLayer_biUnique
    (actions : List PortSystem.Action) (color : Fin 2) :
    Relator.BiUnique (PhaseLayer actions color) := by
  constructor
  · intro first second target hfirst hsecond
    exact (PortSystem.phaseStep_biUnique actions).1 hfirst.1 hsecond.1
  · intro source first second hfirst hsecond
    exact (PortSystem.phaseStep_biUnique actions).2 hfirst.1 hsecond.1

/-- No two edges of one parity layer are composable. -/
public theorem phaseLayer_pathLengthAtMostOne
    (actions : List PortSystem.Action) (color : Fin 2) :
    LinearTwoDiforestReachability.PathLengthAtMostOne
      (PhaseLayer actions color) := by
  intro first middle last hfirst hlast
  have hmiddle : middle.val = first.val + 1 := hfirst.1
  have hfirstParity : first.val % 2 = color.val := hfirst.2
  have hmiddleParity : middle.val % 2 = color.val := hlast.2
  omega

/-- Independently of the scheduled actions, the finite phase line is deterministic and
cofunctional, acyclic, reaches its last phase, and has no transition out of that phase. -/
public theorem phaseLine_biUnique_acyclic_terminating
    (actions : List PortSystem.Action) :
    Relator.BiUnique (PortSystem.PhaseStep actions) ∧
      (∀ phase, ¬ TransGen (PortSystem.PhaseStep actions) phase phase) ∧
      ReflTransGen (PortSystem.PhaseStep actions) 0 (Fin.last actions.length) ∧
      ∀ next, ¬ PortSystem.PhaseStep actions (Fin.last actions.length) next :=
  ⟨PortSystem.phaseStep_biUnique actions,
    PortSystem.phaseStep_acyclic actions,
    PortSystem.zero_reaches_last actions,
    PortSystem.last_terminal actions⟩

/-- Packaged finite-instance result: the exhaustive schedule from a cofunctional root has exact
forward accepting-set semantics, and its deterministic phase line is exactly the union of two
directed matchings.

The relation represented here is the finite phase line, not the source graph itself. -/
public theorem cofunctionalRoot_exact_twoMatching_phasePresentation
    {V : Type u} {edge : V → V → Prop}
    (ports : PortSystem edge)
    (cofunctional : Relator.LeftUnique edge) {root : V}
    (root_initial : ∀ predecessor, ¬ edge predecessor root)
    (accepting : V → Prop) :
    let actions := ports.exhaustiveSchedule (ports.anchor root)
    (AcceptsWhere ports root accepting ↔
      ∃ target, accepting target ∧ ReflTransGen edge root target) ∧
    (∀ source target, PortSystem.PhaseStep actions source target ↔
      ∃! color, PhaseLayer actions color source target) ∧
    (∀ color source target, PhaseLayer actions color source target →
      PortSystem.PhaseStep actions source target) ∧
    (∀ color, Relator.BiUnique (PhaseLayer actions color)) ∧
    ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
      (PhaseLayer actions color) := by
  dsimp only
  exact ⟨acceptsWhere_iff_exists_reaches_of_cofunctional_root
      ports cofunctional root_initial accepting,
    phaseStep_iff_existsUnique_phaseLayer _,
    phaseLayer_sub_phaseStep _,
    phaseLayer_biUnique _,
    phaseLayer_pathLengthAtMostOne _⟩

/-! ## Compilation of a finite source graph through its history unfolding -/

open HistoryUnfolding

variable {V : Type u} [Fintype V]

/-- Canonical reversible edge-end ports for the finite graph of simple histories rooted at a
designated source. -/
public noncomputable def historyPorts (edge : V → V → Prop) (source : V) :
    PortSystem (History.Extension (edge := edge) (source := source)) :=
  letI : DecidableEq V := Classical.decEq V
  CanonicalPortSystem.ofFinite
    (History.Extension (edge := edge) (source := source))

/-- The exhaustive history-port traversal accepts when a represented history ends at a source
vertex satisfying `accepting`. -/
@[expose]
public noncomputable def Accepts
    (edge : V → V → Prop) (source : V) (accepting : V → Prop) : Prop :=
  AcceptsWhere (historyPorts edge source) (History.root edge source)
    (fun history ↦ accepting history.endpoint)

/-- The port compiler accepts exactly when an accepting history is forward-reachable from the
empty history.  This is the direct cofunctional-root composition, before projecting history
endpoints back to the source graph. -/
public theorem accepts_iff_exists_reachable_history
    (edge : V → V → Prop) (source : V) (accepting : V → Prop) :
    Accepts edge source accepting ↔
      ∃ history : History edge source,
        accepting history.endpoint ∧
          ReflTransGen History.Extension (History.root edge source) history := by
  exact acceptsWhere_iff_exists_reaches_of_cofunctional_root
    (historyPorts edge source) History.extension_leftUnique
    (History.root_no_predecessor edge source)
    (fun history : History edge source ↦ accepting history.endpoint)

/-- **Exact source-graph semantics.**  The deterministic exhaustive traversal of finite simple
histories encounters an accepting endpoint exactly when the original directed graph reaches an
accepting vertex from the designated source.

No acyclicity assumption is needed: the history equivalence erases loops from a finite walk
before the finite port traversal is formed. -/
public theorem accepts_iff_exists_reaches
    (edge : V → V → Prop) (source : V) (accepting : V → Prop) :
    Accepts edge source accepting ↔
      ∃ target, accepting target ∧ ReflTransGen edge source target := by
  rw [accepts_iff_exists_reachable_history]
  simpa only [and_comm] using
    (exists_reachable_final_iff_exists_history
      (edge := edge) (source := source) accepting).symm

/-- Direct phase-line form of the source-graph theorem: original accepting reachability is
equivalent to reaching a scheduled phase whose represented history has an accepting endpoint. -/
public theorem exists_reaches_iff_exists_accepting_phase
    (edge : V → V → Prop) (source : V) (accepting : V → Prop) :
    let ports := historyPorts edge source
    let root := History.root edge source
    let actions := ports.exhaustiveSchedule (ports.anchor root)
    (∃ target, accepting target ∧ ReflTransGen edge source target) ↔
      ∃ phase, ReflTransGen (PortSystem.PhaseStep actions) 0 phase ∧
        accepting (ports.endpoint
          (ports.portAt actions (ports.anchor root) phase)).endpoint := by
  dsimp only
  exact (accepts_iff_exists_reaches edge source accepting).symm

/-- The compiled history traversal has exact accepting-history semantics and its phase relation
is exactly partitioned into two directed matchings. -/
public theorem history_exact_twoMatching_phasePresentation
    (edge : V → V → Prop) (source : V) (accepting : V → Prop) :
    let ports := historyPorts edge source
    let root := History.root edge source
    let actions := ports.exhaustiveSchedule (ports.anchor root)
    (Accepts edge source accepting ↔
      ∃ history : History edge source,
        accepting history.endpoint ∧
          ReflTransGen History.Extension root history) ∧
    (∀ old new, PortSystem.PhaseStep actions old new ↔
      ∃! color, PhaseLayer actions color old new) ∧
    (∀ color old new, PhaseLayer actions color old new →
      PortSystem.PhaseStep actions old new) ∧
    (∀ color, Relator.BiUnique (PhaseLayer actions color)) ∧
    ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
      (PhaseLayer actions color) := by
  dsimp only
  exact cofunctionalRoot_exact_twoMatching_phasePresentation
    (historyPorts edge source) History.extension_leftUnique
    (History.root_no_predecessor edge source)
    (fun history : History edge source ↦ accepting history.endpoint)

/-- **Finite exact-two-matching presentation of designated-source reachability.**  For every
finite directed graph, source, and accepting predicate, the exhaustive reversible history-port
schedule yields a finite phase relation which accepts exactly the original reachable accepting
vertices and is exactly partitioned into two directed matchings.

This theorem is deliberately nonuniform and semantic.  The history type can grow exponentially
(and factorially in dense graphs) relative to the source vertex type, `exhaustiveSchedule` uses
finite choice, and the construction does not provide an effective representation of phases, a
same-width simulation, or an LBA. -/
public theorem sourceReachability_exact_twoMatching_phasePresentation
    (edge : V → V → Prop) (source : V) (accepting : V → Prop) :
    let ports := historyPorts edge source
    let root := History.root edge source
    let actions := ports.exhaustiveSchedule (ports.anchor root)
    ((∃ target, accepting target ∧ ReflTransGen edge source target) ↔
      ∃ phase, ReflTransGen (PortSystem.PhaseStep actions) 0 phase ∧
        accepting (ports.endpoint
          (ports.portAt actions (ports.anchor root) phase)).endpoint) ∧
    (∀ old new, PortSystem.PhaseStep actions old new ↔
      ∃! color, PhaseLayer actions color old new) ∧
    (∀ color old new, PhaseLayer actions color old new →
      PortSystem.PhaseStep actions old new) ∧
    (∀ color, Relator.BiUnique (PhaseLayer actions color)) ∧
    ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
      (PhaseLayer actions color) := by
  dsimp only
  exact ⟨exists_reaches_iff_exists_accepting_phase edge source accepting,
    phaseStep_iff_existsUnique_phaseLayer _,
    phaseLayer_sub_phaseStep _,
    phaseLayer_biUnique _,
    phaseLayer_pathLengthAtMostOne _⟩

end HistoryPortCompilation

end
