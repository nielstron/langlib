module

public import Langlib.Automata.LinearBounded.HistoryUnfoldingReachability
public import Langlib.Automata.LinearBounded.SimpleTraceCrossingBound

@[expose]
public section

/-!
# The finite-configuration pumping barrier

Repeating a complete configuration permits deletion of the intervening closed walk.  This is a
sound run-level ``pumping down'' principle, but it does not distinguish deterministic from
nondeterministic finite-configuration reachability:

* in a right-unique relation, every path ending in a terminal final vertex is already simple;
* for an arbitrary relation, directed loop erasure supplies a simple path with the same endpoints;
* in both cases an accepting witness visits at most `Fintype.card V` vertices.

The LBA corollary specializes the second item to the full bounded configuration type.  It is not
a word-pumping lemma: no input segment is repeated or deleted, and the accepting witness may still
have length exponential in the input length because the configuration type has exponential size.
-/

namespace FiniteConfigurationPumpingBarrier

open Relation

universe u

variable {V : Type u} {edge : V → V → Prop} {final : V → Prop}
variable {source target : V}

/-- Existential acceptance in a directed graph. -/
@[expose]
public def Accepts (edge : V → V → Prop) (final : V → Prop) (source : V) : Prop :=
  ∃ target, ReflTransGen edge source target ∧ final target

/-- A right-unique orbit cannot repeat a vertex before reaching a terminal final vertex.

The comparison is made against the duplicate-free history obtained by directed loop erasure.
Right uniqueness and terminality make the two accepting paths equal, so the original path was
already simple. -/
public theorem functional_acceptingPath_nodup
    (functional : Relator.RightUnique edge)
    (finalsTerminal : RelationalRun.FinalsTerminal edge final)
    (path : RelationalRun.PathData edge source)
    (pathFinal : final path.endpoint) :
    (source :: path.visits).Nodup := by
  obtain ⟨history, hendpoint⟩ :=
    HistoryUnfolding.exists_history_endpoint_of_reaches path.reaches
  let original : RelationalRun.AcceptingRun edge final source :=
    ⟨path, pathFinal⟩
  let shortened : RelationalRun.AcceptingRun edge final source :=
    ⟨history.toPath, by
      change final history.endpoint
      rw [hendpoint]
      exact pathFinal⟩
  have heq : original = shortened :=
    (RelationalRun.acceptingRun_subsingleton functional finalsTerminal source).elim _ _
  have hvisits : path.visits = history.visits :=
    congrArg (fun run : RelationalRun.AcceptingRun edge final source ↦ run.path.visits) heq
  rw [hvisits]
  exact history.nodup

/-- Contrapositive barrier form: once a functional finite path repeats a complete vertex, that
path cannot later end at a terminal final vertex. -/
public theorem functional_repetition_precludes_terminal_final
    (functional : Relator.RightUnique edge)
    (finalsTerminal : RelationalRun.FinalsTerminal edge final)
    (path : RelationalRun.PathData edge source)
    (repeats : ¬ (source :: path.visits).Nodup) :
    ¬ final path.endpoint := by
  intro pathFinal
  exact repeats
    (functional_acceptingPath_nodup functional finalsTerminal path pathFinal)

/-- Consequently, a functional accepting orbit ending at a terminal final vertex visits at most
the full vertex set. -/
public theorem functional_acceptingPath_length_add_one_le_card
    [Fintype V]
    (functional : Relator.RightUnique edge)
    (finalsTerminal : RelationalRun.FinalsTerminal edge final)
    (path : RelationalRun.PathData edge source)
    (pathFinal : final path.endpoint) :
    path.visits.length + 1 ≤ Fintype.card V := by
  have hnodup :=
    functional_acceptingPath_nodup functional finalsTerminal path pathFinal
  simpa using hnodup.length_le_card

/-- Functional acceptance has a simple bounded orbit witness.  Unlike the arbitrary-relation
result below, no loop deletion is needed for the selected accepting path. -/
public theorem functional_accepts_iff_exists_bounded_simple_orbit
    [Fintype V]
    (functional : Relator.RightUnique edge)
    (finalsTerminal : RelationalRun.FinalsTerminal edge final) :
    Accepts edge final source ↔
      ∃ path : RelationalRun.PathData edge source,
        final path.endpoint ∧
          (source :: path.visits).Nodup ∧
          path.visits.length + 1 ≤ Fintype.card V := by
  constructor
  · rintro ⟨target, hreach, hfinal⟩
    obtain ⟨⟨path, hendpoint⟩⟩ :=
      (RelationalRun.nonempty_pathTo_iff_reaches (edge := edge)).2 hreach
    have hpathFinal : final path.endpoint := by
      simpa [hendpoint] using hfinal
    exact ⟨path, hpathFinal,
      functional_acceptingPath_nodup functional finalsTerminal path hpathFinal,
      functional_acceptingPath_length_add_one_le_card
        functional finalsTerminal path hpathFinal⟩
  · rintro ⟨path, hfinal, _hsimple, _hbound⟩
    exact ⟨path.endpoint, path.reaches, hfinal⟩

/-- Every path in an arbitrary finite relation has a same-endpoint duplicate-free cut whose
visited-vertex count is at most the cardinality of the whole graph. -/
public theorem arbitrary_path_has_bounded_simple_cut
    [Fintype V]
    (path : RelationalRun.PathData edge source) :
    ∃ shortened : RelationalRun.PathData edge source,
      shortened.endpoint = path.endpoint ∧
        (source :: shortened.visits).Nodup ∧
        shortened.visits.length + 1 ≤ Fintype.card V := by
  obtain ⟨history, hendpoint⟩ :=
    HistoryUnfolding.exists_history_endpoint_of_reaches path.reaches
  exact ⟨history.toPath, hendpoint, history.nodup,
    history.visits_length_add_one_le_card⟩

/-- Arbitrary finite-graph acceptance has a duplicate-free path witness with exactly the same
full-vertex cardinality bound.  This is directed loop erasure and uses neither functionality nor
acyclicity. -/
public theorem arbitrary_accepts_iff_exists_bounded_simple_path
    [Fintype V] :
    Accepts edge final source ↔
      ∃ history : HistoryUnfolding.History edge source,
        final history.endpoint ∧
          history.visits.length + 1 ≤ Fintype.card V := by
  constructor
  · rintro ⟨target, hreach, hfinal⟩
    obtain ⟨history, hendpoint⟩ :=
      HistoryUnfolding.exists_history_endpoint_of_reaches hreach
    refine ⟨history, ?_, history.visits_length_add_one_le_card⟩
    rw [hendpoint]
    exact hfinal
  · rintro ⟨history, hfinal, _hbound⟩
    exact ⟨history.endpoint, history.source_reaches_endpoint, hfinal⟩

/-- The repeated-full-configuration cutoff is already valid for every relation.  Functionality
can show that a terminal accepting orbit needs no shortening, but it cannot improve the generic
`Fintype.card V` existence bound merely by this pigeonhole argument. -/
public theorem fullConfiguration_cutoff_without_functionality
    [Fintype V]
    (haccept : Accepts edge final source) :
    ∃ history : HistoryUnfolding.History edge source,
      final history.endpoint ∧
        history.visits.length + 1 ≤ Fintype.card V :=
  arbitrary_accepts_iff_exists_bounded_simple_path.mp haccept

end FiniteConfigurationPumpingBarrier

namespace LBA

universe u v

variable {Γ : Type u} {Λ : Type v} {n : ℕ}
variable {M : LBA.Machine Γ Λ}
variable {source : DLBA.Cfg Γ Λ n}

/-- Every nondeterministic LBA acceptance has a same-endpoint simple witness bounded by the full
configuration count.  Thus deleting a repeated *complete* configuration is not a deterministic
specific pumping principle. -/
public theorem accepts_has_fullConfiguration_cutoff
    [Fintype Γ] [Fintype Λ]
    (haccept : LBA.Accepts M source) :
    ∃ final : DLBA.Cfg Γ Λ n,
      ∃ trace : LBA.StepTrace M source final,
        M.accept final.state = true ∧
          trace.Simple ∧
          trace.length + 1 ≤ Fintype.card (DLBA.Cfg Γ Λ n) :=
  StepTrace.exists_simple_acceptingTrace_of_accepts haccept

/-- The same cutoff, with the finite configuration cardinality expanded. -/
public theorem accepts_has_expanded_fullConfiguration_cutoff
    [Fintype Γ] [Fintype Λ]
    (haccept : LBA.Accepts M source) :
    ∃ final : DLBA.Cfg Γ Λ n,
      ∃ trace : LBA.StepTrace M source final,
        M.accept final.state = true ∧
          trace.Simple ∧
          trace.length + 1 ≤
            Fintype.card Λ * Fintype.card Γ ^ (n + 1) * (n + 1) :=
  StepTrace.exists_simple_acceptingTrace_card_mul_pow_mul_of_accepts haccept

end LBA

end
