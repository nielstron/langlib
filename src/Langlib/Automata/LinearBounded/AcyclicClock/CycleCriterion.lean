module

public import Langlib.Automata.LinearBounded.Definition

@[expose]
public section

/-!
# A checkpoint criterion for global configuration acyclicity

Clocked machine simulations naturally split their computations at distinguished checkpoint
configurations.  Between checkpoints, a finite protocol rank increases.  Between two checkpoint
visits, a semantic clock rank increases.  This file packages the graph argument which combines
those two facts.

The theorem is deliberately independent of the concrete clock compiler.  Its path dichotomy also
records a checkpoint together with a prefix/suffix decomposition of the original path.  Thus it
applies to malformed configurations and not only to paths starting from canonical inputs.
-/

namespace LBA.AcyclicClock.CycleCriterion

open Relation

variable {α : Type*}
variable (edge : α → α → Prop) (checkpoint : α → Prop)
variable (localRank : α → ℕ)

/-- A nonempty path either visits a checkpoint or strictly raises the local protocol rank.

The checkpoint witness comes with reflexive-transitive prefix and suffix paths, so it is known to
lie on the path being analyzed rather than merely elsewhere in the reachability graph.
-/
public theorem transGen_checkpoint_or_localRank_lt
    (hlocal :
      ∀ {old new}, edge old new →
        ¬ checkpoint old → ¬ checkpoint new →
          localRank old < localRank new)
    {source target : α} (hpath : TransGen edge source target) :
    (∃ middle,
        checkpoint middle ∧
          ReflTransGen edge source middle ∧
          ReflTransGen edge middle target) ∨
      localRank source < localRank target := by
  refine Relation.TransGen.trans_induction_on hpath ?_ ?_
  · intro old new hstep
    by_cases hold : checkpoint old
    · exact Or.inl
        ⟨old, hold, ReflTransGen.refl, ReflTransGen.single hstep⟩
    by_cases hnew : checkpoint new
    · exact Or.inl
        ⟨new, hnew, ReflTransGen.single hstep, ReflTransGen.refl⟩
    exact Or.inr (hlocal hstep hold hnew)
  · intro first middle last hfirst hlast ihfirst ihlast
    rcases ihfirst with
      ⟨visited, hvisited, hprefix, hsuffix⟩ | hfirstRank
    · exact Or.inl
        ⟨visited, hvisited, hprefix,
          hsuffix.trans hlast.to_reflTransGen⟩
    rcases ihlast with
      ⟨visited, hvisited, hprefix, hsuffix⟩ | hlastRank
    · exact Or.inl
        ⟨visited, hvisited,
          hfirst.to_reflTransGen.trans hprefix, hsuffix⟩
    · exact Or.inr (hfirstRank.trans hlastRank)

/-- Every directed cycle can be rotated to a directed cycle based at a checkpoint, provided
non-checkpoint edges strictly raise a local rank. -/
public theorem cycle_rotates_to_checkpoint
    (hlocal :
      ∀ {old new}, edge old new →
        ¬ checkpoint old → ¬ checkpoint new →
          localRank old < localRank new)
    {source : α} (hcycle : TransGen edge source source) :
    ∃ middle, checkpoint middle ∧ TransGen edge middle middle := by
  rcases transGen_checkpoint_or_localRank_lt
      edge checkpoint localRank hlocal hcycle with
    ⟨middle, hmiddle, hprefix, hsuffix⟩ | hrank
  · by_cases heq : middle = source
    · subst middle
      exact ⟨source, hmiddle, hcycle⟩
    · have hprefix' : TransGen edge source middle := by
        rcases (reflTransGen_iff_eq_or_transGen.mp hprefix) with hback | hnonempty
        · exact False.elim (heq hback)
        · exact hnonempty
      have hsuffix' : TransGen edge middle source := by
        rcases (reflTransGen_iff_eq_or_transGen.mp hsuffix) with hforward | hnonempty
        · exact False.elim (heq hforward.symm)
        · exact hnonempty
      exact ⟨middle, hmiddle, hsuffix'.trans hprefix'⟩
  · exact False.elim ((Nat.lt_irrefl (localRank source)) hrank)

/-- **Checkpoint acyclicity criterion.**  If local protocol steps strictly raise one rank away
from checkpoints, and every nonempty checkpoint-to-checkpoint path strictly raises a second rank,
then the whole graph is acyclic.

The conclusion covers every vertex of the graph; no reachability-from-input or well-formedness
assumption is present.
-/
public theorem acyclic_of_checkpointRanks
    (hlocal :
      ∀ {old new}, edge old new →
        ¬ checkpoint old → ¬ checkpoint new →
          localRank old < localRank new)
    (checkpointRank : α → ℕ)
    (hcheckpoint :
      ∀ {old new}, checkpoint old → checkpoint new →
        TransGen edge old new →
          checkpointRank old < checkpointRank new) :
    ∀ cfg : α, ¬ TransGen edge cfg cfg := by
  intro cfg hcycle
  rcases cycle_rotates_to_checkpoint
      edge checkpoint localRank hlocal hcycle with
    ⟨middle, hmiddle, hmiddleCycle⟩
  exact (Nat.lt_irrefl (checkpointRank middle))
    (hcheckpoint hmiddle hmiddle hmiddleCycle)

end LBA.AcyclicClock.CycleCriterion

end
