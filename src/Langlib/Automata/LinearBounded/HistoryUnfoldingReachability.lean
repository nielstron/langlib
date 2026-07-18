module

public import Langlib.Automata.LinearBounded.HistoryUnfolding

@[expose]
public section

/-!
# Reachability through finite rooted histories

Every finite directed walk can be shortened to a simple path.  Consequently the finite type of
duplicate-free rooted histories preserves reachability even when the original relation contains
cycles.  History extension projects to one source edge, while every valid history is reachable
from the empty root by successively revealing its stored vertices.
-/

namespace HistoryUnfolding

open Relation

universe u

variable {V : Type u} {edge : V → V → Prop} {source target : V}

namespace History

/-- Every valid history can be obtained from the empty history by one-vertex extensions. -/
public theorem root_reaches (history : History edge source) :
    ReflTransGen (Extension (edge := edge) (source := source))
      (root edge source) history := by
  let motive : List V → Prop := fun visits ↦
    ∀ (hchain : List.IsChain edge (source :: visits))
      (hnodup : (source :: visits).Nodup),
      ReflTransGen (Extension (edge := edge) (source := source))
        (root edge source) ({ visits := visits, isChain := hchain, nodup := hnodup } :
          History edge source)
  suffices h : motive history.visits by
    simpa only using h history.isChain history.nodup
  apply List.reverseRec (motive := motive)
  · intro hchain hnodup
    have heq :
        ({ visits := [], isChain := hchain, nodup := hnodup } : History edge source) =
          root edge source := by
      apply ext
      rfl
    rw [heq]
  · intro visits next ih hchain hnodup
    have hprefixChain : List.IsChain edge (source :: visits) := by
      exact hchain.prefix ⟨[next], by simp⟩
    have hprefixNodup : (source :: visits).Nodup := by
      rw [show source :: (visits ++ [next]) = (source :: visits) ++ [next] by simp]
        at hnodup
      exact List.Nodup.of_append_left hnodup
    let prior : History edge source :=
      { visits := visits, isChain := hprefixChain, nodup := hprefixNodup }
    let child : History edge source :=
      { visits := visits ++ [next], isChain := hchain, nodup := hnodup }
    have hreach : ReflTransGen (Extension (edge := edge) (source := source))
        (root edge source) prior := ih hprefixChain hprefixNodup
    have hextension : Extension prior child := ⟨next, rfl⟩
    exact hreach.tail hextension

/-- History-extension reachability projects to reachability of the current base vertices. -/
public theorem endpoint_reaches_of_reaches {first last : History edge source}
    (hreach : ReflTransGen (Extension (edge := edge) (source := source)) first last) :
    ReflTransGen edge first.endpoint last.endpoint := by
  exact hreach.lift endpoint fun _ _ hextension ↦
    edge_endpoint_of_extension hextension

/-- In particular, the endpoint of every history is reachable from the distinguished source. -/
public theorem source_reaches_endpoint (history : History edge source) :
    ReflTransGen edge source history.endpoint := by
  simpa using endpoint_reaches_of_reaches (root_reaches history)

private theorem exists_history_endpoint_of_mem
    (history : History edge source) (hmem : target ∈ source :: history.visits) :
    ∃ initial : History edge source, initial.endpoint = target := by
  obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp hmem
  cases before with
  | nil =>
      have hsource : source = target := by
        have hheads := congrArg List.head? hsplit
        simpa using hheads
      subst target
      exact ⟨root edge source, endpoint_root edge source⟩
  | cons first before =>
      have hparts : source = first ∧
          history.visits = before ++ target :: after := by
        simpa only [List.cons_append, List.cons.injEq] using hsplit
      have hfirst : first = source := hparts.1.symm
      subst first
      have hpref : source :: (before ++ [target]) <+: source :: history.visits := by
        refine ⟨after, ?_⟩
        simp only [hparts.2, List.cons_append, List.append_assoc,
          List.nil_append]
      have hchain : List.IsChain edge (source :: (before ++ [target])) :=
        history.isChain.prefix hpref
      have hnodup : (source :: (before ++ [target])).Nodup :=
        List.Nodup.sublist hpref.sublist history.nodup
      let initial : History edge source :=
        { visits := before ++ [target], isChain := hchain, nodup := hnodup }
      refine ⟨initial, ?_⟩
      simp [initial, endpoint_eq_getLast]

end History

/-! ## Exact preservation of arbitrary finite reachability -/

/-- Every finite walk has a duplicate-free history with the same endpoints.  This is the
directed loop-erasure theorem; it does not require the relation itself to be acyclic. -/
public theorem exists_history_endpoint_of_reaches
    (hreach : ReflTransGen edge source target) :
    ∃ history : History edge source, history.endpoint = target := by
  induction hreach with
  | refl =>
      exact ⟨History.root edge source, History.endpoint_root edge source⟩
  | @tail middle newTarget hreach hstep ih =>
      obtain ⟨history, hendpoint⟩ := ih
      rw [← hendpoint] at hstep
      by_cases hmem : newTarget ∈ source :: history.visits
      · exact History.exists_history_endpoint_of_mem history hmem
      · exact ⟨history.extend newTarget hstep hmem,
          History.endpoint_extend history newTarget hstep hmem⟩

/-- Base reachability is equivalent to reaching a finite history whose endpoint is the desired
base vertex.  No acyclicity premise is needed because repeated portions of a walk are erased. -/
public theorem reaches_iff_exists_history :
    ReflTransGen edge source target ↔
      ∃ history : History edge source,
        ReflTransGen (History.Extension (edge := edge) (source := source))
          (History.root edge source) history ∧
        history.endpoint = target := by
  constructor
  · intro hreach
    obtain ⟨history, hendpoint⟩ := exists_history_endpoint_of_reaches hreach
    exact ⟨history, history.root_reaches, hendpoint⟩
  · rintro ⟨history, hreach, hendpoint⟩
    have hprojected := History.endpoint_reaches_of_reaches hreach
    rw [History.endpoint_root, hendpoint] at hprojected
    exact hprojected

/-- Existential acceptance by a predicate on base vertices is preserved exactly by the rooted
history unfolding. -/
public theorem exists_reachable_final_iff_exists_history (final : V → Prop) :
    (∃ target, ReflTransGen edge source target ∧ final target) ↔
      ∃ history : History edge source,
        ReflTransGen (History.Extension (edge := edge) (source := source))
          (History.root edge source) history ∧
        final history.endpoint := by
  constructor
  · rintro ⟨target, hreach, hfinal⟩
    obtain ⟨history, hhistory, hendpoint⟩ :=
      reaches_iff_exists_history.mp hreach
    exact ⟨history, hhistory, hendpoint.symm ▸ hfinal⟩
  · rintro ⟨history, hhistory, hfinal⟩
    exact ⟨history.endpoint,
      reaches_iff_exists_history.mpr ⟨history, hhistory, rfl⟩, hfinal⟩

end HistoryUnfolding

end
