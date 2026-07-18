module

public import Langlib.Automata.LinearBounded.Unambiguous
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.List

@[expose]
public section

/-!
# Finite unfolding by rooted histories

For a finite acyclic directed relation, retaining the complete path from a fixed source turns
every merge into distinct vertices.  The resulting extension relation is therefore
cofunctional: a nonempty history has exactly one immediate prefix.

`History` is defined independently of acyclicity as a simple concrete path.  It is finite over
every finite vertex type because it injects into the finite type of duplicate-free lists.
Acyclicity enters only in `ofPath`, which proves that no ordinary concrete path is lost.
-/

namespace HistoryUnfolding

open Relation

universe u

variable {V : Type u} {edge : V → V → Prop} {source : V}

/-- A complete duplicate-free path beginning at `source`.

The initial source is stored implicitly; `visits` lists every vertex reached after it, in
chronological order. -/
structure History (edge : V → V → Prop) (source : V) where
  visits : List V
  isChain : List.IsChain edge (source :: visits)
  nodup : (source :: visits).Nodup

namespace History

/-- Forget a history's duplicate-freeness witness. -/
public def toPath (history : History edge source) : RelationalRun.PathData edge source where
  visits := history.visits
  isChain := history.isChain

/-- The current vertex of a history. -/
public def endpoint (history : History edge source) : V :=
  history.toPath.endpoint

@[simp]
public theorem endpoint_eq_getLast (history : History edge source) :
    history.endpoint = (source :: history.visits).getLast (by simp) := rfl

/-- A simple history stores at most one occurrence of every base vertex. -/
public theorem length_le_card [Fintype V] (history : History edge source) :
    (source :: history.visits).length ≤ Fintype.card V :=
  history.nodup.length_le_card

/-- Equivalently, the number of non-root visits plus the root is bounded by the size of the
base vertex type. -/
public theorem visits_length_add_one_le_card [Fintype V] (history : History edge source) :
    history.visits.length + 1 ≤ Fintype.card V := by
  simpa [Nat.add_comm] using history.length_le_card

@[ext]
public theorem ext (left right : History edge source)
    (hvisits : left.visits = right.visits) : left = right := by
  cases left
  cases right
  simp_all

/-- The empty history, located at the distinguished source. -/
public def root (edge : V → V → Prop) (source : V) : History edge source where
  visits := []
  isChain := List.isChain_singleton source
  nodup := by simp

@[simp]
public theorem root_visits (edge : V → V → Prop) (source : V) :
    (root edge source).visits = [] := rfl

@[simp]
public theorem endpoint_root (edge : V → V → Prop) (source : V) :
    (root edge source).endpoint = source := rfl

/-- Extend a history by one fresh outgoing vertex. -/
public def extend (history : History edge source) (next : V)
    (hstep : edge history.endpoint next)
    (hfresh : next ∉ source :: history.visits) : History edge source where
  visits := history.visits ++ [next]
  isChain := by
    rw [← List.cons_append, List.isChain_append]
    refine ⟨history.isChain, List.isChain_singleton next, ?_⟩
    intro previous hprevious final hfinal
    rw [List.getLast?_eq_some_getLast (by simp)] at hprevious
    simp only [Option.mem_some_iff] at hprevious
    simp only [List.head?_singleton, Option.mem_some_iff] at hfinal
    subst previous
    subst final
    simpa [endpoint, toPath, RelationalRun.PathData.endpoint] using hstep
  nodup := by
    simpa only [List.cons_append, List.concat_eq_append] using
      List.Nodup.concat hfresh history.nodup

@[simp]
public theorem extend_visits (history : History edge source) (next : V)
    (hstep : edge history.endpoint next) (hfresh : next ∉ source :: history.visits) :
    (history.extend next hstep hfresh).visits = history.visits ++ [next] := rfl

@[simp]
public theorem endpoint_extend (history : History edge source) (next : V)
    (hstep : edge history.endpoint next) (hfresh : next ∉ source :: history.visits) :
    (history.extend next hstep hfresh).endpoint = next := by
  simp [endpoint, toPath, RelationalRun.PathData.endpoint]

/-- One-edge extension of complete rooted histories.

The definition only compares the stored lists.  Since both endpoints are already valid
histories, the new final adjacency is necessarily an `edge`; see
`edge_endpoint_of_extension`. -/
public def Extension (parent child : History edge source) : Prop :=
  ∃ next, child.visits = parent.visits ++ [next]

public theorem extension_iff_exists_visits {parent child : History edge source} :
    Extension parent child ↔
      ∃ next, child.visits = parent.visits ++ [next] := Iff.rfl

/-- Every explicit fresh one-edge extension is an `Extension`. -/
public theorem extension_extend (history : History edge source) (next : V)
    (hstep : edge history.endpoint next) (hfresh : next ∉ source :: history.visits) :
    Extension history (history.extend next hstep hfresh) := by
  exact ⟨next, rfl⟩

/-- The endpoint of a child history is the vertex appended by an extension. -/
public theorem endpoint_eq_of_extension {parent child : History edge source} {next : V}
    (hextension : child.visits = parent.visits ++ [next]) :
    child.endpoint = next := by
  simp [endpoint_eq_getLast, hextension]

/-- Projecting a one-edge history extension to its two endpoints gives an edge of the source
relation. -/
public theorem edge_endpoint_of_extension {parent child : History edge source}
    (hextension : Extension parent child) :
    edge parent.endpoint child.endpoint := by
  obtain ⟨next, hvisits⟩ := hextension
  have hchain := child.isChain
  rw [hvisits, ← List.cons_append, List.isChain_append] at hchain
  have hlast : edge parent.endpoint next := by
    apply hchain.2.2
    · rw [List.getLast?_eq_some_getLast (by simp)]
      simp [endpoint, toPath, RelationalRun.PathData.endpoint]
    · simp
  rwa [endpoint_eq_of_extension hvisits]

/-- Deleting the last vertex is the unique predecessor operation on nonempty histories. -/
public theorem extension_leftUnique :
    Relator.LeftUnique (Extension (edge := edge) (source := source)) := by
  intro left right child hleft hright
  obtain ⟨leftLast, hleftVisits⟩ := hleft
  obtain ⟨rightLast, hrightVisits⟩ := hright
  apply ext
  have happend : left.visits ++ [leftLast] = right.visits ++ [rightLast] :=
    hleftVisits.symm.trans hrightVisits
  have hdrop := congrArg List.dropLast happend
  simpa using hdrop

/-- The empty history has no predecessor in the extension graph. -/
public theorem root_no_predecessor (edge : V → V → Prop) (source : V) :
    ∀ parent, ¬ Extension parent (root edge source) := by
  intro parent hextension
  obtain ⟨next, hnext⟩ := hextension
  have hnonempty : parent.visits ++ [next] ≠ [] := by simp
  exact hnonempty hnext.symm

/-- Equivalently, no extension enters the root history. -/
public theorem not_extension_to_root (edge : V → V → Prop) (source : V)
    (parent : History edge source) :
    ¬ Extension parent (root edge source) :=
  root_no_predecessor edge source parent

/-- A chain in an acyclic relation cannot visit the same vertex twice.  This generic fact does
not require the vertex type to be finite. -/
public theorem nodup_of_isChain_of_acyclic
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex)
    {vertices : List V} (hchain : List.IsChain edge vertices) :
    vertices.Nodup := by
  induction vertices with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have htransChain : List.IsChain (TransGen edge) (head :: tail) :=
          hchain.imp fun _ _ hstep ↦ TransGen.single hstep
        exact hacyclic head (htransChain.rel_cons hmem)
      · exact ih hchain.tail

/-- Every concrete path in an acyclic relation is represented by a finite rooted history. -/
public def ofPath
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex)
    (path : RelationalRun.PathData edge source) : History edge source where
  visits := path.visits
  isChain := path.isChain
  nodup := nodup_of_isChain_of_acyclic hacyclic path.isChain

@[simp]
public theorem ofPath_visits
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex)
    (path : RelationalRun.PathData edge source) :
    (ofPath hacyclic path).visits = path.visits := rfl

@[simp]
public theorem endpoint_ofPath
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex)
    (path : RelationalRun.PathData edge source) :
    (ofPath hacyclic path).endpoint = path.endpoint := rfl

private def toNodupList (history : History edge source) : {list : List V // list.Nodup} :=
  ⟨source :: history.visits, history.nodup⟩

private theorem toNodupList_injective :
    Function.Injective (toNodupList : History edge source → {list : List V // list.Nodup}) := by
  intro left right heq
  apply ext
  have hlist := congrArg Subtype.val heq
  exact List.cons.inj hlist |>.2

instance [Fintype V] : Finite (History edge source) :=
  Finite.of_injective toNodupList toNodupList_injective

/-- Rooted histories form a finite type whenever the base vertex type is finite. -/
public noncomputable instance [Fintype V] : Fintype (History edge source) :=
  Fintype.ofFinite _

/-- History equality is decidable as soon as base-vertex equality is decidable. -/
public instance [DecidableEq V] : DecidableEq (History edge source) := fun left right ↦
  decidable_of_iff (left.visits = right.visits) ⟨ext left right, congrArg visits⟩

/-- One-edge history extension is decidable without deciding the base relation: validity of
each finite history already contains all base-edge proofs. -/
public noncomputable instance : DecidableRel (Extension (edge := edge) (source := source)) :=
  Classical.decRel _

end History

end HistoryUnfolding

end
