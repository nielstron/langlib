module

public import Langlib.Grammars.Indexed.Basics.Higman
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Finite.Basic

@[expose]
public section

/-! # Higman's lemma with one distinguished occurrence

This file packages the marked-letter argument used in the shrinking lemma for
indexed languages.  If one occurrence of a word is distinguished, Higman's
lemma supplies a member of a fixed finite basis whose sublist embedding keeps
that occurrence.

The Boolean component of a marked word records the distinguished occurrence.
Using an explicit marked sublist in `RetainsAt` avoids confusing two equal
letters occurring at different positions.

## Reference

* R. H. Gilman, "A shrinking lemma for indexed languages",
  *Theoretical Computer Science* 163 (1996), 277--281.
-/

open List

namespace MarkedHigman

variable {α : Type*}

/-- Erase the Boolean marks from a marked word. -/
def eraseMarks (z : List (α × Bool)) : List α :=
  z.map Prod.fst

/-- Mark exactly the occurrence at position `i`. -/
def markAt (y : List α) (i : Fin y.length) : List (α × Bool) :=
  (y.take i).map (fun a => (a, false)) ++
    (y.get i, true) :: (y.drop (i + 1)).map (fun a => (a, false))

/-- The position corresponding to `i` after mapping a list. -/
def mappedIndex {β : Type*} (f : α → β) (y : List α) (i : Fin y.length) :
    Fin (y.map f).length :=
  ⟨i, by simpa⟩

/-- An index in the left list, viewed after appending a suffix. -/
def leftIndex (y suffix : List α) (i : Fin y.length) : Fin (y ++ suffix).length :=
  ⟨i, by simp; omega⟩

/-- Shift an index past a prepended prefix. -/
def shiftedIndex (pre y : List α) (i : Fin y.length) :
    Fin (pre ++ y).length :=
  ⟨pre.length + i, by simp⟩

/-- A marked word has exactly one marked occurrence.

The existential decomposition is deliberately structural: it neither needs
decidable equality on the alphabet nor identifies equal occurrences. -/
def ExactlyOneMarked (z : List (α × Bool)) : Prop :=
  ∃ (l : List α) (a : α) (r : List α),
    z = l.map (fun b => (b, false)) ++
      (a, true) :: r.map (fun b => (b, false))

/-- `x` is selected from `y` while retaining the exact occurrence at `i`.

The witness `z` is the marked sublist.  Its true Boolean marker can only be the
marker placed at `i`, even when the underlying letter occurs repeatedly. -/
def RetainsAt (x y : List α) (i : Fin y.length) : Prop :=
  ∃ z : List (α × Bool),
    z <+ markAt y i ∧
      eraseMarks z = x ∧
      (y.get i, true) ∈ z

@[simp]
theorem eraseMarks_markAt (y : List α) (i : Fin y.length) :
    eraseMarks (markAt y i) = y := by
  simp only [eraseMarks, markAt, map_append, map_map, map_cons]
  rw [show Prod.fst ∘ (fun a : α => (a, false)) = id by rfl, map_id, map_id]
  rw [List.cons_get_drop_succ]
  exact List.take_append_drop i y

@[simp]
theorem length_markAt (y : List α) (i : Fin y.length) :
    (markAt y i).length = y.length := by
  have h := congrArg List.length (eraseMarks_markAt y i)
  simpa [eraseMarks] using h

theorem exactlyOneMarked_markAt (y : List α) (i : Fin y.length) :
    ExactlyOneMarked (markAt y i) := by
  exact ⟨y.take i, y.get i, y.drop (i + 1), rfl⟩

@[simp]
theorem markAt_map {β : Type*} (f : α → β) (y : List α) (i : Fin y.length) :
    markAt (y.map f) (mappedIndex f y i) =
      (markAt y i).map (fun p => (f p.1, p.2)) := by
  simp [markAt, mappedIndex, List.map_take, List.map_drop, List.map_append,
    List.map_map, Function.comp_def]

@[simp]
theorem markAt_append_right (y suffix : List α) (i : Fin y.length) :
    markAt (y ++ suffix) (leftIndex y suffix i) =
      markAt y i ++ suffix.map (fun a => (a, false)) := by
  have hi : i + 1 ≤ y.length := by omega
  simp only [markAt, leftIndex]
  rw [List.take_append_of_le_length i.isLt.le,
    List.drop_append_of_le_length hi]
  simp [List.map_append, List.append_assoc]

@[simp]
theorem markAt_append_left (pre y : List α) (i : Fin y.length) :
    markAt (pre ++ y) (shiftedIndex pre y i) =
      pre.map (fun a => (a, false)) ++ markAt y i := by
  have htake : (pre.map fun a => (a, false)).length ≤ pre.length + i := by
    simp
  have hdrop : (pre.map fun a => (a, false)).length ≤ pre.length + i + 1 := by
    simp
    omega
  have hsub : pre.length + i + 1 - pre.length = i + 1 := by
    omega
  simp [markAt, shiftedIndex, List.take_append, List.drop_append,
    List.map_append, List.append_assoc, List.take_of_length_le htake,
    List.drop_eq_nil_of_le hdrop, hsub]

theorem ExactlyOneMarked.exists_marked_mem {z : List (α × Bool)}
    (hz : ExactlyOneMarked z) : ∃ a, (a, true) ∈ z := by
  rcases hz with ⟨l, a, r, rfl⟩
  exact ⟨a, by simp⟩

theorem fst_eq_get_of_marked_mem_markAt {y : List α} {i : Fin y.length} {a : α}
    (h : (a, true) ∈ markAt y i) : a = y.get i := by
  rw [markAt] at h
  rcases List.mem_append.mp h with hleft | hrest
  · rcases List.mem_map.mp hleft with ⟨b, -, hba⟩
    have hfalse : false = true := congrArg Prod.snd hba
    simp at hfalse
  · rcases List.mem_cons.mp hrest with hhead | hright
    · exact congrArg Prod.fst hhead
    · rcases List.mem_map.mp hright with ⟨b, -, hba⟩
      have hfalse : false = true := congrArg Prod.snd hba
      simp at hfalse

theorem RetainsAt.sublist {x y : List α} {i : Fin y.length}
    (h : RetainsAt x y i) : x <+ y := by
  rcases h with ⟨z, hz, rfl, -⟩
  have hmapped := hz.map Prod.fst
  change eraseMarks z <+ eraseMarks (markAt y i) at hmapped
  simpa using hmapped

/-- Transport occurrence retention along equality of the ambient words. -/
theorem RetainsAt.cast {x y y' : List α} (hyy : y = y')
    {i : Fin y.length} (h : RetainsAt x y i) :
    RetainsAt x y' (Fin.cast (congrArg List.length hyy) i) := by
  subst y'
  simpa using h

/-- Every word retains each of its own occurrences. -/
theorem retainsAt_refl (y : List α) (i : Fin y.length) :
    RetainsAt y y i := by
  refine ⟨markAt y i, List.Sublist.refl _, eraseMarks_markAt y i, ?_⟩
  simp [markAt]

/-- Append an arbitrary sublist on the right while retaining an occurrence
from the left word. -/
theorem RetainsAt.append_right_sublist {x y xr yr : List α}
    {i : Fin y.length} (h : RetainsAt x y i) (hright : xr <+ yr) :
    RetainsAt (x ++ xr) (y ++ yr) (leftIndex y yr i) := by
  rcases h with ⟨z, hzsub, hzerase, hzmarked⟩
  let unmarkedRight := xr.map (fun a => (a, false))
  refine ⟨z ++ unmarkedRight, ?_, ?_, ?_⟩
  · rw [markAt_append_right]
    exact hzsub.append (hright.map fun a => (a, false))
  · simp only [eraseMarks, List.map_append]
    have hzmap : z.map Prod.fst = x := hzerase
    rw [hzmap]
    simp [eraseMarks, unmarkedRight, List.map_map, Function.comp_def]
  · simpa [leftIndex] using List.mem_append_left unmarkedRight hzmarked

/-- Prepend an arbitrary sublist while retaining an occurrence from the
right word. -/
theorem RetainsAt.append_left_sublist {xl yl x y : List α}
    {i : Fin y.length} (hleft : xl <+ yl) (h : RetainsAt x y i) :
    RetainsAt (xl ++ x) (yl ++ y) (shiftedIndex yl y i) := by
  rcases h with ⟨z, hzsub, hzerase, hzmarked⟩
  let unmarkedLeft := xl.map (fun a => (a, false))
  refine ⟨unmarkedLeft ++ z, ?_, ?_, ?_⟩
  · rw [markAt_append_left]
    exact (hleft.map fun a => (a, false)).append hzsub
  · simp only [eraseMarks, List.map_append]
    have hzmap : z.map Prod.fst = x := hzerase
    rw [hzmap]
    simp [eraseMarks, unmarkedLeft, List.map_map, Function.comp_def]
  · simpa [shiftedIndex] using List.mem_append_right unmarkedLeft hzmarked

/-- Pointwise maps preserve the selected occurrence. -/
theorem RetainsAt.map {β : Type*} (f : α → β)
    {x y : List α} {i : Fin y.length} (h : RetainsAt x y i) :
    RetainsAt (x.map f) (y.map f) (mappedIndex f y i) := by
  rcases h with ⟨z, hzsub, hzerase, hzmarked⟩
  let lift : α × Bool → β × Bool := fun p => (f p.1, p.2)
  refine ⟨z.map lift, ?_, ?_, ?_⟩
  · simpa [lift, markAt_map] using hzsub.map lift
  · rw [← hzerase]
    simp [eraseMarks, lift, List.map_map, Function.comp_def]
  · have hmapped : lift (y.get i, true) ∈ z.map lift :=
      List.mem_map_of_mem hzmarked
    simpa [lift, mappedIndex] using hmapped

/-- Pull a retained occurrence back through a pointwise map.  Injectivity of
the map is unnecessary: the unique Boolean marker identifies the original
occurrence even when several letters have the same image. -/
theorem RetainsAt.exists_preimage {β : Type*} (f : α → β)
    {x : List β} {y : List α} {i : Fin y.length}
    (h : RetainsAt x (y.map f) (mappedIndex f y i)) :
    ∃ x' : List α, RetainsAt x' y i ∧ x'.map f = x := by
  rcases h with ⟨z, hzsub, hzerase, hzmarked⟩
  rw [markAt_map] at hzsub
  obtain ⟨z', hz'sub, hzeq⟩ := List.sublist_map_iff.mp hzsub
  let x' := eraseMarks z'
  have hxmap : x'.map f = x := by
    rw [← hzerase, hzeq]
    simp [x', eraseMarks, List.map_map, Function.comp_def]
  have htarget : (y.get i, true) ∈ z' := by
    have hget : (y.map f).get (mappedIndex f y i) = f (y.get i) := by
      simp [mappedIndex]
    rw [hget, hzeq] at hzmarked
    obtain ⟨p, hpz', hp⟩ := List.mem_map.mp hzmarked
    rcases p with ⟨a, mark⟩
    have hmark : mark = true := congrArg Prod.snd hp
    subst mark
    have htargetMap : (a, true) ∈ markAt y i := hz'sub.subset hpz'
    have ha : a = y.get i := fst_eq_get_of_marked_mem_markAt htargetMap
    simpa [ha] using hpz'
  exact ⟨x', ⟨z', hz'sub, rfl, htarget⟩, hxmap⟩

/-- The marked lift of a language: every word is supplied with exactly one
distinguished occurrence. -/
private def markedLift (Y : Set (List α)) : Set (List (α × Bool)) :=
  {z | ExactlyOneMarked z ∧ eraseMarks z ∈ Y}

/-- One-position marked form of Higman's finite-basis lemma.

For every language over a finite alphabet there is a finite subset `X` such
that every word outside `X`, with any one occurrence distinguished, has a
proper sublist in `X` whose sublist embedding retains that occurrence. -/
theorem exists_finite_retaining_basis (α : Type*) [Fintype α]
    (Y : Set (List α)) :
    ∃ X : Set (List α),
      X.Finite ∧
        X ⊆ Y ∧
        ∀ y ∈ Y, y ∉ X → ∀ i : Fin y.length,
          ∃ x ∈ X, x.length < y.length ∧ RetainsAt x y i := by
  let M : Set (List (α × Bool)) := markedLift Y
  let B : Set (List (α × Bool)) := minimalElements (α × Bool) M
  let X : Set (List α) := eraseMarks '' B
  have hBfinite : B.Finite := by
    exact higman_finite_antichain (α × Bool) M
  refine ⟨X, Set.Finite.image eraseMarks hBfinite, ?_, ?_⟩
  · rintro x ⟨z, hzB, rfl⟩
    exact hzB.1.2
  · intro y hy hyX i
    have hmarkM : markAt y i ∈ M := by
      exact ⟨exactlyOneMarked_markAt y i, by simpa using hy⟩
    obtain ⟨z, hzB, hzsub⟩ :=
      exists_minimal_sublist (α × Bool) M (markAt y i) hmarkM
    let x := eraseMarks z
    have hxX : x ∈ X := ⟨z, hzB, rfl⟩
    have hzmark : (y.get i, true) ∈ z := by
      obtain ⟨a, ha⟩ := hzB.1.1.exists_marked_mem
      have haTarget : (a, true) ∈ markAt y i := hzsub.subset ha
      simpa [fst_eq_get_of_marked_mem_markAt haTarget] using ha
    have hxRetains : RetainsAt x y i := ⟨z, hzsub, rfl, hzmark⟩
    have hxsub : x <+ y := hxRetains.sublist
    have hxlt : x.length < y.length := by
      by_contra hnot
      have hle : x.length ≤ y.length := hxsub.length_le
      have hlen : x.length = y.length :=
        Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
      have hxy : x = y := hxsub.eq_of_length hlen
      exact hyX (hxy ▸ hxX)
    exact ⟨x, hxX, hxlt, hxRetains⟩

end MarkedHigman
