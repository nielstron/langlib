module

public import Langlib.Automata.LinearBounded.FiniteReachabilityCounting
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic

@[expose]
public section

/-!
# Savitch's midpoint recurrence as reachability semantics

This file isolates the propositional recurrence underlying Savitch's reachability
algorithm.  At depth `d`, `SavitchReach edge d source target` says that a path of at
most `2 ^ d` genuine `edge` steps connects `source` to `target`.  Its definition uses
an existentially chosen midpoint at every positive depth.

The results here are semantic.  In particular, an existential proposition does not
by itself provide an executable midpoint search, a space bound for such a search, or
a compiler from a nondeterministic machine to a deterministic one.
-/

namespace SavitchReachability

open Relation
open FiniteReachabilityCounting

variable {V : Type*} {edge : V → V → Prop}

namespace PaddedPath

/-- Concatenate two padded paths. -/
public theorem append {source middle target : V} {left right : ℕ}
    (hleft : PaddedPath edge source left middle)
    (hright : PaddedPath edge middle right target) :
    PaddedPath edge source (left + right) target := by
  induction hright with
  | zero => simpa using hleft
  | @succ right old new hpath hstep ih =>
      simpa [Nat.add_assoc] using
        (PaddedPath.succ ih hstep :
          PaddedPath edge source ((left + right) + 1) new)

/-- Split a padded path after an exact number of verifier steps. -/
public theorem split {source target : V} (left right : ℕ)
    (hpath : PaddedPath edge source (left + right) target) :
    ∃ middle, PaddedPath edge source left middle ∧
      PaddedPath edge middle right target := by
  induction right generalizing target with
  | zero =>
      exact ⟨target, by simpa using hpath, PaddedPath.zero⟩
  | succ right ih =>
      have hpath' : PaddedPath edge source ((left + right) + 1) target := by
        simpa [Nat.add_assoc] using hpath
      cases hpath' with
      | @succ _ old _ hprefix hstep =>
          obtain ⟨middle, hleft, hright⟩ := ih hprefix
          exact ⟨middle, hleft, PaddedPath.succ hright hstep⟩

/-- Extra verifier fuel can always be filled by stuttering at the endpoint. -/
public theorem mono {source target : V} {small large : ℕ}
    (hpath : PaddedPath edge source small target) (hsmall : small ≤ large) :
    PaddedPath edge source large target := by
  induction large, hsmall using Nat.le_induction with
  | base => exact hpath
  | succ large _ ih => exact PaddedPath.succ ih (Or.inl rfl)

/-- One padded step is either a stutter or one genuine edge. -/
public theorem one_iff {source target : V} :
    PaddedPath edge source 1 target ↔ source = target ∨ edge source target := by
  constructor
  · intro hpath
    cases hpath with
    | @succ _ old _ hprefix hstep =>
        cases hprefix
        exact hstep
  · intro hstep
    exact PaddedPath.succ PaddedPath.zero hstep

end PaddedPath

/-- The depth-recursive midpoint predicate underlying Savitch's theorem.

Depth zero permits one genuine edge (or a stutter).  Every successor depth joins
two witnesses of the preceding depth through an existentially chosen midpoint. -/
public def SavitchReach (edge : V → V → Prop) : ℕ → V → V → Prop
  | 0, source, target => source = target ∨ edge source target
  | depth + 1, source, target =>
      ∃ middle, SavitchReach edge depth source middle ∧
        SavitchReach edge depth middle target

@[simp]
public theorem savitchReach_zero {source target : V} :
    SavitchReach edge 0 source target ↔ source = target ∨ edge source target :=
  Iff.rfl

@[simp]
public theorem savitchReach_succ {depth : ℕ} {source target : V} :
    SavitchReach edge (depth + 1) source target ↔
      ∃ middle, SavitchReach edge depth source middle ∧
        SavitchReach edge depth middle target :=
  Iff.rfl

/-- The midpoint recurrence at depth `d` is exactly a padded path with `2 ^ d`
verifier steps, hence a path with at most that many genuine edges. -/
public theorem savitchReach_iff_paddedPath {depth : ℕ} {source target : V} :
    SavitchReach edge depth source target ↔
      PaddedPath edge source (2 ^ depth) target := by
  induction depth generalizing source target with
  | zero => simpa using (PaddedPath.one_iff (edge := edge) (source := source) (target := target)).symm
  | succ depth ih =>
      rw [savitchReach_succ]
      constructor
      · rintro ⟨middle, hleft, hright⟩
        have hleft' := (ih (source := source) (target := middle)).1 hleft
        have hright' := (ih (source := middle) (target := target)).1 hright
        simpa [Nat.pow_succ, Nat.mul_two] using PaddedPath.append hleft' hright'
      · intro hpath
        have hpath' :
            PaddedPath edge source (2 ^ depth + 2 ^ depth) target := by
          simpa [Nat.pow_succ, Nat.mul_two] using hpath
        obtain ⟨middle, hleft, hright⟩ :=
          PaddedPath.split (edge := edge) (2 ^ depth) (2 ^ depth) hpath'
        exact ⟨middle,
          (ih (source := source) (target := middle)).2 hleft,
          (ih (source := middle) (target := target)).2 hright⟩

/-- On a finite graph, depth `clog 2 |V|` in the midpoint recurrence captures all
reflexive-transitive reachability.  No lower bound on `|V|` is needed: the displayed
`source` and `target` already make the relevant type inhabited. -/
public theorem reaches_iff_savitchReach_clog [Fintype V]
    (edge : V → V → Prop) (source target : V) :
    ReflTransGen edge source target ↔
      SavitchReach edge (Nat.clog 2 (Fintype.card V)) source target := by
  classical
  letI : DecidableRel edge := Classical.decRel edge
  constructor
  · intro hreach
    have hmem :
        target ∈ reached edge source (Fintype.card V) :=
      (mem_reached_card_iff (edge := edge) (source := source)).2 hreach
    have hcardPath :
        PaddedPath edge source (Fintype.card V) target :=
      (mem_reached_iff_paddedPath (edge := edge) (source := source)).1 hmem
    have hcard :
        Fintype.card V ≤ 2 ^ Nat.clog 2 (Fintype.card V) :=
      Nat.le_pow_clog (by omega) _
    exact savitchReach_iff_paddedPath.2 (PaddedPath.mono hcardPath hcard)
  · intro hsavitch
    have hpath :
        PaddedPath edge source (2 ^ Nat.clog 2 (Fintype.card V)) target :=
      savitchReach_iff_paddedPath.1 hsavitch
    have hmem :
        target ∈ reached edge source (2 ^ Nat.clog 2 (Fintype.card V)) :=
      (mem_reached_iff_paddedPath (edge := edge) (source := source)).2 hpath
    exact reached_sound edge source hmem

/-- Row-specialized form of finite saturation.  It applies to every finite cell type and every
width; no lower bound on the alphabet or width is assumed. -/
public theorem row_reaches_iff_savitchReach_clog
    {Cell : Type*} [Fintype Cell] {width : ℕ}
    (edge : (Fin width → Cell) → (Fin width → Cell) → Prop)
    (source target : Fin width → Cell) :
    ReflTransGen edge source target ↔
      SavitchReach edge
        (Nat.clog 2 (Fintype.card Cell ^ width)) source target := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    reaches_iff_savitchReach_clog edge source target

/-- There are exactly `2 ^ width` Boolean rows, so their saturated Savitch recursion has depth
exactly `width`, including width zero. -/
public theorem clog_card_bitRows (width : ℕ) :
    Nat.clog 2 (Fintype.card (Fin width → Bool)) = width := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact Nat.clog_pow 2 width (by omega)

/-- On the complete state type of width-`width` bit rows, depth `width` already captures all
directed reachability.  This is the exact `log N` recursion-depth specialization. -/
public theorem bitRows_reaches_iff_savitchReach
    {width : ℕ}
    (edge : (Fin width → Bool) → (Fin width → Bool) → Prop)
    (source target : Fin width → Bool) :
    ReflTransGen edge source target ↔
      SavitchReach edge width source target := by
  simpa only [clog_card_bitRows] using
    reaches_iff_savitchReach_clog edge source target

end SavitchReachability
