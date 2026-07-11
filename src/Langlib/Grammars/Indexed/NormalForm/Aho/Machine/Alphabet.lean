module

public import Langlib.Grammars.Indexed.NormalForm.AhoCompression
public import Mathlib.Data.Fintype.Prod

@[expose]
public section

/-!
# Aho machine alphabet

Finite marks, work symbols, and their basic structural properties.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## The finite marked work alphabet -/

/-- Aho's four marks on a compressed index.

`firstPending`/`firstUsed` are the paper's marks 0/1, and
`laterPending`/`laterUsed` are marks 2/3.  "Used" means that a productive terminal or binary
event has occurred since the represented index was consumed, so the index may be erased. -/
public inductive IndexMark where
  | firstPending
  | firstUsed
  | laterPending
  | laterUsed
deriving DecidableEq, Fintype

/-- Mark the productive use of an index (Aho's operation `alpha ↦ alpha⁺`). -/
public def IndexMark.markUsed : IndexMark → IndexMark
  | .firstPending => .firstUsed
  | .firstUsed => .firstUsed
  | .laterPending => .laterUsed
  | .laterUsed => .laterUsed

/-- Marks 1 and 3 are precisely the erasable marks. -/
public def IndexMark.erasable : IndexMark → Bool
  | .firstPending => false
  | .firstUsed => true
  | .laterPending => false
  | .laterUsed => true

/-- Marks 2 and 3 denote an index which is not the first consumed index of the current copied
stack.  Only these marks permit Aho's primed continuation after a pop. -/
public def IndexMark.later : IndexMark → Bool
  | .firstPending => false
  | .firstUsed => false
  | .laterPending => true
  | .laterUsed => true

@[simp] public theorem IndexMark.markUsed_firstPending :
    IndexMark.firstPending.markUsed = .firstUsed := rfl

@[simp] public theorem IndexMark.markUsed_firstUsed :
    IndexMark.firstUsed.markUsed = .firstUsed := rfl

@[simp] public theorem IndexMark.markUsed_laterPending :
    IndexMark.laterPending.markUsed = .laterUsed := rfl

@[simp] public theorem IndexMark.markUsed_laterUsed :
    IndexMark.laterUsed.markUsed = .laterUsed := rfl

@[simp] public theorem IndexMark.erasable_markUsed (d : IndexMark) :
    d.markUsed.erasable = true := by
  cases d <;> rfl

/-- A symbol of Aho's unpadded logical work tape.

`plain A` is the paper's `A`, while `live A` is `A'`: at least one compressed index to its
right is promised to be consumed during the expansion of this occurrence. -/
public inductive WorkSym (g : IndexedGrammar T) where
  | terminal : T → WorkSym g
  | plain : g.nt → WorkSym g
  | live : g.nt → WorkSym g
  | index : CFlag g → IndexMark → WorkSym g
  | dollar : WorkSym g
  | close : WorkSym g
  | hash : WorkSym g

public noncomputable instance WorkSym.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (WorkSym g) :=
  Classical.decEq _

public noncomputable instance WorkSym.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (WorkSym g) := by
  classical
  letI : Fintype (CFlag g) := by
    change Fintype (g.nt → g.nt → Bool)
    infer_instance
  let encode : WorkSym g →
      Fin 7 × Option T × Option g.nt × Option (CFlag g) × Option IndexMark
    | .terminal a => (0, some a, none, none, none)
    | .plain A => (1, none, some A, none, none)
    | .live A => (2, none, some A, none, none)
    | .index R d => (3, none, none, some R, some d)
    | .dollar => (4, none, none, none, none)
    | .close => (5, none, none, none, none)
    | .hash => (6, none, none, none, none)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

/-- Does a work symbol carry a compressed index? -/
public def WorkSym.isIndex {g : IndexedGrammar T} : WorkSym g → Bool
  | .index _ _ => true
  | _ => false

/-- Is a work symbol a `$` frame opener? -/
public def WorkSym.isDollar {g : IndexedGrammar T} : WorkSym g → Bool
  | .dollar => true
  | _ => false

/-- A list contains no compressed-index symbol. -/
public def IndexFree {g : IndexedGrammar T} (xs : List (WorkSym g)) : Prop :=
  ∀ R d, WorkSym.index R d ∉ xs

/-- A list contains no `$` frame opener. -/
public def DollarFree {g : IndexedGrammar T} (xs : List (WorkSym g)) : Prop :=
  WorkSym.dollar ∉ xs

/-- Mark the rightmost symbol of `alpha` if it is a compressed index.  This is exactly the
operation written `alpha⁺` by Aho. -/
public def markProductivePrefix {g : IndexedGrammar T}
    (alpha : List (WorkSym g)) : List (WorkSym g) :=
  match alpha.reverse with
  | WorkSym.index R d :: rest =>
      (WorkSym.index R d.markUsed :: rest).reverse
  | _ => alpha

@[simp] public theorem markProductivePrefix_nil {g : IndexedGrammar T} :
    markProductivePrefix (g := g) [] = [] := rfl

@[simp] public theorem markProductivePrefix_append_index {g : IndexedGrammar T}
    (alpha : List (WorkSym g)) (R : CFlag g) (d : IndexMark) :
    markProductivePrefix (alpha ++ [WorkSym.index R d]) =
      alpha ++ [WorkSym.index R d.markUsed] := by
  simp [markProductivePrefix, List.reverse_append]

@[simp] public theorem markProductivePrefix_append_nonindex {g : IndexedGrammar T}
    (alpha : List (WorkSym g)) (z : WorkSym g)
    (hz : ∀ R d, z ≠ WorkSym.index R d) :
    markProductivePrefix (alpha ++ [z]) = alpha ++ [z] := by
  simp only [markProductivePrefix, List.reverse_append, List.reverse_singleton,
    List.singleton_append]
  cases z <;> simp_all


end Aho
end IndexedGrammar

