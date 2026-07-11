module

public import Langlib.Grammars.Indexed.NormalForm.AhoCompression
public import Mathlib.Data.Fintype.Prod

@[expose]
public section

/-!
# Aho's marked compressed-index machine

This file gives the finite alphabet and the operational semantics of the machine from
Section 5 of Aho's 1968 paper.  The grammar-facing saturation and compressed relations live in
`AhoCompression.lean`; here we record the four index marks, the `$`/`¢` frame discipline,
and the eleven productive composite moves used for an epsilon-free normal-form grammar.

There are deliberately two levels of semantics.

* `CompositeStep` is the mathematical machine from the paper.  A configuration uses a zipper,
  making the hatted (active) work symbol explicit.
* The final section provides a finite one/two-cell edit certificate and its left-to-right finite
  checker.  It is a reusable micro-step presentation; the direct compiler may instead recognize
  each bounded-shift composite relation in one synchronized scan of two padded rows.

The logical work tape has twenty-one slots per input symbol. Aho's sharp paper bound is six; the
extra formal slack accounts for explicit task, index, and frame markers.  The constant is
immaterial for context sensitivity.  `encodeRunRow` packs such a tape into one row cell per input
symbol, ready for the generic certified-row LBA compiler.

## Reference

* A. V. Aho, "Indexed grammars -- an extension of context-free grammars", JACM 15(4),
  Section 5, 1968.
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

/-! ## Zipper configurations and finite composite certificates -/

/-- A work word with its hatted (active) symbol exposed. -/
public structure WorkCursor (g : IndexedGrammar T) where
  left : List (WorkSym g)
  focus : WorkSym g
  right : List (WorkSym g)

/-- One logical work square, including the unique active-head marker. -/
public structure WorkSlot (g : IndexedGrammar T) where
  active : Bool
  symbol : WorkSym g

public noncomputable instance WorkSlot.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (WorkSlot g) :=
  Classical.decEq _

public noncomputable instance WorkSlot.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (WorkSlot g) := by
  classical
  let encode : WorkSlot g → Bool × WorkSym g := fun s => (s.active, s.symbol)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x
    cases y
    simp_all [encode])

/-- Forget the work head. -/
public def WorkCursor.word {g : IndexedGrammar T} (c : WorkCursor g) : List (WorkSym g) :=
  c.left ++ c.focus :: c.right

/-- Encode the work cursor without losing its active position. -/
public def WorkCursor.slots {g : IndexedGrammar T} (c : WorkCursor g) : List (WorkSlot g) :=
  c.left.map (fun z => ⟨false, z⟩) ++
    ⟨true, c.focus⟩ :: c.right.map (fun z => ⟨false, z⟩)

@[simp] public theorem WorkCursor.slots_length {g : IndexedGrammar T} (c : WorkCursor g) :
    c.slots.length = c.word.length := by
  simp [WorkCursor.slots, WorkCursor.word]

@[simp] public theorem WorkCursor.slots_symbols {g : IndexedGrammar T} (c : WorkCursor g) :
    c.slots.map WorkSlot.symbol = c.word := by
  simp [WorkCursor.slots, WorkCursor.word, List.map_map, Function.comp_def]

/-- The marked slot word retains the whole cursor, not merely its underlying work word. -/
public theorem WorkCursor.slots_injective {g : IndexedGrammar T} :
    Function.Injective (WorkCursor.slots (g := g)) := by
  intro c d h
  rcases c with ⟨left, focus, right⟩
  rcases d with ⟨left', focus', right'⟩
  simp only [WorkCursor.slots] at h
  have falseSlot_injective : Function.Injective
      (fun z : WorkSym g => (⟨false, z⟩ : WorkSlot g)) := by
    intro x y hxy
    exact congrArg WorkSlot.symbol hxy
  induction left generalizing left' with
  | nil =>
      cases left' with
      | nil =>
          simp only [List.map_nil, List.nil_append] at h
          have hhead := (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          have hfocus : focus = focus' := congrArg WorkSlot.symbol hhead
          have hright : right = right' :=
            (List.map_injective_iff.mpr falseSlot_injective) htail
          subst focus'
          subst right'
          rfl
      | cons z left' =>
          simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append] at h
          have hhead := (List.cons.inj h).1
          have : true = false := congrArg WorkSlot.active hhead
          contradiction
  | cons z left ih =>
      cases left' with
      | nil =>
          simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append] at h
          have hhead := (List.cons.inj h).1
          have : false = true := congrArg WorkSlot.active hhead
          contradiction
      | cons z' left' =>
          simp only [List.map_cons, List.cons_append] at h
          have hhead := (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          have hz : z = z' := congrArg WorkSlot.symbol hhead
          have hcursor :
              (WorkCursor.mk left focus right : WorkCursor g) =
                WorkCursor.mk left' focus' right' :=
            ih left' htail
          cases hcursor
          cases hz
          rfl

@[simp] public theorem WorkCursor.word_length {g : IndexedGrammar T} (c : WorkCursor g) :
    c.word.length = c.left.length + 1 + c.right.length := by
  simp [WorkCursor.word, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A composite configuration: `inputPos` input symbols have already been compared, and
`work` is the marked work-tape zipper. -/
public structure Config (g : IndexedGrammar T) where
  inputPos : ℕ
  work : WorkCursor g

/-- The initial composite configuration on every input. -/
public def initialConfig (g : IndexedGrammar T) : Config g :=
  ⟨0, ⟨[WorkSym.dollar], WorkSym.plain g.initial, [WorkSym.hash]⟩⟩

/-- The final composite configuration after all `n` input symbols have been compared. -/
public def finalConfig (g : IndexedGrammar T) (n : ℕ) : Config g :=
  ⟨n, ⟨[WorkSym.dollar], WorkSym.hash, []⟩⟩

/-- Finite evidence selecting one of Aho's composite moves.  All fields range over types fixed
by the grammar, so this is a finite certificate alphabet. -/
public inductive CompositeCert (g : IndexedGrammar T) where
  | plainBinary : g.nt → g.nt → g.nt → CompositeCert g
  | plainTerminal : g.nt → T → CompositeCert g
  | plainPushSkip : g.nt → g.nt → g.flag → CompositeCert g
  | plainPushUse : g.nt → g.nt → g.flag → CompositeCert g
  | liveBinaryBoth : g.nt → g.nt → g.nt → CompositeCert g
  | liveBinaryLeft : g.nt → g.nt → g.nt → CompositeCert g
  | liveBinaryRight : g.nt → g.nt → g.nt → CompositeCert g
  | livePushFresh : g.nt → g.nt → g.flag → CompositeCert g
  | livePushCompress : g.nt → g.nt → g.flag → CFlag g → IndexMark → CompositeCert g
  | popPlain : CFlag g → IndexMark → g.nt → g.nt → CompositeCert g
  | popLive : CFlag g → IndexMark → g.nt → g.nt → CompositeCert g
  | matchTerminal : T → CompositeCert g
  | eraseIndex : CFlag g → IndexMark → CompositeCert g
  | returnFrame : CompositeCert g

public noncomputable instance CompositeCert.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (CompositeCert g) :=
  Classical.decEq _

public noncomputable instance CompositeCert.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] [Fintype g.flag] : Fintype (CompositeCert g) := by
  classical
  letI : Fintype (CFlag g) := by
    change Fintype (g.nt → g.nt → Bool)
    infer_instance
  let encode : CompositeCert g →
      Fin 14 × Option g.nt × Option g.nt × Option g.nt × Option T ×
        Option g.flag × Option (CFlag g) × Option IndexMark
    | .plainBinary A B C =>
        (0, some A, some B, some C, none, none, none, none)
    | .plainTerminal A a =>
        (1, some A, none, none, some a, none, none, none)
    | .plainPushSkip A B f =>
        (2, some A, some B, none, none, some f, none, none)
    | .plainPushUse A B f =>
        (3, some A, some B, none, none, some f, none, none)
    | .liveBinaryBoth A B C =>
        (4, some A, some B, some C, none, none, none, none)
    | .liveBinaryLeft A B C =>
        (5, some A, some B, some C, none, none, none, none)
    | .liveBinaryRight A B C =>
        (6, some A, some B, some C, none, none, none, none)
    | .livePushFresh A B f =>
        (7, some A, some B, none, none, some f, none, none)
    | .livePushCompress A B f R d =>
        (8, some A, some B, none, none, some f, some R, some d)
    | .popPlain R d A B =>
        (9, some A, some B, none, none, none, some R, some d)
    | .popLive R d A B =>
        (10, some A, some B, none, none, none, some R, some d)
    | .matchTerminal a =>
        (11, none, none, none, some a, none, none, none)
    | .eraseIndex R d =>
        (12, none, none, none, none, none, some R, some d)
    | .returnFrame =>
        (13, none, none, none, none, none, none, none)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

/-- Semantics of one finite composite certificate on a fixed input word.

The clauses are Aho's moves 1--6, split into their nondeterministic subcases.  The paper's
active hat is represented by `WorkCursor.focus`; consequently every equality below also fixes
the new work-head position. -/
public noncomputable def CertStep (g : IndexedGrammar T) [Fintype g.nt] (input : List T) :
    CompositeCert g → Config g → Config g → Prop
  | .plainBinary A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.plain B,
              WorkSym.plain C :: beta⟩⟩
  | .plainTerminal A a, c, c' =>
      AugTerminal g A a ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.terminal a, beta⟩⟩
  | .plainPushSkip A B f, c, c' =>
      AugPush g A B f ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, beta⟩⟩
  | .plainPushUse A B f, c, c' =>
      AugPush g A B f ∧
        ∃ alpha beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.index (cflagBase g f) .firstPending :: beta⟩⟩
  | .liveBinaryBoth A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.live C :: Z :: beta⟩⟩
  | .liveBinaryLeft A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.plain C :: Z :: beta⟩⟩
  | .liveBinaryRight A B C, c, c' =>
      AugBinary g A B C ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.plain B,
              WorkSym.live C :: Z :: beta⟩⟩
  | .livePushFresh A B f, c, c' =>
      AugPush g A B f ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.index (cflagBase g f) .laterPending :: Z :: beta⟩⟩
  | .livePushCompress A B f R d, c, c' =>
      AugPush g A B f ∧ (cflagComp g (cflagBase g f) R).Nonempty ∧
        ∃ alpha beta,
          c = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live A, WorkSym.index R d :: beta⟩⟩ ∧
          c' = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
              WorkSym.index (cflagComp g (cflagBase g f) R) d :: beta⟩⟩
  | .popPlain R d A B, c, c' =>
      R A B = true ∧
        ((∃ alpha beta gamma,
            IndexFree beta ∧
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                beta ++ WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar] ++ beta ++
                  [WorkSym.index R d.markUsed, WorkSym.dollar],
                WorkSym.plain B, WorkSym.close :: gamma⟩⟩) ∨
          (∃ alpha gamma,
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, gamma⟩⟩))
  | .popLive R d A B, c, c' =>
      R A B = true ∧ d.later = true ∧
        ((∃ alpha beta gamma,
            IndexFree beta ∧
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                beta ++ WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar] ++ beta ++
                  [WorkSym.index R d.markUsed, WorkSym.dollar],
                WorkSym.live B, WorkSym.close :: gamma⟩⟩) ∨
          (∃ alpha gamma,
            c = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
                WorkSym.index R d :: gamma⟩⟩ ∧
            c' = ⟨c.inputPos,
              ⟨alpha ++ [WorkSym.dollar], WorkSym.live B, gamma⟩⟩))
  | .matchTerminal a, c, c' =>
      input[c.inputPos]? = some a ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.terminal a, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos + 1, ⟨alpha ++ [WorkSym.dollar], Z, beta⟩⟩
  | .eraseIndex R d, c, c' =>
      d.erasable = true ∧
        ∃ alpha Z beta,
          c = ⟨c.inputPos,
            ⟨alpha ++ [WorkSym.dollar], WorkSym.index R d, Z :: beta⟩⟩ ∧
          c' = ⟨c.inputPos, ⟨alpha ++ [WorkSym.dollar], Z, beta⟩⟩
  | .returnFrame, c, c' =>
      ∃ alpha Z beta gamma,
        Z ≠ WorkSym.dollar ∧ DollarFree beta ∧
        c = ⟨c.inputPos,
          ⟨alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar],
            WorkSym.close, gamma⟩⟩ ∧
        c' = ⟨c.inputPos,
          ⟨alpha ++ [WorkSym.dollar], Z, beta ++ gamma⟩⟩

/-- One composite move is a move selected by some finite certificate. -/
public def CompositeStep (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (c c' : Config g) : Prop :=
  ∃ cert : CompositeCert g, CertStep g input cert c c'

public theorem compositeStep_iff_exists_cert
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T) (c c' : Config g) :
    CompositeStep g input c c' ↔
      ∃ cert : CompositeCert g, CertStep g input cert c c' :=
  Iff.rfl

/-! ## Twenty-one-slot padded rows -/

/-- The fixed number of logical work squares per input position used by the scheduler bound.
Aho proves the sharper constant six; the persistent scheduler invariant currently uses
twenty-one. -/
public def workWidth : ℕ := 21

public theorem workWidth_eq : workWidth = 21 := rfl

attribute [irreducible] workWidth

/-- One packed work block.  `none` is a blank logical work square. -/
public abbrev WorkBlock (g : IndexedGrammar T) : Type :=
  PackedBlock (WorkSlot g) workWidth

/-- The completely unused packed work block. -/
public def blankBlock (g : IndexedGrammar T) : WorkBlock g :=
  fun _ => none

/-- Once a packed-cell offset lies beyond the logical word, that whole block is blank. -/
public theorem packedCell_eq_blankBlock_of_length_le
    (g : IndexedGrammar T) (xs : List (WorkSlot g)) (cell : ℕ)
    (h : xs.length ≤ cell * workWidth) :
    packedCell workWidth xs cell = blankBlock g := by
  funext j
  simp only [packedCell, blankBlock]
  exact List.getElem?_eq_none (le_trans h (Nat.le_add_right _ _))

/-- A running row cell retains its immutable input letter, whether that input position has
already been compared, and twenty-one logical work squares. -/
public structure RunCell (g : IndexedGrammar T) where
  input : T
  consumed : Bool
  block : WorkBlock g

public noncomputable instance RunCell.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (RunCell g) :=
  Classical.decEq _

public noncomputable instance RunCell.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (RunCell g) := by
  classical
  let encode : RunCell g → T × Bool × WorkBlock g :=
    fun c => (c.input, c.consumed, c.block)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x
    cases y
    simp_all [encode])

/-- Row cells are raw input cells before initialization or packed running cells afterwards. -/
public inductive RowCell (g : IndexedGrammar T) where
  | input : T → RowCell g
  | run : RunCell g → RowCell g

public noncomputable instance RowCell.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (RowCell g) :=
  Classical.decEq _

public noncomputable instance RowCell.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (RowCell g) := by
  classical
  let encode : RowCell g → T ⊕ RunCell g
    | .input a => Sum.inl a
    | .run c => Sum.inr c
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

/-- Read the packed block of a running row cell. -/
public def RowCell.block? {g : IndexedGrammar T} : RowCell g → Option (WorkBlock g)
  | .input _ => none
  | .run c => some c.block

/-- Read the consumed-input bit of a running row cell. -/
public def RowCell.consumed? {g : IndexedGrammar T} : RowCell g → Option Bool
  | .input _ => none
  | .run c => some c.consumed

/-- Recover the immutable input letter from either presentation of a row cell. -/
public def RowCell.inputLetter {g : IndexedGrammar T} : RowCell g → T
  | .input a => a
  | .run c => c.input

@[simp] public theorem RowCell.inputLetter_input {g : IndexedGrammar T} (a : T) :
    (RowCell.input a : RowCell g).inputLetter = a := rfl

@[simp] public theorem RowCell.inputLetter_run {g : IndexedGrammar T} (c : RunCell g) :
    (RowCell.run c : RowCell g).inputLetter = c.input := rfl

@[simp] public theorem RowCell.input_ne_run {g : IndexedGrammar T}
    (a : T) (c : RunCell g) : RowCell.input a ≠ RowCell.run c := by
  intro h
  cases h

/-- The row presented to the certified-row system by an input word. -/
public def inputRow (g : IndexedGrammar T) (w : List T) : List (RowCell g) :=
  w.map RowCell.input

/-- Encode a running configuration, starting at physical input-cell offset `cell`. -/
public def encodeRunRowFrom (g : IndexedGrammar T) (work : List (WorkSlot g))
    (inputPos cell : ℕ) : List T → List (RowCell g)
  | [] => []
  | a :: w =>
      RowCell.run
          { input := a
            consumed := decide (cell < inputPos)
            block := packedCell workWidth work cell } ::
        encodeRunRowFrom g work inputPos (cell + 1) w

/-- Pack a composite configuration into one width-twenty-one row cell per input letter. -/
public def encodeRunRow (g : IndexedGrammar T) (w : List T) (c : Config g) :
    List (RowCell g) :=
  encodeRunRowFrom g c.work.slots c.inputPos 0 w

/-- The only nonblank block in an initialized running row. -/
public def initialBlock (g : IndexedGrammar T) : WorkBlock g :=
  packedCell workWidth (initialConfig g).work.slots 0

/-- The only nonblank block in a final running row. -/
public def finalBlock (g : IndexedGrammar T) : WorkBlock g :=
  packedCell workWidth (finalConfig g 0).work.slots 0

private theorem encodeRunRowFrom_short_tail_false
    (g : IndexedGrammar T) (work : List (WorkSlot g))
    (hwork : work.length ≤ workWidth) (w : List T) (cell : ℕ) (hcell : 1 ≤ cell) :
    encodeRunRowFrom g work 0 cell w =
      w.map fun a => RowCell.run
        { input := a, consumed := false, block := blankBlock g } := by
  induction w generalizing cell with
  | nil => rfl
  | cons a w ih =>
      have hblank : packedCell workWidth work cell = blankBlock g :=
        packedCell_eq_blankBlock_of_length_le g work cell (by
          unfold workWidth at hwork ⊢
          omega)
      simp only [encodeRunRowFrom, List.map_cons]
      rw [hblank]
      simp only [Nat.not_lt_zero, decide_false]
      rw [ih (cell + 1) (by omega)]

private theorem encodeRunRowFrom_short_tail_true
    (g : IndexedGrammar T) (work : List (WorkSlot g))
    (hwork : work.length ≤ workWidth) (w : List T) (inputPos cell : ℕ)
    (hcell : 1 ≤ cell) (hpos : cell + w.length ≤ inputPos) :
    encodeRunRowFrom g work inputPos cell w =
      w.map fun a => RowCell.run
        { input := a, consumed := true, block := blankBlock g } := by
  induction w generalizing cell with
  | nil => rfl
  | cons a w ih =>
      simp only [List.length_cons] at hpos
      have hblank : packedCell workWidth work cell = blankBlock g :=
        packedCell_eq_blankBlock_of_length_le g work cell (by
          unfold workWidth at hwork ⊢
          omega)
      have hlt : cell < inputPos := by omega
      simp only [encodeRunRowFrom, List.map_cons]
      rw [hblank]
      simp only [hlt, decide_true]
      rw [ih (cell + 1) (by omega) (by omega)]

/-- Canonical cellwise shape of a nonempty initialization row. -/
public theorem encodeRunRow_initial_cons (g : IndexedGrammar T) (a : T) (w : List T) :
    encodeRunRow g (a :: w) (initialConfig g) =
      RowCell.run { input := a, consumed := false, block := initialBlock g } ::
        w.map fun b => RowCell.run
          { input := b, consumed := false, block := blankBlock g } := by
  simp only [encodeRunRow, initialConfig, WorkCursor.slots, encodeRunRowFrom,
    initialBlock, Nat.not_lt_zero, decide_false]
  simp only [List.map_singleton, List.map_nil, List.singleton_append, List.append_nil,
    Nat.zero_add]
  rw [encodeRunRowFrom_short_tail_false g
    ([⟨false, WorkSym.dollar⟩, ⟨true, WorkSym.plain g.initial⟩,
      ⟨false, WorkSym.hash⟩]) (by
      simp [workWidth]) w 1 (by omega)]

/-- Canonical cellwise shape of a nonempty final row. -/
public theorem encodeRunRow_final_cons (g : IndexedGrammar T) (a : T) (w : List T) :
    encodeRunRow g (a :: w) (finalConfig g (a :: w).length) =
      RowCell.run { input := a, consumed := true, block := finalBlock g } ::
        w.map fun b => RowCell.run
          { input := b, consumed := true, block := blankBlock g } := by
  simp only [encodeRunRow, finalConfig, WorkCursor.slots, encodeRunRowFrom,
    finalBlock, List.length_cons]
  simp only [List.map_singleton, List.map_nil, List.singleton_append, List.append_nil,
    Nat.zero_add]
  have hzero : 0 < w.length + 1 := by omega
  simp only [hzero, decide_true]
  rw [encodeRunRowFrom_short_tail_true g
    ([⟨false, WorkSym.dollar⟩, ⟨true, WorkSym.hash⟩]) (by simp [workWidth]) w
    (w.length + 1) 1 (by omega) (by omega)]

@[simp] public theorem inputRow_length (g : IndexedGrammar T) (w : List T) :
    (inputRow g w).length = w.length := by
  simp [inputRow]

@[simp] public theorem inputRow_map_inputLetter (g : IndexedGrammar T) (w : List T) :
    (inputRow g w).map RowCell.inputLetter = w := by
  simp [inputRow, Function.comp_def]

public theorem encodeRunRowFrom_length (g : IndexedGrammar T) (work : List (WorkSlot g))
    (inputPos cell : ℕ) (w : List T) :
    (encodeRunRowFrom g work inputPos cell w).length = w.length := by
  induction w generalizing cell with
  | nil => rfl
  | cons a w ih =>
      simp [encodeRunRowFrom, ih]

@[simp] public theorem encodeRunRowFrom_map_inputLetter (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (inputPos cell : ℕ) (w : List T) :
    (encodeRunRowFrom g work inputPos cell w).map RowCell.inputLetter = w := by
  induction w generalizing cell with
  | nil => rfl
  | cons a w ih => simp [encodeRunRowFrom, RowCell.inputLetter, ih]

public theorem encodeRunRowFrom_getElem?_block (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (inputPos cell : ℕ) (w : List T) (k : ℕ)
    (hk : k < w.length) :
    (encodeRunRowFrom g work inputPos cell w)[k]?.bind RowCell.block? =
      some (packedCell workWidth work (cell + k)) := by
  induction w generalizing cell k with
  | nil => simp at hk
  | cons a w ih =>
      cases k with
      | zero => simp [encodeRunRowFrom, RowCell.block?]
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          simpa [encodeRunRowFrom, RowCell.block?, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (cell + 1) k hk

public theorem encodeRunRowFrom_getElem?_consumed (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (inputPos cell : ℕ) (w : List T) (k : ℕ)
    (hk : k < w.length) :
    (encodeRunRowFrom g work inputPos cell w)[k]?.bind RowCell.consumed? =
      some (decide (cell + k < inputPos)) := by
  induction w generalizing cell k with
  | nil => simp at hk
  | cons a w ih =>
      cases k with
      | zero => simp [encodeRunRowFrom, RowCell.consumed?]
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          simpa [encodeRunRowFrom, RowCell.consumed?, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (cell + 1) k hk

@[simp] public theorem encodeRunRow_length (g : IndexedGrammar T) (w : List T)
    (c : Config g) :
    (encodeRunRow g w c).length = w.length := by
  exact encodeRunRowFrom_length g c.work.slots c.inputPos 0 w

@[simp] public theorem encodeRunRow_map_inputLetter (g : IndexedGrammar T)
    (w : List T) (c : Config g) :
    (encodeRunRow g w c).map RowCell.inputLetter = w := by
  exact encodeRunRowFrom_map_inputLetter g c.work.slots c.inputPos 0 w

/-- Equal running rows necessarily carry the same immutable input word. -/
public theorem encodeRunRow_input_eq {g : IndexedGrammar T}
    {w w' : List T} {c d : Config g}
    (h : encodeRunRow g w c = encodeRunRow g w' d) : w = w' := by
  have := congrArg (List.map RowCell.inputLetter) h
  simpa using this

private theorem decide_lt_prefix_injective {n p q : ℕ}
    (hp : p ≤ n) (hq : q ≤ n)
    (h : ∀ k, k < n → decide (k < p) = decide (k < q)) :
    p = q := by
  by_contra hpq
  rcases Nat.lt_or_gt_of_ne hpq with hpq | hqp
  · have hpn : p < n := lt_of_lt_of_le hpq hq
    have := h p hpn
    simp [hpq] at this
  · have hqn : q < n := lt_of_lt_of_le hqp hp
    have := h q hqn
    simp [hqp] at this

/-- On a fixed input row, bounded marked encodings are injective in the full configuration,
including both the input position and the active work-head position. -/
public theorem encodeRunRow_injective_of_bounds (g : IndexedGrammar T) (w : List T)
    (c d : Config g)
    (hcpos : c.inputPos ≤ w.length) (hdpos : d.inputPos ≤ w.length)
    (hcwork : c.work.word.length ≤ w.length * workWidth)
    (hdwork : d.work.word.length ≤ w.length * workWidth)
    (hrow : encodeRunRow g w c = encodeRunRow g w d) :
    c = d := by
  have hconsumed : ∀ k, k < w.length →
      decide (k < c.inputPos) = decide (k < d.inputPos) := by
    intro k hk
    have hget := congrArg (fun row : List (RowCell g) =>
      row[k]?.bind RowCell.consumed?) hrow
    change (encodeRunRowFrom g c.work.slots c.inputPos 0 w)[k]?.bind
        RowCell.consumed? =
      (encodeRunRowFrom g d.work.slots d.inputPos 0 w)[k]?.bind
        RowCell.consumed? at hget
    rw [encodeRunRowFrom_getElem?_consumed g _ _ _ _ _ hk,
      encodeRunRowFrom_getElem?_consumed g _ _ _ _ _ hk] at hget
    simpa using Option.some.inj hget
  have hpos : c.inputPos = d.inputPos :=
    decide_lt_prefix_injective hcpos hdpos hconsumed
  have hpack : packedTape workWidth w.length c.work.slots =
      packedTape workWidth w.length d.work.slots := by
    funext i
    have hget := congrArg (fun row : List (RowCell g) =>
      row[i.val]?.bind RowCell.block?) hrow
    change (encodeRunRowFrom g c.work.slots c.inputPos 0 w)[i.val]?.bind
        RowCell.block? =
      (encodeRunRowFrom g d.work.slots d.inputPos 0 w)[i.val]?.bind
        RowCell.block? at hget
    rw [encodeRunRowFrom_getElem?_block g _ _ _ _ _ i.isLt,
      encodeRunRowFrom_getElem?_block g _ _ _ _ _ i.isLt] at hget
    simpa [packedTape] using Option.some.inj hget
  have hslots : c.work.slots = d.work.slots :=
    packedTape_ext_of_length_le (by simp [workWidth])
      (by simpa using hcwork) (by simpa using hdwork) hpack
  have hwork : c.work = d.work := WorkCursor.slots_injective hslots
  cases c
  cases d
  simp_all

/-- Bounded marked rows recover both the immutable input word and the complete configuration. -/
public theorem encodeRunRow_pair_injective_of_bounds (g : IndexedGrammar T)
    (w w' : List T) (c d : Config g)
    (hcpos : c.inputPos ≤ w.length) (hdpos : d.inputPos ≤ w'.length)
    (hcwork : c.work.word.length ≤ w.length * workWidth)
    (hdwork : d.work.word.length ≤ w'.length * workWidth)
    (hrow : encodeRunRow g w c = encodeRunRow g w' d) :
    w = w' ∧ c = d := by
  have hw : w = w' := encodeRunRow_input_eq hrow
  subst w'
  exact ⟨rfl, encodeRunRow_injective_of_bounds g w c d
    hcpos hdpos hcwork hdwork hrow⟩

/-- The initialization row step. -/
public def PaddedInitStep (g : IndexedGrammar T) (x y : List (RowCell g)) : Prop :=
  ∃ w : List T,
    w ≠ [] ∧ x = inputRow g w ∧ y = encodeRunRow g w (initialConfig g)

/-- A bounded packed-row image of one Aho composite move. -/
public def PaddedCompositeStep (g : IndexedGrammar T) [Fintype g.nt]
    (x y : List (RowCell g)) : Prop :=
  ∃ (w : List T) (c c' : Config g),
    w ≠ [] ∧ c.inputPos ≤ w.length ∧ c'.inputPos ≤ w.length ∧
      c.work.word.length ≤ w.length * workWidth ∧
      c'.work.word.length ≤ w.length * workWidth ∧
      CompositeStep g w c c' ∧
      x = encodeRunRow g w c ∧ y = encodeRunRow g w c'

/-- Semantic padded-row relation: initialize once, then perform a bounded composite move. -/
public def PaddedRowStep (g : IndexedGrammar T) [Fintype g.nt]
    (x y : List (RowCell g)) : Prop :=
  PaddedInitStep g x y ∨ PaddedCompositeStep g x y

/-- A final row has consumed the whole frozen input and contains Aho's final `$ #` work word. -/
public def FinalRow (g : IndexedGrammar T) (row : List (RowCell g)) : Prop :=
  ∃ w : List T, w ≠ [] ∧ row = encodeRunRow g w (finalConfig g w.length)

/-! ## Exact finite scans for initialization and final rows -/

/-- Three states suffice for the fixed first-block / blank-tail row formats. -/
public inductive BoundaryScanState where
  | first
  | tail
  | dead
deriving DecidableEq, Fintype

/-- The canonical initialized cell at the first input position. -/
public def initialFirstCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := false, block := initialBlock g }

/-- A canonical blank-tail initialized cell. -/
public def initialTailCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := false, block := blankBlock g }

/-- The canonical final cell at the first input position. -/
public def finalFirstCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := true, block := finalBlock g }

/-- A canonical blank-tail final cell. -/
public def finalTailCell (g : IndexedGrammar T) (a : T) : RowCell g :=
  .run { input := a, consumed := true, block := blankBlock g }

/-- Cell transition for the exact synchronized initialization scan. -/
public noncomputable def initScanCell (g : IndexedGrammar T) :
    BoundaryScanState → RowCell g → RowCell g → BoundaryScanState := by
  classical
  exact fun state old new =>
    match state, old with
    | .first, .input a => if new = initialFirstCell g a then .tail else .dead
    | .tail, .input a => if new = initialTailCell g a then .tail else .dead
    | _, _ => .dead

/-- Run the synchronized initialization scan; unequal row lengths reject. -/
public noncomputable def evalInitScan (g : IndexedGrammar T) :
    BoundaryScanState → List (RowCell g) → List (RowCell g) → BoundaryScanState
  | state, [], [] => state
  | state, old :: olds, new :: news =>
      evalInitScan g (initScanCell g state old new) olds news
  | _, _, _ => .dead

@[simp] private theorem evalInitScan_dead (g : IndexedGrammar T)
    (old new : List (RowCell g)) :
    evalInitScan g .dead old new = .dead := by
  induction old generalizing new with
  | nil => cases new <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => rfl
      | cons new news => simp [evalInitScan, initScanCell, ih]

/-- Cell transition for the exact regular final-row scan. -/
public noncomputable def finalScanCell (g : IndexedGrammar T) :
    BoundaryScanState → RowCell g → BoundaryScanState := by
  classical
  exact fun state cell =>
    match state, cell with
    | .first, .run c => if cell = finalFirstCell g c.input then .tail else .dead
    | .tail, .run c => if cell = finalTailCell g c.input then .tail else .dead
    | _, _ => .dead

/-- Run the final-row scan. -/
public noncomputable def evalFinalScan (g : IndexedGrammar T) :
    BoundaryScanState → List (RowCell g) → BoundaryScanState
  | state, [] => state
  | state, cell :: row => evalFinalScan g (finalScanCell g state cell) row

@[simp] private theorem evalFinalScan_dead (g : IndexedGrammar T)
    (row : List (RowCell g)) :
    evalFinalScan g .dead row = .dead := by
  induction row with
  | nil => rfl
  | cons cell row ih => simp [evalFinalScan, finalScanCell, ih]

private theorem evalInitScan_tail_iff (g : IndexedGrammar T)
    (old new : List (RowCell g)) :
    evalInitScan g .tail old new = .tail ↔
      ∃ w : List T,
        old = inputRow g w ∧ new = w.map (initialTailCell g) := by
  induction old generalizing new with
  | nil =>
      cases new <;> simp [evalInitScan, inputRow]
  | cons old olds ih =>
      cases new with
      | nil =>
          constructor
          · intro h
            simp [evalInitScan] at h
          · rintro ⟨w, hold, hnew⟩
            cases w with
            | nil => simp [inputRow] at hold
            | cons a w => simp at hnew
      | cons new news =>
          cases old with
          | run c =>
              constructor
              · intro h
                simp [evalInitScan, initScanCell] at h
              · rintro ⟨w, hold, _⟩
                cases w <;> simp [inputRow] at hold
          | input a =>
              classical
              by_cases hnew : new = initialTailCell g a
              · subst new
                simp only [evalInitScan, initScanCell]
                change evalInitScan g .tail olds news = .tail ↔
                  ∃ w, RowCell.input a :: olds = inputRow g w ∧
                    initialTailCell g a :: news = w.map (initialTailCell g)
                rw [ih]
                constructor
                · rintro ⟨w, hold, hnew⟩
                  exact ⟨a :: w, by simp [inputRow, hold], by simp [hnew]⟩
                · rintro ⟨w, hold, hnew⟩
                  cases w with
                  | nil => simp [inputRow] at hold
                  | cons b w =>
                      simp only [inputRow, List.map_cons, List.cons.injEq] at hold hnew
                      have hab : a = b := RowCell.input.inj hold.1
                      subst b
                      exact ⟨w, hold.2, hnew.2⟩
              · constructor
                · intro h
                  simp [evalInitScan, initScanCell, hnew] at h
                · rintro ⟨w, hold, hmap⟩
                  cases w with
                  | nil => simp [inputRow] at hold
                  | cons b w =>
                      simp only [inputRow, List.map_cons, List.cons.injEq] at hold hmap
                      have hab : a = b := RowCell.input.inj hold.1
                      subst b
                      exact (hnew hmap.1).elim

/-- The initialization scanner recognizes exactly `PaddedInitStep`. -/
public theorem evalInitScan_iff_paddedInitStep (g : IndexedGrammar T)
    (old new : List (RowCell g)) :
    evalInitScan g .first old new = .tail ↔ PaddedInitStep g old new := by
  constructor
  · intro h
    cases old with
    | nil => cases new <;> simp [evalInitScan] at h
    | cons old olds =>
        cases new with
        | nil => simp [evalInitScan] at h
        | cons new news =>
            cases old with
            | run c => simp [evalInitScan, initScanCell] at h
            | input a =>
                classical
                by_cases hnew : new = initialFirstCell g a
                · subst new
                  simp only [evalInitScan, initScanCell] at h
                  change evalInitScan g .tail olds news = .tail at h
                  rw [evalInitScan_tail_iff] at h
                  rcases h with ⟨w, hold, hnew⟩
                  refine ⟨a :: w, by simp, ?_, ?_⟩
                  · simp [inputRow, hold]
                  · rw [encodeRunRow_initial_cons]
                    simp [initialFirstCell, initialTailCell, hnew]
                · simp [evalInitScan, initScanCell, hnew] at h
  · rintro ⟨w, hw, rfl, rfl⟩
    cases w with
    | nil => exact (hw rfl).elim
    | cons a w =>
        rw [encodeRunRow_initial_cons]
        have htail : evalInitScan g .tail (w.map RowCell.input)
            (w.map (initialTailCell g)) = .tail :=
          (evalInitScan_tail_iff g _ _).2 ⟨w, by simp [inputRow], rfl⟩
        simpa [inputRow, evalInitScan, initScanCell, initialFirstCell,
          initialTailCell] using htail

private theorem evalFinalScan_tail_iff (g : IndexedGrammar T) (row : List (RowCell g)) :
    evalFinalScan g .tail row = .tail ↔
      ∃ w : List T, row = w.map (finalTailCell g) := by
  induction row with
  | nil => simp [evalFinalScan]
  | cons cell row ih =>
      cases cell with
      | input a =>
          constructor
          · intro h
            simp [evalFinalScan, finalScanCell] at h
          · rintro ⟨w, hrow⟩
            cases w <;> simp [finalTailCell] at hrow
      | run c =>
          classical
          by_cases hcell : RowCell.run c = finalTailCell g c.input
          · simp only [evalFinalScan, finalScanCell, hcell, if_pos, ih]
            constructor
            · rintro ⟨w, hw⟩
              exact ⟨c.input :: w, by simp [hw]⟩
            · rintro ⟨w, hw⟩
              cases w with
              | nil => simp at hw
              | cons a w =>
                  simp only [List.map_cons, List.cons.injEq] at hw
                  exact ⟨w, hw.2⟩
          · constructor
            · intro h
              simp [evalFinalScan, finalScanCell, hcell] at h
            · rintro ⟨w, hrow⟩
              cases w with
              | nil => simp at hrow
              | cons a w =>
                  simp only [List.map_cons, List.cons.injEq] at hrow
                  have heq : RowCell.run c = finalTailCell g c.input := by
                    cases c
                    simp_all [finalTailCell]
                  exact (hcell heq).elim

/-- The final scanner recognizes exactly `FinalRow`. -/
public theorem evalFinalScan_iff_finalRow (g : IndexedGrammar T) (row : List (RowCell g)) :
    evalFinalScan g .first row = .tail ↔ FinalRow g row := by
  constructor
  · intro h
    cases row with
    | nil => simp [evalFinalScan] at h
    | cons cell row =>
        cases cell with
        | input a => simp [evalFinalScan, finalScanCell] at h
        | run c =>
            classical
            by_cases hcell : RowCell.run c = finalFirstCell g c.input
            · simp only [evalFinalScan, finalScanCell, hcell, if_pos] at h
              rw [evalFinalScan_tail_iff] at h
              rcases h with ⟨w, hrow⟩
              refine ⟨c.input :: w, by simp, ?_⟩
              rw [encodeRunRow_final_cons]
              simp [finalFirstCell, finalTailCell, hcell, hrow]
            · simp [evalFinalScan, finalScanCell, hcell] at h
  · rintro ⟨w, hw, rfl⟩
    cases w with
    | nil => exact (hw rfl).elim
    | cons a w =>
        rw [encodeRunRow_final_cons]
        have htail : evalFinalScan g .tail (w.map (finalTailCell g)) = .tail :=
          (evalFinalScan_tail_iff g _).2 ⟨w, rfl⟩
        simpa [evalFinalScan, finalScanCell, finalFirstCell, finalTailCell] using htail

/-! ## A finite regular checker for local padded-row edits -/

/-- A local edit changes one physical row cell or two adjacent physical row cells.  The type is
finite and is the elementary certificate alphabet from which the insertion/deletion scans of the
composite machine are built. -/
public inductive LocalEdit (g : IndexedGrammar T) where
  | one : RowCell g → RowCell g → LocalEdit g
  | two : RowCell g → RowCell g → RowCell g → RowCell g → LocalEdit g

public noncomputable instance LocalEdit.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (LocalEdit g) :=
  Classical.decEq _

public noncomputable instance LocalEdit.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (LocalEdit g) := by
  classical
  let encode : LocalEdit g →
      (RowCell g × RowCell g) ⊕
        (RowCell g × RowCell g × RowCell g × RowCell g)
    | .one a b => Sum.inl (a, b)
    | .two a₁ a₂ b₁ b₂ => Sum.inr (a₁, a₂, b₁, b₂)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

/-- Semantics of one permitted local edit. -/
public def LocalStep (allowed : LocalEdit g → Prop)
    (x y : List (RowCell g)) : Prop :=
  (∃ l a b r,
      allowed (.one a b) ∧ x = l ++ a :: r ∧ y = l ++ b :: r) ∨
    (∃ l a₁ a₂ b₁ b₂ r,
      allowed (.two a₁ a₂ b₁ b₂) ∧
        x = l ++ a₁ :: a₂ :: r ∧ y = l ++ b₁ :: b₂ :: r)

/-- Per-cell witness alphabet for the synchronized finite checker of `LocalStep`. -/
public inductive LocalWitness (g : IndexedGrammar T) where
  | copy : LocalWitness g
  | one : LocalEdit g → LocalWitness g
  | left : LocalEdit g → LocalWitness g
  | right : LocalEdit g → LocalWitness g

public noncomputable instance LocalWitness.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (LocalWitness g) :=
  Classical.decEq _

public noncomputable instance LocalWitness.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (LocalWitness g) := by
  classical
  let encode : LocalWitness g → Unit ⊕ LocalEdit g ⊕ LocalEdit g ⊕ LocalEdit g
    | .copy => Sum.inl ()
    | .one e => Sum.inr (Sum.inl e)
    | .left e => Sum.inr (Sum.inr (Sum.inl e))
    | .right e => Sum.inr (Sum.inr (Sum.inr e))
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

/-- Finite control of the local-edit checker. -/
public inductive LocalScanState (g : IndexedGrammar T) where
  | before : LocalScanState g
  | needRight : LocalEdit g → LocalScanState g
  | after : LocalScanState g
  | dead : LocalScanState g

public noncomputable instance LocalScanState.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (LocalScanState g) :=
  Classical.decEq _

public noncomputable instance LocalScanState.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (LocalScanState g) := by
  classical
  let encode : LocalScanState g → Unit ⊕ LocalEdit g ⊕ Unit ⊕ Unit
    | .before => Sum.inl ()
    | .needRight e => Sum.inr (Sum.inl e)
    | .after => Sum.inr (Sum.inr (Sum.inl ()))
    | .dead => Sum.inr (Sum.inr (Sum.inr ()))
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

/-- One left-to-right checker transition.  It accepts equal cells before and after the unique
edit, or the one/two cells named by the edit certificate. -/
public noncomputable def localScanCell (allowed : LocalEdit g → Prop) :
    LocalScanState g → RowCell g → RowCell g → LocalWitness g → LocalScanState g := by
  classical
  exact fun st x y witness =>
    match st, witness with
    | .before, .copy => if x = y then .before else .dead
    | .before, .one e =>
        match e with
        | .one a b => if allowed e ∧ x = a ∧ y = b then .after else .dead
        | .two .. => .dead
    | .before, .left e =>
        match e with
        | .two a₁ _ b₁ _ => if allowed e ∧ x = a₁ ∧ y = b₁ then .needRight e else .dead
        | .one .. => .dead
    | .needRight e, .right e' =>
        if e = e' then
          match e with
          | .two _ a₂ _ b₂ => if x = a₂ ∧ y = b₂ then .after else .dead
          | .one .. => .dead
        else .dead
    | .after, .copy => if x = y then .after else .dead
    | _, _ => .dead

/-- Successful final states of the local checker. -/
public def localScanDone {g : IndexedGrammar T} : LocalScanState g → Bool
  | .after => true
  | _ => false

@[simp] public theorem localScanDone_after {g : IndexedGrammar T} :
    localScanDone (LocalScanState.after : LocalScanState g) = true := rfl

@[simp] public theorem localScanDone_before {g : IndexedGrammar T} :
    localScanDone (LocalScanState.before : LocalScanState g) = false := rfl

/-- A one-cell edit supplies one successful local witness at the edited cell. -/
public theorem localScanCell_one_success [DecidableEq (RowCell g)]
    (allowed : LocalEdit g → Prop) (a b : RowCell g)
    (hallowed : allowed (.one a b)) :
    localScanCell allowed .before a b (.one (.one a b)) = .after := by
  classical
  simp [localScanCell, hallowed]

/-- A two-cell edit supplies consecutive left/right witnesses and reaches the successful state. -/
public theorem localScanCell_two_success [DecidableEq (RowCell g)]
    (allowed : LocalEdit g → Prop) (a₁ a₂ b₁ b₂ : RowCell g)
    (hallowed : allowed (.two a₁ a₂ b₁ b₂)) :
    localScanCell allowed
        (localScanCell allowed .before a₁ b₁ (.left (.two a₁ a₂ b₁ b₂)))
        a₂ b₂ (.right (.two a₁ a₂ b₁ b₂)) = .after := by
  classical
  simp [localScanCell, hallowed]

/-- Copy witnesses preserve the pre-edit scan state on equal cells. -/
@[simp] public theorem localScanCell_copy_before [DecidableEq (RowCell g)]
    (allowed : LocalEdit g → Prop) (a : RowCell g) :
    localScanCell allowed .before a a .copy = .before := by
  simp [localScanCell]

/-- Copy witnesses preserve the post-edit scan state on equal cells. -/
@[simp] public theorem localScanCell_copy_after [DecidableEq (RowCell g)]
    (allowed : LocalEdit g → Prop) (a : RowCell g) :
    localScanCell allowed .after a a .copy = .after := by
  simp [localScanCell]

end Aho
end IndexedGrammar
