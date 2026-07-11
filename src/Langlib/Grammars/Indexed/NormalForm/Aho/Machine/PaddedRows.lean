module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Transitions

@[expose]
public section

/-!
# Padded Aho machine rows

The fixed-width row encoding and semantic padded transition relation used by the LBA compiler.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho

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
  simp only [List.map_singleton, List.singleton_append, Nat.zero_add]
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
  simp only [List.map_singleton, List.map_nil, List.singleton_append, Nat.zero_add]
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


end Aho
end IndexedGrammar

