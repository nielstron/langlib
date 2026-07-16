module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories
public import Langlib.Classes.Regular.Closure.Concatenation
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Star
public import Langlib.Classes.Regular.Examples.SingletonWord
public import Langlib.Automata.FiniteState.Equivalence.Regular

@[expose]
public section

/-!
# Regular syntax around selected history rows

These languages describe arbitrary row blocks and the even/odd number of
complete blocks preceding a selected adjacent pair.  They intentionally impose
no common-width condition.
-/

namespace ContextFree.MalformedHistories

variable {A : Type}

def cellWordLanguage : Language (Symbol A) :=
  {w | ∃ row : List A, w = row.map Symbol.cell}

private def cellWordDFA : DFA (Symbol A) Bool where
  start := true
  step
    | true, .cell _ => true
    | _, _ => false
  accept := {true}

private theorem cellWordDFA_evalFrom_false (w : List (Symbol A)) :
    cellWordDFA.evalFrom false w = false := by
  induction w with
  | nil => rfl
  | cons s w ih => cases s <;> simpa [DFA.evalFrom, cellWordDFA] using ih

private theorem cellWordDFA_evalFrom (w : List (Symbol A)) :
    cellWordDFA.evalFrom true w = true ↔
      ∃ row : List A, w = row.map Symbol.cell := by
  induction w with
  | nil => exact ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩
  | cons s w ih =>
      cases s with
      | separator =>
          constructor
          · intro h
            change cellWordDFA.evalFrom false w = true at h
            rw [cellWordDFA_evalFrom_false] at h
            contradiction
          · rintro ⟨row, hrow⟩
            cases row <;> simp at hrow
      | cell a =>
          change cellWordDFA.evalFrom true w = true ↔ _
          constructor
          · intro hw
            obtain ⟨row, rfl⟩ := ih.mp hw
            exact ⟨a :: row, rfl⟩
          · rintro ⟨row, hrow⟩
            cases row with
            | nil => simp at hrow
            | cons b row =>
                simp only [List.map_cons, List.cons.injEq] at hrow
                have hab : a = b := Symbol.cell.inj hrow.1
                subst b
                exact ih.mpr ⟨row, hrow.2⟩

theorem cellWordLanguage_isRegular : cellWordLanguage (A := A).IsRegular := by
  refine ⟨Bool, inferInstance, cellWordDFA, ?_⟩
  ext w
  change cellWordDFA.eval w ∈ ({true} : Set Bool) ↔ _
  rw [Set.mem_singleton_iff]
  exact cellWordDFA_evalFrom w

/-- One row followed by its separator. -/
def blockLanguage : Language (Symbol A) :=
  cellWordLanguage * ({[Symbol.separator]} : Language (Symbol A))

theorem mem_blockLanguage_iff (w : List (Symbol A)) :
    w ∈ blockLanguage (A := A) ↔
      ∃ row : List A, w = row.map Symbol.cell ++ [Symbol.separator] := by
  rw [blockLanguage, Language.mem_mul]
  constructor
  · rintro ⟨cells, ⟨row, rfl⟩, suffix, hsuffix, rfl⟩
    change suffix = [Symbol.separator] at hsuffix
    subst suffix
    exact ⟨row, rfl⟩
  · rintro ⟨row, rfl⟩
    exact ⟨row.map Symbol.cell, ⟨row, rfl⟩,
      [Symbol.separator], Set.mem_singleton _, rfl⟩

theorem blockLanguage_isRegular : blockLanguage (A := A).IsRegular :=
  cellWordLanguage_isRegular.mul'
    (Language.isRegular_singleton_word [Symbol.separator])

/-- Any finite sequence of complete row blocks. -/
def blocksLanguage : Language (Symbol A) :=
  KStar.kstar (blockLanguage (A := A))

theorem blocksLanguage_isRegular : blocksLanguage (A := A).IsRegular :=
  blockLanguage_isRegular.kstar'

theorem mem_blocksLanguage_iff (w : List (Symbol A)) :
    w ∈ blocksLanguage (A := A) ↔
      ∃ rows : List (List A),
        w = (rows.map fun row =>
          row.map Symbol.cell ++ [Symbol.separator]).flatten := by
  rw [blocksLanguage, Language.mem_kstar]
  constructor
  · rintro ⟨blocks, rfl, hblocks⟩
    induction blocks with
    | nil => exact ⟨[], rfl⟩
    | cons block blocks ih =>
        obtain ⟨row, hrow⟩ := (mem_blockLanguage_iff block).mp
          (hblocks block (by simp))
        obtain ⟨rows, hrows⟩ := ih (fun b hb => hblocks b (by simp [hb]))
        refine ⟨row :: rows, ?_⟩
        simp [hrow, hrows]
  · rintro ⟨rows, rfl⟩
    refine ⟨rows.map fun row =>
      row.map Symbol.cell ++ [Symbol.separator], rfl, ?_⟩
    intro block hblock
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hblock
    exact (mem_blockLanguage_iff _).mpr ⟨row, rfl⟩

/-- Apply the alternating orientation to a whole row sequence.  This operation
is its own inverse. -/
def alternateOrient : Bool → List (List A) → List (List A)
  | _, [] => []
  | even, row :: rows =>
      orientRow even row :: alternateOrient (!even) rows

@[simp] theorem orientRow_orientRow (even : Bool) (row : List A) :
    orientRow even (orientRow even row) = row := by
  cases even <;> simp [orientRow]

@[simp] theorem alternateOrient_involutive (even : Bool)
    (rows : List (List A)) :
    alternateOrient even (alternateOrient even rows) = rows := by
  induction rows generalizing even with
  | nil => rfl
  | cons row rows ih =>
      simp [alternateOrient, ih]

theorem encodeAux_eq_flatten_blocks (even : Bool) (rows : List (List A)) :
    encodeAux even rows =
      ((alternateOrient even rows).map fun row =>
        row.map Symbol.cell ++ [Symbol.separator]).flatten := by
  induction rows generalizing even with
  | nil => rfl
  | cons row rows ih =>
      simp [encodeAux, alternateOrient, ih, List.append_assoc]

theorem mem_blocksLanguage_iff_exists_encodeAux
    (even : Bool) (w : List (Symbol A)) :
    w ∈ blocksLanguage (A := A) ↔
      ∃ rows : List (List A), encodeAux even rows = w := by
  rw [mem_blocksLanguage_iff]
  constructor
  · rintro ⟨rows, rfl⟩
    refine ⟨alternateOrient even rows, ?_⟩
    rw [encodeAux_eq_flatten_blocks, alternateOrient_involutive]
  · rintro ⟨rows, rfl⟩
    exact ⟨alternateOrient even rows, encodeAux_eq_flatten_blocks even rows⟩

/-- Syntactically valid encodings of one or more rows, without a width check. -/
def rawFormatLanguage : Language (Symbol A) :=
  ({[Symbol.separator]} : Language (Symbol A)) *
    (blockLanguage * blocksLanguage)

theorem rawFormatLanguage_isRegular : rawFormatLanguage (A := A).IsRegular :=
  (Language.isRegular_singleton_word [Symbol.separator]).mul'
    (blockLanguage_isRegular.mul' blocksLanguage_isRegular)

theorem mem_rawFormatLanguage_iff (w : List (Symbol A)) :
    w ∈ rawFormatLanguage (A := A) ↔
      ∃ h : Rows A, RawRepresents h w := by
  rw [rawFormatLanguage, Language.mem_mul]
  constructor
  · rintro ⟨pre, hpre, suffix, hsuffix, rfl⟩
    change pre = [Symbol.separator] at hpre
    subst pre
    rw [Language.mem_mul] at hsuffix
    obtain ⟨firstBlock, hfirst, tailWord, htail, rfl⟩ := hsuffix
    obtain ⟨encodedFirst, rfl⟩ := (mem_blockLanguage_iff _).mp hfirst
    obtain ⟨tail, htail⟩ :=
      (mem_blocksLanguage_iff_exists_encodeAux false tailWord).mp htail
    refine ⟨⟨encodedFirst, tail⟩, ?_⟩
    simp [RawRepresents, encode, Rows.toList, encodeAux, orientRow, htail]
  · rintro ⟨⟨first, tail⟩, rfl⟩
    refine ⟨[Symbol.separator], Set.mem_singleton _,
      encodeAux true (first :: tail), ?_, ?_⟩
    · rw [Language.mem_mul]
      refine ⟨first.map Symbol.cell ++ [Symbol.separator],
        (mem_blockLanguage_iff _).mpr ⟨first, rfl⟩,
        encodeAux false tail, ?_, ?_⟩
      · exact (mem_blocksLanguage_iff_exists_encodeAux false _).mpr ⟨tail, rfl⟩
      · simp [encodeAux, orientRow, List.append_assoc]
    · simp [encode, Rows.toList, encodeAux, orientRow, List.append_assoc]

/-- Raw histories whose first row has width zero. -/
def emptyFirstLanguage : Language (Symbol A) :=
  ({[Symbol.separator, Symbol.separator]} : Language (Symbol A)) *
    blocksLanguage

theorem emptyFirstLanguage_isRegular : emptyFirstLanguage (A := A).IsRegular :=
  (Language.isRegular_singleton_word
    [Symbol.separator, Symbol.separator]).mul' blocksLanguage_isRegular

theorem mem_emptyFirstLanguage_iff (w : List (Symbol A)) :
    w ∈ emptyFirstLanguage (A := A) ↔
      ∃ h : Rows A, RawRepresents h w ∧ h.first = [] := by
  rw [emptyFirstLanguage, Language.mem_mul]
  constructor
  · rintro ⟨pre, hpre, suffix, hsuffix, rfl⟩
    change pre = [Symbol.separator, Symbol.separator] at hpre
    subst pre
    obtain ⟨tail, htail⟩ :=
      (mem_blocksLanguage_iff_exists_encodeAux false suffix).mp hsuffix
    refine ⟨⟨[], tail⟩, ?_, rfl⟩
    simp [RawRepresents, encode, Rows.toList, encodeAux, orientRow, htail]
  · rintro ⟨⟨first, tail⟩, hraw, hfirst⟩
    change first = [] at hfirst
    subst first
    refine ⟨[Symbol.separator, Symbol.separator], Set.mem_singleton _,
      encodeAux false tail,
      (mem_blocksLanguage_iff_exists_encodeAux false _).mpr ⟨tail, rfl⟩, ?_⟩
    simpa [RawRepresents, encode, Rows.toList, encodeAux, orientRow] using hraw

/-- Prefix ending immediately before an even-indexed selected row. -/
def evenPrefixLanguage : Language (Symbol A) :=
  ({[Symbol.separator]} : Language (Symbol A)) *
    KStar.kstar (blockLanguage (A := A) * blockLanguage)

/-- Prefix ending immediately before an odd-indexed selected row. -/
def oddPrefixLanguage : Language (Symbol A) :=
  evenPrefixLanguage * blockLanguage

theorem evenPrefixLanguage_isRegular : evenPrefixLanguage (A := A).IsRegular :=
  (Language.isRegular_singleton_word [Symbol.separator]).mul'
    ((blockLanguage_isRegular.mul' blockLanguage_isRegular).kstar')

theorem oddPrefixLanguage_isRegular : oddPrefixLanguage (A := A).IsRegular :=
  evenPrefixLanguage_isRegular.mul' blockLanguage_isRegular

def rowsOfPairs (pairs : List (List A × List A)) : List (List A) :=
  pairs.flatMap fun p => [p.1, p.2]

@[simp] theorem encodeAux_rowsOfPairs_append
    (pairs : List (List A × List A)) (tail : List (List A)) :
    encodeAux true (rowsOfPairs pairs ++ tail) =
      encodeAux true (rowsOfPairs pairs) ++ encodeAux true tail := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
      rcases p with ⟨old, new⟩
      simp only [rowsOfPairs, List.flatMap_cons, List.append_assoc]
      simp [encodeAux, orientRow, List.append_assoc]
      simpa only [rowsOfPairs] using ih

@[simp] theorem encodeAux_rowsOfPairs (pairs : List (List A × List A)) :
    encodeAux true (rowsOfPairs pairs) =
      (pairs.map fun p =>
        (p.1.map Symbol.cell ++ [Symbol.separator]) ++
          (p.2.reverse.map Symbol.cell ++ [Symbol.separator])).flatten := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
      rcases p with ⟨old, new⟩
      simp only [rowsOfPairs, List.flatMap_cons, List.map_cons,
        List.flatten_cons]
      simp [encodeAux, orientRow, List.map_reverse,
        List.append_assoc]
      simpa only [rowsOfPairs, List.map_reverse, List.append_assoc,
        List.singleton_append] using ih

theorem mem_evenPrefixLanguage_iff (w : List (Symbol A)) :
    w ∈ evenPrefixLanguage (A := A) ↔
      ∃ pairs : List (List A × List A),
        w = Symbol.separator :: encodeAux true (rowsOfPairs pairs) := by
  rw [evenPrefixLanguage, Language.mem_mul]
  constructor
  · rintro ⟨pre, hpre, chunksWord, hchunks, rfl⟩
    change pre = [Symbol.separator] at hpre
    subst pre
    rw [Language.mem_kstar] at hchunks
    obtain ⟨chunks, rfl, hchunks⟩ := hchunks
    have hpairs : ∃ pairs : List (List A × List A),
        chunks.flatten =
          (pairs.map fun p =>
            (p.1.map Symbol.cell ++ [Symbol.separator]) ++
              (p.2.reverse.map Symbol.cell ++ [Symbol.separator])).flatten := by
      induction chunks with
      | nil => exact ⟨[], rfl⟩
      | cons chunk chunks ih =>
          have hchunk := hchunks chunk (by simp)
          rw [Language.mem_mul] at hchunk
          obtain ⟨left, hleft, right, hright, rfl⟩ := hchunk
          obtain ⟨old, rfl⟩ := (mem_blockLanguage_iff _).mp hleft
          obtain ⟨encodedNew, rfl⟩ := (mem_blockLanguage_iff _).mp hright
          obtain ⟨pairs, hpairs⟩ := ih (fun c hc => hchunks c (by simp [hc]))
          refine ⟨(old, encodedNew.reverse) :: pairs, ?_⟩
          simp [hpairs, List.append_assoc]
    obtain ⟨pairs, hpairs⟩ := hpairs
    refine ⟨pairs, ?_⟩
    rw [encodeAux_rowsOfPairs]
    exact congrArg (Symbol.separator :: ·) hpairs
  · rintro ⟨pairs, rfl⟩
    refine ⟨[Symbol.separator], Set.mem_singleton _,
      encodeAux true (rowsOfPairs pairs), ?_, rfl⟩
    rw [Language.mem_kstar]
    let chunks := pairs.map fun p =>
      (p.1.map Symbol.cell ++ [Symbol.separator]) ++
        (p.2.reverse.map Symbol.cell ++ [Symbol.separator])
    refine ⟨chunks, ?_, ?_⟩
    · exact encodeAux_rowsOfPairs pairs
    · intro chunk hchunk
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hchunk
      rw [Language.mem_mul]
      exact ⟨p.1.map Symbol.cell ++ [Symbol.separator],
        (mem_blockLanguage_iff _).mpr ⟨p.1, rfl⟩,
        p.2.reverse.map Symbol.cell ++ [Symbol.separator],
        (mem_blockLanguage_iff _).mpr ⟨p.2.reverse, rfl⟩, rfl⟩

theorem mem_oddPrefixLanguage_iff (w : List (Symbol A)) :
    w ∈ oddPrefixLanguage (A := A) ↔
      ∃ (pairs : List (List A × List A)) (last : List A),
        w = Symbol.separator ::
          encodeAux true (rowsOfPairs pairs ++ [last]) := by
  rw [oddPrefixLanguage, Language.mem_mul]
  constructor
  · rintro ⟨evenWord, heven, lastBlock, hlast, rfl⟩
    obtain ⟨pairs, rfl⟩ := (mem_evenPrefixLanguage_iff _).mp heven
    obtain ⟨last, rfl⟩ := (mem_blockLanguage_iff _).mp hlast
    refine ⟨pairs, last, ?_⟩
    simp [encodeAux_rowsOfPairs_append, encodeAux, orientRow]
  · rintro ⟨pairs, last, rfl⟩
    refine ⟨Symbol.separator :: encodeAux true (rowsOfPairs pairs),
      (mem_evenPrefixLanguage_iff _).mpr ⟨pairs, rfl⟩,
      last.map Symbol.cell ++ [Symbol.separator],
      (mem_blockLanguage_iff _).mpr ⟨last, rfl⟩, ?_⟩
    simp [encodeAux_rowsOfPairs_append, encodeAux, orientRow]

end ContextFree.MalformedHistories
