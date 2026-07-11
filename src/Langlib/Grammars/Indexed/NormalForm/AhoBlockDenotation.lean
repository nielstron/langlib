module

public import Langlib.Grammars.Indexed.NormalForm.AhoCorrectness

@[expose]
public section

/-!
# Mark-aware block denotation for Aho's work tape

Compressed indices must be interpreted as separate visible stack blocks.  Flags omitted by a
`plainPushSkip` move are ghost gaps between those blocks: flattening the visible blocks loses the
position of such a gap and makes `plainPushUse` followed by `popPlain` impossible to justify.

The `continues` bit is Aho's first/later distinction (`IndexMark.later`).  A continuing block has
no hidden gap after it and exposes another live block when popped.  A first block may expose an
arbitrary hidden gap and therefore returns to a plain nonterminal.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace BlockDenotation

/-! ## Visible blocks and hidden decorations -/

/-- Concrete ghost information denoted by one compressed-index token. -/
public structure VisibleBlock (g : IndexedGrammar T) where
  flags : List g.flag
  continues : Bool

/-- Visible block stack, nearest compressed token first. -/
public abbrev VisibleStack (g : IndexedGrammar T) := List (VisibleBlock g)

mutual
  /-- A plain nonterminal may have an arbitrary hidden gap before the first visible block and
  after every non-continuing block. -/
  public def Decorates {g : IndexedGrammar T} : VisibleStack g → List g.flag → Prop
    | [], _ => True
    | block :: blocks, actual =>
        ∃ hidden rest,
          actual = hidden ++ block.flags ++ rest ∧
            if block.continues then LiveDecorates blocks rest
            else Decorates blocks rest

  /-- A live nonterminal starts with the first visible block.  Its following gap is controlled by
  that block's `continues` bit. -/
  public def LiveDecorates {g : IndexedGrammar T} : VisibleStack g → List g.flag → Prop
    | [], _ => False
    | block :: blocks, actual =>
        ∃ rest,
          actual = block.flags ++ rest ∧
            if block.continues then LiveDecorates blocks rest
            else Decorates blocks rest
end

/-- Mode-indexed wrapper used by generic preservation statements. -/
public def StackDecorates {g : IndexedGrammar T} (live : Bool)
    (blocks : VisibleStack g) (actual : List g.flag) : Prop :=
  if live then LiveDecorates blocks actual else Decorates blocks actual

namespace Decorates

/-- Add one unused flag to the leading hidden gap of a plain stack. -/
public theorem pushHidden {g : IndexedGrammar T} {blocks : VisibleStack g}
    {actual : List g.flag} (f : g.flag) (h : Decorates blocks actual) :
    Decorates blocks (f :: actual) := by
  cases blocks with
  | nil => trivial
  | cons block blocks =>
      rcases h with ⟨hidden, rest, rfl, htail⟩
      exact ⟨f :: hidden, rest, by simp, htail⟩

/-- A first used push turns a decorated plain stack into a live stack with a fresh first block. -/
public theorem pushFirst {g : IndexedGrammar T} {blocks : VisibleStack g}
    {actual : List g.flag} (f : g.flag) (h : Decorates blocks actual) :
    LiveDecorates (⟨[f], false⟩ :: blocks) (f :: actual) := by
  exact ⟨actual, by simp, h⟩

end Decorates

namespace LiveDecorates

/-- Forget that the first visible block is forced to start at the top of the actual stack. -/
public theorem toDecorates {g : IndexedGrammar T} {blocks : VisibleStack g}
    {actual : List g.flag} (h : LiveDecorates blocks actual) :
    Decorates blocks actual := by
  cases blocks with
  | nil => exact False.elim h
  | cons block blocks =>
      rcases h with ⟨rest, rfl, htail⟩
      exact ⟨[], rest, by simp, htail⟩

/-- A later used push creates a fresh continuing block above a live stack. -/
public theorem pushLater {g : IndexedGrammar T} {blocks : VisibleStack g}
    {actual : List g.flag} (f : g.flag) (h : LiveDecorates blocks actual) :
    LiveDecorates (⟨[f], true⟩ :: blocks) (f :: actual) := by
  exact ⟨actual, by simp, h⟩

/-- Compressing a new flag into the current visible block preserves its continuation bit and all
hidden gaps below it. -/
public theorem pushCompress {g : IndexedGrammar T}
    {old : VisibleBlock g} {blocks : VisibleStack g} {actual : List g.flag}
    (f : g.flag) (h : LiveDecorates (old :: blocks) actual) :
    LiveDecorates (⟨f :: old.flags, old.continues⟩ :: blocks) (f :: actual) := by
  rcases h with ⟨rest, rfl, htail⟩
  exact ⟨rest, by simp, htail⟩

/-- Pop a first/non-continuing block.  The remainder is a plain decorated stack. -/
public theorem popPlain {g : IndexedGrammar T}
    {block : VisibleBlock g} {blocks : VisibleStack g} {actual : List g.flag}
    (h : LiveDecorates (block :: blocks) actual) :
    ∃ rest, actual = block.flags ++ rest ∧ Decorates blocks rest := by
  rcases h with ⟨rest, hactual, htail⟩
  refine ⟨rest, hactual, ?_⟩
  cases hc : block.continues
  · simpa [hc] using htail
  · exact (by
      have hlive : LiveDecorates blocks rest := by simpa [hc] using htail
      exact hlive.toDecorates)

/-- Pop a continuing block.  Aho's `later=true` guard exposes a live decorated tail. -/
public theorem popLive {g : IndexedGrammar T}
    {block : VisibleBlock g} {blocks : VisibleStack g} {actual : List g.flag}
    (hcontinues : block.continues = true)
    (h : LiveDecorates (block :: blocks) actual) :
    ∃ rest, actual = block.flags ++ rest ∧ LiveDecorates blocks rest := by
  rcases h with ⟨rest, hactual, htail⟩
  exact ⟨rest, hactual, by simpa [hcontinues] using htail⟩

end LiveDecorates

/-! ## Delimiter-free segments -/

/-- Right-to-left denotation of one delimiter-free segment.  Visible indices build a block stack;
each nonterminal independently chooses the hidden gaps permitted by its plain/live decoration. -/
public inductive SegmentRep (g : IndexedGrammar T) [Fintype g.nt] :
    VisibleStack g → List (WorkSym g) → VisibleStack g → List g.ISym → Prop where
  | nil (inherited : VisibleStack g) : SegmentRep g inherited [] inherited []
  | terminal {inherited stack : VisibleStack g} {xs : List (WorkSym g)}
      {form : List g.ISym} (a : T)
      (tail : SegmentRep g inherited xs stack form) :
      SegmentRep g inherited (WorkSym.terminal a :: xs) stack
        (ISym.terminal a :: form)
  | plain {inherited stack : VisibleStack g} {xs : List (WorkSym g)}
      {form : List g.ISym} (A : g.nt) (actual : List g.flag)
      (decorates : Decorates stack actual)
      (tail : SegmentRep g inherited xs stack form) :
      SegmentRep g inherited (WorkSym.plain A :: xs) stack
        (ISym.indexed A actual :: form)
  | live {inherited stack : VisibleStack g} {xs : List (WorkSym g)}
      {form : List g.ISym} (A : g.nt) (actual : List g.flag)
      (decorates : LiveDecorates stack actual)
      (tail : SegmentRep g inherited xs stack form) :
      SegmentRep g inherited (WorkSym.live A :: xs) stack
        (ISym.indexed A actual :: form)
  | index {inherited stack : VisibleStack g} {xs : List (WorkSym g)}
      {form : List g.ISym} {R : CFlag g} (d : IndexMark)
      (flags : List g.flag) (denotes : CFlag.Denotes g flags R)
      (tail : SegmentRep g inherited xs stack form) :
      SegmentRep g inherited (WorkSym.index R d :: xs)
        (⟨flags, d.later⟩ :: stack) form

@[simp] public theorem segmentRep_nil_iff
    (g : IndexedGrammar T) [Fintype g.nt]
    {inherited before : VisibleStack g} {form : List g.ISym} :
    SegmentRep g inherited [] before form ↔ before = inherited ∧ form = [] := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact SegmentRep.nil _

/-- Splitting a segment exposes the intermediate visible block stack and splits its form. -/
public theorem segmentRep_append_iff
    {g : IndexedGrammar T} [Fintype g.nt]
    (xs ys : List (WorkSym g))
    {inherited before : VisibleStack g} {form : List g.ISym} :
    SegmentRep g inherited (xs ++ ys) before form ↔
      ∃ middle leftForm rightForm,
        SegmentRep g inherited ys middle rightForm ∧
          SegmentRep g middle xs before leftForm ∧
          form = leftForm ++ rightForm := by
  induction xs generalizing inherited before form with
  | nil =>
      constructor
      · intro h
        exact ⟨before, [], form, h, SegmentRep.nil before, by simp⟩
      · rintro ⟨middle, leftForm, rightForm, hright, hleft, rfl⟩
        cases hleft
        simpa using hright
  | cons x xs ih =>
      cases x with
      | terminal a =>
          constructor
          · intro h
            cases h with
            | terminal _ tail =>
                rcases ih.mp tail with ⟨middle, lf, rf, hr, hl, hform⟩
                exact ⟨middle, ISym.terminal a :: lf, rf, hr,
                  SegmentRep.terminal a hl, by simp [hform]⟩
          · rintro ⟨middle, lf, rf, hr, hl, hform⟩
            cases hl with
            | terminal _ leftTail =>
                rw [hform]
                exact SegmentRep.terminal a
                  (ih.mpr ⟨middle, _, rf, hr, leftTail, rfl⟩)
      | plain A =>
          constructor
          · intro h
            cases h with
            | plain _ actual decorates tail =>
                rcases ih.mp tail with ⟨middle, lf, rf, hr, hl, hform⟩
                exact ⟨middle, ISym.indexed A actual :: lf, rf, hr,
                  SegmentRep.plain A actual decorates hl, by simp [hform]⟩
          · rintro ⟨middle, lf, rf, hr, hl, hform⟩
            cases hl with
            | plain _ actual decorates leftTail =>
                rw [hform]
                exact SegmentRep.plain A actual decorates
                  (ih.mpr ⟨middle, _, rf, hr, leftTail, rfl⟩)
      | live A =>
          constructor
          · intro h
            cases h with
            | live _ actual decorates tail =>
                rcases ih.mp tail with ⟨middle, lf, rf, hr, hl, hform⟩
                exact ⟨middle, ISym.indexed A actual :: lf, rf, hr,
                  SegmentRep.live A actual decorates hl, by simp [hform]⟩
          · rintro ⟨middle, lf, rf, hr, hl, hform⟩
            cases hl with
            | live _ actual decorates leftTail =>
                rw [hform]
                exact SegmentRep.live A actual decorates
                  (ih.mpr ⟨middle, _, rf, hr, leftTail, rfl⟩)
      | index R d =>
          constructor
          · intro h
            cases h with
            | index _ flags denotes tail =>
                rcases ih.mp tail with ⟨middle, lf, rf, hr, hl, hform⟩
                exact ⟨middle, lf, rf, hr,
                  SegmentRep.index d flags denotes hl, hform⟩
          · rintro ⟨middle, lf, rf, hr, hl, hform⟩
            cases hl with
            | index _ flags denotes leftTail =>
                rw [hform]
                exact SegmentRep.index d flags denotes
                  (ih.mpr ⟨middle, lf, rf, hr, leftTail, rfl⟩)
      | dollar =>
          constructor
          · intro h; cases h
          · rintro ⟨_, _, _, _, hleft, _⟩; cases hleft
      | close =>
          constructor
          · intro h; cases h
          · rintro ⟨_, _, _, _, hleft, _⟩; cases hleft
      | hash =>
          constructor
          · intro h; cases h
          · rintro ⟨_, _, _, _, hleft, _⟩; cases hleft

/-- Index-free segments preserve the visible inherited block stack. -/
public theorem SegmentRep.stack_eq_of_indexFree
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited before : VisibleStack g} {xs : List (WorkSym g)}
    {form : List g.ISym} (hfree : IndexFree xs)
    (h : SegmentRep g inherited xs before form) : before = inherited := by
  induction h with
  | nil => rfl
  | terminal a tail ih =>
      exact ih (fun R d hm => hfree R d (List.mem_cons_of_mem _ hm))
  | plain A actual decorates tail ih =>
      exact ih (fun R d hm => hfree R d (List.mem_cons_of_mem _ hm))
  | live A actual decorates tail ih =>
      exact ih (fun R d hm => hfree R d (List.mem_cons_of_mem _ hm))
  | index d flags denotes tail ih =>
      rename_i R
      exact False.elim (hfree R d (by simp))

/-- Changing an index mark without changing its first/later bit preserves the denotation. -/
public theorem SegmentRep.changeIndexMark
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited stack : VisibleStack g} {xs : List (WorkSym g)}
    {form : List g.ISym} {R : CFlag g} {d e : IndexMark}
    (hlater : d.later = e.later)
    (h : SegmentRep g inherited (WorkSym.index R d :: xs) stack form) :
    SegmentRep g inherited (WorkSym.index R e :: xs) stack form := by
  cases h with
  | index _ flags denotes tail =>
      simpa [hlater] using SegmentRep.index e flags denotes tail

public theorem IndexMark.later_markUsed (d : IndexMark) :
    d.markUsed.later = d.later := by
  cases d <;> rfl

/-! ## Nested frame layout -/

public abbrev FrameBoundary (g : IndexedGrammar T) :=
  List (WorkSym g) × List (WorkSym g)

public def frameLeft (g : IndexedGrammar T) : List (FrameBoundary g) → List (WorkSym g)
  | [] => [WorkSym.dollar]
  | (pending, _) :: frames =>
      WorkSym.dollar :: pending ++ frameLeft g frames

public def frameTail (g : IndexedGrammar T)
    (frames : List (FrameBoundary g)) : List (WorkSym g) :=
  frames.reverse.flatMap (fun frame => WorkSym.close :: frame.2) ++ [WorkSym.hash]

public def CursorLayout (g : IndexedGrammar T) (frames : List (FrameBoundary g))
    (current : List (WorkSym g)) (cursor : WorkCursor g) : Prop :=
  ∃ z zs,
    current ++ frameTail g frames = z :: zs ∧
      cursor.left = frameLeft g frames ∧ cursor.focus = z ∧ cursor.right = zs

public inductive NestedRep (g : IndexedGrammar T) [Fintype g.nt] :
    VisibleStack g → List (FrameBoundary g) → List (WorkSym g) →
      List g.ISym → Prop where
  | current {inherited before : VisibleStack g} {current : List (WorkSym g)}
      {form : List g.ISym}
      (segment : SegmentRep g inherited current before form) :
      NestedRep g inherited [] current form
  | frame {inherited tailStack pendingStack : VisibleStack g}
      {pending suffix current : List (WorkSym g)}
      {frames : List (FrameBoundary g)}
      {suffixForm pendingForm innerForm : List g.ISym}
      (suffixRep : SegmentRep g inherited suffix tailStack suffixForm)
      (pendingRep : SegmentRep g tailStack pending pendingStack pendingForm)
      (pendingEndsIndex : ∃ beta R d, pending = beta ++ [WorkSym.index R d])
      (innerRep : NestedRep g tailStack frames current innerForm) :
      NestedRep g inherited ((pending, suffix) :: frames) current
        (innerForm ++ pendingForm ++ suffixForm)

public def WorkCursor.Represents {g : IndexedGrammar T} [Fintype g.nt]
    (cursor : WorkCursor g) (form : List g.ISym) : Prop :=
  ∃ frames current,
    CursorLayout g frames current cursor ∧ NestedRep g [] frames current form

public def Config.Represents {g : IndexedGrammar T} [Fintype g.nt]
    (c : Config g) (form : List g.ISym) : Prop :=
  BlockDenotation.WorkCursor.Represents c.work form

/-! ## Boundary configurations -/

public theorem initialConfig_represents (g : IndexedGrammar T) [Fintype g.nt] :
    Config.Represents (initialConfig g) [ISym.indexed g.initial []] := by
  refine ⟨[], [WorkSym.plain g.initial], ?_, ?_⟩
  · refine ⟨WorkSym.plain g.initial, [WorkSym.hash], ?_, ?_, rfl, rfl⟩
    · simp [frameTail]
    · simp [initialConfig, frameLeft]
  · exact NestedRep.current
      (SegmentRep.plain g.initial [] (by trivial) (SegmentRep.nil []))

public theorem finalConfig_represents (g : IndexedGrammar T) [Fintype g.nt] (n : ℕ) :
    Config.Represents (finalConfig g n) [] := by
  refine ⟨[], [], ?_, ?_⟩
  · refine ⟨WorkSym.hash, [], ?_, ?_, rfl, rfl⟩
    · simp [frameTail]
    · simp [finalConfig, frameLeft]
  · exact NestedRep.current (SegmentRep.nil [])

end BlockDenotation
end Aho
end IndexedGrammar
