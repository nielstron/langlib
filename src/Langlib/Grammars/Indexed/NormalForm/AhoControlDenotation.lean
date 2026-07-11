module

public import Langlib.Grammars.Indexed.NormalForm.AhoBlockDenotation

@[expose]
public section

/-!
# Whole-tape denotation for Aho's close-crossing control stack

Stack visibility and execution order are deliberately separated. `PhysicalRep` scans the whole
physical tape right-to-left, ignoring control delimiters. `Exec` follows active symbols and the
`$`/`¢` return discipline to emit the remaining sentential form in execution order. This handles
later pops whose index-free scan crosses one or more `¢` markers.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace ControlDenotation

open BlockDenotation

/-! ## Mark-insensitive alignment -/

public def normalizeIndexMark (d : IndexMark) : IndexMark :=
  if d.later then .laterPending else .firstPending

@[simp] public theorem normalizeIndexMark_later (d : IndexMark) :
    (normalizeIndexMark d).later = d.later := by
  cases d <;> rfl

@[simp] public theorem normalizeIndexMark_markUsed (d : IndexMark) :
    normalizeIndexMark d.markUsed = normalizeIndexMark d := by
  cases d <;> rfl

public def normalizeWorkSym {g : IndexedGrammar T} : WorkSym g → WorkSym g
  | .index R d => .index R (normalizeIndexMark d)
  | z => z

@[simp] public theorem normalizeWorkSym_index {g : IndexedGrammar T}
    (R : CFlag g) (d : IndexMark) :
    normalizeWorkSym (WorkSym.index R d) =
      WorkSym.index R (normalizeIndexMark d) := rfl

@[simp] public theorem normalizeWorkSym_markUsed {g : IndexedGrammar T}
    (R : CFlag g) (d : IndexMark) :
    normalizeWorkSym (WorkSym.index R d.markUsed) =
      normalizeWorkSym (WorkSym.index R d) := by
  simp [normalizeWorkSym]

@[simp] public theorem normalizeWorkSym_markProductivePrefix
    {g : IndexedGrammar T} (alpha : List (WorkSym g)) :
    (markProductivePrefix alpha).map normalizeWorkSym =
      alpha.map normalizeWorkSym := by
  unfold markProductivePrefix
  cases hrev : alpha.reverse with
  | nil =>
      have halpha : alpha = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      simp [halpha]
  | cons z zs =>
      cases z with
      | index R d =>
          have halpha : alpha = (WorkSym.index R d :: zs).reverse := by
            rw [← hrev, List.reverse_reverse]
          subst alpha
          simp [List.map_reverse]
      | terminal a => simp
      | plain A => simp
      | live A => simp
      | dollar => simp
      | close => simp
      | hash => simp

@[simp] public theorem indexFree_map_normalizeWorkSym
    {g : IndexedGrammar T} (xs : List (WorkSym g)) :
    IndexFree (xs.map normalizeWorkSym) ↔ IndexFree xs := by
  constructor
  · intro h R d hm
    exact h R (normalizeIndexMark d)
      (List.mem_map.mpr ⟨WorkSym.index R d, hm, rfl⟩)
  · intro h R d hm
    rcases List.mem_map.mp hm with ⟨z, hz, heq⟩
    cases z with
    | terminal a => cases heq
    | plain A => cases heq
    | live A => cases heq
    | index Q e => exact h Q e hz
    | dollar => cases heq
    | close => cases heq
    | hash => cases heq

@[simp] public theorem dollarFree_map_normalizeWorkSym
    {g : IndexedGrammar T} (xs : List (WorkSym g)) :
    DollarFree (xs.map normalizeWorkSym) ↔ DollarFree xs := by
  constructor
  · intro h hm
    exact h (List.mem_map.mpr ⟨WorkSym.dollar, hm, rfl⟩)
  · intro h hm
    rcases List.mem_map.mp hm with ⟨z, hz, heq⟩
    cases z with
    | terminal a => cases heq
    | plain A => cases heq
    | live A => cases heq
    | index Q e => cases heq
    | dollar => exact h hz
    | close => cases heq
    | hash => cases heq

@[simp] public theorem normalizeWorkSym_ne_dollar_iff
    {g : IndexedGrammar T} (z : WorkSym g) :
    normalizeWorkSym z ≠ WorkSym.dollar ↔ z ≠ WorkSym.dollar := by
  cases z <;> simp [normalizeWorkSym]

public def normalizeCursor {g : IndexedGrammar T} (cursor : WorkCursor g) : WorkCursor g :=
  ⟨cursor.left.map normalizeWorkSym, normalizeWorkSym cursor.focus,
    cursor.right.map normalizeWorkSym⟩

/-- Ghost work symbols. An index remembers its denoted concrete block and only its first/later
class; the operational pending/used bit has no semantic content. -/
public inductive AnnSym (g : IndexedGrammar T) [Fintype g.nt] where
  | terminal : T → AnnSym g
  | plain : g.nt → List g.flag → AnnSym g
  | live : g.nt → List g.flag → AnnSym g
  | index (R : CFlag g) (continues : Bool) (flags : List g.flag)
      (denotes : CFlag.Denotes g flags R) : AnnSym g
  | dollar : AnnSym g
  | close : AnnSym g
  | hash : AnnSym g

public def AnnSym.erase {g : IndexedGrammar T} [Fintype g.nt] : AnnSym g → WorkSym g
  | .terminal a => .terminal a
  | .plain A _ => .plain A
  | .live A _ => .live A
  | .index R false _ _ => .index R .firstPending
  | .index R true _ _ => .index R .laterPending
  | .dollar => .dollar
  | .close => .close
  | .hash => .hash

public structure AnnCursor (g : IndexedGrammar T) [Fintype g.nt] where
  left : List (AnnSym g)
  focus : AnnSym g
  right : List (AnnSym g)

public def AnnCursor.word {g : IndexedGrammar T} [Fintype g.nt]
    (cursor : AnnCursor g) : List (AnnSym g) :=
  cursor.left ++ cursor.focus :: cursor.right

public def AnnCursor.erase {g : IndexedGrammar T} [Fintype g.nt]
    (cursor : AnnCursor g) : WorkCursor g :=
  ⟨cursor.left.map AnnSym.erase, cursor.focus.erase,
    cursor.right.map AnnSym.erase⟩

/-! ## Physical stack assignment -/

public inductive PhysicalRep (g : IndexedGrammar T) [Fintype g.nt] :
    VisibleStack g → List (AnnSym g) → VisibleStack g → Prop where
  | nil (inherited : VisibleStack g) : PhysicalRep g inherited [] inherited
  | terminal {inherited stack : VisibleStack g} {xs : List (AnnSym g)}
      (a : T) (tail : PhysicalRep g inherited xs stack) :
      PhysicalRep g inherited (AnnSym.terminal a :: xs) stack
  | plain {inherited stack : VisibleStack g} {xs : List (AnnSym g)}
      (A : g.nt) (actual : List g.flag) (decorates : Decorates stack actual)
      (tail : PhysicalRep g inherited xs stack) :
      PhysicalRep g inherited (AnnSym.plain A actual :: xs) stack
  | live {inherited stack : VisibleStack g} {xs : List (AnnSym g)}
      (A : g.nt) (actual : List g.flag) (decorates : LiveDecorates stack actual)
      (tail : PhysicalRep g inherited xs stack) :
      PhysicalRep g inherited (AnnSym.live A actual :: xs) stack
  | index {inherited stack : VisibleStack g} {xs : List (AnnSym g)}
      (R : CFlag g) (continues : Bool) (flags : List g.flag)
      (denotes : CFlag.Denotes g flags R)
      (tail : PhysicalRep g inherited xs stack) :
      PhysicalRep g inherited (AnnSym.index R continues flags denotes :: xs)
        (⟨flags, continues⟩ :: stack)
  | dollar {inherited stack : VisibleStack g} {xs : List (AnnSym g)}
      (tail : PhysicalRep g inherited xs stack) :
      PhysicalRep g inherited (AnnSym.dollar :: xs) stack
  | close {inherited stack : VisibleStack g} {xs : List (AnnSym g)}
      (tail : PhysicalRep g inherited xs stack) :
      PhysicalRep g inherited (AnnSym.close :: xs) stack
  | hash {inherited stack : VisibleStack g} {xs : List (AnnSym g)}
      (tail : PhysicalRep g inherited xs stack) :
      PhysicalRep g inherited (AnnSym.hash :: xs) stack

public theorem physicalRep_append_iff
    {g : IndexedGrammar T} [Fintype g.nt]
    (xs ys : List (AnnSym g)) {inherited before : VisibleStack g} :
    PhysicalRep g inherited (xs ++ ys) before ↔
      ∃ middle, PhysicalRep g inherited ys middle ∧
        PhysicalRep g middle xs before := by
  induction xs generalizing inherited before with
  | nil =>
      constructor
      · intro h; exact ⟨before, h, PhysicalRep.nil before⟩
      · rintro ⟨middle, hr, hl⟩; cases hl; exact hr
  | cons x xs ih =>
      cases x with
      | terminal a =>
          constructor
          · intro h; cases h with
            | terminal _ tail =>
                rcases ih.mp tail with ⟨middle, hr, hl⟩
                exact ⟨middle, hr, PhysicalRep.terminal a hl⟩
          · rintro ⟨middle, hr, hl⟩; cases hl with
            | terminal _ tail => exact PhysicalRep.terminal a (ih.mpr ⟨middle, hr, tail⟩)
      | plain A actual =>
          constructor
          · intro h; cases h with
            | plain _ _ decorates tail =>
                rcases ih.mp tail with ⟨middle, hr, hl⟩
                exact ⟨middle, hr, PhysicalRep.plain A actual decorates hl⟩
          · rintro ⟨middle, hr, hl⟩; cases hl with
            | plain _ _ decorates tail =>
                exact PhysicalRep.plain A actual decorates (ih.mpr ⟨middle, hr, tail⟩)
      | live A actual =>
          constructor
          · intro h; cases h with
            | live _ _ decorates tail =>
                rcases ih.mp tail with ⟨middle, hr, hl⟩
                exact ⟨middle, hr, PhysicalRep.live A actual decorates hl⟩
          · rintro ⟨middle, hr, hl⟩; cases hl with
            | live _ _ decorates tail =>
                exact PhysicalRep.live A actual decorates (ih.mpr ⟨middle, hr, tail⟩)
      | index R continues flags denotes =>
          constructor
          · intro h; cases h with
            | index _ _ _ _ tail =>
                rcases ih.mp tail with ⟨middle, hr, hl⟩
                exact ⟨middle, hr, PhysicalRep.index R continues flags denotes hl⟩
          · rintro ⟨middle, hr, hl⟩; cases hl with
            | index _ _ _ _ tail =>
                exact PhysicalRep.index R continues flags denotes (ih.mpr ⟨middle, hr, tail⟩)
      | dollar =>
          constructor
          · intro h; cases h with
            | dollar tail =>
                rcases ih.mp tail with ⟨middle, hr, hl⟩
                exact ⟨middle, hr, PhysicalRep.dollar hl⟩
          · rintro ⟨middle, hr, hl⟩; cases hl with
            | dollar tail => exact PhysicalRep.dollar (ih.mpr ⟨middle, hr, tail⟩)
      | close =>
          constructor
          · intro h; cases h with
            | close tail =>
                rcases ih.mp tail with ⟨middle, hr, hl⟩
                exact ⟨middle, hr, PhysicalRep.close hl⟩
          · rintro ⟨middle, hr, hl⟩; cases hl with
            | close tail => exact PhysicalRep.close (ih.mpr ⟨middle, hr, tail⟩)
      | hash =>
          constructor
          · intro h; cases h with
            | hash tail =>
                rcases ih.mp tail with ⟨middle, hr, hl⟩
                exact ⟨middle, hr, PhysicalRep.hash hl⟩
          · rintro ⟨middle, hr, hl⟩; cases hl with
            | hash tail => exact PhysicalRep.hash (ih.mpr ⟨middle, hr, tail⟩)

public def AnnIndexFree {g : IndexedGrammar T} [Fintype g.nt]
    (xs : List (AnnSym g)) : Prop :=
  ∀ R continues flags denotes, AnnSym.index R continues flags denotes ∉ xs

public theorem PhysicalRep.stack_eq_of_indexFree
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited before : VisibleStack g} {xs : List (AnnSym g)}
    (hfree : AnnIndexFree xs) (h : PhysicalRep g inherited xs before) :
    before = inherited := by
  induction h with
  | nil => rfl
  | terminal a tail ih => exact ih (fun R c fs den hm => hfree R c fs den (by simp [hm]))
  | plain A actual decorates tail ih =>
      exact ih (fun R c fs den hm => hfree R c fs den (by simp [hm]))
  | live A actual decorates tail ih =>
      exact ih (fun R c fs den hm => hfree R c fs den (by simp [hm]))
  | index R continues flags denotes tail ih =>
      exact False.elim (hfree R continues flags denotes (by simp))
  | dollar tail ih => exact ih (fun R c fs den hm => hfree R c fs den (by simp [hm]))
  | close tail ih => exact ih (fun R c fs den hm => hfree R c fs den (by simp [hm]))
  | hash tail ih => exact ih (fun R c fs den hm => hfree R c fs den (by simp [hm]))

/-! ## Shrinking execution-order interpreter -/

/-- Traverse active symbols in machine order. Every recursive cursor is shorter: an ordinary or
index step deletes its focus, and a return step deletes one `$`/`¢` pair. -/
public inductive Exec (g : IndexedGrammar T) [Fintype g.nt] :
    AnnCursor g → List g.ISym → Prop where
  | done : Exec g ⟨[AnnSym.dollar], AnnSym.hash, []⟩ []
  | terminal {left : List (AnnSym g)} {next : AnnSym g} {right : List (AnnSym g)}
      {form : List g.ISym} (a : T)
      (tail : Exec g ⟨left, next, right⟩ form) :
      Exec g ⟨left, AnnSym.terminal a, next :: right⟩ (ISym.terminal a :: form)
  | plain {left : List (AnnSym g)} {next : AnnSym g} {right : List (AnnSym g)}
      {form : List g.ISym} (A : g.nt) (actual : List g.flag)
      (tail : Exec g ⟨left, next, right⟩ form) :
      Exec g ⟨left, AnnSym.plain A actual, next :: right⟩
        (ISym.indexed A actual :: form)
  | live {left : List (AnnSym g)} {next : AnnSym g} {right : List (AnnSym g)}
      {form : List g.ISym} (A : g.nt) (actual : List g.flag)
      (tail : Exec g ⟨left, next, right⟩ form) :
      Exec g ⟨left, AnnSym.live A actual, next :: right⟩
        (ISym.indexed A actual :: form)
  | index {left : List (AnnSym g)} {next : AnnSym g} {right : List (AnnSym g)}
      {form : List g.ISym} (R : CFlag g) (continues : Bool) (flags : List g.flag)
      (denotes : CFlag.Denotes g flags R)
      (tail : Exec g ⟨left, next, right⟩ form) :
      Exec g ⟨left, AnnSym.index R continues flags denotes, next :: right⟩ form
  | returnFrame {alpha beta gamma : List (AnnSym g)} {Z : AnnSym g}
      {form : List g.ISym} (hfree : AnnSym.dollar ∉ beta)
      (tail : Exec g ⟨alpha ++ [AnnSym.dollar], Z, beta ++ gamma⟩ form) :
      Exec g
        ⟨alpha ++ [AnnSym.dollar, Z] ++ beta ++ [AnnSym.dollar],
          AnnSym.close, gamma⟩ form

/-!
## Active-right stack semantics

Only symbols to the right of the active focus index that occurrence. A `close` does not stop the
scan: this is exactly how a later pop reaches a lower block across completed inner frames. When a
frame returns, `ExecRep.returnFrame` reactivates its saved left material and the right stack is
recomputed in that new cursor, preventing an inner consumed block from leaking across older `$`
scopes.
-/

public inductive RightRep (g : IndexedGrammar T) [Fintype g.nt] :
    List (WorkSym g) → VisibleStack g → Prop where
  | nil : RightRep g [] []
  | terminal {xs : List (WorkSym g)} {stack : VisibleStack g} (a : T)
      (tail : RightRep g xs stack) :
      RightRep g (WorkSym.terminal a :: xs) stack
  | plain {xs : List (WorkSym g)} {stack : VisibleStack g} (A : g.nt)
      (tail : RightRep g xs stack) :
      RightRep g (WorkSym.plain A :: xs) stack
  | live {xs : List (WorkSym g)} {stack : VisibleStack g} (A : g.nt)
      (tail : RightRep g xs stack) :
      RightRep g (WorkSym.live A :: xs) stack
  | index {xs : List (WorkSym g)} {stack : VisibleStack g}
      (R : CFlag g) (d : IndexMark) (flags : List g.flag)
      (denotes : CFlag.Denotes g flags R) (tail : RightRep g xs stack) :
      RightRep g (WorkSym.index R d :: xs) (⟨flags, d.later⟩ :: stack)
  | close {xs : List (WorkSym g)} {stack : VisibleStack g}
      (tail : RightRep g xs stack) : RightRep g (WorkSym.close :: xs) stack
  | hash {xs : List (WorkSym g)} {stack : VisibleStack g}
      (tail : RightRep g xs stack) : RightRep g (WorkSym.hash :: xs) stack

/-- A right-stack prefix transformer, used to split at a selected compressed token without
inventing annotations for ordinary symbols. -/
public inductive RightPrefix (g : IndexedGrammar T) [Fintype g.nt] :
    List (WorkSym g) → VisibleStack g → VisibleStack g → Prop where
  | nil (stack : VisibleStack g) : RightPrefix g [] stack stack
  | terminal {xs : List (WorkSym g)} {before after : VisibleStack g} (a : T)
      (tail : RightPrefix g xs before after) :
      RightPrefix g (WorkSym.terminal a :: xs) before after
  | plain {xs : List (WorkSym g)} {before after : VisibleStack g} (A : g.nt)
      (tail : RightPrefix g xs before after) :
      RightPrefix g (WorkSym.plain A :: xs) before after
  | live {xs : List (WorkSym g)} {before after : VisibleStack g} (A : g.nt)
      (tail : RightPrefix g xs before after) :
      RightPrefix g (WorkSym.live A :: xs) before after
  | index {xs : List (WorkSym g)} {before after : VisibleStack g}
      (R : CFlag g) (d : IndexMark) (flags : List g.flag)
      (denotes : CFlag.Denotes g flags R) (tail : RightPrefix g xs before after) :
      RightPrefix g (WorkSym.index R d :: xs) (⟨flags, d.later⟩ :: before) after
  | close {xs : List (WorkSym g)} {before after : VisibleStack g}
      (tail : RightPrefix g xs before after) :
      RightPrefix g (WorkSym.close :: xs) before after
  | hash {xs : List (WorkSym g)} {before after : VisibleStack g}
      (tail : RightPrefix g xs before after) :
      RightPrefix g (WorkSym.hash :: xs) before after

public theorem rightRep_append
    {g : IndexedGrammar T} [Fintype g.nt]
    {xs ys : List (WorkSym g)} {stack : VisibleStack g}
    (h : RightRep g (xs ++ ys) stack) :
    ∃ middle, RightRep g ys middle ∧ RightPrefix g xs stack middle := by
  induction xs generalizing stack with
  | nil => exact ⟨stack, h, RightPrefix.nil stack⟩
  | cons x xs ih =>
      cases x with
      | terminal a => cases h with
        | terminal _ tail =>
            rcases ih tail with ⟨middle, hr, hp⟩
            exact ⟨middle, hr, RightPrefix.terminal a hp⟩
      | plain A => cases h with
        | plain _ tail =>
            rcases ih tail with ⟨middle, hr, hp⟩
            exact ⟨middle, hr, RightPrefix.plain A hp⟩
      | live A => cases h with
        | live _ tail =>
            rcases ih tail with ⟨middle, hr, hp⟩
            exact ⟨middle, hr, RightPrefix.live A hp⟩
      | index R d => cases h with
        | index _ _ flags denotes tail =>
            rcases ih tail with ⟨middle, hr, hp⟩
            exact ⟨middle, hr, RightPrefix.index R d flags denotes hp⟩
      | dollar => cases h
      | close => cases h with
        | close tail =>
            rcases ih tail with ⟨middle, hr, hp⟩
            exact ⟨middle, hr, RightPrefix.close hp⟩
      | hash => cases h with
        | hash tail =>
            rcases ih tail with ⟨middle, hr, hp⟩
            exact ⟨middle, hr, RightPrefix.hash hp⟩

public theorem RightPrefix.stack_eq_of_indexFree
    {g : IndexedGrammar T} [Fintype g.nt]
    {xs : List (WorkSym g)} {before after : VisibleStack g}
    (hfree : IndexFree xs) (h : RightPrefix g xs before after) : before = after := by
  induction h with
  | nil => rfl
  | terminal a tail ih => exact ih (fun R d hm => hfree R d (by simp [hm]))
  | plain A tail ih => exact ih (fun R d hm => hfree R d (by simp [hm]))
  | live A tail ih => exact ih (fun R d hm => hfree R d (by simp [hm]))
  | index R d flags denotes tail ih => exact False.elim (hfree R d (by simp))
  | close tail ih => exact ih (fun R d hm => hfree R d (by simp [hm]))
  | hash tail ih => exact ih (fun R d hm => hfree R d (by simp [hm]))

public theorem RightPrefix.dollarFree
    {g : IndexedGrammar T} [Fintype g.nt]
    {xs : List (WorkSym g)} {before after : VisibleStack g}
    (h : RightPrefix g xs before after) : DollarFree xs := by
  induction h with
  | nil => simp [DollarFree]
  | terminal a tail ih => simpa [DollarFree] using ih
  | plain A tail ih => simpa [DollarFree] using ih
  | live A tail ih => simpa [DollarFree] using ih
  | index R d flags denotes tail ih => simpa [DollarFree] using ih
  | close tail ih => simpa [DollarFree] using ih
  | hash tail ih => simpa [DollarFree] using ih

public theorem RightPrefix.toRightRep
    {g : IndexedGrammar T} [Fintype g.nt]
    {xs ys : List (WorkSym g)} {before after : VisibleStack g}
    (hp : RightPrefix g xs before after) (hr : RightRep g ys after) :
    RightRep g (xs ++ ys) before := by
  induction hp with
  | nil => exact hr
  | terminal a tail ih => exact RightRep.terminal a (ih hr)
  | plain A tail ih => exact RightRep.plain A (ih hr)
  | live A tail ih => exact RightRep.live A (ih hr)
  | index R d flags denotes tail ih => exact RightRep.index R d flags denotes (ih hr)
  | close tail ih => exact RightRep.close (ih hr)
  | hash tail ih => exact RightRep.hash (ih hr)

/-- Execution traversal coupled to the concrete stack visible from every active focus. -/
public inductive ExecRep (g : IndexedGrammar T) [Fintype g.nt] :
    WorkCursor g → List g.ISym → Prop where
  | done : ExecRep g ⟨[WorkSym.dollar], WorkSym.hash, []⟩ []
  | terminal {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
      {form : List g.ISym} (a : T)
      (tail : ExecRep g ⟨left, next, right⟩ form) :
      ExecRep g ⟨left, WorkSym.terminal a, next :: right⟩ (ISym.terminal a :: form)
  | plain {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
      {form : List g.ISym} {stack : VisibleStack g}
      (A : g.nt) (actual : List g.flag)
      (rightRep : RightRep g (next :: right) stack)
      (decorates : Decorates stack actual)
      (tail : ExecRep g ⟨left, next, right⟩ form) :
      ExecRep g ⟨left, WorkSym.plain A, next :: right⟩
        (ISym.indexed A actual :: form)
  | live {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
      {form : List g.ISym} {stack : VisibleStack g}
      (A : g.nt) (actual : List g.flag)
      (rightRep : RightRep g (next :: right) stack)
      (decorates : LiveDecorates stack actual)
      (tail : ExecRep g ⟨left, next, right⟩ form) :
      ExecRep g ⟨left, WorkSym.live A, next :: right⟩
        (ISym.indexed A actual :: form)
  | index {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
      {form : List g.ISym} (R : CFlag g) (d : IndexMark)
      (tail : ExecRep g ⟨left, next, right⟩ form) :
      ExecRep g ⟨left, WorkSym.index R d, next :: right⟩ form
  | returnFrame {alpha beta gamma : List (WorkSym g)} {Z : WorkSym g}
      {form : List g.ISym} (hfree : DollarFree beta)
      (tail : ExecRep g ⟨alpha ++ [WorkSym.dollar], Z, beta ++ gamma⟩ form) :
      ExecRep g
        ⟨alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar],
          WorkSym.close, gamma⟩ form

/-- Whole-tape, execution-ordered cursor denotation. -/
public def WorkCursor.Represents {g : IndexedGrammar T} [Fintype g.nt]
    (cursor : WorkCursor g) (form : List g.ISym) : Prop :=
  ExecRep g (normalizeCursor cursor) form

public def Config.Represents {g : IndexedGrammar T} [Fintype g.nt]
    (c : Config g) (form : List g.ISym) : Prop :=
  ControlDenotation.WorkCursor.Represents c.work form

/-! ## Boundary configurations -/

public theorem initialConfig_represents (g : IndexedGrammar T) [Fintype g.nt] :
    Config.Represents (initialConfig g) [ISym.indexed g.initial []] := by
  exact ExecRep.plain g.initial [] (RightRep.hash RightRep.nil)
    (by trivial) ExecRep.done

public theorem finalConfig_represents (g : IndexedGrammar T) [Fintype g.nt] (n : ℕ) :
    Config.Represents (finalConfig g n) [] := by
  exact ExecRep.done

end ControlDenotation
end Aho
end IndexedGrammar
