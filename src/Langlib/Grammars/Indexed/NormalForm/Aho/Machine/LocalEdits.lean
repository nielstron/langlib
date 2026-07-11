module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.BoundaryScans

@[expose]
public section

/-!
# Local padded-row edits

Finite one/two-cell edit certificates and their regular left-to-right checker.
-/

open List

variable {T : Type}

namespace IndexedGrammar
namespace Aho

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

