module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem
public import Langlib.Automata.LinearBounded.RowEnumeration
public import Langlib.Automata.LinearBounded.ThreeMatchingReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# A local odometer chain with exponentially many sequential diamonds

This file gives a fixed finite-state row verifier whose width-`w` canonical states contain a
chain of `2 ^ w` diamonds.  A state carries one binary odometer row and a phase repeated in every
cell.  The protocol is

```
junction i -> branch i bit -> merge i -> junction (i + 1)
                                      -> final              (on overflow).
```

The repetition of the phase is intentional: it lets a single left-to-right finite-state scan
check the whole transition.  Counter advances use `RowNumeral.DigitCodec.succStep`, so this is a
local certified row relation rather than an arbitrary injection of a finite graph into rows.

On the canonical semantic states, the first two halves of each diamond are interleaved into two
directed matchings and all odometer advances form a third directed matching.  The resulting
`rowReachLanguage` has a uniform LBA presentation through the certified-row compiler.  We do **not** claim
that the compiler's larger graph of raw machine configurations retains the three-matching cover:
initialization, verifier sweeps, and return sweeps introduce additional administrative states.

Positive width is essential for this particular encoding because the repeated phase cannot be
stored in an empty row.  There is no lower bound on the work-cell alphabet beyond the explicitly
fixed finite alphabet below.
-/

namespace OdometerDiamondRowSystem

open Relation RowNumeral

/-! ## The fixed local verifier -/

/-- Control phase repeated in every cell of a well-formed semantic row. -/
public inductive Phase where
  | junction
  | branch (choice : Bool)
  | merge
  | final
  deriving DecidableEq, Fintype, Repr

/-- One row cell: a finite-control phase and one binary odometer digit. -/
public abbrev Cell := Phase × Bool

/-- Finite state of the one-pass transition verifier. -/
public inductive StepState where
  | start
  | enter (choice : Bool)
  | merge (choice : Bool)
  | advance (toFinal : Bool) (carryState : CarryState)
  | bad
  deriving DecidableEq, Fintype, Repr

/-- State of the regular final-row checker. -/
public inductive FinalState where
  | start
  | checking
  | bad
  deriving DecidableEq, Fintype, Repr

/-- The canonical binary digit codec. -/
public def bitCodec : DigitCodec Bool :=
  orderedCodec Bool

@[simp]
public theorem bitCodec_radix : bitCodec.radix = 2 := by
  simp [DigitCodec.radix]

public def checkCopy (expectedOld expectedNew : Phase)
    (old new : Cell) : Bool :=
  decide (old.1 = expectedOld ∧ new.1 = expectedNew ∧ new.2 = old.2)

/-- Check one aligned cell of a protocol step. -/
public def stepCell : StepState → Cell → Cell → Unit → StepState
  | .bad, _, _, _ => .bad
  | .start, old, new, _ =>
      match old.1, new.1 with
      | .junction, .branch choice =>
          if new.2 = old.2 then .enter choice else .bad
      | .branch choice, .merge =>
          if new.2 = old.2 then .merge choice else .bad
      | .merge, .junction =>
          .advance false (bitCodec.succStep .carry old.2 new.2)
      | .merge, .final =>
          .advance true (bitCodec.succStep .carry old.2 new.2)
      | _, _ => .bad
  | .enter choice, old, new, _ =>
      if checkCopy .junction (.branch choice) old new then .enter choice else .bad
  | .merge choice, old, new, _ =>
      if checkCopy (.branch choice) .merge old new then .merge choice else .bad
  | .advance toFinal carryState, old, new, _ =>
      let expectedNew := if toFinal then Phase.final else Phase.junction
      if old.1 = .merge ∧ new.1 = expectedNew then
        .advance toFinal (bitCodec.succStep carryState old.2 new.2)
      else
        .bad

/-- Accept exactly a completed copy step, a nonoverflowing advance to a junction, or an
overflowing advance to the final phase. -/
public def stepDone : StepState → Bool
  | .enter _ => true
  | .merge _ => true
  | .advance false .done => true
  | .advance true .carry => true
  | _ => false

/-- Check that every final-row cell has final phase and zero digit. -/
public def finalCell : FinalState → Cell → FinalState
  | .bad, _ => .bad
  | .start, cell | .checking, cell =>
      if cell = (Phase.final, false) then .checking else .bad

public def finalDone : FinalState → Bool
  | .checking => true
  | _ => false

/-- A single row system, independent of the eventual row width. -/
public def system : CertifiedRowSystem Cell Cell Unit StepState FinalState where
  inputCell := id
  stepStart := .start
  stepCell := stepCell
  stepDone := stepDone
  finalStart := .start
  finalCell := finalCell
  finalDone := finalDone

/-- The fixed system's nonempty row-reachability language has an input-sized LBA presentation. -/
public theorem rowReachLanguage_is_LBA_pos :
    is_LBA_pos system.rowReachLanguage :=
  CertifiedRowSystem.is_LBA_pos_rowReachLanguage system

/-! ## Canonical rows and local transition witnesses -/

/-- Attach one phase to every digit of a binary row. -/
public def phaseRow (phase : Phase) (digits : List Bool) : List Cell :=
  digits.map fun digit ↦ (phase, digit)

@[simp]
public theorem phaseRow_length (phase : Phase) (digits : List Bool) :
    (phaseRow phase digits).length = digits.length := by
  simp [phaseRow]

private theorem evalStep_enter_tail (choice : Bool) (digits : List Bool) :
    system.evalStep (.enter choice)
        (phaseRow .junction digits) (phaseRow (.branch choice) digits)
        (List.replicate digits.length ()) = some (.enter choice) := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
      simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
        CertifiedRowSystem.evalStep]
      change system.evalStep
        (stepCell (.enter choice) (.junction, digit) (.branch choice, digit) ())
        (phaseRow .junction digits) (phaseRow (.branch choice) digits)
        (List.replicate digits.length ()) = some (.enter choice)
      rw [show stepCell (.enter choice) (.junction, digit) (.branch choice, digit) () =
        .enter choice by simp [stepCell, checkCopy]]
      exact ih

private theorem evalStep_merge_tail (choice : Bool) (digits : List Bool) :
    system.evalStep (.merge choice)
        (phaseRow (.branch choice) digits) (phaseRow .merge digits)
        (List.replicate digits.length ()) = some (.merge choice) := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
      simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
        CertifiedRowSystem.evalStep]
      change system.evalStep
        (stepCell (.merge choice) (.branch choice, digit) (.merge, digit) ())
        (phaseRow (.branch choice) digits) (phaseRow .merge digits)
        (List.replicate digits.length ()) = some (.merge choice)
      rw [show stepCell (.merge choice) (.branch choice, digit) (.merge, digit) () =
        .merge choice by simp [stepCell, checkCopy]]
      exact ih

/-- A nonempty canonical junction row has both Boolean branch successors. -/
public theorem rowStep_enter {digits : List Bool} (hne : digits ≠ []) (choice : Bool) :
    system.RowStep (phaseRow .junction digits) (phaseRow (.branch choice) digits) := by
  obtain ⟨digit, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨List.replicate (digit :: tail).length (), .enter choice, ?_, rfl⟩
  simp only [phaseRow, List.map_cons]
  change system.evalStep
    (stepCell .start (.junction, digit) (.branch choice, digit) ())
    (phaseRow .junction tail) (phaseRow (.branch choice) tail)
    (List.replicate tail.length ()) = some (.enter choice)
  rw [show stepCell .start (.junction, digit) (.branch choice, digit) () =
    .enter choice by simp [stepCell]]
  exact evalStep_enter_tail choice tail

/-- Each nonempty canonical branch row copies into its merge row. -/
public theorem rowStep_merge {digits : List Bool} (hne : digits ≠ []) (choice : Bool) :
    system.RowStep (phaseRow (.branch choice) digits) (phaseRow .merge digits) := by
  obtain ⟨digit, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨List.replicate (digit :: tail).length (), .merge choice, ?_, rfl⟩
  simp only [phaseRow, List.map_cons]
  change system.evalStep
    (stepCell .start (.branch choice, digit) (.merge, digit) ())
    (phaseRow (.branch choice) tail) (phaseRow .merge tail)
    (List.replicate tail.length ()) = some (.merge choice)
  rw [show stepCell .start (.branch choice, digit) (.merge, digit) () =
    .merge choice by simp [stepCell]]
  exact evalStep_merge_tail choice tail

private theorem evalStep_advance_tail (toFinal : Bool) (carryState : CarryState)
    (old new : List Bool) :
    system.evalStep (.advance toFinal carryState)
        (phaseRow .merge old)
        (phaseRow (if toFinal then Phase.final else Phase.junction) new)
        (List.replicate old.length ()) =
      (bitCodec.evalSucc carryState old new).map (.advance toFinal) := by
  induction old generalizing new carryState with
  | nil =>
      cases new <;> rfl
  | cons digit old ih =>
      cases new with
      | nil => rfl
      | cons next new =>
          simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, DigitCodec.evalSucc, Option.map]
          change system.evalStep
            (stepCell (.advance toFinal carryState) (.merge, digit)
              ((if toFinal then .final else .junction), next) ())
            (phaseRow .merge old)
            (phaseRow (if toFinal then Phase.final else Phase.junction) new)
            (List.replicate old.length ()) =
              (bitCodec.evalSucc (bitCodec.succStep carryState digit next) old new).map
                (.advance toFinal)
          rw [show stepCell (.advance toFinal carryState) (.merge, digit)
              ((if toFinal then .final else .junction), next) () =
                .advance toFinal (bitCodec.succStep carryState digit next) by
            cases toFinal <;> simp [stepCell]]
          exact ih (bitCodec.succStep carryState digit next) new

private theorem evalStep_advance (toFinal : Bool) (old new : List Bool)
    (hne : old ≠ []) :
    system.evalStep .start
        (phaseRow .merge old)
        (phaseRow (if toFinal then Phase.final else Phase.junction) new)
        (List.replicate old.length ()) =
      (bitCodec.evalSucc .carry old new).map (.advance toFinal) := by
  obtain ⟨digit, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases new with
  | nil => rfl
  | cons next new =>
      simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
        CertifiedRowSystem.evalStep, DigitCodec.evalSucc, Option.map]
      change system.evalStep
        (stepCell .start (.merge, digit)
          ((if toFinal then .final else .junction), next) ())
        (phaseRow .merge tail)
        (phaseRow (if toFinal then Phase.final else Phase.junction) new)
        (List.replicate tail.length ()) =
          (bitCodec.evalSucc (bitCodec.succStep .carry digit next) tail new).map
            (.advance toFinal)
      rw [show stepCell .start (.merge, digit)
          ((if toFinal then .final else .junction), next) () =
            .advance toFinal (bitCodec.succStep .carry digit next) by
        cases toFinal <;> simp [stepCell]]
      exact evalStep_advance_tail toFinal (bitCodec.succStep .carry digit next) tail new

/-- A nonoverflowing binary odometer step is locally certified from merge to junction. -/
public theorem rowStep_advance {old : List Bool} (hne : old ≠ [])
    (hno : (bitCodec.increment old).2 = false) :
    system.RowStep (phaseRow .merge old)
      (phaseRow .junction (bitCodec.nextRow old)) := by
  let new := bitCodec.nextRow old
  refine ⟨List.replicate old.length (), .advance false .done, ?_, rfl⟩
  change system.evalStep .start (phaseRow .merge old) (phaseRow .junction new)
    (List.replicate old.length ()) = some (.advance false .done)
  rw [show Phase.junction = (if false then Phase.final else Phase.junction) by rfl,
    evalStep_advance false old new hne]
  have hs : bitCodec.evalSucc .carry old new = some .done := by
    simpa [new, DigitCodec.nextRow] using
      (bitCodec.evalSucc_eq_done_iff old (bitCodec.increment old).1).2 ⟨rfl, hno⟩
  rw [hs]
  rfl

/-- An overflowing binary odometer step is locally certified from merge to the final row. -/
public theorem rowStep_final {old : List Bool} (hne : old ≠ [])
    (hover : (bitCodec.increment old).2 = true) :
    system.RowStep (phaseRow .merge old)
      (phaseRow .final (bitCodec.nextRow old)) := by
  let new := bitCodec.nextRow old
  refine ⟨List.replicate old.length (), .advance true .carry, ?_, rfl⟩
  change system.evalStep .start (phaseRow .merge old) (phaseRow .final new)
    (List.replicate old.length ()) = some (.advance true .carry)
  rw [show Phase.final = (if true then Phase.final else Phase.junction) by rfl,
    evalStep_advance true old new hne]
  have hs : bitCodec.evalSucc .carry old new = some .carry := by
    simpa [new, DigitCodec.nextRow] using
      (bitCodec.evalSucc_eq_carry_iff old (bitCodec.increment old).1).2 ⟨rfl, hover⟩
  rw [hs]
  rfl

/-! ### Exact behavior of the local verifier on well-formed rows -/

private theorem unitList_eq_replicate (cert : List Unit) :
    cert = List.replicate cert.length () := by
  induction cert with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simpa only [List.length_cons, List.replicate_succ] using
        congrArg (List.cons ()) ih

private theorem evalStep_bad_eq_some_imp (old new : List Cell) (cert : List Unit)
    {q : StepState} (heval : system.evalStep .bad old new cert = some q) : q = .bad := by
  induction old generalizing new cert q with
  | nil =>
      cases new <;> cases cert <;> simp [CertifiedRowSystem.evalStep] at heval
      simpa using heval.symm
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at heval
      | cons newHead newTail =>
          cases cert with
          | nil => simp [CertifiedRowSystem.evalStep] at heval
          | cons _ certTail =>
              apply ih newTail certTail
              simpa [CertifiedRowSystem.evalStep, system, stepCell] using heval

private theorem evalStep_enter_done_iff (choice : Bool) {old new : List Bool}
    (hlen : old.length = new.length) (q : StepState) :
    system.evalStep (.enter choice)
        (phaseRow .junction old) (phaseRow (.branch choice) new)
        (List.replicate old.length ()) = some q ∧ stepDone q = true ↔
      new = old ∧ q = .enter choice := by
  induction old generalizing new q with
  | nil =>
      cases new with
      | nil =>
          constructor
          · rintro ⟨heq, _⟩
            simpa [phaseRow, CertifiedRowSystem.evalStep] using heq.symm
          · rintro ⟨_, rfl⟩
            simp [phaseRow, CertifiedRowSystem.evalStep, stepDone]
      | cons _ _ => simp at hlen
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp at hlen
      | cons newHead newTail =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          by_cases hhead : newHead = oldHead
          · subst newHead
            simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep]
            change
              system.evalStep
                  (stepCell (.enter choice) (.junction, oldHead)
                    (.branch choice, oldHead) ())
                  (phaseRow .junction oldTail) (phaseRow (.branch choice) newTail)
                  (List.replicate oldTail.length ()) = some q ∧ stepDone q = true ↔ _
            rw [show stepCell (.enter choice) (.junction, oldHead)
                (.branch choice, oldHead) () = .enter choice by simp [stepCell, checkCopy]]
            simpa using ih hlen q
          · simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep]
            change
              system.evalStep
                  (stepCell (.enter choice) (.junction, oldHead)
                    (.branch choice, newHead) ())
                  (phaseRow .junction oldTail) (phaseRow (.branch choice) newTail)
                  (List.replicate oldTail.length ()) = some q ∧ stepDone q = true ↔ _
            rw [show stepCell (.enter choice) (.junction, oldHead)
                (.branch choice, newHead) () = .bad by simp [stepCell, checkCopy, hhead]]
            constructor
            · rintro ⟨heval, hdone⟩
              have hq := evalStep_bad_eq_some_imp _ _ _ heval
              subst q
              simp [stepDone] at hdone
            · rintro ⟨heq, _⟩
              exact (hhead (List.cons.inj heq).1).elim

private theorem evalStep_merge_done_iff (choice : Bool) {old new : List Bool}
    (hlen : old.length = new.length) (q : StepState) :
    system.evalStep (.merge choice)
        (phaseRow (.branch choice) old) (phaseRow .merge new)
        (List.replicate old.length ()) = some q ∧ stepDone q = true ↔
      new = old ∧ q = .merge choice := by
  induction old generalizing new q with
  | nil =>
      cases new with
      | nil =>
          constructor
          · rintro ⟨heq, _⟩
            simpa [phaseRow, CertifiedRowSystem.evalStep] using heq.symm
          · rintro ⟨_, rfl⟩
            simp [phaseRow, CertifiedRowSystem.evalStep, stepDone]
      | cons _ _ => simp at hlen
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp at hlen
      | cons newHead newTail =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          by_cases hhead : newHead = oldHead
          · subst newHead
            simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep]
            change
              system.evalStep
                  (stepCell (.merge choice) (.branch choice, oldHead) (.merge, oldHead) ())
                  (phaseRow (.branch choice) oldTail) (phaseRow .merge newTail)
                  (List.replicate oldTail.length ()) = some q ∧ stepDone q = true ↔ _
            rw [show stepCell (.merge choice) (.branch choice, oldHead)
                (.merge, oldHead) () = .merge choice by simp [stepCell, checkCopy]]
            simpa using ih hlen q
          · simp only [phaseRow, List.map_cons, List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep]
            change
              system.evalStep
                  (stepCell (.merge choice) (.branch choice, oldHead) (.merge, newHead) ())
                  (phaseRow (.branch choice) oldTail) (phaseRow .merge newTail)
                  (List.replicate oldTail.length ()) = some q ∧ stepDone q = true ↔ _
            rw [show stepCell (.merge choice) (.branch choice, oldHead)
                (.merge, newHead) () = .bad by simp [stepCell, checkCopy, hhead]]
            constructor
            · rintro ⟨heval, hdone⟩
              have hq := evalStep_bad_eq_some_imp _ _ _ heval
              subst q
              simp [stepDone] at hdone
            · rintro ⟨heq, _⟩
              exact (hhead (List.cons.inj heq).1).elim

private theorem canonicalCert {old new : List Cell} {cert : List Unit} {q : StepState}
    (heval : system.evalStep .start old new cert = some q) :
    cert = List.replicate old.length () := by
  have hlen := (system.evalStep_nil_iff heval).2
  calc
    cert = List.replicate cert.length () := unitList_eq_replicate cert
    _ = List.replicate old.length () := by rw [← hlen]

/-- Exact copy behavior from canonical junction rows to canonical branch rows. -/
public theorem rowStep_enter_iff {old new : List Bool} (hne : old ≠ [])
    (hlen : old.length = new.length) (choice : Bool) :
    system.RowStep (phaseRow .junction old) (phaseRow (.branch choice) new) ↔
      new = old := by
  constructor
  · rintro ⟨cert, q, heval, hdone⟩
    have hcert := canonicalCert heval
    subst cert
    obtain ⟨oldHead, oldTail, rfl⟩ := List.exists_cons_of_ne_nil hne
    cases new with
    | nil => simp at hlen
    | cons newHead newTail =>
        have heval' : system.evalStep .start
            (phaseRow .junction (oldHead :: oldTail))
            (phaseRow (.branch choice) (newHead :: newTail))
            (List.replicate (oldHead :: oldTail).length ()) = some q := by
          simpa [system] using heval
        simp only [phaseRow, List.map_cons] at heval'
        change system.evalStep
            (stepCell .start (.junction, oldHead) (.branch choice, newHead) ())
            (phaseRow .junction oldTail) (phaseRow (.branch choice) newTail)
            (List.replicate oldTail.length ()) = some q at heval'
        by_cases hhead : newHead = oldHead
        · subst newHead
          rw [show stepCell .start (.junction, oldHead) (.branch choice, oldHead) () =
            .enter choice by simp [stepCell]] at heval'
          have htail := (evalStep_enter_done_iff choice
            (by simpa using hlen) q).mp ⟨heval', hdone⟩
          simp [htail.1]
        · rw [show stepCell .start (.junction, oldHead) (.branch choice, newHead) () =
            .bad by simp [stepCell, hhead]] at heval'
          have hq := evalStep_bad_eq_some_imp _ _ _ heval'
          subst q
          change false = true at hdone
          contradiction
  · rintro rfl
    exact rowStep_enter hne choice

/-- Exact copy behavior from canonical branch rows to canonical merge rows. -/
public theorem rowStep_merge_iff {old new : List Bool} (hne : old ≠ [])
    (hlen : old.length = new.length) (choice : Bool) :
    system.RowStep (phaseRow (.branch choice) old) (phaseRow .merge new) ↔
      new = old := by
  constructor
  · rintro ⟨cert, q, heval, hdone⟩
    have hcert := canonicalCert heval
    subst cert
    obtain ⟨oldHead, oldTail, rfl⟩ := List.exists_cons_of_ne_nil hne
    cases new with
    | nil => simp at hlen
    | cons newHead newTail =>
        have heval' : system.evalStep .start
            (phaseRow (.branch choice) (oldHead :: oldTail))
            (phaseRow .merge (newHead :: newTail))
            (List.replicate (oldHead :: oldTail).length ()) = some q := by
          simpa [system] using heval
        simp only [phaseRow, List.map_cons] at heval'
        change system.evalStep
            (stepCell .start (.branch choice, oldHead) (.merge, newHead) ())
            (phaseRow (.branch choice) oldTail) (phaseRow .merge newTail)
            (List.replicate oldTail.length ()) = some q at heval'
        by_cases hhead : newHead = oldHead
        · subst newHead
          rw [show stepCell .start (.branch choice, oldHead) (.merge, oldHead) () =
            .merge choice by simp [stepCell]] at heval'
          have htail := (evalStep_merge_done_iff choice
            (by simpa using hlen) q).mp ⟨heval', hdone⟩
          simp [htail.1]
        · rw [show stepCell .start (.branch choice, oldHead) (.merge, newHead) () =
            .bad by simp [stepCell, hhead]] at heval'
          have hq := evalStep_bad_eq_some_imp _ _ _ heval'
          subst q
          change false = true at hdone
          contradiction
  · rintro rfl
    exact rowStep_merge hne choice

/-- Exact nonoverflowing behavior from canonical merge rows to canonical junction rows. -/
public theorem rowStep_advance_iff {old new : List Bool} (hne : old ≠ [])
    (hlen : old.length = new.length) :
    system.RowStep (phaseRow .merge old) (phaseRow .junction new) ↔
      new = bitCodec.nextRow old ∧ (bitCodec.increment old).2 = false := by
  constructor
  · rintro ⟨cert, q, heval, hdone⟩
    have hcert := canonicalCert heval
    subst cert
    have heval' : system.evalStep .start (phaseRow .merge old)
        (phaseRow .junction new) (List.replicate old.length ()) = some q := by
      simpa [system] using heval
    rw [show Phase.junction = (if false then Phase.final else Phase.junction) by rfl,
      evalStep_advance false old new hne] at heval'
    obtain ⟨carryState, hcarry, rfl⟩ := Option.map_eq_some_iff.mp heval'
    change stepDone (.advance false carryState) = true at hdone
    cases carryState with
    | carry => simp [stepDone] at hdone
    | done =>
        exact (bitCodec.evalSucc_eq_done_iff old new).mp hcarry
    | bad => simp [stepDone] at hdone
  · rintro ⟨rfl, hno⟩
    exact rowStep_advance hne hno

/-- Exact overflowing behavior from canonical merge rows to canonical final rows. -/
public theorem rowStep_final_iff {old new : List Bool} (hne : old ≠ [])
    (hlen : old.length = new.length) :
    system.RowStep (phaseRow .merge old) (phaseRow .final new) ↔
      new = bitCodec.nextRow old ∧ (bitCodec.increment old).2 = true := by
  constructor
  · rintro ⟨cert, q, heval, hdone⟩
    have hcert := canonicalCert heval
    subst cert
    have heval' : system.evalStep .start (phaseRow .merge old)
        (phaseRow .final new) (List.replicate old.length ()) = some q := by
      simpa [system] using heval
    rw [show Phase.final = (if true then Phase.final else Phase.junction) by rfl,
      evalStep_advance true old new hne] at heval'
    obtain ⟨carryState, hcarry, rfl⟩ := Option.map_eq_some_iff.mp heval'
    change stepDone (.advance true carryState) = true at hdone
    cases carryState with
    | carry =>
        exact (bitCodec.evalSucc_eq_carry_iff old new).mp hcarry
    | done => simp [stepDone] at hdone
    | bad => simp [stepDone] at hdone
  · rintro ⟨rfl, hover⟩
    exact rowStep_final hne hover

/-! ### Arbitrary accepted rows are well formed -/

private theorem evalStep_enter_shape (choice : Bool) {old new : List Cell}
    {cert : List Unit} {q : StepState}
    (heval : system.evalStep (.enter choice) old new cert = some q)
    (hdone : stepDone q = true) :
    ∃ bits, old = phaseRow .junction bits ∧ new = phaseRow (.branch choice) bits := by
  induction old generalizing new cert q with
  | nil =>
      cases new <;> cases cert <;> simp [CertifiedRowSystem.evalStep] at heval
      subst q
      exact ⟨[], rfl, rfl⟩
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at heval
      | cons newHead newTail =>
          cases cert with
          | nil => simp [CertifiedRowSystem.evalStep] at heval
          | cons _ certTail =>
              rcases oldHead with ⟨oldPhase, oldDigit⟩
              rcases newHead with ⟨newPhase, newDigit⟩
              by_cases hcheck : checkCopy .junction (.branch choice)
                  (oldPhase, oldDigit) (newPhase, newDigit) = true
              · have hfields : oldPhase = .junction ∧
                    newPhase = .branch choice ∧ newDigit = oldDigit := by
                  simpa [checkCopy] using hcheck
                rcases hfields with ⟨rfl, rfl, hdigit⟩
                subst newDigit
                have hevalTail : system.evalStep (.enter choice) oldTail newTail certTail =
                    some q := by
                  simpa [CertifiedRowSystem.evalStep, system, stepCell, checkCopy] using heval
                obtain ⟨bits, hold, hnew⟩ := ih hevalTail hdone
                refine ⟨oldDigit :: bits, ?_, ?_⟩
                · simp [phaseRow, hold]
                · simp [phaseRow, hnew]
              · have hevalBad : system.evalStep .bad oldTail newTail certTail = some q := by
                  simpa [CertifiedRowSystem.evalStep, system, stepCell, hcheck] using heval
                have hq := evalStep_bad_eq_some_imp _ _ _ hevalBad
                subst q
                simp [stepDone] at hdone

private theorem evalStep_merge_shape (choice : Bool) {old new : List Cell}
    {cert : List Unit} {q : StepState}
    (heval : system.evalStep (.merge choice) old new cert = some q)
    (hdone : stepDone q = true) :
    ∃ bits, old = phaseRow (.branch choice) bits ∧ new = phaseRow .merge bits := by
  induction old generalizing new cert q with
  | nil =>
      cases new <;> cases cert <;> simp [CertifiedRowSystem.evalStep] at heval
      subst q
      exact ⟨[], rfl, rfl⟩
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at heval
      | cons newHead newTail =>
          cases cert with
          | nil => simp [CertifiedRowSystem.evalStep] at heval
          | cons _ certTail =>
              rcases oldHead with ⟨oldPhase, oldDigit⟩
              rcases newHead with ⟨newPhase, newDigit⟩
              by_cases hcheck : checkCopy (.branch choice) .merge
                  (oldPhase, oldDigit) (newPhase, newDigit) = true
              · have hfields : oldPhase = .branch choice ∧
                    newPhase = .merge ∧ newDigit = oldDigit := by
                  simpa [checkCopy] using hcheck
                rcases hfields with ⟨rfl, rfl, hdigit⟩
                subst newDigit
                have hevalTail : system.evalStep (.merge choice) oldTail newTail certTail =
                    some q := by
                  simpa [CertifiedRowSystem.evalStep, system, stepCell, checkCopy] using heval
                obtain ⟨bits, hold, hnew⟩ := ih hevalTail hdone
                refine ⟨oldDigit :: bits, ?_, ?_⟩
                · simp [phaseRow, hold]
                · simp [phaseRow, hnew]
              · have hevalBad : system.evalStep .bad oldTail newTail certTail = some q := by
                  simpa [CertifiedRowSystem.evalStep, system, stepCell, hcheck] using heval
                have hq := evalStep_bad_eq_some_imp _ _ _ hevalBad
                subst q
                simp [stepDone] at hdone

private theorem evalStep_advance_shape (toFinal : Bool) (carryState : CarryState)
    {old new : List Cell} {cert : List Unit} {q : StepState}
    (heval : system.evalStep (.advance toFinal carryState) old new cert = some q)
    (hdone : stepDone q = true) :
    ∃ oldBits newBits finalCarry,
      old = phaseRow .merge oldBits ∧
        new = phaseRow (if toFinal then .final else .junction) newBits ∧
        bitCodec.evalSucc carryState oldBits newBits = some finalCarry ∧
        q = .advance toFinal finalCarry := by
  induction old generalizing new cert carryState q with
  | nil =>
      cases new <;> cases cert <;> simp [CertifiedRowSystem.evalStep] at heval
      subst q
      exact ⟨[], [], carryState, rfl, rfl, rfl, rfl⟩
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at heval
      | cons newHead newTail =>
          cases cert with
          | nil => simp [CertifiedRowSystem.evalStep] at heval
          | cons _ certTail =>
              rcases oldHead with ⟨oldPhase, oldDigit⟩
              rcases newHead with ⟨newPhase, newDigit⟩
              let expected := if toFinal then Phase.final else Phase.junction
              by_cases hphases : oldPhase = .merge ∧ newPhase = expected
              · rcases hphases with ⟨rfl, rfl⟩
                have hevalTail : system.evalStep
                    (.advance toFinal (bitCodec.succStep carryState oldDigit newDigit))
                    oldTail newTail certTail = some q := by
                  simpa [CertifiedRowSystem.evalStep, system, stepCell, expected] using heval
                obtain ⟨oldBits, newBits, finalCarry, hold, hnew, hsucc, hq⟩ :=
                  ih (bitCodec.succStep carryState oldDigit newDigit) hevalTail hdone
                refine ⟨oldDigit :: oldBits, newDigit :: newBits, finalCarry, ?_, ?_, ?_, hq⟩
                · simp [phaseRow, hold]
                · simp [phaseRow, hnew, expected]
                · simpa [DigitCodec.evalSucc] using hsucc
              · have hevalBad : system.evalStep .bad oldTail newTail certTail = some q := by
                  simpa [CertifiedRowSystem.evalStep, system, stepCell, expected, hphases] using heval
                have hq := evalStep_bad_eq_some_imp _ _ _ hevalBad
                subst q
                simp [stepDone] at hdone

/-- The four well-formed macrostep shapes checked by `system`. -/
public def ProtocolStep (old new : List Cell) : Prop :=
  (∃ choice bits, old = phaseRow .junction bits ∧
      new = phaseRow (.branch choice) bits) ∨
    (∃ choice bits, old = phaseRow (.branch choice) bits ∧
      new = phaseRow .merge bits) ∨
    (∃ oldBits newBits, old = phaseRow .merge oldBits ∧
      new = phaseRow .junction newBits ∧
      newBits = bitCodec.nextRow oldBits ∧ (bitCodec.increment oldBits).2 = false) ∨
    (∃ oldBits newBits, old = phaseRow .merge oldBits ∧
      new = phaseRow .final newBits ∧
      newBits = bitCodec.nextRow oldBits ∧ (bitCodec.increment oldBits).2 = true)

/-- On nonempty rows, the complete certified relation has exactly the four protocol shapes; in
particular malformed phase rows have no incident accepted step. -/
public theorem rowStep_iff_protocolStep {old new : List Cell} (hne : old ≠ []) :
    system.RowStep old new ↔ ProtocolStep old new := by
  constructor
  · rintro ⟨cert, q, heval, hdone⟩
    obtain ⟨oldHead, oldTail, rfl⟩ := List.exists_cons_of_ne_nil hne
    cases new with
    | nil => simp [CertifiedRowSystem.evalStep] at heval
    | cons newHead newTail =>
        cases cert with
        | nil => simp [CertifiedRowSystem.evalStep] at heval
        | cons _ certTail =>
            rcases oldHead with ⟨oldPhase, oldDigit⟩
            rcases newHead with ⟨newPhase, newDigit⟩
            replace heval : system.evalStep .start
                ((oldPhase, oldDigit) :: oldTail) ((newPhase, newDigit) :: newTail)
                (() :: certTail) = some q := by
              simpa [system] using heval
            simp only [CertifiedRowSystem.evalStep] at heval
            change system.evalStep
                (stepCell .start (oldPhase, oldDigit) (newPhase, newDigit) ())
                oldTail newTail certTail = some q at heval
            cases oldPhase <;> cases newPhase <;> simp only [stepCell] at heval
            all_goals try {
              have hq := evalStep_bad_eq_some_imp _ _ _ heval
              subst q
              change false = true at hdone
              contradiction }
            · rename_i choice
              split at heval
              · rename_i hdigit
                obtain ⟨bits, hold, hnew⟩ := evalStep_enter_shape choice heval hdone
                left
                refine ⟨choice, oldDigit :: bits, ?_, ?_⟩
                · simp [phaseRow, hold]
                · simp [phaseRow, hnew, hdigit]
              · have hq := evalStep_bad_eq_some_imp _ _ _ heval
                subst q
                change false = true at hdone
                contradiction
            · rename_i choice
              split at heval
              · rename_i hdigit
                obtain ⟨bits, hold, hnew⟩ := evalStep_merge_shape choice heval hdone
                right; left
                refine ⟨choice, oldDigit :: bits, ?_, ?_⟩
                · simp [phaseRow, hold]
                · simp [phaseRow, hnew, hdigit]
              · have hq := evalStep_bad_eq_some_imp _ _ _ heval
                subst q
                change false = true at hdone
                contradiction
            · obtain ⟨oldBits, newBits, finalCarry, hold, hnew, hsucc, hq⟩ :=
                evalStep_advance_shape false _ heval hdone
              subst q
              change stepDone (.advance false finalCarry) = true at hdone
              cases finalCarry with
              | carry => simp [stepDone] at hdone
              | done =>
                  right; right; left
                  have hfull : bitCodec.evalSucc .carry (oldDigit :: oldBits)
                      (newDigit :: newBits) = some .done := by
                    simpa [DigitCodec.evalSucc] using hsucc
                  obtain ⟨hnext, hno⟩ := (bitCodec.evalSucc_eq_done_iff _ _).mp hfull
                  exact ⟨oldDigit :: oldBits, newDigit :: newBits,
                    by simp [phaseRow, hold], by simp [phaseRow, hnew], hnext, hno⟩
              | bad => simp [stepDone] at hdone
            · obtain ⟨oldBits, newBits, finalCarry, hold, hnew, hsucc, hq⟩ :=
                evalStep_advance_shape true _ heval hdone
              subst q
              change stepDone (.advance true finalCarry) = true at hdone
              cases finalCarry with
              | carry =>
                  right; right; right
                  have hfull : bitCodec.evalSucc .carry (oldDigit :: oldBits)
                      (newDigit :: newBits) = some .carry := by
                    simpa [DigitCodec.evalSucc] using hsucc
                  obtain ⟨hnext, hover⟩ := (bitCodec.evalSucc_eq_carry_iff _ _).mp hfull
                  exact ⟨oldDigit :: oldBits, newDigit :: newBits,
                    by simp [phaseRow, hold], by simp [phaseRow, hnew], hnext, hover⟩
              | done => simp [stepDone] at hdone
              | bad => simp [stepDone] at hdone
  · rintro (⟨choice, bits, rfl, rfl⟩ | ⟨choice, bits, rfl, rfl⟩ |
        ⟨oldBits, newBits, rfl, rfl, rfl, hno⟩ |
        ⟨oldBits, newBits, rfl, rfl, rfl, hover⟩)
    · exact rowStep_enter (by
        intro hnil
        subst bits
        simp [phaseRow] at hne) choice
    · exact rowStep_merge (by
        intro hnil
        subst bits
        simp [phaseRow] at hne) choice
    · exact rowStep_advance (by
        intro hnil
        subst oldBits
        simp [phaseRow] at hne) hno
    · exact rowStep_final (by
        intro hnil
        subst oldBits
        simp [phaseRow] at hne) hover

/-! ## The canonical semantic graph -/

/-- Semantic vertices of the width-`w` odometer protocol. -/
public inductive Vertex (w : ℕ) where
  | junction (index : Fin (2 ^ w))
  | branch (index : Fin (2 ^ w)) (choice : Bool)
  | merge (index : Fin (2 ^ w))
  | target
  deriving DecidableEq, Fintype

/-- The designated source is junction zero. -/
public def source (w : ℕ) : Vertex w :=
  .junction 0

/-- Directed protocol edges. -/
public def Edge {w : ℕ} : Vertex w → Vertex w → Prop
  | .junction index, .branch next _ => next = index
  | .branch index _, .merge next => next = index
  | .merge index, .junction next => next.val = index.val + 1
  | .merge index, .target => index.val + 1 = 2 ^ w
  | _, _ => False

/-- The three matching colors: the two branch halves are interleaved, while advances have the
fresh third color. -/
public def Layer {w : ℕ} (color : Fin 3) : Vertex w → Vertex w → Prop
  | .junction index, .branch next choice =>
      next = index ∧ color.val = if choice then (1 : ℕ) else 0
  | .branch index choice, .merge next =>
      next = index ∧ color.val = if choice then (0 : ℕ) else 1
  | .merge index, .junction next =>
      next.val = index.val + 1 ∧ color.val = 2
  | .merge index, .target =>
      index.val + 1 = 2 ^ w ∧ color.val = 2
  | _, _ => False

/-! ### Exact three-matching structure -/

private theorem iff_existsUnique_fin3_value (P : Prop) (value : ℕ) (hvalue : value < 3) :
    P ↔ ∃! color : Fin 3, P ∧ color.val = value := by
  constructor
  · intro hP
    refine ⟨⟨value, hvalue⟩, ⟨hP, rfl⟩, ?_⟩
    intro color hcolor
    apply Fin.ext
    exact hcolor.2
  · rintro ⟨_, hcolor, _⟩
    exact hcolor.1

/-- Every protocol edge has exactly one of the three displayed colors. -/
public theorem edge_iff_existsUnique_layer {w : ℕ} (old new : Vertex w) :
    Edge old new ↔ ∃! color, Layer color old new := by
  cases old <;> cases new <;> simp only [Edge, Layer]
  all_goals try simp
  all_goals apply iff_existsUnique_fin3_value
  all_goals first | omega | (split <;> omega)

/-- A colored protocol edge is a genuine edge. -/
public theorem layer_sub_edge {w : ℕ} (color : Fin 3) (old new : Vertex w)
    (hlayer : Layer color old new) : Edge old new := by
  cases old <;> cases new <;> simp_all [Layer, Edge]

private theorem bool_eq_of_enterColor {color : Fin 3} {left right : Bool}
    (hleft : color.val = if left then (1 : ℕ) else 0)
    (hright : color.val = if right then (1 : ℕ) else 0) : left = right := by
  cases left <;> cases right <;> simp_all

private theorem bool_eq_of_mergeColor {color : Fin 3} {left right : Bool}
    (hleft : color.val = if left then (0 : ℕ) else 1)
    (hright : color.val = if right then (0 : ℕ) else 1) : left = right := by
  cases left <;> cases right <;> simp_all

private theorem enter_merge_color_ne {color : Fin 3} {choice : Bool}
    (henter : color.val = if choice then (1 : ℕ) else 0)
    (hmerge : color.val = if choice then (0 : ℕ) else 1) : False := by
  cases choice <;> simp_all

private theorem branch_color_ne_two {color : Fin 3} {choice : Bool} {zeroFirst : Bool}
    (hbranch : color.val = if choice then (if zeroFirst then (0 : ℕ) else 1)
      else (if zeroFirst then (1 : ℕ) else 0))
    (htwo : color.val = 2) : False := by
  cases choice <;> cases zeroFirst <;> simp_all

private theorem advance_successor_unique {w : ℕ} {index : Fin (2 ^ w)}
    {left right : Vertex w} (hleft : Edge (.merge index) left)
    (hright : Edge (.merge index) right) : left = right := by
  cases left <;> cases right <;> simp only [Edge] at hleft hright
  · apply congrArg Vertex.junction
    apply Fin.ext
    omega
  · exfalso
    omega
  · exfalso
    omega
  · rfl

/-- Every color is functional and cofunctional. -/
public theorem layer_biUnique {w : ℕ} (color : Fin 3) :
    Relator.BiUnique (@Layer w color) := by
  constructor
  · intro left right destination hleft hright
    cases left <;> cases right <;> cases destination <;> simp_all [Layer]
    all_goals first | omega | aesop
  · intro old left right hleft hright
    cases old with
    | junction index =>
        cases left <;> cases right <;> simp_all [Layer]
        all_goals aesop
    | branch index choice =>
        cases left <;> cases right <;> simp_all [Layer]
    | merge index =>
        exact advance_successor_unique
          (layer_sub_edge color (.merge index) left hleft)
          (layer_sub_edge color (.merge index) right hright)
    | target =>
        cases left <;> simp_all [Layer]

/-- No two edges of one color are composable. -/
public theorem layer_pathLengthAtMostOne {w : ℕ} (color : Fin 3) :
    LinearTwoDiforestReachability.PathLengthAtMostOne (@Layer w color) := by
  intro first middle last hfirst hlast
  cases first <;> cases middle <;> cases last <;>
    simp only [Layer] at hfirst hlast
  all_goals
    rcases hfirst with ⟨hfirstEdge, hfirstColor⟩
    rcases hlast with ⟨hlastEdge, hlastColor⟩
    all_goals first
      | exact enter_merge_color_ne hfirstColor hlastColor
      | exact branch_color_ne_two (zeroFirst := true) hfirstColor hlastColor
      | exact branch_color_ne_two (zeroFirst := false) hfirstColor hlastColor
      | exact branch_color_ne_two (zeroFirst := false) hlastColor hfirstColor

/-! ### Acyclicity -/

/-- A topological rank for the protocol graph. -/
public def rank {w : ℕ} : Vertex w → ℕ
  | .junction index => index.val + index.val + index.val + index.val
  | .branch index _ => index.val + index.val + index.val + index.val + 1
  | .merge index => index.val + index.val + index.val + index.val + 2
  | .target => (2 ^ w) + (2 ^ w) + (2 ^ w) + (2 ^ w)

/-- Every protocol edge strictly raises rank. -/
public theorem rank_lt_of_edge {w : ℕ} {old new : Vertex w}
    (hedge : Edge old new) : rank old < rank new := by
  cases old <;> cases new <;> simp only [Edge] at hedge
  all_goals simp only [rank]
  all_goals omega

/-- Every nonempty protocol path strictly raises rank. -/
public theorem rank_lt_of_transGen {w : ℕ} {old new : Vertex w}
    (hpath : TransGen (@Edge w) old new) : rank old < rank new := by
  induction hpath with
  | single hedge => exact rank_lt_of_edge hedge
  | tail _ hedge ih => exact ih.trans (rank_lt_of_edge hedge)

/-- The semantic protocol graph is acyclic. -/
public theorem acyclic (w : ℕ) (vertex : Vertex w) :
    ¬ TransGen (@Edge w) vertex vertex := by
  intro hcycle
  exact (Nat.lt_irrefl _) (rank_lt_of_transGen hcycle)

/-- The counter row at an in-range semantic index. -/
public def counterRow {w : ℕ} (index : Fin (2 ^ w)) : List Bool :=
  bitCodec.nextRow^[index.val] (bitCodec.zeroRow w)

/-- The numeric index of an arbitrary width-`w` bit row. -/
public def indexOfBits {w : ℕ} (bits : List Bool) (hlen : bits.length = w) :
    Fin (2 ^ w) :=
  ⟨bitCodec.value bits, by
    have hlt := bitCodec.value_lt_pow_length bits
    simpa [bitCodec_radix, hlen] using hlt⟩

/-- Decoding the numeric index of a width-`w` bit row returns that row. -/
public theorem counterRow_indexOfBits {w : ℕ} (bits : List Bool)
    (hlen : bits.length = w) :
    counterRow (indexOfBits bits hlen) = bits := by
  simpa [counterRow, indexOfBits, hlen] using
    bitCodec.iterate_nextRow_value_eq bits

@[simp]
public theorem counterRow_length {w : ℕ} (index : Fin (2 ^ w)) :
    (counterRow index).length = w := by
  simp [counterRow]

/-- Phase carried by a semantic vertex. -/
public def vertexPhase {w : ℕ} : Vertex w → Phase
  | .junction _ => .junction
  | .branch _ choice => .branch choice
  | .merge _ => .merge
  | .target => .final

/-- Odometer digits carried by a semantic vertex. -/
public def vertexDigits {w : ℕ} : Vertex w → List Bool
  | .junction index => counterRow index
  | .branch index _ => counterRow index
  | .merge index => counterRow index
  | .target => bitCodec.zeroRow w

/-- Encode semantic vertices as actual rows, without arbitrary finite-type numbering. -/
public def encode {w : ℕ} (vertex : Vertex w) : List Cell :=
  phaseRow (vertexPhase vertex) (vertexDigits vertex)

@[simp]
public theorem encode_length {w : ℕ} (vertex : Vertex w) :
    (encode vertex).length = w := by
  cases vertex <;> simp [encode, vertexDigits]

private theorem phase_eq_of_phaseRow_eq {leftPhase rightPhase : Phase}
    {leftDigits rightDigits : List Bool} (hne : leftDigits ≠ [])
    (heq : phaseRow leftPhase leftDigits = phaseRow rightPhase rightDigits) :
    leftPhase = rightPhase := by
  obtain ⟨digit, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases rightDigits with
  | nil => simp [phaseRow] at heq
  | cons rightDigit rightTail =>
      change
        (leftPhase, digit) :: phaseRow leftPhase tail =
          (rightPhase, rightDigit) :: phaseRow rightPhase rightTail at heq
      have hhead := (List.cons.inj heq).1
      exact congrArg Prod.fst hhead

private theorem digits_eq_of_phaseRow_eq (phase : Phase) {left right : List Bool}
    (heq : phaseRow phase left = phaseRow phase right) : left = right := by
  exact (List.map_injective_iff.mpr fun _ _ h ↦ congrArg Prod.snd h) heq

/-- Distinct in-range indices have distinct canonical counter rows. -/
public theorem counterRow_injective (w : ℕ) :
    Function.Injective (@counterRow w) := by
  intro left right heq
  apply Fin.ext
  exact bitCodec.eq_of_iterate_nextRow_eq left.isLt right.isLt heq

/-- The canonical semantic encoding is injective at every positive width. -/
public theorem encode_injective {w : ℕ} (hw : 0 < w) :
    Function.Injective (@encode w) := by
  intro left right heq
  have hleft : vertexDigits left ≠ [] := by
    apply List.ne_nil_of_length_pos
    cases left <;> simpa [vertexDigits] using hw
  have heq' : phaseRow (vertexPhase left) (vertexDigits left) =
      phaseRow (vertexPhase right) (vertexDigits right) := by
    simpa [encode] using heq
  have hphase : vertexPhase left = vertexPhase right :=
    phase_eq_of_phaseRow_eq hleft heq'
  rw [hphase] at heq'
  have hdigits : vertexDigits left = vertexDigits right :=
    digits_eq_of_phaseRow_eq (vertexPhase right) heq'
  cases left <;> cases right <;> simp only [vertexPhase] at hphase
  all_goals try contradiction
  · exact congrArg Vertex.junction
      (counterRow_injective w (by simpa [vertexDigits] using hdigits))
  · rename_i leftIndex leftChoice rightIndex rightChoice
    have hchoice : leftChoice = rightChoice := Phase.branch.inj hphase
    have hindex : leftIndex = rightIndex :=
      counterRow_injective w (by simpa [vertexDigits] using hdigits)
    subst rightChoice
    subst rightIndex
    rfl
  · exact congrArg Vertex.merge
      (counterRow_injective w (by simpa [vertexDigits] using hdigits))
  · rfl

/-- The only phase pairs accepted by the fixed local step verifier. -/
public def PhaseTransition : Phase → Phase → Prop
  | .junction, .branch _ => True
  | .branch _, .merge => True
  | .merge, .junction => True
  | .merge, .final => True
  | _, _ => False

private theorem phaseTransition_of_rowStep {oldPhase newPhase : Phase}
    {old new : List Bool} (hne : old ≠ []) (hlen : old.length = new.length)
    (hstep : system.RowStep (phaseRow oldPhase old) (phaseRow newPhase new)) :
    PhaseTransition oldPhase newPhase := by
  obtain ⟨cert, q, heval, hdone⟩ := hstep
  have hcert := canonicalCert heval
  subst cert
  obtain ⟨oldHead, oldTail, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases new with
  | nil => simp at hlen
  | cons newHead newTail =>
      have heval' : system.evalStep .start
          (phaseRow oldPhase (oldHead :: oldTail))
          (phaseRow newPhase (newHead :: newTail))
          (List.replicate (oldHead :: oldTail).length ()) = some q := by
        simpa [system] using heval
      simp only [phaseRow, List.map_cons] at heval'
      change system.evalStep
          (stepCell .start (oldPhase, oldHead) (newPhase, newHead) ())
          (phaseRow oldPhase oldTail) (phaseRow newPhase newTail)
          (List.replicate oldTail.length ()) = some q at heval'
      cases oldPhase <;> cases newPhase <;> simp only [PhaseTransition]
      all_goals
        simp only [stepCell] at heval'
        have hq := evalStep_bad_eq_some_imp _ _ _ heval'
        subst q
        change false = true at hdone
        contradiction

/-- No spurious transition occurs between canonical encoded states. -/
public theorem edge_of_rowStep {w : ℕ} (hw : 0 < w) {old new : Vertex w}
    (hstep : system.RowStep (encode old) (encode new)) : Edge old new := by
  have hne : vertexDigits old ≠ [] := by
    apply List.ne_nil_of_length_pos
    cases old <;> simpa [vertexDigits] using hw
  have hlen : (vertexDigits old).length = (vertexDigits new).length := by
    cases old <;> cases new <;> simp [vertexDigits]
  have hphase : PhaseTransition (vertexPhase old) (vertexPhase new) := by
    apply phaseTransition_of_rowStep hne hlen
    simpa [encode] using hstep
  cases old <;> cases new <;> simp only [vertexPhase, PhaseTransition] at hphase
  · rename_i oldIndex newIndex choice
    change system.RowStep (phaseRow .junction (counterRow oldIndex))
      (phaseRow (.branch choice) (counterRow newIndex)) at hstep
    have hrow := (rowStep_enter_iff hne hlen choice).mp hstep
    change newIndex = oldIndex
    exact counterRow_injective w hrow
  · rename_i oldIndex oldChoice newIndex
    change system.RowStep (phaseRow (.branch oldChoice) (counterRow oldIndex))
      (phaseRow .merge (counterRow newIndex)) at hstep
    have hrow := (rowStep_merge_iff hne hlen oldChoice).mp hstep
    change newIndex = oldIndex
    exact counterRow_injective w hrow
  · rename_i oldIndex newIndex
    change system.RowStep (phaseRow .merge (counterRow oldIndex))
      (phaseRow .junction (counterRow newIndex)) at hstep
    obtain ⟨hrow, hno⟩ := (rowStep_advance_iff hne hlen).mp hstep
    have hno' : (bitCodec.increment (counterRow oldIndex)).2 = false := by
      simpa [vertexDigits] using hno
    have hvalue := congrArg bitCodec.value hrow
    change bitCodec.value (counterRow newIndex) =
      bitCodec.value (bitCodec.increment (counterRow oldIndex)).1 at hvalue
    rw [bitCodec.value_increment_of_not_overflow _ hno'] at hvalue
    change bitCodec.value
        (bitCodec.nextRow^[newIndex.val] (bitCodec.zeroRow w)) =
      bitCodec.value (bitCodec.nextRow^[oldIndex.val] (bitCodec.zeroRow w)) + 1 at hvalue
    rw [bitCodec.value_iterate_nextRow_zeroRow newIndex.isLt,
      bitCodec.value_iterate_nextRow_zeroRow oldIndex.isLt] at hvalue
    exact hvalue
  · rename_i oldIndex
    change system.RowStep (phaseRow .merge (counterRow oldIndex))
      (phaseRow .final (bitCodec.zeroRow w)) at hstep
    obtain ⟨_, hover⟩ := (rowStep_final_iff hne hlen).mp hstep
    have hover' : (bitCodec.increment (counterRow oldIndex)).2 = true := by
      simpa [vertexDigits] using hover
    exact (bitCodec.increment_iterate_nextRow_overflow_iff oldIndex.isLt).mp hover'

/-- Every semantic edge is a certified local row step. -/
public theorem rowStep_of_edge {w : ℕ} (hw : 0 < w)
    {old new : Vertex w} (hedge : Edge old new) :
    system.RowStep (encode old) (encode new) := by
  cases old <;> cases new <;> simp only [Edge] at hedge
  · subst_vars
    change system.RowStep (phaseRow .junction (counterRow _))
      (phaseRow (.branch _) (counterRow _))
    exact rowStep_enter (by
      apply List.ne_nil_of_length_pos
      simpa using hw) _
  · subst_vars
    change system.RowStep (phaseRow (.branch _) (counterRow _))
      (phaseRow .merge (counterRow _))
    exact rowStep_merge (by
      apply List.ne_nil_of_length_pos
      simpa using hw) _
  · rename_i index next
    have hnext : index.val + 1 < 2 ^ w := by simpa [hedge] using next.isLt
    have hno : (bitCodec.increment (counterRow index)).2 = false := by
      apply (bitCodec.increment_iterate_nextRow_not_overflow_iff index.isLt).2
      simpa using hnext
    have hrow : bitCodec.nextRow (counterRow index) = counterRow next := by
      apply bitCodec.value_injective_of_length_eq
      · simp
      · change bitCodec.value (bitCodec.increment (counterRow index)).1 =
          bitCodec.value (counterRow next)
        rw [bitCodec.value_increment_of_not_overflow _ hno]
        change bitCodec.value
            (bitCodec.nextRow^[index.val] (bitCodec.zeroRow w)) + 1 =
          bitCodec.value (bitCodec.nextRow^[next.val] (bitCodec.zeroRow w))
        rw [bitCodec.value_iterate_nextRow_zeroRow index.isLt,
          bitCodec.value_iterate_nextRow_zeroRow next.isLt]
        exact hedge.symm
    change system.RowStep (phaseRow .merge (counterRow index))
      (phaseRow .junction (counterRow next))
    rw [← hrow]
    exact rowStep_advance (by
      apply List.ne_nil_of_length_pos
      simpa using hw) hno
  · rename_i index
    have hover := (bitCodec.increment_iterate_nextRow_overflow_iff index.isLt).2 hedge
    have hzero : bitCodec.nextRow (counterRow index) = bitCodec.zeroRow w := by
      simpa [DigitCodec.nextRow] using
        bitCodec.increment_fst_of_overflow (counterRow index) hover
    change system.RowStep (phaseRow .merge (counterRow index))
      (phaseRow .final (bitCodec.zeroRow w))
    rw [← hzero]
    exact rowStep_final (by
      apply List.ne_nil_of_length_pos
      simpa using hw) hover

/-- On positive widths, the certified row relation restricted to canonical states is exactly
the semantic exponentially long three-matching diamond chain. -/
public theorem rowStep_encode_iff_edge {w : ℕ} (hw : 0 < w) (old new : Vertex w) :
    system.RowStep (encode old) (encode new) ↔ Edge old new :=
  ⟨edge_of_rowStep hw, rowStep_of_edge hw⟩

/-- Complete fixed-width characterization: at every positive width, *all* accepted row steps,
not just a preselected subgraph, are exactly encodings of semantic odometer edges.  Thus malformed
width-`w` rows are isolated from the certified relation. -/
public theorem rowStep_iff_exists_encoded_edge {w : ℕ} (hw : 0 < w)
    {old new : List Cell} (holdLength : old.length = w) :
    system.RowStep old new ↔
      ∃ source destination : Vertex w,
        old = encode source ∧ new = encode destination ∧ Edge source destination := by
  have hne : old ≠ [] := by
    intro hnil
    subst old
    simp at holdLength
    omega
  constructor
  · intro hstep
    obtain (⟨choice, bits, rfl, rfl⟩ | ⟨choice, bits, rfl, rfl⟩ |
        ⟨oldBits, newBits, rfl, rfl, hnext, hno⟩ |
        ⟨oldBits, newBits, rfl, rfl, hnext, hover⟩) :=
      (rowStep_iff_protocolStep hne).mp hstep
    · have hbits : bits.length = w := by simpa using holdLength
      let index := indexOfBits bits hbits
      have hrow : counterRow index = bits := counterRow_indexOfBits bits hbits
      refine ⟨.junction index, .branch index choice, ?_, ?_, ?_⟩
      · simp [encode, vertexPhase, vertexDigits, hrow]
      · simp [encode, vertexPhase, vertexDigits, hrow]
      · simp [Edge]
    · have hbits : bits.length = w := by simpa using holdLength
      let index := indexOfBits bits hbits
      have hrow : counterRow index = bits := counterRow_indexOfBits bits hbits
      refine ⟨.branch index choice, .merge index, ?_, ?_, ?_⟩
      · simp [encode, vertexPhase, vertexDigits, hrow]
      · simp [encode, vertexPhase, vertexDigits, hrow]
      · simp [Edge]
    · have holdBits : oldBits.length = w := by simpa using holdLength
      have hnewBits : newBits.length = w := by
        rw [hnext, bitCodec.nextRow_length, holdBits]
      let oldIndex := indexOfBits oldBits holdBits
      let newIndex := indexOfBits newBits hnewBits
      have holdRow : counterRow oldIndex = oldBits :=
        counterRow_indexOfBits oldBits holdBits
      have hnewRow : counterRow newIndex = newBits :=
        counterRow_indexOfBits newBits hnewBits
      refine ⟨.merge oldIndex, .junction newIndex, ?_, ?_, ?_⟩
      · simp [encode, vertexPhase, vertexDigits, holdRow]
      · simp [encode, vertexPhase, vertexDigits, hnewRow]
      · change (indexOfBits newBits hnewBits).val =
          (indexOfBits oldBits holdBits).val + 1
        simp only [indexOfBits]
        rw [hnext]
        change bitCodec.value (bitCodec.increment oldBits).1 =
          bitCodec.value oldBits + 1
        exact bitCodec.value_increment_of_not_overflow oldBits hno
    · have holdBits : oldBits.length = w := by simpa using holdLength
      let oldIndex := indexOfBits oldBits holdBits
      have holdRow : counterRow oldIndex = oldBits :=
        counterRow_indexOfBits oldBits holdBits
      have hnextZero : bitCodec.nextRow oldBits = bitCodec.zeroRow w := by
        simpa [DigitCodec.nextRow, holdBits] using
          bitCodec.increment_fst_of_overflow oldBits hover
      have hnewZero : newBits = bitCodec.zeroRow w := hnext.trans hnextZero
      refine ⟨.merge oldIndex, .target, ?_, ?_, ?_⟩
      · simp [encode, vertexPhase, vertexDigits, holdRow]
      · simp [encode, vertexPhase, vertexDigits, hnewZero]
      · change (indexOfBits oldBits holdBits).val + 1 = 2 ^ w
        simpa [indexOfBits, bitCodec_radix, holdBits] using
          (bitCodec.increment_overflow_iff_value oldBits).mp hover
  · rintro ⟨source, destination, rfl, rfl, hedge⟩
    exact rowStep_of_edge hw hedge

/-! ## Exponentially many sequential relevant branches -/

/-- Every semantic junction is a genuine binary branch. -/
public theorem junction_branches {w : ℕ} (index : Fin (2 ^ w)) :
    ThreeMatchingReachability.Branches (@Edge w) (.junction index) := by
  refine ⟨.branch index false, .branch index true, ?_, ?_, ?_⟩
  · simp [Edge]
  · simp [Edge]
  · intro heq
    injection heq with _ hchoice
    simp at hchoice

private theorem branch_successor_unique {w : ℕ} {index : Fin (2 ^ w)} {choice : Bool}
    {left right : Vertex w} (hleft : Edge (.branch index choice) left)
    (hright : Edge (.branch index choice) right) : left = right := by
  cases left <;> cases right <;> simp only [Edge] at hleft hright
  subst_vars
  rfl

/-- Genuine branch vertices are exactly the odometer junctions. -/
public theorem branches_iff_exists_junction {w : ℕ} {vertex : Vertex w} :
    ThreeMatchingReachability.Branches (@Edge w) vertex ↔
      ∃ index : Fin (2 ^ w), vertex = .junction index := by
  cases vertex with
  | junction index =>
      constructor
      · intro _
        exact ⟨index, rfl⟩
      · intro _
        exact junction_branches index
  | branch index choice =>
      constructor
      · rintro ⟨left, right, hleft, hright, hne⟩
        exact (hne (branch_successor_unique hleft hright)).elim
      · rintro ⟨_, heq⟩
        contradiction
  | merge index =>
      constructor
      · rintro ⟨left, right, hleft, hright, hne⟩
        exact (hne (advance_successor_unique hleft hright)).elim
      · rintro ⟨_, heq⟩
        contradiction
  | target =>
      constructor
      · rintro ⟨left, _, hleft, _, _⟩
        cases left <;> contradiction
      · rintro ⟨_, heq⟩
        contradiction

/-- A total level notation: in-range levels are junctions and the capacity level is the target. -/
public def levelAt (w level : ℕ) : Vertex w :=
  if h : level < 2 ^ w then .junction ⟨level, h⟩ else .target

@[simp]
public theorem levelAt_index {w : ℕ} (index : Fin (2 ^ w)) :
    levelAt w index.val = .junction index := by
  simp only [levelAt, dif_pos index.isLt]

@[simp]
public theorem levelAt_capacity (w : ℕ) :
    levelAt w (2 ^ w) = .target := by
  simp [levelAt]

@[simp]
public theorem levelAt_zero (w : ℕ) : levelAt w 0 = source w := by
  have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
  simp [levelAt, source, hpos]

/-- Traverse one entire diamond, choosing its false branch. -/
public theorem junction_reaches_nextLevel {w : ℕ} (index : Fin (2 ^ w)) :
    ReflTransGen (@Edge w) (.junction index) (levelAt w (index.val + 1)) := by
  have henter : Edge (.junction index) (.branch index false) := by simp [Edge]
  have hmerge : Edge (.branch index false) (.merge index) := by simp [Edge]
  have hadvance : Edge (.merge index) (levelAt w (index.val + 1)) := by
    unfold levelAt
    split
    · simp [Edge]
    · simp only [Edge]
      have := index.isLt
      omega
  exact ((ReflTransGen.single henter).trans (ReflTransGen.single hmerge)).trans
    (ReflTransGen.single hadvance)

private theorem levelAt_reaches_of_le {w left right : ℕ}
    (hle : left ≤ right) (hright : right ≤ 2 ^ w) :
    ReflTransGen (@Edge w) (levelAt w left) (levelAt w right) := by
  induction right generalizing left with
  | zero =>
      have : left = 0 := by omega
      subst left
      exact ReflTransGen.refl
  | succ right ih =>
      by_cases heq : left = right + 1
      · subst left
        exact ReflTransGen.refl
      · have hleft : left ≤ right := by omega
        have hrightLt : right < 2 ^ w := by omega
        have hlevel : levelAt w right = .junction ⟨right, hrightLt⟩ := by
          unfold levelAt
          rw [dif_pos hrightLt]
        have hstep : ReflTransGen (@Edge w) (levelAt w right)
            (levelAt w (right + 1)) := by
          rw [hlevel]
          exact junction_reaches_nextLevel ⟨right, hrightLt⟩
        exact (ih hleft (by omega)).trans hstep

/-- The source reaches every one of the `2 ^ w` junctions. -/
public theorem source_reaches_junction {w : ℕ} (index : Fin (2 ^ w)) :
    ReflTransGen (@Edge w) (source w) (.junction index) := by
  simpa using levelAt_reaches_of_le (w := w) (left := 0) (right := index.val)
    (Nat.zero_le _) (Nat.le_of_lt index.isLt)

/-- Every junction can still reach the designated target. -/
public theorem junction_reaches_target {w : ℕ} (index : Fin (2 ^ w)) :
    ReflTransGen (@Edge w) (.junction index) .target := by
  simpa using levelAt_reaches_of_le (w := w) (left := index.val) (right := 2 ^ w)
    (Nat.le_of_lt index.isLt) (Nat.le_refl _)

/-- Junctions occur in their odometer-index order. -/
public theorem junction_reaches_junction_of_le {w : ℕ}
    (first last : Fin (2 ^ w)) (hle : first ≤ last) :
    ReflTransGen (@Edge w) (.junction first) (.junction last) := by
  simpa using levelAt_reaches_of_le (w := w) (left := first.val) (right := last.val)
    hle (Nat.le_of_lt last.isLt)

/-- Distinct odometer indices give distinct branch junctions. -/
public theorem junction_injective (w : ℕ) :
    Function.Injective (fun index : Fin (2 ^ w) ↦ Vertex.junction index) := by
  intro left right heq
  injection heq

/-- The semantic graph has exactly `2 ^ w` genuine branch vertices. -/
public theorem ncard_branchVertices (w : ℕ) :
    Set.ncard {vertex : Vertex w |
      ThreeMatchingReachability.Branches (@Edge w) vertex} = 2 ^ w := by
  have hset : {vertex : Vertex w |
      ThreeMatchingReachability.Branches (@Edge w) vertex} =
      Set.range (fun index : Fin (2 ^ w) ↦ Vertex.junction index) := by
    ext vertex
    constructor
    · intro hbranch
      obtain ⟨index, rfl⟩ := branches_iff_exists_junction.mp hbranch
      exact ⟨index, rfl⟩
    · rintro ⟨index, rfl⟩
      exact junction_branches index
  rw [hset, Set.ncard_range_of_injective (junction_injective w)]
  simp

/-- There are exactly `2 ^ w` canonically indexed branch events, each relevant to the designated
source and target, and they occur in index order. -/
public theorem exists_twoPow_relevant_branches (w : ℕ) :
    ∃ branches : Fin (2 ^ w) → Vertex w,
      Function.Injective branches ∧
        (∀ index, ReflTransGen (@Edge w) (source w) (branches index) ∧
          ThreeMatchingReachability.Branches (@Edge w) (branches index) ∧
          ReflTransGen (@Edge w) (branches index) .target) ∧
        ∀ first last, first ≤ last →
          ReflTransGen (@Edge w) (branches first) (branches last) := by
  refine ⟨fun index ↦ .junction index, junction_injective w, ?_, ?_⟩
  · intro index
    exact ⟨source_reaches_junction index, junction_branches index,
      junction_reaches_target index⟩
  · exact junction_reaches_junction_of_le

/-- Omnibus local exponential-branch witness.  For every positive width, one fixed finite-state
certified row system contains, exactly on its canonical rows, an acyclic exact union of three
directed matchings with `2 ^ w` sequential source-to-target-relevant branch events. -/
public theorem local_exponential_threeMatching_witness (w : ℕ) (hw : 0 < w) :
    Function.Injective (@encode w) ∧
      (∀ old new : Vertex w, system.RowStep (encode old) (encode new) ↔ Edge old new) ∧
      (∀ old new : Vertex w, Edge old new ↔ ∃! color, Layer color old new) ∧
      (∀ color, Relator.BiUnique (@Layer w color) ∧
        LinearTwoDiforestReachability.PathLengthAtMostOne (@Layer w color)) ∧
      (∀ vertex, ¬ TransGen (@Edge w) vertex vertex) ∧
      ∃ branches : Fin (2 ^ w) → Vertex w,
        Function.Injective branches ∧
          (∀ index, ReflTransGen (@Edge w) (source w) (branches index) ∧
            ThreeMatchingReachability.Branches (@Edge w) (branches index) ∧
            ReflTransGen (@Edge w) (branches index) .target) ∧
          ∀ first last, first ≤ last →
            ReflTransGen (@Edge w) (branches first) (branches last) := by
  exact ⟨encode_injective hw, rowStep_encode_iff_edge hw,
    edge_iff_existsUnique_layer, fun color ↦
      ⟨layer_biUnique color, layer_pathLengthAtMostOne color⟩,
    acyclic w, exists_twoPow_relevant_branches w⟩

end OdometerDiamondRowSystem
