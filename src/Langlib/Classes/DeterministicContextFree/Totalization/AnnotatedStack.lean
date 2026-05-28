module

public import Langlib.Classes.DeterministicContextFree.Totalization.RegularAnalysis
public import Langlib.Classes.DeterministicContextFree.Totalization.StackSummary
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! # Totalizer Annotated Stack

This file defines the finite stack annotations and regular lookahead queries used
by the DPDA totalizer once a `RegularEpsilonAnalysis` has been built.
-/

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
variable {M : DPDA Q T S} (A : M.RegularEpsilonAnalysis)

noncomputable section

/-- The vector of DFA transition summaries stored for the stack suffix below a symbol. -/
structure AnalysisSummary where
  stop : ∀ q, A.StopState q → A.StopState q
  accept : ∀ q, A.AcceptState q → A.AcceptState q

/-- `AnalysisSummary` is just a pair of finite dependent function spaces. -/
def AnalysisSummary.equivProd :
    AnalysisSummary A ≃
      ((∀ q, A.StopState q → A.StopState q) ×
        (∀ q, A.AcceptState q → A.AcceptState q)) where
  toFun s := (s.stop, s.accept)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro s; cases s; rfl
  right_inv := by intro p; cases p; rfl

noncomputable instance instFintypeAnalysisSummary : Fintype (AnalysisSummary A) := by
  classical
  exact Fintype.ofEquiv _ (AnalysisSummary.equivProd A).symm

/-- The empty-suffix summary vector. -/
def AnalysisSummary.id : AnalysisSummary A where
  stop := fun _ x => x
  accept := fun _ x => x

/-- A summary vector represents an original stack suffix when every component is
the DFA transition function induced by reading that suffix. -/
def SummaryRepresents (summary : AnalysisSummary A) (γ : List S) : Prop :=
  (∀ q, summary.stop q = (A.stopDFA q).stackSummary γ) ∧
  (∀ q, summary.accept q = (A.acceptDFA q).stackSummary γ)

theorem SummaryRepresents.eq {summary₁ summary₂ : AnalysisSummary A} {γ : List S}
    (h₁ : SummaryRepresents A summary₁ γ) (h₂ : SummaryRepresents A summary₂ γ) :
    summary₁ = summary₂ := by
  cases summary₁
  cases summary₂
  congr
  · funext q x
    exact (congrFun (h₁.1 q) x).trans (congrFun (h₂.1 q) x).symm
  · funext q x
    exact (congrFun (h₁.2 q) x).trans (congrFun (h₂.2 q) x).symm

/-- The identity summary represents the empty stack suffix. -/
theorem summaryRepresents_id : SummaryRepresents A (AnalysisSummary.id A) [] := by
  constructor <;> intro q <;> funext x <;> rfl

/-- Update a summary vector by placing a block of original stack symbols above it. -/
def AnalysisSummary.above (below : AnalysisSummary A) (γ : List S) : AnalysisSummary A where
  stop := fun q => (A.stopDFA q).summaryAbove (below.stop q) γ
  accept := fun q => (A.acceptDFA q).summaryAbove (below.accept q) γ

/-- Updating a correct summary with a block keeps it correct for the larger suffix. -/
theorem SummaryRepresents.above {below : AnalysisSummary A} {δ : List S}
    (hbelow : SummaryRepresents A below δ) (γ : List S) :
    SummaryRepresents A (below.above A γ) (γ ++ δ) := by
  constructor
  · intro q
    funext x
    unfold AnalysisSummary.above DFA.summaryAbove
    change (below.stop q ∘ (A.stopDFA q).stackSummary γ) x =
      (A.stopDFA q).stackSummary (γ ++ δ) x
    rw [hbelow.1 q]
    simp [DFA.stackSummary_append]
  · intro q
    funext x
    unfold AnalysisSummary.above DFA.summaryAbove
    change (below.accept q ∘ (A.acceptDFA q).stackSummary γ) x =
      (A.acceptDFA q).stackSummary (γ ++ δ) x
    rw [hbelow.2 q]
    simp [DFA.stackSummary_append]

/-- Placing one top symbol above a represented suffix gives a represented full stack. -/
theorem SummaryRepresents.cons {below : AnalysisSummary A} {γ : List S}
    (hbelow : SummaryRepresents A below γ) (Z : S) :
    SummaryRepresents A (below.above A [Z]) (Z :: γ) := by
  simpa using hbelow.above (A := A) [Z]

/-- Stack symbols of the totalized machine.  `none` is the permanent bottom marker;
`some (Z, s)` is an original stack symbol annotated with the summary vector of the
original stack suffix below it. -/
abbrev TotalStackSymbol := Option (S × AnalysisSummary A)

/-- Annotate a replacement block above an already summarized suffix. -/
def annotateAbove (below : AnalysisSummary A) : List S → List (TotalStackSymbol A)
  | [] => []
  | Z :: γ => some (Z, below.above A γ) :: annotateAbove below γ

@[simp]
theorem annotateAbove_nil (below : AnalysisSummary A) :
    annotateAbove (A := A) below [] = [] :=
  rfl

@[simp]
theorem annotateAbove_cons (below : AnalysisSummary A) (Z : S) (γ : List S) :
    annotateAbove (A := A) below (Z :: γ) =
      some (Z, below.above A γ) :: annotateAbove (A := A) below γ :=
  rfl

/-- Erase annotations from a totalized stack, dropping the bottom marker. -/
def eraseAnnotatedStack : List (TotalStackSymbol A) → List S
  | [] => []
  | none :: γ => eraseAnnotatedStack γ
  | some (Z, _) :: γ => Z :: eraseAnnotatedStack γ

theorem erase_annotateAbove (below : AnalysisSummary A) (γ : List S) :
    eraseAnnotatedStack (A := A) (annotateAbove (A := A) below γ) = γ := by
  induction γ with
  | nil => rfl
  | cons Z γ ih => simp [eraseAnnotatedStack, ih]

theorem eraseAnnotatedStack_append (γ δ : List (TotalStackSymbol A)) :
    eraseAnnotatedStack (A := A) (γ ++ δ) =
      eraseAnnotatedStack (A := A) γ ++ eraseAnnotatedStack (A := A) δ := by
  induction γ with
  | nil => rfl
  | cons top γ ih =>
      cases top <;> simp [eraseAnnotatedStack, ih]

/-- The annotation invariant for totalizer stacks.  Every original stack symbol stores
a summary for the erased suffix below it; `none` is the unique bottom marker. -/
def StackWellAnnotated : List (TotalStackSymbol A) → Prop
  | [] => True
  | none :: rest => rest = []
  | some (_, below) :: rest =>
      SummaryRepresents A below (eraseAnnotatedStack (A := A) rest) ∧ StackWellAnnotated rest

theorem stackWellAnnotated_nil : StackWellAnnotated (A := A) [] :=
  trivial

theorem stackWellAnnotated_none :
    StackWellAnnotated (A := A) [none] := by
  simp [StackWellAnnotated]

theorem stackWellAnnotated_cons_some_iff (Z : S) (below : AnalysisSummary A)
    (rest : List (TotalStackSymbol A)) :
    StackWellAnnotated (A := A) (some (Z, below) :: rest) ↔
      SummaryRepresents A below (eraseAnnotatedStack (A := A) rest) ∧
        StackWellAnnotated (A := A) rest :=
  Iff.rfl

theorem stackWellAnnotated_annotateAbove_append {below : AnalysisSummary A}
    {rest : List (TotalStackSymbol A)}
    (hbelow : SummaryRepresents A below (eraseAnnotatedStack (A := A) rest))
    (hrest : StackWellAnnotated (A := A) rest) (γ : List S) :
    StackWellAnnotated (A := A) (annotateAbove (A := A) below γ ++ rest) := by
  induction γ with
  | nil => exact hrest
  | cons Z γ ih =>
      simp [annotateAbove_cons, StackWellAnnotated,
        eraseAnnotatedStack_append, erase_annotateAbove,
        hbelow.above (A := A) γ, ih]

theorem stackWellAnnotated_annotateAbove_bottom (γ : List S) :
    StackWellAnnotated (A := A) (annotateAbove (A := A) (AnalysisSummary.id A) γ ++ [none]) :=
  stackWellAnnotated_annotateAbove_append (A := A)
    (by simpa [eraseAnnotatedStack] using summaryRepresents_id A)
    (stackWellAnnotated_none (A := A)) γ

/-- Reachable totalizer stacks retain a permanent bottom marker. -/
def StackHasBottom : List (TotalStackSymbol A) → Prop
  | [] => False
  | none :: rest => rest = []
  | some _ :: rest => StackHasBottom rest

theorem stackHasBottom_none :
    StackHasBottom (A := A) [none] := by
  simp [StackHasBottom]

theorem stackHasBottom_nonempty {stack : List (TotalStackSymbol A)}
    (hstack : StackHasBottom (A := A) stack) :
    ∃ top rest, stack = top :: rest := by
  cases stack with
  | nil => cases hstack
  | cons top rest => exact ⟨top, rest, rfl⟩

theorem stackHasBottom_annotateAbove_append {below : AnalysisSummary A}
    {rest : List (TotalStackSymbol A)}
    (hrest : StackHasBottom (A := A) rest) (γ : List S) :
    StackHasBottom (A := A) (annotateAbove (A := A) below γ ++ rest) := by
  induction γ with
  | nil => exact hrest
  | cons Z γ ih =>
      simp [annotateAbove_cons, StackHasBottom, ih]

theorem stackHasBottom_annotateAbove_bottom (γ : List S) :
    StackHasBottom (A := A) (annotateAbove (A := A) (AnalysisSummary.id A) γ ++ [none]) :=
  stackHasBottom_annotateAbove_append (A := A) (stackHasBottom_none (A := A)) γ

/-- Does the semantic epsilon phase terminate from the configuration represented by
the current top stack symbol? -/
def topStops (q : Q) : TotalStackSymbol A → Prop
  | none => (A.stopDFA q).evalFrom (A.stopDFA q).start [] ∈ (A.stopDFA q).accept
  | some (Z, below) =>
      below.stop q ((A.stopDFA q).step (A.stopDFA q).start Z) ∈ (A.stopDFA q).accept

/-- If the input is exhausted at the configuration represented by the current top
stack symbol, does the original machine accept along its epsilon closure? -/
def topAcceptsEpsilonClosure (q : Q) : TotalStackSymbol A → Prop
  | none => (A.acceptDFA q).evalFrom (A.acceptDFA q).start [] ∈ (A.acceptDFA q).accept
  | some (Z, below) =>
      below.accept q ((A.acceptDFA q).step (A.acceptDFA q).start Z) ∈ (A.acceptDFA q).accept

theorem topStops_some_correct (q : Q) (Z : S) (below : AnalysisSummary A) :
    topStops A q (some (Z, below)) ↔
      below.stop q ((A.stopDFA q).step (A.stopDFA q).start Z) ∈ (A.stopDFA q).accept :=
  Iff.rfl

theorem topAccepts_some_correct (q : Q) (Z : S) (below : AnalysisSummary A) :
    topAcceptsEpsilonClosure A q (some (Z, below)) ↔
      below.accept q ((A.acceptDFA q).step (A.acceptDFA q).start Z) ∈ (A.acceptDFA q).accept :=
  Iff.rfl

/-- The full original-stack summary represented by the current top symbol. -/
def fullSummaryOfTop : TotalStackSymbol A → AnalysisSummary A
  | none => AnalysisSummary.id A
  | some (Z, below) => below.above A [Z]

theorem stackWellAnnotated_fullSummaryOfTop {top : TotalStackSymbol A}
    {rest : List (TotalStackSymbol A)}
    (hstack : StackWellAnnotated (A := A) (top :: rest)) :
    SummaryRepresents A (fullSummaryOfTop A top)
      (eraseAnnotatedStack (A := A) (top :: rest)) := by
  cases top with
  | none =>
      simp [StackWellAnnotated] at hstack
      subst rest
      exact summaryRepresents_id A
  | some payload =>
      rcases payload with ⟨Z, below⟩
      exact (hstack.1.cons (A := A) Z)

/-- The stop lookahead evaluated from a full-stack summary. -/
def stopsFromSummary (q : Q) (summary : AnalysisSummary A) : Prop :=
  summary.stop q (A.stopDFA q).start ∈ (A.stopDFA q).accept

/-- The epsilon-acceptance lookahead evaluated from a full-stack summary. -/
def acceptsFromSummary (q : Q) (summary : AnalysisSummary A) : Prop :=
  summary.accept q (A.acceptDFA q).start ∈ (A.acceptDFA q).accept

/-- Stop-lookahead correctness for a summary representing the current original stack. -/
theorem stopsFromSummary_correct {summary : AnalysisSummary A} {γ : List S}
    (hsummary : SummaryRepresents A summary γ) (q : Q) :
    stopsFromSummary A q summary ↔ ∃ c', M.EpsilonStopsAt (q, γ) c' := by
  unfold stopsFromSummary
  rw [hsummary.1 q]
  exact A.stop_correct q γ

/-- Epsilon-acceptance lookahead correctness for a summary representing the current
original stack. -/
theorem acceptsFromSummary_correct {summary : AnalysisSummary A} {γ : List S}
    (hsummary : SummaryRepresents A summary γ) (q : Q) :
    acceptsFromSummary A q summary ↔
      ∃ q' γ', M.EpsilonReaches (q, γ) (q', γ') ∧ q' ∈ M.final_states := by
  unfold acceptsFromSummary
  rw [hsummary.2 q]
  exact A.accept_correct q γ

/-- Boolean form of `acceptsFromSummary`, used in the finite control. -/
def acceptBit (q : Q) (summary : AnalysisSummary A) : Bool :=
  by
    classical
    exact if acceptsFromSummary A q summary then true else false

theorem acceptBit_eq_true_iff (q : Q) (summary : AnalysisSummary A) :
    acceptBit A q summary = true ↔ acceptsFromSummary A q summary := by
  classical
  simp [acceptBit]

theorem acceptBit_eq_false_iff (q : Q) (summary : AnalysisSummary A) :
    acceptBit A q summary = false ↔ ¬ acceptsFromSummary A q summary := by
  classical
  simp [acceptBit]

theorem topStops_eq_stopsFromSummary (q : Q) (top : TotalStackSymbol A) :
    topStops A q top ↔ stopsFromSummary A q (fullSummaryOfTop A top) := by
  cases top with
  | none => rfl
  | some payload =>
      rcases payload with ⟨Z, below⟩
      simp [topStops, stopsFromSummary, fullSummaryOfTop, AnalysisSummary.above,
        DFA.summaryAbove, DFA.stackSummary, DFA.evalFrom]

theorem topAccepts_eq_acceptsFromSummary (q : Q) (top : TotalStackSymbol A) :
    topAcceptsEpsilonClosure A q top ↔ acceptsFromSummary A q (fullSummaryOfTop A top) := by
  cases top with
  | none => rfl
  | some payload =>
      rcases payload with ⟨Z, below⟩
      simp [topAcceptsEpsilonClosure, acceptsFromSummary, fullSummaryOfTop, AnalysisSummary.above,
        DFA.summaryAbove, DFA.stackSummary, DFA.evalFrom]

theorem topStops_semantic_of_stackWellAnnotated {top : TotalStackSymbol A}
    {rest : List (TotalStackSymbol A)}
    (hstack : StackWellAnnotated (A := A) (top :: rest)) (q : Q) :
    topStops A q top ↔
      ∃ c', M.EpsilonStopsAt (q, eraseAnnotatedStack (A := A) (top :: rest)) c' := by
  rw [topStops_eq_stopsFromSummary]
  exact stopsFromSummary_correct A (stackWellAnnotated_fullSummaryOfTop (A := A) hstack) q

theorem topAccepts_semantic_of_stackWellAnnotated {top : TotalStackSymbol A}
    {rest : List (TotalStackSymbol A)}
    (hstack : StackWellAnnotated (A := A) (top :: rest)) (q : Q) :
    topAcceptsEpsilonClosure A q top ↔
      ∃ q' γ',
        M.EpsilonReaches (q, eraseAnnotatedStack (A := A) (top :: rest)) (q', γ') ∧
          q' ∈ M.final_states := by
  rw [topAccepts_eq_acceptsFromSummary]
  exact acceptsFromSummary_correct A (stackWellAnnotated_fullSummaryOfTop (A := A) hstack) q

theorem topStops_none_correct (q : Q) :
    topStops A q none ↔ ∃ c', M.EpsilonStopsAt (q, ([] : List S)) c' := by
  rw [topStops_eq_stopsFromSummary]
  exact stopsFromSummary_correct A (summaryRepresents_id A) q

theorem topAccepts_none_correct (q : Q) :
    topAcceptsEpsilonClosure A q none ↔
      ∃ q' γ', M.EpsilonReaches (q, ([] : List S)) (q', γ') ∧ q' ∈ M.final_states := by
  rw [topAccepts_eq_acceptsFromSummary]
  exact acceptsFromSummary_correct A (summaryRepresents_id A) q

theorem topStops_some_semantic {below : AnalysisSummary A} {γ : List S}
    (hbelow : SummaryRepresents A below γ) (q : Q) (Z : S) :
    topStops A q (some (Z, below)) ↔ ∃ c', M.EpsilonStopsAt (q, Z :: γ) c' := by
  rw [topStops_eq_stopsFromSummary]
  exact stopsFromSummary_correct A (hbelow.cons (A := A) Z) q

theorem topAccepts_some_semantic {below : AnalysisSummary A} {γ : List S}
    (hbelow : SummaryRepresents A below γ) (q : Q) (Z : S) :
    topAcceptsEpsilonClosure A q (some (Z, below)) ↔
      ∃ q' γ', M.EpsilonReaches (q, Z :: γ) (q', γ') ∧ q' ∈ M.final_states := by
  rw [topAccepts_eq_acceptsFromSummary]
  exact acceptsFromSummary_correct A (hbelow.cons (A := A) Z) q

end

end DPDA
