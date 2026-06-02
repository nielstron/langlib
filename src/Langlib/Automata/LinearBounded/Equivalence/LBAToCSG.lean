module

public import Langlib.Automata.LinearBounded.Definition
public import Langlib.Grammars.ContextSensitive.Definition
public import Mathlib.Data.Fintype.Option
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
@[expose]
public section



/-!
# LBA → Context-Sensitive Grammar (Myhill's Construction)

This file constructs a context-sensitive grammar from a nondeterministic linear
bounded automaton (LBA), establishing the direction LBA → CSG.

Given an LBA `M` with tape alphabet `Γ`, states `Λ`, and input embedding `embed : T ↪ Γ`,
we construct a context-sensitive grammar whose language equals the LBA's language.

The nonterminals encode the LBA's computation at each tape cell, simulation rules
mirror transitions, and cleanup rules recover terminals upon acceptance.

## Simulation rules

For interior head moves (left/right), the simulation uses a three-step process because
CS rules can only rewrite one nonterminal at a time:

1. **Step 1**: Remove the head from the current cell, write the new tape symbol,
   and record the pending state in a `cellPending` nonterminal. The transition
   check `(q', a', d) ∈ M.transition q a` is enforced here.

2. **Step 2**: Place the head on the adjacent cell with the correct state `q'`.
   The state is read from the `cellPending` context, ensuring correctness.

3. **Step 3**: Convert the `cellPending` nonterminal back to a normal `cell`
   with `q = none`.

## References

* Myhill, J. (1960), "Linear bounded automata"
* Hopcroft, Motwani, Ullman, *Introduction to Automata Theory*, Chapter 9
-/

open List Relation Classical

noncomputable section

namespace MyhillConstruction

variable {T Γ Λ : Type}
variable [Fintype T] [Fintype Γ] [Fintype Λ]
variable [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

/-! ### Nonterminal Type -/

/-- Nonterminals for the Myhill construction. -/
inductive MyhillNT (T Γ Λ : Type) where
  | start : MyhillNT T Γ Λ
  | startAux : MyhillNT T Γ Λ
  | cell (lb rb : Bool) (q : Option Λ) (a : Γ) (t : T) : MyhillNT T Γ Λ
  | cellPending (lb rb dir : Bool) (q' : Λ) (a : Γ) (t : T) : MyhillNT T Γ Λ
  deriving DecidableEq

instance [Fintype T] [Fintype Γ] [Fintype Λ] : Fintype (MyhillNT T Γ Λ) := by
  have : Fintype (Bool × Bool × Option Λ × Γ × T) := inferInstance
  have : Fintype (Bool × Bool × Bool × Λ × Γ × T) := inferInstance
  exact Fintype.ofEquiv
    (Unit ⊕ Unit ⊕ (Bool × Bool × Option Λ × Γ × T) ⊕ (Bool × Bool × Bool × Λ × Γ × T))
    { toFun := fun
        | .inl () => .start
        | .inr (.inl ()) => .startAux
        | .inr (.inr (.inl (lb, rb, q, a, t))) => .cell lb rb q a t
        | .inr (.inr (.inr (lb, rb, dir, q', a, t))) => .cellPending lb rb dir q' a t
      invFun := fun
        | .start => .inl ()
        | .startAux => .inr (.inl ())
        | .cell lb rb q a t => .inr (.inr (.inl (lb, rb, q, a, t)))
        | .cellPending lb rb dir q' a t => .inr (.inr (.inr (lb, rb, dir, q', a, t)))
      left_inv := by rintro (_ | _ | ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _, _⟩) <;> rfl
      right_inv := by intro x; cases x <;> rfl }

/-- Abbreviation for a cell nonterminal as a grammar symbol. -/
abbrev cellSym (lb rb : Bool) (q : Option Λ) (a : Γ) (t : T) :
    symbol T (MyhillNT T Γ Λ) :=
  symbol.nonterminal (MyhillNT.cell lb rb q a t)

/-- Abbreviation for a cellPending nonterminal as a grammar symbol. The `dir` flag records the
move direction (`true` = right move, `false` = left move) so that only the matching `step2`
rule can consume the pending — without it, an interior pending `(false, false)` would be
accepted by both step2 rules, letting a right move's state land on the wrong (left) neighbour. -/
abbrev cellPendingSym (lb rb dir : Bool) (q' : Λ) (a : Γ) (t : T) :
    symbol T (MyhillNT T Γ Λ) :=
  symbol.nonterminal (MyhillNT.cellPending lb rb dir q' a t)

variable (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)

/-- All grammar rules for the Myhill construction, organized by phase. -/
def myhillAllRules : List (csrule T (MyhillNT T Γ Λ)) :=
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .start, [], [cellSym true true (some M.initial) (embed t) t]⟩)
  ++
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .start, [], [symbol.nonterminal .startAux,
                       cellSym false true none (embed t) t]⟩)
  ++
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .startAux, [], [symbol.nonterminal .startAux,
                          cellSym false false none (embed t) t]⟩)
  ++
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .startAux, [], [cellSym true false (some M.initial) (embed t) t]⟩)
  ++
  (do let q ← (Finset.univ.toList : List Λ)
      let a ← (Finset.univ.toList : List Γ)
      let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      let d ← [DLBA.Dir.stay, DLBA.Dir.left, DLBA.Dir.right]
      if h : (q', a', d) ∈ M.transition q a then
        let t ← (Finset.univ.toList : List T)
        let lb ← [true, false]
        let rb ← [true, false]
        if d = DLBA.Dir.stay then
          pure ⟨[], MyhillNT.cell lb rb (some q) a t, [],
                [cellSym lb rb (some q') a' t]⟩
        else if d = DLBA.Dir.right ∧ rb = true then
          pure ⟨[], MyhillNT.cell lb true (some q) a t, [],
                [cellSym lb true (some q') a' t]⟩
        else if d = DLBA.Dir.left ∧ lb = true then
          pure ⟨[], MyhillNT.cell true rb (some q) a t, [],
                [cellSym true rb (some q') a' t]⟩
        else []
      else [])
  ++
  (do let q ← (Finset.univ.toList : List Λ)
      let a ← (Finset.univ.toList : List Γ)
      let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      if h : (q', a', DLBA.Dir.right) ∈ M.transition q a then
        let t₁ ← (Finset.univ.toList : List T)
        let t₂ ← (Finset.univ.toList : List T)
        let hi ← (Finset.univ.toList : List (Option Λ))
        let b ← (Finset.univ.toList : List Γ)
        let rb₂ ← [true, false]
        pure ⟨[], MyhillNT.cell true false (some q) a t₁,
              [cellSym false rb₂ hi b t₂],
              [cellPendingSym true false true q' a' t₁]⟩
      else [])
  ++
  (do let q ← (Finset.univ.toList : List Λ)
      let a ← (Finset.univ.toList : List Γ)
      let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      if h : (q', a', DLBA.Dir.right) ∈ M.transition q a then
        let t₁ ← (Finset.univ.toList : List T)
        let t₂ ← (Finset.univ.toList : List T)
        let hi ← (Finset.univ.toList : List (Option Λ))
        let b ← (Finset.univ.toList : List Γ)
        let rb₂ ← [true, false]
        let lb₀ ← [true, false]
        let a₀ ← (Finset.univ.toList : List Γ)
        let t₀ ← (Finset.univ.toList : List T)
        pure ⟨[cellSym lb₀ false none a₀ t₀], MyhillNT.cell false false (some q) a t₁,
              [cellSym false rb₂ hi b t₂],
              [cellPendingSym false false true q' a' t₁]⟩
      else [])
  ++
  (do let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      let t₁ ← (Finset.univ.toList : List T)
      let t₂ ← (Finset.univ.toList : List T)
      let b ← (Finset.univ.toList : List Γ)
      let lb₁ ← [true, false]
      let rb₂ ← [true, false]
      pure ⟨[cellPendingSym lb₁ false true q' a' t₁],
            MyhillNT.cell false rb₂ none b t₂, [],
            [cellSym false rb₂ (some q') b t₂]⟩)
  ++
  (do let q ← (Finset.univ.toList : List Λ)
      let a ← (Finset.univ.toList : List Γ)
      let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      if h : (q', a', DLBA.Dir.left) ∈ M.transition q a then
        let t₁ ← (Finset.univ.toList : List T)
        let t₂ ← (Finset.univ.toList : List T)
        let hi ← (Finset.univ.toList : List (Option Λ))
        let b ← (Finset.univ.toList : List Γ)
        let lb₁ ← [true, false]
        pure ⟨[cellSym lb₁ false hi b t₁],
              MyhillNT.cell false true (some q) a t₂, [],
              [cellPendingSym false true false q' a' t₂]⟩
      else [])
  ++
  (do let q ← (Finset.univ.toList : List Λ)
      let a ← (Finset.univ.toList : List Γ)
      let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      if h : (q', a', DLBA.Dir.left) ∈ M.transition q a then
        let t₁ ← (Finset.univ.toList : List T)
        let t₂ ← (Finset.univ.toList : List T)
        let hi ← (Finset.univ.toList : List (Option Λ))
        let b ← (Finset.univ.toList : List Γ)
        let lb₁ ← [true, false]
        let rb₀ ← [true, false]
        let a₀ ← (Finset.univ.toList : List Γ)
        let t₀ ← (Finset.univ.toList : List T)
        pure ⟨[cellSym lb₁ false hi b t₁],
              MyhillNT.cell false false (some q) a t₂, [cellSym false rb₀ none a₀ t₀],
              [cellPendingSym false false false q' a' t₂]⟩
      else [])
  ++
  (do let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      let t₁ ← (Finset.univ.toList : List T)
      let t₂ ← (Finset.univ.toList : List T)
      let b ← (Finset.univ.toList : List Γ)
      let lb₁ ← [true, false]
      let rb₂ ← [true, false]
      pure ⟨[], MyhillNT.cell lb₁ false none b t₁,
            [cellPendingSym false rb₂ false q' a' t₂],
            [cellSym lb₁ false (some q') b t₁]⟩)
  ++
  (do let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      let t ← (Finset.univ.toList : List T)
      let lb ← [true, false]
      let rb ← [true, false]
      let dir ← [true, false]
      pure ⟨[], MyhillNT.cellPending lb rb dir q' a' t, [],
            [cellSym lb rb none a' t]⟩)
  ++
  (do let q ← (Finset.univ.toList : List Λ)
      if M.accept q = true then
        let a ← (Finset.univ.toList : List Γ)
        let t ← (Finset.univ.toList : List T)
        let lb ← [true, false]
        let rb ← [true, false]
        pure ⟨[], MyhillNT.cell lb rb (some q) a t, [],
              [symbol.terminal t]⟩
      else [])
  ++
  (do let t₁ ← (Finset.univ.toList : List T)
      let a ← (Finset.univ.toList : List Γ)
      let t₂ ← (Finset.univ.toList : List T)
      let lb ← [true, false]
      let rb ← [true, false]
      pure ⟨[symbol.terminal t₁],
            MyhillNT.cell lb rb none a t₂, [],
            [symbol.terminal t₂]⟩)
  ++
  (do let a ← (Finset.univ.toList : List Γ)
      let t₁ ← (Finset.univ.toList : List T)
      let t₂ ← (Finset.univ.toList : List T)
      let lb ← [true, false]
      let rb ← [true, false]
      pure ⟨[], MyhillNT.cell lb rb none a t₁,
            [symbol.terminal t₂],
            [symbol.terminal t₁]⟩)

set_option maxHeartbeats 1000000 in
/-- Every rule in the Myhill construction has non-empty output string. -/
theorem myhillAllRules_output_nonempty :
    ∀ r ∈ myhillAllRules M embed, r.output_string ≠ [] := by
  unfold myhillAllRules
  aesop

/-- The Myhill context-sensitive grammar recognizing the LBA's language. -/
def myhillGrammar : CS_grammar T where
  nt := MyhillNT T Γ Λ
  initial := MyhillNT.start
  rules := myhillAllRules M embed
  output_nonempty := myhillAllRules_output_nonempty M embed

public lemma single_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.start, [], [cellSym true true (some M.initial) (embed t) t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  simp [myhillAllRules]

/-- Rightmost initial cell (laid first, with `startAux` on its left). -/
public lemma right_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.start, [],
      [symbol.nonterminal .startAux,
       cellSym false true none (embed t) t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append]

/-- A middle initial cell, inserted just to the right of `startAux`. -/
public lemma middle_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.startAux, [],
      [symbol.nonterminal .startAux,
       cellSym false false none (embed t) t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide

/-- Leftmost initial cell carrying the start state (laid last, removing `startAux`). -/
public lemma left_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.startAux, [],
      [cellSym true false (some M.initial) (embed t) t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  aesop

public lemma accept_rule_mem (q : Λ) (hq : M.accept q = true) (a : Γ) (t : T)
    (lb rb : Bool) :
    (⟨[], MyhillNT.cell lb rb (some q) a t, [],
      [symbol.terminal t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_flatMap, List.mem_map]
  grind +extAll

public lemma left_propagation_rule_mem (t₁ : T) (a : Γ) (t₂ : T)
    (lb rb : Bool) :
    (⟨[symbol.terminal t₁],
      MyhillNT.cell lb rb none a t₂, [],
      [symbol.terminal t₂]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide
  grind +ring

public lemma right_propagation_rule_mem (a : Γ) (t₁ t₂ : T)
    (lb rb : Bool) :
    (⟨[], MyhillNT.cell lb rb none a t₁,
      [symbol.terminal t₂],
      [symbol.terminal t₁]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_map]
  exact ⟨a, t₁, t₂, by cases lb <;> cases rb <;> aesop⟩

/-! ### Simulation rule membership lemmas -/

public lemma sim_stay_rule_mem (q q' : Λ) (a a' : Γ) (t : T) (lb rb : Bool)
    (h : (q', a', DLBA.Dir.stay) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell lb rb (some q) a t, [],
      [cellSym lb rb (some q') a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [h]
  use q, a, q', a'
  cases lb <;> cases rb <;> simp +decide [*]

public lemma sim_right_boundary_rule_mem (q q' : Λ) (a a' : Γ) (t : T) (lb : Bool)
    (h : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell lb true (some q) a t, [],
      [cellSym lb true (some q') a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp_all +decide [Finset.mem_toList]
  grind

public lemma sim_left_boundary_rule_mem (q q' : Λ) (a a' : Γ) (t : T) (rb : Bool)
    (h : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell true rb (some q) a t, [],
      [cellSym true rb (some q') a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  simp [myhillAllRules, h]
  grind

set_option maxHeartbeats 1000000 in
public lemma sim_right_interior_step1_boundary_mem (q q' : Λ) (a a' : Γ) (t₁ t₂ : T)
    (rb₂ : Bool) (hi : Option Λ) (b : Γ)
    (h : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell true false (some q) a t₁,
      [cellSym false rb₂ hi b t₂],
      [cellPendingSym true false true q' a' t₁]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp only [List.mem_append]
  iterate 9 apply Or.inl
  apply Or.inr
  simp +decide only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.bind_eq_flatMap, bind, List.mem_ite_nil_right, List.mem_dite_nil_right,
    List.pure_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  exact ⟨q, a, q', a', h, t₁, t₂, hi, b, rb₂, by cases rb₂ <;> simp, rfl⟩

set_option maxHeartbeats 1000000 in
public lemma sim_right_interior_step1_interior_mem (q q' : Λ) (a a' : Γ) (t₁ t₂ : T)
    (rb₂ : Bool) (hi : Option Λ) (b : Γ) (lb₀ : Bool) (a₀ : Γ) (t₀ : T)
    (h : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
    (⟨[cellSym lb₀ false none a₀ t₀], MyhillNT.cell false false (some q) a t₁,
      [cellSym false rb₂ hi b t₂],
      [cellPendingSym false false true q' a' t₁]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp only [List.mem_append]
  iterate 8 apply Or.inl
  apply Or.inr
  simp +decide only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.bind_eq_flatMap, bind, List.mem_ite_nil_right, List.mem_dite_nil_right,
    List.pure_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  exact ⟨q, a, q', a', h, t₁, t₂, hi, b, rb₂, by cases rb₂ <;> simp, lb₀,
    by cases lb₀ <;> simp, a₀, t₀, rfl⟩

public lemma sim_right_interior_step2_mem (q' : Λ) (a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (rb₂ : Bool) (b : Γ) :
    (⟨[cellPendingSym lb₁ false true q' a' t₁],
      MyhillNT.cell false rb₂ none b t₂, [],
      [cellSym false rb₂ (some q') b t₂]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_map]
  cases lb₁ <;> cases rb₂ <;> aesop

set_option maxHeartbeats 1000000 in
public lemma sim_left_interior_step1_boundary_mem (q q' : Λ) (a a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (hi : Option Λ) (b : Γ)
    (h : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
    (⟨[cellSym lb₁ false hi b t₁],
      MyhillNT.cell false true (some q) a t₂, [],
      [cellPendingSym false true false q' a' t₂]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp only [List.mem_append]
  iterate 6 apply Or.inl
  apply Or.inr
  simp +decide only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.bind_eq_flatMap, bind, List.mem_ite_nil_right, List.mem_dite_nil_right,
    List.pure_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  exact ⟨q, a, q', a', h, t₁, t₂, hi, b, lb₁, by cases lb₁ <;> simp, rfl⟩

set_option maxHeartbeats 1000000 in
public lemma sim_left_interior_step1_interior_mem (q q' : Λ) (a a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (hi : Option Λ) (b : Γ) (rb₀ : Bool) (a₀ : Γ) (t₀ : T)
    (h : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
    (⟨[cellSym lb₁ false hi b t₁],
      MyhillNT.cell false false (some q) a t₂, [cellSym false rb₀ none a₀ t₀],
      [cellPendingSym false false false q' a' t₂]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp only [List.mem_append]
  iterate 5 apply Or.inl
  apply Or.inr
  simp +decide only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.bind_eq_flatMap, bind, List.mem_ite_nil_right, List.mem_dite_nil_right,
    List.pure_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  exact ⟨q, a, q', a', h, t₁, t₂, hi, b, lb₁, by cases lb₁ <;> simp, rb₀,
    by cases rb₀ <;> simp, a₀, t₀, rfl⟩

public lemma sim_left_interior_step2_mem (q' : Λ) (a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (rb₂ : Bool) (b : Γ) :
    (⟨[], MyhillNT.cell lb₁ false none b t₁,
      [cellPendingSym false rb₂ false q' a' t₂],
      [cellSym lb₁ false (some q') b t₁]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  revert q' a' t₁ t₂ lb₁ rb₂ b
  simp [myhillAllRules]

public lemma pending_resolution_rule_mem (q' : Λ) (a' : Γ) (t : T) (lb rb dir : Bool) :
    (⟨[], MyhillNT.cellPending lb rb dir q' a' t, [],
      [cellSym lb rb none a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_map]
  exact ⟨q', a', t, by cases lb <;> cases rb <;> cases dir <;> aesop⟩

end MyhillConstruction
