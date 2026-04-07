import Mathlib
import Langlib.Automata.LinearBounded.Definition
import Langlib.Classes.ContextSensitive.Definition
import Langlib.Grammars.ContextSensitive.Toolbox
import Langlib.Grammars.Unrestricted.Definition
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Grammars.NonContracting.Equivalence.ContextSensitive

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
  | cellPending (lb rb : Bool) (q' : Λ) (a : Γ) (t : T) : MyhillNT T Γ Λ
  deriving DecidableEq

instance [Fintype T] [Fintype Γ] [Fintype Λ] : Fintype (MyhillNT T Γ Λ) := by
  have : Fintype (Bool × Bool × Option Λ × Γ × T) := inferInstance
  have : Fintype (Bool × Bool × Λ × Γ × T) := inferInstance
  exact Fintype.ofEquiv
    (Unit ⊕ Unit ⊕ (Bool × Bool × Option Λ × Γ × T) ⊕ (Bool × Bool × Λ × Γ × T))
    { toFun := fun
        | .inl () => .start
        | .inr (.inl ()) => .startAux
        | .inr (.inr (.inl (lb, rb, q, a, t))) => .cell lb rb q a t
        | .inr (.inr (.inr (lb, rb, q', a, t))) => .cellPending lb rb q' a t
      invFun := fun
        | .start => .inl ()
        | .startAux => .inr (.inl ())
        | .cell lb rb q a t => .inr (.inr (.inl (lb, rb, q, a, t)))
        | .cellPending lb rb q' a t => .inr (.inr (.inr (lb, rb, q', a, t)))
      left_inv := by rintro (_ | _ | ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩) <;> rfl
      right_inv := by intro x; cases x <;> rfl }

/-- Abbreviation for a cell nonterminal as a grammar symbol. -/
abbrev cellSym (lb rb : Bool) (q : Option Λ) (a : Γ) (t : T) :
    symbol T (MyhillNT T Γ Λ) :=
  symbol.nonterminal (MyhillNT.cell lb rb q a t)

/-- Abbreviation for a cellPending nonterminal as a grammar symbol. -/
abbrev cellPendingSym (lb rb : Bool) (q' : Λ) (a : Γ) (t : T) :
    symbol T (MyhillNT T Γ Λ) :=
  symbol.nonterminal (MyhillNT.cellPending lb rb q' a t)

variable (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)

/-- All grammar rules for the Myhill construction, organized by phase. -/
def myhillAllRules : List (csrule T (MyhillNT T Γ Λ)) :=
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .start, [], [cellSym true true (some M.initial) (embed t) t]⟩)
  ++
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .start, [], [cellSym true false (some M.initial) (embed t) t,
                       symbol.nonterminal .startAux]⟩)
  ++
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .startAux, [], [cellSym false false none (embed t) t,
                          symbol.nonterminal .startAux]⟩)
  ++
  (Finset.univ.toList : List T).map (fun t =>
    ⟨[], .startAux, [], [cellSym false true none (embed t) t]⟩)
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
        let lb₁ ← [true, false]
        let rb₂ ← [true, false]
        pure ⟨[], MyhillNT.cell lb₁ false (some q) a t₁,
              [cellSym false rb₂ hi b t₂],
              [cellPendingSym lb₁ false q' a' t₁]⟩
      else [])
  ++
  (do let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      let t₁ ← (Finset.univ.toList : List T)
      let t₂ ← (Finset.univ.toList : List T)
      let hi ← (Finset.univ.toList : List (Option Λ))
      let b ← (Finset.univ.toList : List Γ)
      let lb₁ ← [true, false]
      let rb₂ ← [true, false]
      pure ⟨[cellPendingSym lb₁ false q' a' t₁],
            MyhillNT.cell false rb₂ hi b t₂, [],
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
        let rb₂ ← [true, false]
        pure ⟨[cellSym lb₁ false hi b t₁],
              MyhillNT.cell false rb₂ (some q) a t₂, [],
              [cellPendingSym false rb₂ q' a' t₂]⟩
      else [])
  ++
  (do let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      let t₁ ← (Finset.univ.toList : List T)
      let t₂ ← (Finset.univ.toList : List T)
      let hi ← (Finset.univ.toList : List (Option Λ))
      let b ← (Finset.univ.toList : List Γ)
      let lb₁ ← [true, false]
      let rb₂ ← [true, false]
      pure ⟨[], MyhillNT.cell lb₁ false hi b t₁,
            [cellPendingSym false rb₂ q' a' t₂],
            [cellSym lb₁ false (some q') b t₁]⟩)
  ++
  (do let q' ← (Finset.univ.toList : List Λ)
      let a' ← (Finset.univ.toList : List Γ)
      let t ← (Finset.univ.toList : List T)
      let lb ← [true, false]
      let rb ← [true, false]
      pure ⟨[], MyhillNT.cellPending lb rb q' a' t, [],
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

lemma single_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.start, [], [cellSym true true (some M.initial) (embed t) t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  simp [myhillAllRules]

lemma first_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.start, [],
      [cellSym true false (some M.initial) (embed t) t,
       symbol.nonterminal .startAux]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append]

lemma middle_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.startAux, [],
      [cellSym false false none (embed t) t,
       symbol.nonterminal .startAux]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide

lemma last_cell_init_rule_mem (t : T) :
    (⟨[], MyhillNT.startAux, [],
      [cellSym false true none (embed t) t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  aesop

lemma accept_rule_mem (q : Λ) (hq : M.accept q = true) (a : Γ) (t : T)
    (lb rb : Bool) :
    (⟨[], MyhillNT.cell lb rb (some q) a t, [],
      [symbol.terminal t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_flatMap, List.mem_map]
  grind +extAll

lemma left_propagation_rule_mem (t₁ : T) (a : Γ) (t₂ : T)
    (lb rb : Bool) :
    (⟨[symbol.terminal t₁],
      MyhillNT.cell lb rb none a t₂, [],
      [symbol.terminal t₂]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide
  grind +ring

lemma right_propagation_rule_mem (a : Γ) (t₁ t₂ : T)
    (lb rb : Bool) :
    (⟨[], MyhillNT.cell lb rb none a t₁,
      [symbol.terminal t₂],
      [symbol.terminal t₁]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_map]
  exact ⟨a, t₁, t₂, by cases lb <;> cases rb <;> aesop⟩

/-! ### Simulation rule membership lemmas -/

lemma sim_stay_rule_mem (q q' : Λ) (a a' : Γ) (t : T) (lb rb : Bool)
    (h : (q', a', DLBA.Dir.stay) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell lb rb (some q) a t, [],
      [cellSym lb rb (some q') a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [h]
  use q, a, q', a'
  cases lb <;> cases rb <;> simp +decide [*]

lemma sim_right_boundary_rule_mem (q q' : Λ) (a a' : Γ) (t : T) (lb : Bool)
    (h : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell lb true (some q) a t, [],
      [cellSym lb true (some q') a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp_all +decide [Finset.mem_toList]
  grind

lemma sim_left_boundary_rule_mem (q q' : Λ) (a a' : Γ) (t : T) (rb : Bool)
    (h : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell true rb (some q) a t, [],
      [cellSym true rb (some q') a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  simp [myhillAllRules, h]
  grind

lemma sim_right_interior_step1_mem (q q' : Λ) (a a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (rb₂ : Bool) (hi : Option Λ) (b : Γ)
    (h : (q', a', DLBA.Dir.right) ∈ M.transition q a) :
    (⟨[], MyhillNT.cell lb₁ false (some q) a t₁,
      [cellSym false rb₂ hi b t₂],
      [cellPendingSym lb₁ false q' a' t₁]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  convert List.mem_append.mpr _ using 1
  simp +zetaDelta at *
  exact ⟨q, a, q', a', h, t₁, t₂, hi, b, by cases lb₁ <;> cases rb₂ <;> aesop⟩

lemma sim_right_interior_step2_mem (q' : Λ) (a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (rb₂ : Bool) (hi : Option Λ) (b : Γ) :
    (⟨[cellPendingSym lb₁ false q' a' t₁],
      MyhillNT.cell false rb₂ hi b t₂, [],
      [cellSym false rb₂ (some q') b t₂]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_map]
  cases lb₁ <;> cases rb₂ <;> aesop

lemma sim_left_interior_step1_mem (q q' : Λ) (a a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (rb₂ : Bool) (hi : Option Λ) (b : Γ)
    (h : (q', a', DLBA.Dir.left) ∈ M.transition q a) :
    (⟨[cellSym lb₁ false hi b t₁],
      MyhillNT.cell false rb₂ (some q) a t₂, [],
      [cellPendingSym false rb₂ q' a' t₂]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [h]
  exact ⟨q, a, q', a', h, t₁, t₂, hi, b, by cases lb₁ <;> cases rb₂ <;> aesop⟩

lemma sim_left_interior_step2_mem (q' : Λ) (a' : Γ) (t₁ t₂ : T)
    (lb₁ : Bool) (rb₂ : Bool) (hi : Option Λ) (b : Γ) :
    (⟨[], MyhillNT.cell lb₁ false hi b t₁,
      [cellPendingSym false rb₂ q' a' t₂],
      [cellSym lb₁ false (some q') b t₁]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  revert q' a' t₁ t₂ lb₁ rb₂ hi b
  simp [myhillAllRules]

lemma pending_resolution_rule_mem (q' : Λ) (a' : Γ) (t : T) (lb rb : Bool) :
    (⟨[], MyhillNT.cellPending lb rb q' a' t, [],
      [cellSym lb rb none a' t]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed := by
  unfold myhillAllRules
  simp +decide [List.mem_append, List.mem_map]
  exact ⟨q', a', t, by cases lb <;> cases rb <;> aesop⟩

end MyhillConstruction
