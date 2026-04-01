import Mathlib
import Grammars.Automata.Turing.Basics.Definition
import Grammars.Classes.Unrestricted.Basics.Definition
import Grammars.Classes.Unrestricted.Basics.Toolbox

/-! # Equivalence of Unrestricted Grammars and Turing Machines

This file defines the grammar construction for simulating TM0 machines, and states
the equivalence between unrestricted (Type-0) grammars and Turing machines.

The correctness proofs and the main equivalence theorem are in `TMtoGrammarHelpers.lean`.

## Main definitions

- `is_TM_recognizable`: A language is TM-recognizable if there exists a finite-state
  Turing machine (using Mathlib's `Turing.TM0` model) that halts on input `w` iff `w ∈ L`.
- `TMtoGrammarNT`: Nonterminal symbols for the grammar simulating a TM.
- `tmToGrammar`: The grammar that simulates a TM0 machine.
-/

open Turing

/-! ### Construction

We construct an unrestricted grammar that simulates a TM0 machine using
"two-track" nonterminals. -/

section TMtoGrammar

variable (T : Type) [DecidableEq T] [Fintype T]
         (Λ : Type) [Inhabited Λ] [DecidableEq Λ] [Fintype Λ]

/-- Nonterminals for the grammar simulating a TM0 machine.

- `start`: Initial symbol
- `genMore`: Generation-phase marker for adding more input cells
- `cell orig cur`: Tape cell with original input `orig` and current content `cur`
- `headCell q orig cur`: Head position in state `q`, original input `orig`, current `cur`
- `leftBound` / `rightBound`: Tape boundary markers
- `haltCell orig`: Cell in cleanup phase, remembering original input `orig`
-/
inductive TMtoGrammarNT where
  | start        : TMtoGrammarNT
  | genMore      : TMtoGrammarNT
  | cell         : Option T → Option T → TMtoGrammarNT
  | headCell     : Λ → Option T → Option T → TMtoGrammarNT
  | leftBound    : TMtoGrammarNT
  | rightBound   : TMtoGrammarNT
  | haltCell     : Option T → TMtoGrammarNT

open TMtoGrammarNT

/-- All values of `Option T`. -/
noncomputable def allOptT : List (Option T) :=
  none :: (Finset.univ.val.toList.map some)

/-- All values of `Λ`. -/
noncomputable def allΛ : List Λ :=
  Finset.univ.val.toList

/-- Generation rules: nondeterministically create an initial TM configuration
for an arbitrary input word.

The grammar builds the initial configuration from right to left:
1. `S → leftBound · genMore · rightBound`
2. Repeatedly: `genMore → genMore · cell(some t, some t)` (adds cells to the RIGHT)
3. Finally: `genMore → headCell(q₀, some t, some t)` or `genMore → headCell(q₀, none, none)`
   (replaces genMore with the TM head, placing it at the leftmost position)

For input `[t₁, t₂, ..., tₙ]`, the derivation is:
  `S → LB · genMore · RB`
  `→ LB · genMore · cell(tₙ) · RB`
  `→ ... → LB · genMore · cell(t₂) · ... · cell(tₙ) · RB`
  `→ LB · headCell(q₀, t₁) · cell(t₂) · ... · cell(tₙ) · RB`
-/
noncomputable def generationRules (_ : Turing.TM0.Machine (Option T) Λ) :
    List (grule T (TMtoGrammarNT T Λ)) :=
  -- S → leftBound genMore rightBound
  [⟨[], start, [], [.nonterminal leftBound, .nonterminal genMore, .nonterminal rightBound]⟩] ++
  -- For each t: genMore → genMore · cell(some t, some t)  (add cell to the right)
  (Finset.univ.val.toList.map fun (t : T) =>
    (⟨[], genMore, [],
      [.nonterminal genMore, .nonterminal (cell (some t) (some t))]⟩ :
      grule T (TMtoGrammarNT T Λ))) ++
  -- For each t: genMore → headCell(q₀, some t, some t)  (place head, end generation)
  (Finset.univ.val.toList.map fun (t : T) =>
    (⟨[], genMore, [],
      [.nonterminal (headCell (default : Λ) (some t) (some t))]⟩ :
      grule T (TMtoGrammarNT T Λ))) ++
  -- Empty input: genMore · rightBound → headCell(q₀, none, none) · rightBound
  -- (Context ensures this only fires when no cells have been generated.)
  [⟨[], genMore, [.nonterminal rightBound],
    [.nonterminal (headCell (default : Λ) none none), .nonterminal rightBound]⟩]

/-- Simulation rules: encode TM transitions as grammar rules.

For each `(q, γ)` with `M q γ = some (q', action)`:
- **Write γ'**: `headCell(q, orig, γ) → headCell(q', orig, γ')`
- **Move right**: `headCell(q, orig, γ) cell(orig', γ') → cell(orig, γ) headCell(q', orig', γ')`
  (with boundary extension when at the right edge)
- **Move left**: `cell(o'', γ'') headCell(q, orig, γ) → headCell(q', o'', γ'') cell(orig, γ)`
  (with boundary extension when at the left edge)
-/
noncomputable def simulationRules (M : Turing.TM0.Machine (Option T) Λ) :
    List (grule T (TMtoGrammarNT T Λ)) :=
  (allΛ Λ).flatMap fun q =>
    (allOptT T).flatMap fun γ =>
      match M q γ with
      | none => []
      | some (q', Turing.TM0.Stmt.write γ') =>
        -- Write: headCell(q, orig, γ) → headCell(q', orig, γ')
        (allOptT T).map fun orig =>
          (⟨[], headCell q orig γ, [],
            [.nonterminal (headCell q' orig γ')]⟩ : grule T (TMtoGrammarNT T Λ))
      | some (q', Turing.TM0.Stmt.move Dir.right) =>
        -- Move right with neighbor
        ((allOptT T).flatMap fun orig =>
          (allOptT T).flatMap fun orig' =>
            (allOptT T).map fun γ' =>
              (⟨[], headCell q orig γ, [.nonterminal (cell orig' γ')],
                [.nonterminal (cell orig γ),
                 .nonterminal (headCell q' orig' γ')]⟩ : grule T (TMtoGrammarNT T Λ))) ++
        -- Move right at right boundary (extend tape)
        ((allOptT T).map fun orig =>
          (⟨[], headCell q orig γ, [.nonterminal rightBound],
            [.nonterminal (cell orig γ),
             .nonterminal (headCell q' none none),
             .nonterminal rightBound]⟩ : grule T (TMtoGrammarNT T Λ)))
      | some (q', Turing.TM0.Stmt.move Dir.left) =>
        -- Move left with neighbor
        ((allOptT T).flatMap fun orig =>
          (allOptT T).flatMap fun orig'' =>
            (allOptT T).map fun γ'' =>
              (⟨[.nonterminal (cell orig'' γ'')], headCell q orig γ, [],
                [.nonterminal (headCell q' orig'' γ''),
                 .nonterminal (cell orig γ)]⟩ : grule T (TMtoGrammarNT T Λ))) ++
        -- Move left at left boundary (extend tape)
        ((allOptT T).map fun orig =>
          (⟨[.nonterminal leftBound], headCell q orig γ, [],
            [.nonterminal leftBound,
             .nonterminal (headCell q' none none),
             .nonterminal (cell orig γ)]⟩ : grule T (TMtoGrammarNT T Λ)))

/-- Cleanup rules: when TM halts, extract original input as terminals.

1. Convert halted head cell to halt marker
2. Propagate halt to all remaining cells
3. Replace halt markers with original terminal symbols (or ε for blanks)
4. Remove boundary markers
-/
noncomputable def cleanupRules (M : Turing.TM0.Machine (Option T) Λ) :
    List (grule T (TMtoGrammarNT T Λ)) :=
  -- headCell → haltCell when M q γ = none (TM halts)
  ((allΛ Λ).flatMap fun q =>
    (allOptT T).flatMap fun γ =>
      match M q γ with
      | none =>
        (allOptT T).map fun orig =>
          (⟨[], headCell q orig γ, [],
            [.nonterminal (haltCell orig)]⟩ : grule T (TMtoGrammarNT T Λ))
      | some _ => []) ++
  -- Propagate halt right: haltCell cell → haltCell haltCell
  ((allOptT T).flatMap fun orig =>
    (allOptT T).flatMap fun orig' =>
      (allOptT T).map fun γ' =>
        (⟨[], haltCell orig, [.nonterminal (cell orig' γ')],
          [.nonterminal (haltCell orig),
           .nonterminal (haltCell orig')]⟩ : grule T (TMtoGrammarNT T Λ))) ++
  -- Propagate halt left: cell haltCell → haltCell haltCell
  ((allOptT T).flatMap fun orig =>
    (allOptT T).flatMap fun orig'' =>
      (allOptT T).map fun γ'' =>
        (⟨[.nonterminal (cell orig'' γ'')], haltCell orig, [],
          [.nonterminal (haltCell orig''),
           .nonterminal (haltCell orig)]⟩ : grule T (TMtoGrammarNT T Λ))) ++
  -- haltCell(some t) → terminal t
  (Finset.univ.val.toList.map fun (t : T) =>
    (⟨[], haltCell (some t), [], [.terminal t]⟩ : grule T (TMtoGrammarNT T Λ))) ++
  -- haltCell(none) → ε (erase blank cells)
  [(⟨[], haltCell none, [], []⟩ : grule T (TMtoGrammarNT T Λ))] ++
  -- Remove boundary markers (context-dependent to prevent removal during generation/simulation)
  -- LB · RB → ε  (empty tape case)
  [(⟨[], leftBound, [.nonterminal rightBound], []⟩ : grule T (TMtoGrammarNT T Λ))] ++
  -- LB · haltCell(orig) → haltCell(orig)  (remove LB when next to haltCell)
  ((allOptT T).map fun orig =>
    (⟨[], leftBound, [.nonterminal (haltCell orig)],
      [.nonterminal (haltCell orig)]⟩ : grule T (TMtoGrammarNT T Λ))) ++
  -- haltCell(orig) · RB → haltCell(orig)  (remove RB when next to haltCell)
  ((allOptT T).map fun orig =>
    (⟨[.nonterminal (haltCell orig)], rightBound, [],
      [.nonterminal (haltCell orig)]⟩ : grule T (TMtoGrammarNT T Λ)))

/-- The grammar simulating TM0 machine `M`. -/
noncomputable def tmToGrammar (M : Turing.TM0.Machine (Option T) Λ) :
    grammar T where
  nt := TMtoGrammarNT T Λ
  initial := start
  rules := generationRules T Λ M ++ simulationRules T Λ M ++ cleanupRules T Λ M

end TMtoGrammar
