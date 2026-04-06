import Mathlib
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Automata.Turing.Equivalence.TMToGrammar.Construction

/-! # Helper Lemmas for TM → Grammar Construction

This file contains the detailed helper lemmas needed to prove the correctness
of the `tmToGrammar` construction.

## Encoding TM configurations as sentential forms

A TM0 configuration `⟨q, tape⟩` together with an "original input track" is encoded
as a sentential form of the grammar. The encoding represents a finite window of the
tape as a sequence of `cell`/`headCell` nonterminals flanked by boundary markers.
-/

open Turing TMtoGrammarNT

variable {T : Type} [DecidableEq T] [Fintype T]
         {Λ : Type} [Inhabited Λ] [DecidableEq Λ] [Fintype Λ]

/-- A "two-track tape segment" encodes a finite portion of the TM tape
along with the original input at each position.

`leftCells` are the cells to the left of the head (in order from left to right).
`headState` is the TM state at the head position.
`headOrig` is the original input at the head position.
`headCur` is the current tape content at the head position.
`rightCells` are the cells to the right of the head (in order from left to right).

Each cell is a pair `(original, current)`. -/
structure TwoTrackConfig where
  leftCells  : List (Option T × Option T)
  headState  : Λ
  headOrig   : Option T
  headCur    : Option T
  rightCells : List (Option T × Option T)

/-- Encode a `TwoTrackConfig` as a sentential form of the grammar. -/
def encodeTwoTrack (cfg : @TwoTrackConfig T Λ) :
    List (symbol T (TMtoGrammarNT T Λ)) :=
  [.nonterminal leftBound] ++
  (cfg.leftCells.map fun ⟨orig, cur⟩ => .nonterminal (cell orig cur)) ++
  [.nonterminal (headCell cfg.headState cfg.headOrig cfg.headCur)] ++
  (cfg.rightCells.map fun ⟨orig, cur⟩ => .nonterminal (cell orig cur)) ++
  [.nonterminal rightBound]

/-- The initial two-track configuration for input `w`. The head is at the leftmost
position (or on blank for empty input). -/
def initTwoTrack (w : List T) : @TwoTrackConfig T Λ :=
  match w with
  | [] => ⟨[], default, none, none, []⟩
  | t :: ts => ⟨[], default, some t, some t,
                ts.map fun t' => (some t', some t')⟩

/-! ### Phase 1: Generation

The grammar derives the encoding of the initial configuration from [start]:
1. S → leftBound · genMore · rightBound
2. Repeatedly: genMore → genMore · cell(tᵢ) (adding cells right-to-left)
3. genMore → headCell(q₀, t₁) (or headCell(q₀, none, none) for empty input)
-/

/-
PROBLEM
The grammar can derive the encoding of the initial configuration from [start].

PROVIDED SOLUTION
We prove by cases on w and then induction on the tail.

Case w = []:
  Target: grammar_derives g [nonterminal start] [leftBound, headCell(default, none, none), rightBound]

  Step 1: Apply S → leftBound genMore rightBound.
    rule: ⟨[], start, [], [leftBound, genMore, rightBound]⟩ ∈ generationRules (first element)
    u = [], v = []
    Result: [leftBound, genMore, rightBound]

  Step 2: Apply genMore → headCell(default, none, none).
    rule: ⟨[], genMore, [], [headCell(default, none, none)]⟩ ∈ generationRules (last element)
    u = [leftBound], v = [rightBound]
    Result: [leftBound, headCell(default, none, none), rightBound] ✓

Case w = t :: ts:
  Target: grammar_derives g [nonterminal start] (encodeTwoTrack ⟨[], default, some t, some t, ts.map(...)⟩)
  = [leftBound, headCell(default, some t, some t)] ++ ts.map(fun t' => cell(some t', some t')) ++ [rightBound]

  Step 1: Apply S → leftBound genMore rightBound.
    Result: [leftBound, genMore, rightBound]

  Step 2: For each element of ts.reverse, apply genMore → genMore cell(some tᵢ, some tᵢ).

  We prove by induction on ts.reverse (or equivalently on ts using List.reverseRecOn) that:
  from [leftBound, genMore, rightBound]
  we can derive [leftBound, genMore] ++ ts.map(fun t' => cell(some t', some t')) ++ [rightBound]

  Actually, it's easier to prove: for any list cells : List (Option T × Option T),
  grammar_derives g
    ([leftBound, genMore] ++ (cells.map fun ⟨o,c⟩ => cell(o,c)) ++ [rightBound])
    ([leftBound, genMore] ++ ((t', (some t', some t')) :: cells).map(...) ++ [rightBound])
  by applying genMore → genMore cell(some t', some t') with context u = [leftBound] and v = cells.map(...) ++ [rightBound].

  Actually more precisely:

  Sub-goal: for any suffix s : List T,
    grammar_derives g
      ([leftBound, genMore] ++ s.map(fun t' => cell(some t', some t')) ++ [rightBound])
      ([leftBound, genMore] ++ (s ++ [t']).map(fun t' => cell(some t', some t')) ++ [rightBound])

  Hmm this is getting complicated. Let me try a cleaner approach.

  Prove an auxiliary lemma by induction on a list `cells : List T`:
  grammar_derives g
    ([leftBound, genMore] ++ cells.map(fun t => nonterminal (cell (some t) (some t))) ++ [rightBound])
    is reachable from [leftBound, genMore, rightBound].

  Base: cells = [], trivial (grammar_deri_self).

  Step: cells = cells' ++ [t']. By IH we can reach the form with cells'. Then apply
    genMore → genMore cell(some t', some t')
    with u = [leftBound] and v = cells'.map(...) ++ [rightBound]
    to get: [leftBound, genMore, cell(some t', some t')] ++ cells'.map(...) ++ [rightBound]
    = [leftBound, genMore] ++ (t' :: cells').map(...) ++ [rightBound]

  Hmm but we want cells' ++ [t'] not t' :: cells'. The order matters.

  Let me reconsider. For input [t, t₂, t₃]:
  - Start: [LB, gM, RB]
  - Add t₃: [LB, gM, cell(t₃), RB]     (genMore → genMore cell(t₃))
  - Add t₂: [LB, gM, cell(t₂), cell(t₃), RB]   (genMore → genMore cell(t₂))
  - Replace genMore with head(t): [LB, head(t), cell(t₂), cell(t₃), RB]

  So the cells are added in REVERSE order: t₃ first, then t₂.
  The final list of cells to the right of the head is [t₂, t₃] = ts.

  So the auxiliary lemma should be: by induction on ts.reverse:

  grammar_derives g [LB, gM, RB] ([LB, gM] ++ ts.map(...) ++ [RB])

  Then apply genMore → headCell(default, some t, some t) to finish.

  By induction on ts using List.reverseRecOn:
  - Base: ts = [], [LB, gM, RB] already equals [LB, gM] ++ [].map(...) ++ [RB] ✓
  - Step: ts = init ++ [last].
    By IH: grammar_derives g [LB, gM, RB] ([LB, gM] ++ init.map(...) ++ [RB])
    Now apply genMore → genMore cell(some last, some last):
      u = [LB], v = init.map(...) ++ [RB]
      Before: [LB, gM] ++ init.map(...) ++ [RB]
      After: [LB, gM, cell(last)] ++ init.map(...) ++ [RB]

    But we want: [LB, gM] ++ (init ++ [last]).map(...) ++ [RB]
             = [LB, gM] ++ init.map(...) ++ [cell(last)] ++ [RB]

    But we got: [LB, gM, cell(last)] ++ init.map(...) ++ [RB]

    These are different! The cell(last) is right after genMore, not at the end of init.map.

  Hmm, so actually adding cells goes: genMore → genMore cell(t).
  This puts cell(t) immediately after genMore, before any existing cells.
  So repeated applications give cells in the ORDER they were added:

  [LB, gM, RB] → [LB, gM, cell(t₃), RB] → [LB, gM, cell(t₂), cell(t₃), RB]

  So the cells list is [t₂, t₃] when we added t₃ first then t₂.

  For the target ts = [t₂, t₃], we need to add in reverse order: add t₃ first, then t₂.

  So actually, by induction on ts (normal, not reverse):
  - Base: ts = [], already done.
  - Step: ts = t' :: ts'.
    By IH: grammar_derives g [LB, gM, RB] ([LB, gM] ++ ts'.map(...) ++ [RB])
    Apply genMore → genMore cell(some t', some t'):
      u = [LB], v = ts'.map(...) ++ [RB]
      Result: [LB, gM, cell(t')] ++ ts'.map(...) ++ [RB]
            = [LB, gM] ++ [cell(t')] ++ ts'.map(...) ++ [RB]
            = [LB, gM] ++ (t' :: ts').map(...) ++ [RB]  ✓

This works with normal induction on ts.

So the full proof:
1. Apply S → LB genMore RB: [start] →* [LB, gM, RB]
2. By induction on ts, apply genMore → genMore cell(t') for each t' in ts:
   [LB, gM, RB] →* [LB, gM] ++ ts.map(...) ++ [RB]
3. Apply genMore → headCell(default, some t, some t) (or none,none for empty input):
   [LB, gM] ++ ts.map(...) ++ [RB] → [LB, headCell(default, t, t)] ++ ts.map(...) ++ [RB]
   = encodeTwoTrack(initTwoTrack(t :: ts))

Use grammar_deri_of_deri_tran to chain.
-/
theorem generation_derives (M : Turing.TM0.Machine (Option T) Λ) (w : List T) :
    grammar_derives (tmToGrammar T Λ M)
      [.nonterminal start]
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig T Λ)) := by
  revert w M;
  intro M w
  by_cases hw : w = [];
  · subst hw;
    -- Apply the first rule of the generationRules to get [leftBound, genMore, rightBound].
    have h1 : grammar_transforms (tmToGrammar T Λ M) [symbol.nonterminal start] [symbol.nonterminal leftBound, symbol.nonterminal genMore, symbol.nonterminal rightBound] := by
      use ⟨ [ ], start, [ ], [ symbol.nonterminal leftBound, symbol.nonterminal genMore, symbol.nonterminal rightBound ] ⟩ ; simp +decide [ tmToGrammar ] ;
      exact ⟨ Or.inl <| List.mem_cons_self, [ ], [ ], rfl, rfl ⟩;
    exact .single h1 |> Relation.ReflTransGen.trans <| .single <| by
      use ⟨[], genMore, [.nonterminal rightBound], [.nonterminal (headCell (default : Λ) none none), .nonterminal rightBound]⟩; simp +decide [ encodeTwoTrack, initTwoTrack ] ;
      exact ⟨ by unfold tmToGrammar; simp +decide [ generationRules ], [ symbol.nonterminal leftBound ], [], by simp, by simp ⟩;
  · -- Apply the induction hypothesis to the tail of the list.
    have h_ind : ∀ (ts : List T), grammar_derives (tmToGrammar T Λ M) [symbol.nonterminal start] ([symbol.nonterminal leftBound, symbol.nonterminal genMore] ++ ts.map (fun t => symbol.nonterminal (cell (some t) (some t))) ++ [symbol.nonterminal rightBound]) := by
      intro ts
      induction' ts with t ts ih
      generalize_proofs at *; (
      apply Relation.ReflTransGen.single
      simp [generationRules];
      use ⟨[], start, [], [symbol.nonterminal leftBound, symbol.nonterminal genMore, symbol.nonterminal rightBound]⟩
      simp [tmToGrammar, generationRules];
      exact ⟨ [ ], [ ], rfl, rfl ⟩);
      apply grammar_deri_of_deri_tran ih
      generalize_proofs at *; (
      use ⟨[], genMore, [], [.nonterminal genMore, .nonterminal (cell (some t) (some t))]⟩; simp +decide [ tmToGrammar ] ; (
      exact ⟨ Or.inl <| by unfold generationRules; aesop, [ symbol.nonterminal leftBound ], ( List.map ( fun t => symbol.nonterminal ( cell ( some t ) ( some t ) ) ) ts ++ [ symbol.nonterminal rightBound ] ), by aesop ⟩ ;););
    rcases w with ( _ | ⟨ t, ts ⟩ ) <;> simp_all +decide [ encodeTwoTrack, initTwoTrack ];
    have h_genMore : grammar_transforms (tmToGrammar T Λ M) (symbol.nonterminal leftBound :: symbol.nonterminal genMore :: (List.map (fun t => symbol.nonterminal (cell (some t) (some t))) ts ++ [symbol.nonterminal rightBound])) (symbol.nonterminal leftBound :: symbol.nonterminal (headCell default (some t) (some t)) :: (List.map (fun t => symbol.nonterminal (cell (some t) (some t))) ts ++ [symbol.nonterminal rightBound])) := by
      use ⟨[], genMore, [], [.nonterminal (headCell default (some t) (some t))]⟩; simp +decide [ tmToGrammar ] ; (
      exact ⟨ Or.inl <| by unfold generationRules; aesop, [ symbol.nonterminal leftBound ], List.map ( fun t => symbol.nonterminal ( cell ( some t ) ( some t ) ) ) ts ++ [ symbol.nonterminal rightBound ], rfl, rfl ⟩);
    exact Relation.ReflTransGen.trans ( h_ind ts ) ( Relation.ReflTransGen.single h_genMore )

/-! ### Phase 3: Cleanup

After the TM halts, the grammar converts all nonterminals to terminals. -/

/-- Encode the "halted" configuration: all cells converted to haltCells. -/
def encodeHalted (originals : List (Option T)) :
    List (symbol T (TMtoGrammarNT T Λ)) :=
  [.nonterminal leftBound] ++
  (originals.map fun orig => .nonterminal (haltCell orig)) ++
  [.nonterminal rightBound]

/-- Extract the original input from a list of originals (keep only `some` values). -/
def extractInput (originals : List (Option T)) : List T :=
  originals.filterMap id

/-
PROBLEM
From a halted encoding, the grammar can derive the original input terminals.

Convert a bare list of haltCells to terminals (no boundary markers).

PROVIDED SOLUTION
We prove by induction on `originals` that the grammar derives the terminal list from the halted encoding.

The halted encoding is: [leftBound] ++ originals.map haltCell ++ [rightBound]
The target is: originals.filterMap id |>.map terminal

Strategy: First convert all haltCells to terminals (or ε), then remove the boundary markers.

Step 1: Convert haltCells from left to right.
We prove an auxiliary fact: for any prefix (already converted to terminals) and suffix (remaining haltCells), the grammar derives the conversion.

More precisely, by induction on originals:
- Base case []: encodeHalted [] = [leftBound, rightBound].
  Apply leftBound → ε (rule in cleanupRules, u=[], v=[rightBound]).
  Then apply rightBound → ε (rule in cleanupRules, u=[], v=[]).
  Result: [] = [].map terminal (extractInput []) ✓

- Inductive case (some t) :: rest:
  encodeHalted ((some t) :: rest) = [leftBound, haltCell(some t)] ++ rest.map haltCell ++ [rightBound]
  Apply haltCell(some t) → terminal t (u=[leftBound], v=rest.map haltCell ++ [rightBound]).
  Result: [leftBound, terminal t] ++ rest.map haltCell ++ [rightBound]

  Now we need to derive from [leftBound, terminal t] ++ rest.map haltCell ++ [rightBound]
  to [terminal t] ++ extractInput(rest).map terminal.

  Using the IH on rest: from [leftBound] ++ rest.map haltCell ++ [rightBound] we can derive
  extractInput(rest).map terminal.

  But we have an extra [terminal t] prefix and the leftBound is displaced!

  Actually, let me reconsider. We can use grammar_deri_with_prefix to add a prefix.
  But the issue is that leftBound is inside the form, not as a prefix.

  Alternative approach: First convert ALL haltCells, then remove boundaries.

  Prove: [leftBound] ++ originals.map haltCell ++ [rightBound]
  derives to: [leftBound] ++ extractInput(originals).map terminal ++ [rightBound]
  (by converting haltCells one at a time from left to right)

  Then: [leftBound] ++ extractInput(originals).map terminal ++ [rightBound]
  derives to: extractInput(originals).map terminal
  (by removing leftBound then rightBound)

  For converting haltCells, by induction on originals:
  - []: no haltCells, done.
  - (some t) :: rest: Apply haltCell(some t) → terminal t with context u = [leftBound], v = rest.map haltCell ++ [rightBound]. This gives [leftBound, terminal t] ++ rest.map haltCell ++ [rightBound]. Then use grammar_deri_with_prefix with prefix [leftBound, terminal t] and the IH for rest (but the IH gives derivation from [leftBound] ++ ..., not from rest alone).

  Hmm, let me try a different decomposition. Prove a helper:
  For any prefix p of terminals, [leftBound] ++ p ++ originals.map haltCell ++ [rightBound]
  derives to [leftBound] ++ p ++ extractInput(originals).map terminal ++ [rightBound]

  By induction on originals, using grammar_deri_with_prefix and grammar_deri_with_postfix.

Actually, the simplest approach: just do induction and at each step use the grammar transform rule with the appropriate context u and v.

For the convert step with (some t)::rest:
u = [leftBound] ++ (already converted terminals)
rule: haltCell(some t) → terminal(t)  (input_L = [], input_N = haltCell(some t), input_R = [], output = [terminal t])
v = rest.map haltCell ++ [rightBound]

For the convert step with none::rest:
u = [leftBound] ++ (already converted terminals)
rule: haltCell(none) → ε  (input_L = [], input_N = haltCell(none), input_R = [], output = [])
v = rest.map haltCell ++ [rightBound]

After all conversions: [leftBound] ++ extractInput(originals).map terminal ++ [rightBound]

Then remove leftBound: rule leftBound → ε, u=[], v=extractInput(originals).map terminal ++ [rightBound]
Then remove rightBound: rule rightBound → ε, u=extractInput(originals).map terminal, v=[]

Use gen_rule_mem / cleanup_rule_mem to show rules are in the grammar.

By induction on originals.

Base case []: both sides are [], use grammar_deri_self (ReflTransGen.refl).

Inductive case (none :: rest):
- LHS: [nonterminal (haltCell none)] ++ rest.map(...)
- Apply haltCell(none) → ε rule: ⟨[], haltCell none, [], []⟩. This is in tmToGrammar.rules via cleanupRules.
  u = [], v = rest.map(...). Result: rest.map(...).
- Then by IH, rest.map(...) →* (rest.filterMap id).map terminal.
- And (none :: rest).filterMap id = rest.filterMap id.
- So chain: LHS → rest.map(haltCell) →* RHS. Use grammar_deri_of_tran_deri.

Inductive case (some t :: rest):
- LHS: [nonterminal (haltCell (some t))] ++ rest.map(...)
- Apply haltCell(some t) → terminal t rule: ⟨[], haltCell (some t), [], [terminal t]⟩. In cleanupRules.
  u = [], v = rest.map(...). Result: [terminal t] ++ rest.map(...).
- Then use grammar_deri_with_prefix with prefix [terminal t] and IH on rest.
- And (some t :: rest).filterMap id = t :: rest.filterMap id, so the target is [terminal t] ++ (rest.filterMap id).map terminal.
- So chain: LHS → [terminal t] ++ rest.map(haltCell) →* [terminal t] ++ (rest.filterMap id).map terminal = RHS.
-/
theorem haltCells_to_terminals (M : Turing.TM0.Machine (Option T) Λ)
    (originals : List (Option T)) :
    grammar_derives (tmToGrammar T Λ M)
      (originals.map fun orig => symbol.nonterminal (haltCell orig))
      ((originals.filterMap id).map symbol.terminal) := by
  induction' originals with orig originals ih;
  · constructor;
  · cases' orig with t t <;> simp_all +decide [ List.filterMap_cons ];
    · -- Apply the rule for `haltCell none` to remove the nonterminal.
      have h_halt_none : grammar_transforms (tmToGrammar T Λ M) (symbol.nonterminal (haltCell none) :: List.map (fun orig => symbol.nonterminal (haltCell orig)) originals) (List.map (fun orig => symbol.nonterminal (haltCell orig)) originals) := by
        use ⟨[], haltCell none, [], []⟩;
        simp +decide [ tmToGrammar, generationRules, simulationRules, cleanupRules ];
        exact ⟨ [ ], _, rfl, rfl ⟩;
      exact grammar_deri_of_tran_deri h_halt_none ih;
    · convert grammar_deri_of_deri_deri _ _ using 1;
      exact [ symbol.terminal t ] ++ List.map ( fun orig => symbol.nonterminal ( haltCell orig ) ) originals;
      · convert grammar_deri_of_tran _ using 1;
        use ⟨[], haltCell (some t), [], [symbol.terminal t]⟩; simp +decide [ tmToGrammar ] ;
        refine' ⟨ _, [ ], _, rfl, rfl ⟩;
        unfold cleanupRules; aesop;
      · convert grammar_deri_with_prefix _ ih using 1

/-
PROBLEM
Remove LB from [LB] ++ haltCells ++ [RB], producing haltCells ++ [RB] (non-empty case)
    or [] (empty case).

PROVIDED SOLUTION
By cases on originals.

Case []:
- encodeHalted [] = [nonterminal leftBound, nonterminal rightBound]
- Target: [].map (...) = []
- Apply rule LB · RB → ε: ⟨[], leftBound, [nonterminal rightBound], []⟩
  This is in cleanupRules. u = [], v = [].
  w₁ = [] ++ [] ++ [nonterminal leftBound] ++ [nonterminal rightBound] ++ [] = [LB, RB]
  w₂ = [] ++ [] ++ [] = []
- Use grammar_deri_of_tran (ReflTransGen.single).

Case (o :: rest):
- encodeHalted (o :: rest) = [LB] ++ [haltCell(o)] ++ rest.map(haltCell) ++ [RB]
- Target: (o :: rest).map(haltCell) = [haltCell(o)] ++ rest.map(haltCell)

Step 1: Remove LB using rule LB · haltCell(o) → haltCell(o):
  Rule: ⟨[], leftBound, [nonterminal (haltCell o)], [nonterminal (haltCell o)]⟩
  In cleanupRules via (allOptT T).map. Use mem_allOptT to show o ∈ allOptT T.
  u = [], v = rest.map(haltCell) ++ [RB]
  w₁ = [LB, haltCell(o)] ++ rest.map(haltCell) ++ [RB]
  w₂ = [haltCell(o)] ++ rest.map(haltCell) ++ [RB]

Step 2: Remove RB using rule haltCell(last) · RB → haltCell(last):
  We need the LAST haltCell. For the list (o :: rest), the last element is (o :: rest).getLast.
  The form is [haltCell(o)] ++ rest.map(haltCell) ++ [RB].
  Use List.getLast to find the last element. The last haltCell is adjacent to RB.

  Rule: ⟨[nonterminal (haltCell last_orig)], rightBound, [], [nonterminal (haltCell last_orig)]⟩
  In cleanupRules. Use mem_allOptT.

  u = init((o :: rest).map(haltCell)), v = []
  This removes RB and keeps the haltCell.
  Result: (o :: rest).map(haltCell)

Chain steps 1 and 2 using grammar_deri_of_tran_deri or grammar_deri_of_deri_deri.

For Step 2, to get the last element: use List.map_getLast or show that
  (o :: rest).map(haltCell) ++ [RB] decomposes as
  List.dropLast((o :: rest).map(haltCell)) ++ [haltCell(List.getLast (o :: rest) ...)] ++ [RB]

Actually, simpler: use the fact that for a non-empty list l,
  l ++ [RB] = l.dropLast ++ [l.getLast ..., RB]
Then the rule matches with u = l.dropLast, input_L = [haltCell(last)], input_N = rightBound.
And the result is l.dropLast ++ [haltCell(last)] = l.
-/
theorem remove_boundaries (M : Turing.TM0.Machine (Option T) Λ)
    (originals : List (Option T)) :
    grammar_derives (tmToGrammar T Λ M)
      (encodeHalted originals)
      (originals.map fun orig => symbol.nonterminal (haltCell orig)) := by
  unfold encodeHalted;
  induction' originals with orig rest ih;
  · -- Apply the rule that removes the leftBound and rightBound.
    apply Relation.ReflTransGen.single
    use ⟨[], leftBound, [.nonterminal rightBound], []⟩
    simp [cleanupRules];
    unfold tmToGrammar; simp +decide [ cleanupRules ] ;
  · have h_transform : grammar_transforms (tmToGrammar T Λ M) ([symbol.nonterminal leftBound] ++ [symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest ++ [symbol.nonterminal rightBound]) ([symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest ++ [symbol.nonterminal rightBound]) := by
      -- Apply the rule that removes the left bound.
      use ⟨[], leftBound, [symbol.nonterminal (haltCell orig)], [symbol.nonterminal (haltCell orig)]⟩;
      simp +decide [ tmToGrammar ];
      refine' ⟨ _, [ ], List.map ( fun orig => symbol.nonterminal ( haltCell orig ) ) rest ++ [ symbol.nonterminal rightBound ], rfl, rfl ⟩;
      unfold cleanupRules; simp +decide [ allOptT ] ;
      cases orig <;> tauto;
    have h_transform : grammar_transforms (tmToGrammar T Λ M) ([symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest ++ [symbol.nonterminal rightBound]) ([symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest) := by
      use ⟨[.nonterminal (haltCell (List.getLast! (orig :: rest)))] , rightBound, [], [.nonterminal (haltCell (List.getLast! (orig :: rest)))]⟩; simp_all +decide [ List.getLast! ] ;
      constructor;
      · apply_rules [ List.mem_append_right ];
        simp +decide [ allOptT ];
        cases h : ( orig :: rest ).getLast ( by simp +decide ) <;> aesop;
      · induction rest using List.reverseRecOn <;> simp_all +decide [ List.getLast ];
        · exact ⟨ [ ], [ ], rfl, rfl ⟩;
        · exact ⟨ [ symbol.nonterminal ( haltCell orig ) ] ++ List.map ( fun orig => symbol.nonterminal ( haltCell orig ) ) ‹_›, [ ], by simp +decide ⟩;
    exact Relation.ReflTransGen.single ‹_› |> Relation.ReflTransGen.trans <| Relation.ReflTransGen.single ‹_›

theorem cleanup_derives (M : Turing.TM0.Machine (Option T) Λ)
    (originals : List (Option T)) :
    grammar_derives (tmToGrammar T Λ M)
      (encodeHalted originals)
      (List.map symbol.terminal (extractInput originals)) := by
  exact grammar_deri_of_deri_deri (remove_boundaries M originals) (haltCells_to_terminals M originals)

/-! ### Rule membership helpers -/

/-- A rule from the generation rules is in the grammar. -/

theorem gen_rule_mem (M : Turing.TM0.Machine (Option T) Λ)
    (r : grule T (TMtoGrammarNT T Λ)) (hr : r ∈ generationRules T Λ M) :
    r ∈ (tmToGrammar T Λ M).rules := by
  simp only [tmToGrammar]
  exact List.mem_append_left _ (List.mem_append_left _ hr)

/-- A rule from the simulation rules is in the grammar. -/

theorem sim_rule_mem (M : Turing.TM0.Machine (Option T) Λ)
    (r : grule T (TMtoGrammarNT T Λ)) (hr : r ∈ simulationRules T Λ M) :
    r ∈ (tmToGrammar T Λ M).rules := by
  simp only [tmToGrammar]
  exact List.mem_append_left _ (List.mem_append_right _ hr)

/-- A rule from the cleanup rules is in the grammar. -/

theorem cleanup_rule_mem (M : Turing.TM0.Machine (Option T) Λ)
    (r : grule T (TMtoGrammarNT T Λ)) (hr : r ∈ cleanupRules T Λ M) :
    r ∈ (tmToGrammar T Λ M).rules := by
  simp only [tmToGrammar]
  exact List.mem_append_right _ hr

/-- Get the originals from a TwoTrackConfig. -/
def twoTrackOriginals (cfg : @TwoTrackConfig T Λ) : List (Option T) :=
  (cfg.leftCells.map Prod.fst) ++ [cfg.headOrig] ++ (cfg.rightCells.map Prod.fst)

/-! ### Phase 2: Simulation

The simulation phase shows that each TM0 step can be mirrored by a grammar
derivation step on the encoded sentential form. -/

/-- Compute the next TwoTrackConfig after one TM0 step. Returns `none` if the TM halts. -/
noncomputable def stepTwoTrack
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg : @TwoTrackConfig T Λ) : Option (@TwoTrackConfig T Λ) :=
  match M cfg.headState cfg.headCur with
  | none => none
  | some (q', Turing.TM0.Stmt.write γ') =>
    some ⟨cfg.leftCells, q', cfg.headOrig, γ', cfg.rightCells⟩
  | some (q', Turing.TM0.Stmt.move Dir.right) =>
    match cfg.rightCells with
    | [] => some ⟨cfg.leftCells ++ [(cfg.headOrig, cfg.headCur)], q', none, none, []⟩
    | (ro, rc) :: rest =>
      some ⟨cfg.leftCells ++ [(cfg.headOrig, cfg.headCur)], q', ro, rc, rest⟩
  | some (q', Turing.TM0.Stmt.move Dir.left) =>
    match cfg.leftCells.reverse with
    | [] => some ⟨[], q', none, none, (cfg.headOrig, cfg.headCur) :: cfg.rightCells⟩
    | (lo, lc) :: rest =>
      some ⟨rest.reverse, q', lo, lc,
            (cfg.headOrig, cfg.headCur) :: cfg.rightCells⟩

/-
PROBLEM
The original input (modulo blank extension) is preserved by `stepTwoTrack`.

PROVIDED SOLUTION
Unfold stepTwoTrack and case split on M cfg.headState cfg.headCur.

Case none: contradiction with hstep.

Case some (q', write γ'): cfg' has same leftCells, headOrig, rightCells. So twoTrackOriginals cfg' = twoTrackOriginals cfg, hence extractInput equal.

Case some (q', move right), rightCells = []:
cfg' = ⟨leftCells ++ [(headOrig, headCur)], q', none, none, []⟩
twoTrackOriginals cfg' = (leftCells ++ [(headOrig, headCur)]).map fst ++ [none] ++ []
= leftCells.map fst ++ [headOrig] ++ [none]
extractInput of this = extractInput (leftCells.map fst ++ [headOrig] ++ [none])
= extractInput (leftCells.map fst ++ [headOrig]) ++ extractInput [none]
= extractInput (leftCells.map fst ++ [headOrig])  (since extractInput [none] = [])
= extractInput (twoTrackOriginals cfg) ✓ (since rightCells = [], twoTrackOriginals cfg = leftCells.map fst ++ [headOrig])

Case some (q', move right), rightCells = (ro, rc) :: rest:
cfg' = ⟨leftCells ++ [(headOrig, headCur)], q', ro, rc, rest⟩
twoTrackOriginals cfg' = (leftCells ++ [(headOrig, headCur)]).map fst ++ [ro] ++ rest.map fst
= leftCells.map fst ++ [headOrig] ++ [ro] ++ rest.map fst
= leftCells.map fst ++ [headOrig] ++ (ro :: rest.map fst)
twoTrackOriginals cfg = leftCells.map fst ++ [headOrig] ++ ((ro,rc) :: rest).map fst
= leftCells.map fst ++ [headOrig] ++ (ro :: rest.map fst) ✓ (same)

Case some (q', move left), leftCells.reverse = []:
This means leftCells = [].
cfg' = ⟨[], q', none, none, (headOrig, headCur) :: rightCells⟩
twoTrackOriginals cfg' = [].map fst ++ [none] ++ ((headOrig, headCur) :: rightCells).map fst
= [none] ++ [headOrig] ++ rightCells.map fst
extractInput = extractInput [none] ++ extractInput ([headOrig] ++ rightCells.map fst)
= extractInput ([headOrig] ++ rightCells.map fst)
twoTrackOriginals cfg = [].map fst ++ [headOrig] ++ rightCells.map fst
= [headOrig] ++ rightCells.map fst ✓ (same extractInput)

Case some (q', move left), leftCells.reverse = (lo, lc) :: rest_rev:
leftCells = (rest_rev ++ [(lo, lc)]).reverse = ... actually leftCells.reverse = (lo, lc) :: rest_rev, so leftCells = rest_rev.reverse ++ [(lo, lc)]... wait no.
If leftCells.reverse = (lo, lc) :: rest_rev, then leftCells = rest_rev.reverse ++ [(lo, lc)].
Hmm, actually List.reverse reverses the order. If l.reverse = h :: t, then l = t.reverse ++ [h].

cfg' = ⟨rest_rev.reverse, q', lo, lc, (headOrig, headCur) :: rightCells⟩
twoTrackOriginals cfg' = rest_rev.reverse.map fst ++ [lo] ++ ((headOrig, headCur) :: rightCells).map fst
= rest_rev.reverse.map fst ++ [lo] ++ [headOrig] ++ rightCells.map fst

twoTrackOriginals cfg = leftCells.map fst ++ [headOrig] ++ rightCells.map fst
leftCells = rest_rev.reverse ++ [(lo, lc)]  (since leftCells.reverse = (lo,lc) :: rest_rev means leftCells = rest_rev.reverse ++ [(lo,lc)])
leftCells.map fst = rest_rev.reverse.map fst ++ [lo]
So twoTrackOriginals cfg = rest_rev.reverse.map fst ++ [lo] ++ [headOrig] ++ rightCells.map fst ✓ (same)

So in all cases, extractInput is preserved (sometimes twoTrackOriginals itself is preserved, sometimes only extractInput is).

Key lemma needed: extractInput (l ++ [none]) = extractInput l, which follows from List.filterMap_append and the fact that filterMap id [none] = [].
-/
theorem stepTwoTrack_preserves_extractInput
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg cfg' : @TwoTrackConfig T Λ)
    (hstep : stepTwoTrack M cfg = some cfg') :
    extractInput (twoTrackOriginals cfg') = extractInput (twoTrackOriginals cfg) := by
  unfold stepTwoTrack at hstep;
  rcases h : M cfg.headState cfg.headCur with ( _ | ⟨ q', _ ⟩ ) <;> simp_all +decide;
  rename_i h';
  rcases h' with ( _ | Dir ) <;> norm_num at *;
  · cases ‹Dir› <;> cases h' : cfg.rightCells <;> cases h'' : cfg.leftCells.reverse <;> simp_all +decide [ twoTrackOriginals ];
    all_goals subst_vars; simp +decide [ extractInput ] ;
    · cases cfg.headOrig <;> rfl;
    · cases ‹Option T × Option T› ; aesop;
  · unfold twoTrackOriginals; aesop;

/-
PROBLEM
Any element of `Option T` is in `allOptT`.

PROVIDED SOLUTION
allOptT T = none :: Finset.univ.val.toList.map some. Cases on x: if none, it's List.mem_cons_self. If some t, use List.mem_cons_of_mem and List.mem_map.mpr with Finset.mem_toList.mpr (Finset.mem_univ t).
-/
theorem mem_allOptT (x : Option T) : x ∈ allOptT T := by
  unfold allOptT; cases x <;> simp +decide [ * ] ;

/-
PROBLEM
Any element of `Λ` is in `allΛ`.

PROVIDED SOLUTION
allΛ Λ = Finset.univ.val.toList. Use Finset.mem_toList.mpr (Finset.mem_univ q).
-/
theorem mem_allΛ (q : Λ) : q ∈ allΛ Λ := by
  convert Finset.mem_toList.mpr ( Finset.mem_univ q ) using 1

/-
PROBLEM
Simulation: write case.

PROVIDED SOLUTION
Use the rule ⟨[], headCell q orig γ, [], [.nonterminal (headCell q' orig γ')]⟩ which is in simulationRules.

Proof:
refine ⟨⟨[], headCell q orig γ, [], [.nonterminal (headCell q' orig γ')]⟩, ?_, prefix_, suffix_, ?_, ?_⟩
- Rule membership: apply sim_rule_mem. The rule is in simulationRules because:
  simulationRules unfolds to (allΛ).flatMap (fun q => (allOptT).flatMap (fun γ => match M q γ ...)).
  For our q and γ, M q γ = some (q', write γ'), so we get (allOptT).map (fun orig => ⟨[], headCell q orig γ, [], [headCell q' orig γ']⟩).
  Our specific rule is the one with our `orig`. So we need: q ∈ allΛ, γ ∈ allOptT, orig ∈ allOptT. Use mem_allΛ and mem_allOptT.
  Concretely: List.mem_flatMap.mpr ⟨q, mem_allΛ q, List.mem_flatMap.mpr ⟨γ, mem_allOptT γ, by simp [hM]; exact List.mem_map.mpr ⟨orig, mem_allOptT orig, rfl⟩⟩⟩
- w₁ equation: simp
- w₂ equation: simp
-/
theorem sim_write
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ γ' : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.write γ'))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig γ)] ++ suffix_)
      (prefix_ ++ [.nonterminal (headCell q' orig γ')] ++ suffix_) := by
  refine' ⟨ ⟨ [], headCell q orig γ, [], [ symbol.nonterminal ( headCell q' orig γ' ) ] ⟩, _, _ ⟩;
  · apply sim_rule_mem;
    unfold simulationRules;
    rw [ List.mem_flatMap ];
    use q;
    rw [ List.mem_flatMap ];
    use mem_allΛ q, γ, mem_allOptT γ, by
      rw [ hM ];
      exact List.mem_map.mpr ⟨ orig, mem_allOptT orig, rfl ⟩;
  · grind

/-
PROBLEM
Simulation: move right with neighbor.

PROVIDED SOLUTION
Use the rule ⟨[], headCell q orig γ, [.nonterminal (cell orig' γ')], [.nonterminal (cell orig γ), .nonterminal (headCell q' orig' γ')]⟩.

This rule is in simulationRules: in the move right case, we have (allOptT).flatMap fun orig => (allOptT).flatMap fun orig' => (allOptT).map fun γ' => ⟨...⟩. Our rule has the right q, γ (with M q γ = some (q', move right)), and the right orig, orig', γ'.

For membership: List.mem_flatMap with q ∈ allΛ, γ ∈ allOptT, then in the match branch for move right, List.mem_append_left, then List.mem_flatMap three times with orig, orig', γ' ∈ allOptT.

Then u = prefix_, v = suffix_, and the equations follow by simp.
-/
theorem sim_move_right
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ orig' γ' : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.right))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig γ), .nonterminal (cell orig' γ')] ++ suffix_)
      (prefix_ ++ [.nonterminal (cell orig γ), .nonterminal (headCell q' orig' γ')] ++ suffix_) := by
  constructor;
  constructor;
  apply sim_rule_mem;
  convert List.mem_flatMap.mpr _;
  exact ⟨ [ ], headCell q orig γ, [ symbol.nonterminal ( cell orig' γ' ) ], [ symbol.nonterminal ( cell orig γ ), symbol.nonterminal ( headCell q' orig' γ' ) ] ⟩;
  · refine' ⟨ q, _, _ ⟩ <;> simp +decide [ hM, allΛ ];
    use γ; simp [hM];
    exact ⟨ mem_allOptT γ, mem_allOptT orig, mem_allOptT orig', mem_allOptT γ' ⟩;
  · grind

/-
PROBLEM
Simulation: move right at right boundary.

PROVIDED SOLUTION
Use the rule ⟨[], headCell q orig γ, [.nonterminal rightBound], [.nonterminal (cell orig γ), .nonterminal (headCell q' none none), .nonterminal rightBound]⟩.

This rule is in simulationRules: in the move right case, it's in the second part (the boundary extension rules). The rule has (allOptT).map fun orig => ⟨[], headCell q orig γ, [rightBound], [cell orig γ, headCell q' none none, rightBound]⟩. Our rule matches with our orig.

For membership: q ∈ allΛ, γ ∈ allOptT, then List.mem_append_right to get to the boundary rules, then List.mem_map with orig ∈ allOptT.

u = prefix_, v = suffix_.
-/
theorem sim_move_right_boundary
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.right))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig γ), .nonterminal rightBound] ++ suffix_)
      (prefix_ ++ [.nonterminal (cell orig γ), .nonterminal (headCell q' none none), .nonterminal rightBound] ++ suffix_) := by
  use (⟨[], headCell q orig γ, [symbol.nonterminal rightBound], [symbol.nonterminal (cell orig γ), symbol.nonterminal (headCell q' none none), symbol.nonterminal rightBound]⟩);
  constructor;
  · apply sim_rule_mem;
    unfold simulationRules; simp +decide [ hM ] ;
    use q, by
      exact?, γ, by
      exact?
    generalize_proofs at *;
    rw [ hM ] ; simp +decide [ allOptT ] ;
    cases orig <;> aesop;
  · grind

/-
PROBLEM
Simulation: move left with neighbor.

PROVIDED SOLUTION
Use the rule ⟨[.nonterminal (cell orig'' γ'')], headCell q orig γ, [], [.nonterminal (headCell q' orig'' γ''), .nonterminal (cell orig γ)]⟩.

This rule is in simulationRules in the move left case, first part (flatMap).

refine ⟨⟨[.nonterminal (cell orig'' γ'')], headCell q orig γ, [], [.nonterminal (headCell q' orig'' γ''), .nonterminal (cell orig γ)]⟩, ?_, prefix_, suffix_, ?_, ?_⟩
- Rule membership: apply sim_rule_mem. Unfold simulationRules. Use List.mem_flatMap with q ∈ allΛ, γ ∈ allOptT. In the match branch (move left), use List.mem_append_left for the first group. Then List.mem_flatMap three times with orig, orig'', γ'' ∈ allOptT.
- w₁ equation: by simp
- w₂ equation: by simp
-/
theorem sim_move_left
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ orig'' γ'' : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.left))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (cell orig'' γ''), .nonterminal (headCell q orig γ)] ++ suffix_)
      (prefix_ ++ [.nonterminal (headCell q' orig'' γ''), .nonterminal (cell orig γ)] ++ suffix_) := by
  refine' ⟨ _, _, _, _ ⟩;
  exact ⟨ [ .nonterminal ( cell orig'' γ'' ) ], headCell q orig γ, [ ], [ .nonterminal ( headCell q' orig'' γ'' ), .nonterminal ( cell orig γ ) ] ⟩;
  convert sim_rule_mem M _ _ using 1;
  all_goals norm_num [ simulationRules ];
  use q, mem_allΛ q, γ, mem_allOptT γ;
  all_goals norm_num [ hM ];
  exact ⟨ orig, mem_allOptT orig, orig'', mem_allOptT orig'', γ'', mem_allOptT γ'', by tauto ⟩;
  exacts [ prefix_, ⟨ suffix_, rfl, rfl ⟩ ]

/-
PROBLEM
Simulation: move left at left boundary.

PROVIDED SOLUTION
Use the rule ⟨[.nonterminal leftBound], headCell q orig γ, [], [.nonterminal leftBound, .nonterminal (headCell q' none none), .nonterminal (cell orig γ)]⟩.

This rule is in simulationRules in the move left case, second part (the boundary extension rules): (allOptT).map fun orig => ⟨[leftBound], headCell q orig γ, [], [leftBound, headCell q' none none, cell orig γ]⟩.

refine ⟨⟨[.nonterminal leftBound], headCell q orig γ, [], [.nonterminal leftBound, .nonterminal (headCell q' none none), .nonterminal (cell orig γ)]⟩, ?_, prefix_, suffix_, ?_, ?_⟩
- Rule membership: sim_rule_mem. In simulationRules, use flatMap for q ∈ allΛ, γ ∈ allOptT. In match branch (move left), use List.mem_append_right. Then List.mem_map with orig ∈ allOptT.
- Equations: simp
-/
theorem sim_move_left_boundary
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.left))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal leftBound, .nonterminal (headCell q orig γ)] ++ suffix_)
      (prefix_ ++ [.nonterminal leftBound, .nonterminal (headCell q' none none), .nonterminal (cell orig γ)] ++ suffix_) := by
  refine' ⟨ _, _, _, _ ⟩;
  exact ⟨ [ .nonterminal leftBound ], headCell q orig γ, [ ], [ .nonterminal leftBound, .nonterminal ( headCell q' none none ), .nonterminal ( cell orig γ ) ] ⟩;
  any_goals exact prefix_;
  · apply sim_rule_mem;
    unfold simulationRules;
    simp +decide [ List.mem_flatMap, List.mem_append, List.mem_map, hM ];
    refine' ⟨ q, _, γ, _, _ ⟩ <;> simp +decide [ hM, allΛ, allOptT ];
    · cases γ <;> tauto;
    · cases orig <;> aesop;
  · grind +revert

/-
PROBLEM
One step of `stepTwoTrack` can be simulated by the grammar.

PROVIDED SOLUTION
Unfold stepTwoTrack in hstep. Case split on hM : M cfg.headState cfg.headCur.

Case none: contradiction (stepTwoTrack returns none).

Case some (q', write γ'):
cfg' = ⟨cfg.leftCells, q', cfg.headOrig, γ', cfg.rightCells⟩.
Apply grammar_deri_of_tran (sim_write M cfg.headState q' cfg.headOrig cfg.headCur γ' hM
  ([.nonterminal leftBound] ++ cfg.leftCells.map(cell))
  (cfg.rightCells.map(cell) ++ [.nonterminal rightBound])).
Need to show source/target match encodeTwoTrack cfg / encodeTwoTrack cfg'. Unfold encodeTwoTrack and simp.

Case some (q', move right):
  Subcase cfg.rightCells = []:
    cfg' = ⟨cfg.leftCells ++ [(cfg.headOrig, cfg.headCur)], q', none, none, []⟩
    Apply grammar_deri_of_tran (sim_move_right_boundary M cfg.headState q' cfg.headOrig cfg.headCur hM
      ([leftBound] ++ leftCells.map(cell))
      []).
    Check encodeTwoTrack equations match.

  Subcase cfg.rightCells = (ro, rc) :: rest:
    cfg' = ⟨cfg.leftCells ++ [(cfg.headOrig, cfg.headCur)], q', ro, rc, rest⟩
    Apply grammar_deri_of_tran (sim_move_right M cfg.headState q' cfg.headOrig cfg.headCur ro rc hM
      ([leftBound] ++ leftCells.map(cell))
      (rest.map(cell) ++ [rightBound])).

Case some (q', move left):
  Subcase cfg.leftCells.reverse = []:
    leftCells = [], cfg' = ⟨[], q', none, none, (headOrig, headCur) :: rightCells⟩
    Apply grammar_deri_of_tran (sim_move_left_boundary M cfg.headState q' cfg.headOrig cfg.headCur hM
      []
      (rightCells.map(cell) ++ [rightBound])).

  Subcase cfg.leftCells.reverse = (lo, lc) :: rest_rev:
    cfg' = ⟨rest_rev.reverse, q', lo, lc, (headOrig, headCur) :: rightCells⟩
    Apply grammar_deri_of_tran (sim_move_left M cfg.headState q' cfg.headOrig cfg.headCur lo lc hM
      ([leftBound] ++ rest_rev.reverse.map(cell))
      (rightCells.map(cell) ++ [rightBound])).
    Need: encodeTwoTrack cfg = ... ++ [cell(lo, lc), headCell(q, headO, headC)] ++ ...
    Since leftCells.reverse = (lo, lc) :: rest_rev, leftCells = rest_rev.reverse ++ [(lo, lc)].
    So leftCells.map(cell) = rest_rev.reverse.map(cell) ++ [cell(lo, lc)].

Each case is a single ReflTransGen.single application using the appropriate sim_* lemma. The equations just need simp/list normalization.
-/
theorem simulation_one_step
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg cfg' : @TwoTrackConfig T Λ)
    (hstep : stepTwoTrack M cfg = some cfg') :
    grammar_derives (tmToGrammar T Λ M)
      (encodeTwoTrack cfg)
      (encodeTwoTrack cfg') := by
  unfold stepTwoTrack at hstep;
  rcases h : M cfg.headState cfg.headCur with ( _ | ⟨ q', _ ⟩ ) <;> simp_all +decide;
  cases' ‹TM0.Stmt ( Option T ) › with γ' hγ';
  · cases' γ' with γ' hγ';
    · rcases h' : cfg.leftCells.reverse with ( _ | ⟨ lo, lc ⟩ ) <;> simp_all +decide [ encodeTwoTrack ];
      · convert grammar_deri_of_tran _ using 1;
        convert sim_move_left_boundary M cfg.headState q' cfg.headOrig cfg.headCur h [ ] ( List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.rightCells ++ [ symbol.nonterminal rightBound ] ) using 1 ; aesop ( simp_config := { singlePass := true } ) ;
      · convert grammar_deri_of_tran _ using 1;
        convert sim_move_left M cfg.headState q' cfg.headOrig cfg.headCur lo.1 lo.2 h ( [ symbol.nonterminal leftBound ] ++ List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) lc.reverse ) ( List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.rightCells ++ [ symbol.nonterminal rightBound ] ) using 1;
        · simp +decide [ List.map_reverse ];
        · aesop;
    · rcases cfg with ⟨ leftCells, headState, headOrig, headCur, rightCells ⟩ ; rcases rightCells with ( _ | ⟨ ro, rc ⟩ ) <;> simp_all +decide ;
      · convert grammar_deri_of_tran _ using 1;
        convert sim_move_right_boundary M headState q' headOrig headCur h _ _ using 1;
        rotate_left;
        rotate_left;
        exact [ symbol.nonterminal leftBound ] ++ List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) leftCells;
        exact [ ];
        · unfold encodeTwoTrack; aesop;
        · unfold encodeTwoTrack; aesop;
      · refine' Relation.ReflTransGen.single _;
        convert sim_move_right M headState q' headOrig headCur ro.1 ro.2 h ( [ .nonterminal leftBound ] ++ leftCells.map ( fun x => .nonterminal ( cell x.1 x.2 ) ) ) ( rc.map ( fun x => .nonterminal ( cell x.1 x.2 ) ) ++ [ .nonterminal rightBound ] ) using 1;
        · unfold encodeTwoTrack; aesop;
        · unfold encodeTwoTrack; aesop;
  · unfold encodeTwoTrack at *;
    apply Relation.ReflTransGen.single;
    convert sim_write M cfg.headState q' cfg.headOrig cfg.headCur hγ' h _ _ using 1;
    rotate_left;
    rotate_left;
    exact [ symbol.nonterminal leftBound ] ++ List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.leftCells;
    exact List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.rightCells ++ [ symbol.nonterminal rightBound ];
    · simp +decide [ List.append_assoc ];
    · grind

/-
PROBLEM
Multiple steps of `stepTwoTrack` can be simulated by the grammar.

PROVIDED SOLUTION
By induction on n.

Base case (n = 0): hsteps says some cfg = some cfg', so cfg = cfg'. Use grammar_deri_self.

Inductive step (n + 1):
Nat.iterate f (n+1) (some cfg) = Nat.iterate f n (f (some cfg)) = Nat.iterate f n (some cfg >>= stepTwoTrack M).

If stepTwoTrack M cfg = none, then some cfg >>= stepTwoTrack M = none, so Nat.iterate on none gives none (since none >>= f = none for all f and all iterations). Then none = some cfg' is a contradiction.

If stepTwoTrack M cfg = some cfg_mid, then:
Nat.iterate f n (some cfg_mid) = some cfg'.
By IH: grammar_derives (encodeTwoTrack cfg_mid) (encodeTwoTrack cfg').
By simulation_one_step: grammar_derives (encodeTwoTrack cfg) (encodeTwoTrack cfg_mid).
Chain: grammar_deri_of_deri_deri.
-/
theorem simulation_multi_step
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg : @TwoTrackConfig T Λ)
    (n : ℕ)
    (cfg' : @TwoTrackConfig T Λ)
    (hsteps : (Nat.iterate (fun c => c >>= stepTwoTrack M) n (some cfg)) = some cfg') :
    grammar_derives (tmToGrammar T Λ M)
      (encodeTwoTrack cfg)
      (encodeTwoTrack cfg') := by
  induction' n with n ih generalizing cfg cfg' <;> simp_all +decide [ Function.iterate_succ_apply' ];
  · exact?;
  · cases h' : ( fun c : Option ( TwoTrackConfig ) => c.bind ( stepTwoTrack M ) ) ^[ n ] ( some cfg ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
    exact grammar_deri_of_deri_deri ( ih _ _ h' ) ( simulation_one_step _ _ _ hsteps )

/-! ### Phase 2.5: Halt conversion

When the TM halts, convert the two-track encoding to the halted encoding. -/

/-
PROBLEM
Step 1 of halt-to-halted: convert headCell to haltCell when TM halts.

PROVIDED SOLUTION
We need to show a grammar_transforms step. The cleanup rule `⟨[], headCell q orig γ, [], [.nonterminal (haltCell orig)]⟩` is in cleanupRules when M q γ = none (which is our hypothesis h_halts where γ = cur). Use this rule with u = prefix_ and v = suffix_. The rule is in the grammar via cleanup_rule_mem. Unfold grammar_transforms: the rule exists in g.rules, and w₁ = prefix_ ++ [] ++ [nonterminal (headCell q orig cur)] ++ [] ++ suffix_ and w₂ = prefix_ ++ [nonterminal (haltCell orig)] ++ suffix_.
-/
theorem halt_headCell_to_haltCell
    (M : Turing.TM0.Machine (Option T) Λ)
    (q : Λ) (orig cur : Option T)
    (h_halts : M q cur = none)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig cur)] ++ suffix_)
      (prefix_ ++ [.nonterminal (haltCell orig)] ++ suffix_) := by
  refine' ⟨ _, _, prefix_, suffix_, _, _ ⟩ <;> norm_num [ h_halts ];
  exact ⟨ [ ], headCell q orig cur, [ ], [ symbol.nonterminal ( haltCell orig ) ] ⟩
  all_goals generalize_proofs at *; simp_all +decide [ tmToGrammar ] ;
  unfold cleanupRules; simp +decide [ h_halts ] ;
  refine' Or.inr ( Or.inr ⟨ q, _, cur, _, _ ⟩ );
  · exact Finset.mem_toList.mpr ( Finset.mem_univ q );
  · cases cur <;> [ exact List.mem_cons_self; exact List.mem_cons_of_mem _ ( List.mem_map.mpr ⟨ _, Finset.mem_toList.mpr ( Finset.mem_univ _ ), rfl ⟩ ) ] ;
  · cases orig <;> simp +decide [ h_halts ];
    · exact List.mem_cons_self;
    · exact List.mem_cons_of_mem _ ( List.mem_map.mpr ⟨ _, Finset.mem_toList.mpr ( Finset.mem_univ _ ), rfl ⟩ )

/-
PROBLEM
Step 2: propagate halt to right cells.

PROVIDED SOLUTION
By induction on cells.
Base case: cells = [], the source and target are the same, use grammar_deri_self.
Inductive case: cells = (o', c') :: rest.
  Source: prefix_ ++ [haltCell orig] ++ [(cell o' c')] ++ rest.map(...) ++ suffix_
  Apply the cleanup rule: haltCell orig · cell(o', c') → haltCell(orig) · haltCell(o')
  This rule is: ⟨[], haltCell orig, [.nonterminal (cell o' c')], [.nonterminal (haltCell orig), .nonterminal (haltCell o')]⟩
  with u = prefix_ and v = rest.map(...) ++ suffix_.
  Result: prefix_ ++ [haltCell orig, haltCell o'] ++ rest.map(...) ++ suffix_
  Then apply IH with orig := o' and prefix_ := prefix_ ++ [haltCell orig] to convert rest.
  The IH gives: (prefix_ ++ [haltCell orig]) ++ [haltCell o'] ++ rest.map(cell) ++ suffix_ derives (prefix_ ++ [haltCell orig]) ++ [haltCell o'] ++ rest.map(haltCell) ++ suffix_.
  Chain with grammar_deri_of_tran_deri.
-/
theorem propagate_halt_right
    (M : Turing.TM0.Machine (Option T) Λ)
    (cells : List (Option T × Option T))
    (orig : Option T)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_derives (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (haltCell orig)] ++
        cells.map (fun ⟨o, c⟩ => .nonterminal (cell o c)) ++ suffix_)
      (prefix_ ++ [.nonterminal (haltCell orig)] ++
        cells.map (fun ⟨o, _⟩ => .nonterminal (haltCell o)) ++ suffix_) := by
  induction' cells with cells_head cells_tail ih generalizing orig prefix_ suffix_ <;> simp_all +decide [ List.map ];
  · constructor;
  · -- Apply theتحديث rule to replace `cell cells_head.1 cells_head.2` with `haltCell cells_head.1`.
    have h_replace : grammar_transforms (tmToGrammar T Λ M) (prefix_ ++ [symbol.nonterminal (haltCell orig), symbol.nonterminal (cell cells_head.1 cells_head.2)] ++ (List.map (fun x => symbol.nonterminal (cell x.1 x.2)) cells_tail ++ suffix_)) (prefix_ ++ [symbol.nonterminal (haltCell orig), symbol.nonterminal (haltCell cells_head.1)] ++ (List.map (fun x => symbol.nonterminal (cell x.1 x.2)) cells_tail ++ suffix_)) := by
      refine' ⟨ ⟨ [ ], haltCell orig, [ .nonterminal ( cell cells_head.1 cells_head.2 ) ], [ .nonterminal ( haltCell orig ), .nonterminal ( haltCell cells_head.1 ) ] ⟩, _, _ ⟩ <;> simp +decide [ tmToGrammar ];
      · unfold cleanupRules; simp +decide [ List.mem_append, List.mem_map ] ;
        refine' Or.inr <| Or.inr <| Or.inr ⟨ _, _, _ ⟩;
        · exact List.mem_cons.mpr ( by cases orig <;> simp +decide );
        · -- Since `cells_head.1` is an `Option T`, it must be either `none` or `some t` for some `t`. In either case, it is included in the list `allOptT`.
          cases' cells_head.1 with t ht;
          · exact List.mem_cons_self;
          · exact List.mem_cons_of_mem _ ( List.mem_map.mpr ⟨ t, Finset.mem_toList.mpr ( Finset.mem_univ _ ), rfl ⟩ );
        · exact List.mem_cons.mpr ( by cases cells_head.2 <;> simp +decide );
      · exact ⟨ prefix_, List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cells_tail ++ suffix_, rfl, rfl ⟩;
    specialize ih cells_head.1 ( prefix_ ++ [ symbol.nonterminal ( haltCell orig ) ] ) suffix_ ; simp_all +decide [ Relation.ReflTransGen ] ; (
    exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single h_replace ) ih;)

/-
PROBLEM
Single left-propagation step: convert one cell immediately left of a haltCell.

PROVIDED SOLUTION
The cleanup rule is: ⟨[.nonterminal (cell o c)], haltCell anchor_orig, [], [.nonterminal (haltCell o), .nonterminal (haltCell anchor_orig)]⟩.

Use this rule with u = prefix_ and v = suffix_.

In grammar_transforms:
w₁ = u ++ input_L ++ [nonterminal input_N] ++ input_R ++ v
= prefix_ ++ [nonterminal (cell o c)] ++ [nonterminal (haltCell anchor_orig)] ++ [] ++ suffix_
= prefix_ ++ [nonterminal (cell o c), nonterminal (haltCell anchor_orig)] ++ suffix_ ✓

w₂ = u ++ output_string ++ v
= prefix_ ++ [nonterminal (haltCell o), nonterminal (haltCell anchor_orig)] ++ suffix_ ✓

The rule is in tmToGrammar.rules because it's in cleanupRules. Show membership by unfolding cleanupRules and using the fact that anchor_orig, o, c are all in allOptT (by cases on Option T; none is in the list, and some t is mapped from Finset.univ).
-/
theorem propagate_halt_left_one_step
    (M : Turing.TM0.Machine (Option T) Λ)
    (o c : Option T) (anchor_orig : Option T)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (cell o c), .nonterminal (haltCell anchor_orig)] ++ suffix_)
      (prefix_ ++ [.nonterminal (haltCell o), .nonterminal (haltCell anchor_orig)] ++ suffix_) := by
  unfold tmToGrammar
  generalize_proofs at *;
  use ⟨ [ .nonterminal ( cell o c ) ], haltCell anchor_orig, [ ], [ .nonterminal ( haltCell o ), .nonterminal ( haltCell anchor_orig ) ] ⟩
  simp [cleanupRules];
  refine' ⟨ Or.inr <| Or.inr <| Or.inr _, _, _, rfl, rfl ⟩;
  -- Since `allOptT` is defined as `none :: (Finset.univ.val.toList.map some)`, any element of `Option T` is either `none` or `some t` for some `t` in `T`.
  have h_allOptT : ∀ x : Option T, x ∈ none :: (Finset.univ.val.toList.map some) := by
    rintro ( _ | x ) <;> simp +decide;
  exact ⟨ h_allOptT anchor_orig, h_allOptT o, h_allOptT c ⟩

/-
PROBLEM
Step 3: propagate halt to left cells, using a haltCell anchor on the right.

The cleanup rule `cell(o'', c'') · haltCell(orig) → haltCell(o'') · haltCell(orig)` converts
cells from right to left, using the rightmost haltCell as an anchor.

PROVIDED SOLUTION
By reverse induction on cells using List.reverseRecOn.

Base case (cells = []): source = target, use ReflTransGen.refl.

Step case (cells = init ++ [⟨o_last, c_last⟩]):
Source = prefix_ ++ (init ++ [⟨o_last, c_last⟩]).map(cell) ++ [haltCell anchor_orig] ++ suffix_
= prefix_ ++ init.map(cell) ++ [cell(o_last, c_last), haltCell(anchor_orig)] ++ suffix_

Step 1: Apply propagate_halt_left_one_step to convert the last cell:
u = prefix_ ++ init.map(cell), converts cell(o_last, c_last) · haltCell(anchor_orig) → haltCell(o_last) · haltCell(anchor_orig).
Result: prefix_ ++ init.map(cell) ++ [haltCell(o_last), haltCell(anchor_orig)] ++ suffix_

Step 2: Apply IH on init with anchor_orig := o_last and suffix_ := [haltCell(anchor_orig)] ++ suffix_:
Result: prefix_ ++ init.map(haltCell) ++ [haltCell(o_last), haltCell(anchor_orig)] ++ suffix_

The target is: prefix_ ++ (init ++ [⟨o_last, c_last⟩]).map(haltCell) ++ [haltCell(anchor_orig)] ++ suffix_
= prefix_ ++ init.map(haltCell) ++ [haltCell(o_last)] ++ [haltCell(anchor_orig)] ++ suffix_ ✓

Use grammar_deri_of_tran_deri to chain step 1 and step 2. Need List.map_append and simp for list associativity.
-/
theorem propagate_halt_left
    (M : Turing.TM0.Machine (Option T) Λ)
    (cells : List (Option T × Option T))
    (anchor_orig : Option T)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_derives (tmToGrammar T Λ M)
      (prefix_ ++ cells.map (fun ⟨o, c⟩ => .nonterminal (cell o c)) ++
        [.nonterminal (haltCell anchor_orig)] ++ suffix_)
      (prefix_ ++ cells.map (fun ⟨o, _⟩ => .nonterminal (haltCell o)) ++
        [.nonterminal (haltCell anchor_orig)] ++ suffix_) := by
  -- By the definition of `grammar_transforms`, we can apply the cleanup rule `cell(o'', c'') · haltCell(orig) → haltCell(o'') · haltCell(orig)` to each cell in `cells`.
  have h_transforms : ∀ (o c : Option T) (anchor_orig : Option T) (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))),
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [symbol.nonterminal (cell o c), symbol.nonterminal (haltCell anchor_orig)] ++ suffix_)
      (prefix_ ++ [symbol.nonterminal (haltCell o), symbol.nonterminal (haltCell anchor_orig)] ++ suffix_) := by
        grind +suggestions;
  induction' cells using List.reverseRecOn with cells ih generalizing anchor_orig prefix_ suffix_;
  · constructor;
  · rename_i h;
    specialize h_transforms ih.1 ih.2 anchor_orig ( prefix_ ++ List.map ( fun x => match x with | ( o, c ) => symbol.nonterminal ( cell o c ) ) cells ) ( suffix_ ) ; simp_all +decide [ List.map_append ] ;
    exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single h_transforms ) ( h _ _ _ ) |> fun h => by simpa [ List.append_assoc ] using h;

/-
PROBLEM
From a halting two-track config, the grammar derives the halted encoding.

Composition of halt_headCell_to_haltCell, propagate_halt_right, and propagate_halt_left.

PROVIDED SOLUTION
Unfold encodeTwoTrack and encodeHalted/twoTrackOriginals.

Source (encodeTwoTrack cfg):
[leftBound] ++ cfg.leftCells.map(cell) ++ [headCell(q, headOrig, headCur)] ++ cfg.rightCells.map(cell) ++ [rightBound]

Target (encodeHalted (twoTrackOriginals cfg)):
[leftBound] ++ (cfg.leftCells.map(Prod.fst) ++ [cfg.headOrig] ++ cfg.rightCells.map(Prod.fst)).map(haltCell) ++ [rightBound]
= [leftBound] ++ cfg.leftCells.map(fun ⟨o,_⟩ => haltCell o) ++ [haltCell(headOrig)] ++ cfg.rightCells.map(fun ⟨o,_⟩ => haltCell o) ++ [rightBound]

Step 1: Apply halt_headCell_to_haltCell with prefix_ = [leftBound] ++ cfg.leftCells.map(cell), suffix_ = cfg.rightCells.map(cell) ++ [rightBound].
This converts headCell to haltCell:
→ [leftBound] ++ leftCells.map(cell) ++ [haltCell(headOrig)] ++ rightCells.map(cell) ++ [rightBound]

Step 2: Apply propagate_halt_right with orig = headOrig, prefix_ = [leftBound] ++ leftCells.map(cell), suffix_ = [rightBound], cells = rightCells.
→* [leftBound] ++ leftCells.map(cell) ++ [haltCell(headOrig)] ++ rightCells.map(haltCell) ++ [rightBound]

Step 3: Apply propagate_halt_left with anchor_orig = headOrig, prefix_ = [leftBound], suffix_ = rightCells.map(haltCell) ++ [rightBound], cells = leftCells.
→* [leftBound] ++ leftCells.map(haltCell) ++ [haltCell(headOrig)] ++ rightCells.map(haltCell) ++ [rightBound]

Chain all three with grammar_deri_of_tran_deri and grammar_deri_of_deri_deri.

Note: need to carefully handle List.append associativity using simp [List.append_assoc] etc.
-/
theorem halt_to_halted
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg : @TwoTrackConfig T Λ)
    (h_halts : M cfg.headState cfg.headCur = none) :
    grammar_derives (tmToGrammar T Λ M)
      (encodeTwoTrack cfg)
      (encodeHalted (twoTrackOriginals cfg)) := by
  convert grammar_deri_of_deri_deri _ _ using 1;
  exact ( [ .nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => .nonterminal ( cell o c ) ) ++ [ .nonterminal ( haltCell cfg.headOrig ) ] ++ cfg.rightCells.map ( fun ⟨ o, c ⟩ => .nonterminal ( cell o c ) ) ++ [ .nonterminal rightBound ] );
  · convert grammar_deri_of_tran_deri ( halt_headCell_to_haltCell M cfg.headState cfg.headOrig cfg.headCur h_halts _ _ ) _ using 1;
    rotate_left;
    exact [ symbol.nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( cell o c ) );
    exact cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( cell o c ) ) ++ [ symbol.nonterminal rightBound ];
    · simp +decide [ List.append_assoc ];
      constructor;
    · unfold encodeTwoTrack; aesop;
  · convert grammar_deri_of_deri_deri _ _ using 1;
    exact [ symbol.nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( cell o c ) ) ++ [ symbol.nonterminal ( haltCell cfg.headOrig ) ] ++ cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal rightBound ];
    · convert propagate_halt_right M cfg.rightCells cfg.headOrig _ _ using 1;
    · convert grammar_deri_of_deri_deri _ _ using 1;
      exact [ symbol.nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal ( haltCell cfg.headOrig ) ] ++ cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal rightBound ];
      · convert propagate_halt_left M cfg.leftCells cfg.headOrig [ symbol.nonterminal leftBound ] ( cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal rightBound ] ) using 1;
        · grind;
        · simp +decide [ List.append_assoc ];
      · convert grammar_deri_self using 1;
        unfold encodeHalted twoTrackOriginals; aesop;

/-! ### Composing all phases -/

/-
PROBLEM
The original input stored in the initial two-track config for word `w` is exactly `w.map some`.
That is, `extractInput (twoTrackOriginals (initTwoTrack w)) = w`.

PROVIDED SOLUTION
By cases on w:

Case w = []:
  initTwoTrack [] = ⟨[], default, none, none, []⟩
  twoTrackOriginals this = [].map Prod.fst ++ [none] ++ [].map Prod.fst = [none]
  extractInput [none] = [none].filterMap id = [] = w ✓

Case w = t :: ts:
  initTwoTrack (t :: ts) = ⟨[], default, some t, some t, ts.map (fun t' => (some t', some t'))⟩
  twoTrackOriginals = [].map Prod.fst ++ [some t] ++ (ts.map (fun t' => (some t', some t'))).map Prod.fst

  Now (ts.map (fun t' => (some t', some t'))).map Prod.fst = ts.map (fun t' => some t') = ts.map some

  So twoTrackOriginals = [some t] ++ ts.map some = (t :: ts).map some

  extractInput ((t :: ts).map some) = ((t :: ts).map some).filterMap id
  = (some t :: ts.map some).filterMap id
  = t :: (ts.map some).filterMap id

  And (ts.map some).filterMap id = ts (by induction on ts: filterMap id (some x :: rest) = x :: filterMap id rest)

  So extractInput = t :: ts = w ✓

Just unfold definitions and simp. The key steps are:
1. Unfold initTwoTrack, twoTrackOriginals, extractInput
2. Simplify List.map, List.filterMap
3. Show List.filterMap id (List.map some xs) = xs by induction
-/
theorem extractInput_initTwoTrack (w : List T) :
    extractInput (twoTrackOriginals (initTwoTrack w : @TwoTrackConfig T Λ)) = w := by
  unfold twoTrackOriginals extractInput initTwoTrack; induction w <;> aesop;

/-! ### Correspondence between TM0.Cfg and TwoTrackConfig -/

/-- A TwoTrackConfig corresponds to a TM0.Cfg if the head state, head symbol,
and tape contents match (with the tape being blank beyond the TwoTrackConfig window). -/
structure TMCorresponds
    (tc : @TwoTrackConfig T Λ)
    (tmCfg : Turing.TM0.Cfg (Option T) Λ) : Prop where
  state_eq : tc.headState = tmCfg.q
  head_eq : tc.headCur = tmCfg.Tape.head
  left_match : ∀ i,
    (tc.leftCells.reverse.map Prod.snd).getI i = tmCfg.Tape.left.nth i
  right_match : ∀ i,
    (tc.rightCells.map Prod.snd).getI i = tmCfg.Tape.right.nth i

/-
PROBLEM
The initial TwoTrackConfig corresponds to the initial TM0 config.

PROVIDED SOLUTION
Unfold initTwoTrack and TM0.init.

For w = []:
- initTwoTrack [] = ⟨[], default, none, none, []⟩
- TM0.init [] = ⟨default, Tape.mk₁ []⟩ = ⟨default, Tape.mk' (ListBlank.mk []) (ListBlank.mk [])⟩
- state_eq: default = default ✓
- head_eq: none = (Tape.mk' (ListBlank.mk []) (ListBlank.mk [])).head = (ListBlank.mk []).head = default = none ✓
- left_match: [].reverse.map Prod.snd = [], so getI i = default = none. And (ListBlank.mk []).nth i = [].getI i = default = none ✓
- right_match: similarly ✓

For w = t :: ts:
- initTwoTrack (t :: ts) = ⟨[], default, some t, some t, ts.map (fun t' => (some t', some t'))⟩
- TM0.init (t :: ts).map some = ⟨default, Tape.mk₁ (some t :: ts.map some)⟩
- Tape.mk₁ l = Tape.mk' (ListBlank.mk []) (ListBlank.mk l)
- So tape.head = (ListBlank.mk (some t :: ts.map some)).head = some t
- tape.left = ListBlank.mk []
- tape.right = (ListBlank.mk (some t :: ts.map some)).tail
- state_eq: default = default ✓
- head_eq: some t = some t ✓
- left_match: [].reverse.map Prod.snd = [], getI i = none = (ListBlank.mk []).nth i ✓
- right_match: rightCells = ts.map (fun t' => (some t', some t')), so rightCells.map Prod.snd = ts.map some.
  getI i = (ts.map some).getI i = tape.right.nth i
  We need: tape.right.nth i = (ts.map some).getI i
  tape.right = (ListBlank.mk (some t :: ts.map some)).tail
  = ListBlank.mk (ts.map some) (by ListBlank.tail applied to mk gives mk of the tail)
  Wait, I need to verify: ListBlank.mk (a :: l).tail = ListBlank.mk l ? Or is it different?

  Actually, Tape.mk' L R has right = R.tail where R = ListBlank.mk l.
  ListBlank.tail (ListBlank.mk (some t :: ts.map some)) should give ListBlank.mk (ts.map some).

  Then right.nth i = (ListBlank.mk (ts.map some)).nth i = (ts.map some).getI i ✓

Use Turing.ListBlank.nth_mk to convert ListBlank.nth to List.getI.
Use Turing.Tape.mk'_head for the head.
For Tape structure: Tape.mk' L R has head = R.head, left = L, right = R.tail.
-/
theorem initCorresponds (w : List T) :
    TMCorresponds
      (initTwoTrack w : @TwoTrackConfig T Λ)
      (Turing.TM0.init (w.map Option.some)) := by
  constructor;
  · cases w <;> aesop;
  · cases w <;> aesop;
  · cases w <;> aesop;
  · unfold initTwoTrack TM0.init; aesop;

/-
PROBLEM
If tc corresponds to tmCfg and the TM halts, then stepTwoTrack also returns none.

PROVIDED SOLUTION
TM0.step M tmCfg = none means M tmCfg.q tmCfg.Tape.head = none.
From hcorr.state_eq: tc.headState = tmCfg.q
From hcorr.head_eq: tc.headCur = tmCfg.Tape.head
So M tc.headState tc.headCur = none.
Unfold stepTwoTrack: match M tc.headState tc.headCur = none, so returns none. ✓

TM0.step is:
  match M tmCfg.q tmCfg.Tape.head with
  | none => none
  | some _ => some _
So TM0.step M tmCfg = none ↔ M tmCfg.q tmCfg.Tape.head = none.
Use simp [Turing.TM0.step] on hhalt to get M tmCfg.q tmCfg.Tape.head = none.
Then rewrite using hcorr.state_eq and hcorr.head_eq.
Unfold stepTwoTrack and simp.
-/
theorem corresponds_step_none
    (M : Turing.TM0.Machine (Option T) Λ)
    (tc : @TwoTrackConfig T Λ)
    (tmCfg : Turing.TM0.Cfg (Option T) Λ)
    (hcorr : TMCorresponds tc tmCfg)
    (hhalt : Turing.TM0.step M tmCfg = none) :
    stepTwoTrack M tc = none := by
  -- By definition of `stepTwoTrack`, we know that if `M tc.headState tc.headCur = none`, then `stepTwoTrack M tc = none`.
  simp [stepTwoTrack, hhalt];
  rw [ show M tc.headState tc.headCur = none from ?_ ];
  rw [ hcorr.state_eq, hcorr.head_eq ];
  convert hhalt using 1;
  unfold TM0.step; aesop;

/-
PROBLEM
If tc corresponds to tmCfg and the TM steps to tmCfg', then stepTwoTrack
produces a tc' that corresponds to tmCfg'.

PROVIDED SOLUTION
TM0.step M tmCfg = some tmCfg' means M tmCfg.q tmCfg.Tape.head = some (q', action) for some q' and action, and tmCfg' is the result of applying the action.

From hcorr, tc.headState = tmCfg.q and tc.headCur = tmCfg.Tape.head.
So M tc.headState tc.headCur = some (q', action).

Case split on action:

Case write γ':
tmCfg' = { q := q', Tape := Tape.write γ' tmCfg.Tape }
stepTwoTrack M tc = some ⟨tc.leftCells, q', tc.headOrig, γ', tc.rightCells⟩ =: tc'

Correspondence tc' tmCfg':
- state_eq: q' = q' ✓
- head_eq: γ' = (Tape.write γ' tmCfg.Tape).head = γ' ✓ (Tape.write sets the head)
- left_match: tc'.leftCells = tc.leftCells, same as before. And (Tape.write γ' T).left = T.left. So same ✓
- right_match: tc'.rightCells = tc.rightCells. And (Tape.write γ' T).right = T.right. So same ✓

Case move Dir.right:
tmCfg' = { q := q', Tape := Tape.move Dir.right tmCfg.Tape }
Tape.move Dir.right T = { head := T.right.head, left := ListBlank.cons T.head T.left, right := T.right.tail }

Subcase tc.rightCells non-empty = (ro, rc) :: rest:
stepTwoTrack gives tc' = ⟨tc.leftCells ++ [(tc.headOrig, tc.headCur)], q', ro, rc, rest⟩

Correspondence:
- state_eq: q' = q' ✓
- head_eq: rc = T.right.head (from hcorr.right_match at i=0: tc.rightCells.map(Prod.snd).getI 0 = T.right.nth 0 = T.right.head, and tc.rightCells.map(Prod.snd).getI 0 = rc) ✓
- right_match: rest.map(Prod.snd).getI i = T.right.tail.nth i
  = T.right.nth (i+1) (by ListBlank.tail/nth relationship)
  = tc.rightCells.map(Prod.snd).getI (i+1) (from hcorr.right_match at i+1)
  = (rc :: rest.map(Prod.snd)).getI (i+1)  hmm this is (rest.map Prod.snd).getI i ✓ (by List.getI_cons_succ)
- left_match: (tc.leftCells ++ [(tc.headOrig, tc.headCur)]).reverse.map(Prod.snd).getI i
  = ((tc.headOrig, tc.headCur) :: tc.leftCells.reverse).map(Prod.snd).getI i
  = (tc.headCur :: tc.leftCells.reverse.map(Prod.snd)).getI i
  For i = 0: tc.headCur = T.head (from hcorr.head_eq). And (ListBlank.cons T.head T.left).nth 0 = T.head ✓
  For i > 0: tc.leftCells.reverse.map(Prod.snd).getI (i-1) = T.left.nth (i-1) (from hcorr.left_match)
  And (ListBlank.cons T.head T.left).nth i = T.left.nth (i-1) ✓

Subcase tc.rightCells empty:
stepTwoTrack gives tc' = ⟨tc.leftCells ++ [(tc.headOrig, tc.headCur)], q', none, none, []⟩
T.right.head = T.right.nth 0 = tc.rightCells.map(Prod.snd).getI 0 = default = none (since rightCells = [])
So tmCfg'.Tape.head = none ✓

Case move Dir.left: Similar logic with left/right reversed.

The key Mathlib lemmas needed:
- ListBlank.cons_nth_zero, ListBlank.cons_nth_succ (or ListBlank.nth_cons)
- ListBlank.tail_nth (ListBlank.tail l).nth i = l.nth (i+1)
- Tape.write_head, Tape.write_left, Tape.write_right
- List.getI_cons_zero, List.getI_cons_succ
- List.reverse_append

This is complex but each case follows the same pattern. Let the subagent handle the details.
-/
theorem corresponds_step_some
    (M : Turing.TM0.Machine (Option T) Λ)
    (tc : @TwoTrackConfig T Λ)
    (tmCfg tmCfg' : Turing.TM0.Cfg (Option T) Λ)
    (hcorr : TMCorresponds tc tmCfg)
    (hstep : Turing.TM0.step M tmCfg = some tmCfg') :
    ∃ tc', stepTwoTrack M tc = some tc' ∧ TMCorresponds tc' tmCfg' := by
  unfold TM0.step at hstep;
  rcases hcorr with ⟨ hq, hhead, hleft, hright ⟩;
  obtain ⟨q', a, hq', ha⟩ : ∃ q' a, M tc.headState tc.headCur = some (q', a) ∧ tmCfg' = (match a with | TM0.Stmt.move d => { q := q', Tape := Tape.move d tmCfg.Tape } | TM0.Stmt.write a => { q := q', Tape := Tape.write a tmCfg.Tape }) := by
                                                                                                                                                                                                cases h : M tc.headState tc.headCur <;> aesop;
  rcases a with ( _ | _ ) <;> simp_all +decide [ TMCorresponds ];
  · rename_i d; unfold stepTwoTrack; rcases d with ( _ | _ ) <;> simp_all +decide [ TMCorresponds ] ;
    · rcases h : tc.leftCells.reverse with ( _ | ⟨ ⟨ lo, lc ⟩, rest ⟩ ) <;> simp_all +decide [ TMCorresponds ];
      · constructor <;> simp_all +decide [ TMCorresponds ];
        · specialize hleft 0 ; aesop;
        · intro i; specialize hleft ( i + 1 ) ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ Tape.move ] ;
      · constructor <;> simp_all +decide [ TMCorresponds ];
        · specialize hleft 0 ; aesop;
        · intro i; specialize hleft ( i + 1 ) ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ Tape.move ] ;
    · rcases tc with ⟨ leftCells, headState, headOrig, headCur, rightCells ⟩ ; rcases rightCells with ( _ | ⟨ ro, rc ⟩ ) <;> simp_all +decide [ TMCorresponds ] ;
      · constructor <;> simp +decide [ *, Tape.move ];
        · specialize hright 0 ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ List.getI ] ;
        · intro i; specialize hright ( i + 1 ) ; aesop;
      · constructor <;> simp_all +decide [ Tape.move ];
        · specialize hright 0 ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ List.getI ] ;
        · intro i; specialize hright ( i + 1 ) ; aesop;
  · unfold stepTwoTrack;
    simp_all +decide [ TMCorresponds ];
    constructor <;> aesop

/-! ### Main Correctness Theorems -/

/-
PROBLEM
If tc corresponds to tmCfg, and the TM reaches a halting config from tmCfg,
then the grammar can derive from tc's encoding to some halting tc_final's encoding,
with the original track preserved.

PROVIDED SOLUTION
By induction on hreaches : Reaches (TM0.step M) tmCfg tmCfg_halt, which is ReflTransGen (fun a b => b ∈ TM0.step M a) tmCfg tmCfg_halt.

Note: Reaches f a b = ReflTransGen (fun x y => y ∈ f x) a b. And for Option-valued f, y ∈ f x means f x = some y.

Base case (tmCfg = tmCfg_halt):
The TM is already at the halting config. Use tc_final = tc.
- grammar_derives: grammar_deri_self
- M tc.headState tc.headCur = none: From hhalt, TM0.step M tmCfg_halt = none, which means M tmCfg_halt.q tmCfg_halt.Tape.head = none. Since hcorr.state_eq: tc.headState = tmCfg.q = tmCfg_halt.q, and hcorr.head_eq: tc.headCur = tmCfg.Tape.head = tmCfg_halt.Tape.head. Use corresponds_step_none or unfold directly.
Actually, TM0.step M tmCfg = none means M tmCfg.q tmCfg.Tape.head = none. Rewrite using hcorr.
- extractInput preserved: rfl

Inductive step: there exists tmCfg_mid with tmCfg → tmCfg_mid and Reaches tmCfg_mid tmCfg_halt.
  Specifically, ReflTransGen gives us: tmCfg_mid ∈ TM0.step M tmCfg (i.e., TM0.step M tmCfg = some tmCfg_mid) and Reaches (TM0.step M) tmCfg_mid tmCfg_halt.

  1. Use corresponds_step_some M tc tmCfg tmCfg_mid hcorr (the step hypothesis) to get tc_mid with stepTwoTrack M tc = some tc_mid ∧ TMCorresponds tc_mid tmCfg_mid.
  2. By IH on (Reaches tmCfg_mid tmCfg_halt, hhalt, TMCorresponds tc_mid tmCfg_mid): get tc_final with grammar_derives from encodeTwoTrack tc_mid to encodeTwoTrack tc_final, M tc_final.headState tc_final.headCur = none, extractInput preserved.
  3. Use simulation_one_step to get grammar_derives from encodeTwoTrack tc to encodeTwoTrack tc_mid.
  4. Chain: grammar_deri_of_deri_deri.
  5. extractInput: chain stepTwoTrack_preserves_extractInput and IH.

Use Relation.ReflTransGen.head_induction_on or cases_head for the induction.
-/
theorem sim_reaches_halts
    (M : Turing.TM0.Machine (Option T) Λ)
    (tc : @TwoTrackConfig T Λ) (tmCfg : Turing.TM0.Cfg (Option T) Λ)
    (hcorr : TMCorresponds tc tmCfg)
    (tmCfg_halt : Turing.TM0.Cfg (Option T) Λ)
    (hreaches : Turing.Reaches (Turing.TM0.step M) tmCfg tmCfg_halt)
    (hhalt : Turing.TM0.step M tmCfg_halt = none) :
    ∃ tc_final : @TwoTrackConfig T Λ,
      grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack tc) (encodeTwoTrack tc_final) ∧
      M tc_final.headState tc_final.headCur = none ∧
      extractInput (twoTrackOriginals tc_final) = extractInput (twoTrackOriginals tc) := by
  by_contra h_contra;
  apply_mod_cast absurd _ h_contra;
  have h_ind : ∀ tmCfg tmCfg', Reaches (TM0.step M) tmCfg tmCfg' → ∀ tc, TMCorresponds tc tmCfg → ∃ tc', grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack tc) (encodeTwoTrack tc') ∧ TMCorresponds tc' tmCfg' ∧ extractInput (twoTrackOriginals tc') = extractInput (twoTrackOriginals tc) := by
    intros tmCfg tmCfg' hreaches tc hcorr
    induction' hreaches with tmCfg_mid hmid hreaches_mid ih generalizing tc
    <;> simp_all +decide [ Reaches ];
    · exact ⟨ tc, by tauto, by tauto, by tauto ⟩;
    · obtain ⟨ tc', h₁, h₂, h₃ ⟩ := ‹∀ ( tc : TwoTrackConfig ), TMCorresponds tc tmCfg → ∃ tc', grammar_derives ( tmToGrammar T Λ M ) ( encodeTwoTrack tc ) ( encodeTwoTrack tc' ) ∧ TMCorresponds tc' tmCfg_mid ∧ extractInput ( twoTrackOriginals tc' ) = extractInput ( twoTrackOriginals tc ) › tc hcorr;
      obtain ⟨ tc'', h₄, h₅ ⟩ := corresponds_step_some M tc' tmCfg_mid hmid h₂ ih;
      exact ⟨ tc'', grammar_deri_of_deri_deri h₁ ( simulation_one_step M tc' tc'' h₄ ), h₅, stepTwoTrack_preserves_extractInput M tc' tc'' h₄ ▸ h₃ ⟩;
  obtain ⟨tc_final, htc_final⟩ := h_ind tmCfg tmCfg_halt hreaches tc hcorr;
  refine' ⟨ tc_final, htc_final.1, _, htc_final.2.2 ⟩;
  convert hhalt using 1;
  simp +decide [ TM0.step, htc_final.2.1.state_eq, htc_final.2.1.head_eq ]

/-
PROBLEM
If the TM halts on input `w`, then the grammar derives `w`.

PROVIDED SOLUTION
Given: (TM0.eval M (w.map some)).Dom
Goal: grammar_generates (tmToGrammar T Λ M) w = grammar_derives g [.nonterminal start] (w.map .terminal)

Step 1: From hypothesis, extract halting config.
TM0.eval M l = Part.map (·.Tape.right₀) (Turing.eval (TM0.step M) (TM0.init l))
(TM0.eval M l).Dom = (Turing.eval (TM0.step M) (TM0.init l)).Dom (Part.map preserves Dom: just exact h)
Using Part.dom_iff_mem: ∃ cfg, cfg ∈ Turing.eval (TM0.step M) (TM0.init (w.map some))
Using Turing.mem_eval: ∃ cfg, Reaches (TM0.step M) (TM0.init (w.map some)) cfg ∧ TM0.step M cfg = none

Step 2: Apply sim_reaches_halts with tc = initTwoTrack w, tmCfg = TM0.init (w.map some), hcorr = initCorresponds w.
Get tc_final with:
- grammar_derives (encodeTwoTrack (initTwoTrack w)) (encodeTwoTrack tc_final)
- M tc_final.headState tc_final.headCur = none
- extractInput (twoTrackOriginals tc_final) = extractInput (twoTrackOriginals (initTwoTrack w)) = w (by extractInput_initTwoTrack)

Step 3: Chain:
[start] →* encodeTwoTrack(initTwoTrack w)   (generation_derives)
→* encodeTwoTrack(tc_final)                  (from sim_reaches_halts)
→* encodeHalted(twoTrackOriginals tc_final)  (halt_to_halted, using M tc_final.headState tc_final.headCur = none)
→* (extractInput(twoTrackOriginals tc_final)).map terminal  (cleanup_derives)
= w.map terminal                              (using extractInput preservation and extractInput_initTwoTrack)

Use grammar_deri_of_deri_deri to chain. Use rw/simp at the end to show the final result equals w.map terminal.
-/
theorem tmToGrammar_generates_of_halts
    (M : Turing.TM0.Machine (Option T) Λ) (w : List T)
    (h : (Turing.TM0.eval M (w.map Option.some)).Dom) :
    grammar_generates (tmToGrammar T Λ M) w := by
  -- By definition of `TM0.eval`, there exists a configuration `cfg` such that `cfg` is reachable from the initial configuration and `cfg` halts.
  obtain ⟨cfg, hcfg⟩ : ∃ cfg : Turing.TM0.Cfg (Option T) Λ, Turing.Reaches (Turing.TM0.step M) (Turing.TM0.init (w.map some)) cfg ∧ Turing.TM0.step M cfg = none := by
    -- By definition of `TM0.eval`, there exists a configuration `cfg` such that `cfg` is reachable from the initial configuration and `cfg` halts. Use this fact to conclude the proof.
    have h_eval_dom : (Turing.eval (TM0.step M) (TM0.init (w.map some))).Dom := by
      convert h using 1;
    grind +suggestions;
  -- Apply `sim_reaches_halts` to obtain the final configuration `tc_final`.
  obtain ⟨tc_final, htc_final⟩ : ∃ tc_final : @TwoTrackConfig T Λ,
    grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack (initTwoTrack w)) (encodeTwoTrack tc_final) ∧
    M tc_final.headState tc_final.headCur = none ∧
    extractInput (twoTrackOriginals tc_final) = w := by
      convert sim_reaches_halts M (initTwoTrack w) (Turing.TM0.init (w.map some)) (initCorresponds w) cfg hcfg.1 hcfg.2 using 1;
      rw [ extractInput_initTwoTrack ];
  -- Apply `halt_to_halted` and `cleanup_derives` to conclude the proof.
  have h_final : grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack tc_final) (List.map symbol.terminal (extractInput (twoTrackOriginals tc_final))) := by
    exact Relation.ReflTransGen.trans ( halt_to_halted M tc_final htc_final.2.1 ) ( cleanup_derives M _ );
  exact Relation.ReflTransGen.trans ( generation_derives M w ) ( Relation.ReflTransGen.trans htc_final.1 h_final ) |> fun h => h |> fun h => h |> fun h => by simpa [ htc_final.2.2 ] using h;

-- The theorems `tmToGrammar_halts_of_generates`, `tmToGrammar_correct`,
-- `tm_recognizable_implies_re`, and `re_iff_tm_recognizable` have been moved to
-- `Langlib.Classes.RecursivelyEnumerable.Equivalence.TMtoGrammarSoundness` where the
-- corrected soundness proof is located.
