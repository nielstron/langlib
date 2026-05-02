import Mathlib
import Langlib.Grammars.Indexed.Definition

/-! # Binarization for Indexed Grammars

This file constructs a binarization transformation for indexed grammars.
Given an indexed grammar with no ε-productions, isolated terminals, separated flags,
and a fresh start symbol, it produces an equivalent grammar in normal form.

This is Step 5 of Aho's Normal Form theorem.

## Construction

After terminal isolation and flag separation, the rules have the following forms:
1. `A → a` (single terminal, consume = none)
2. `A[f·] → B` (flag pop, single nonterminal, no push)
3. `A → B[f·]` (flag push, single nonterminal)
4. `A → B₁ B₂ ... Bₖ` (no consume, no pushes, all nonterminals)

Rules of forms 1-3 are already in normal form (they're unary/terminal).
Rules of form 4 need to be binarized: `A → B₁ C₁`, `C₁ → B₂ C₂`, ..., `Cₖ₋₂ → Bₖ₋₁ Bₖ`.

For form 4 rules with k=1 (single nonterminal, no push): This is a unit rule.
We can handle it by inlining, but for simplicity we keep it (it satisfies IsNF as
flag push with `none` — actually no, it doesn't. Let me handle it properly.)

Actually, looking at the IsNF definition, a rule with a single nonterminal (no push,
no consume) doesn't fit any of the four forms. So we need to handle unit rules too.
For simplicity, we inline: A → B is replaced by copying all of B's rules to A.

But this gets complex. Instead, let me use a different approach:
Single nonterminal rules (A → B, no consume, no push) can be encoded as
A → B[dummy_flag·], where dummy_flag is a fresh flag, plus B[dummy_flag·] → B.
But this is unnecessarily complex.

For the normal form theorem, the simplest approach is: the combination of
FlagsSeparated + TerminalsIsolated + NoEpsilon' + binarization gives us rules where:
- Terminal rules: A → a (already NF)
- Flag pop: A[f·] → B (already NF)
- Flag push: A → B[f·] (already NF)
- Multi-nonterminal (no flags): A → B₁ ... Bₖ, k ≥ 2
  → Binarize to A → B₁ C₁, C₁ → B₂ C₂, ..., Cₖ₋₂ → Bₖ₋₁ Bₖ
- Single nonterminal (no flags): A → B, k = 1
  → This is a unit rule. Need to eliminate it or encode it.

For the unit rule case: since NoEpsilon' ensures k ≥ 1, and TerminalsIsolated means
RHS is either a single terminal or all nonterminals, we can have k = 1 nonterminal rules.
These are unit rules and should be eliminated for proper normal form.

However, the IsNF definition allows flag push rules of the form A → B[f·].
A unit rule A → B (no push) doesn't fit any IsNF form.

The standard approach is to eliminate unit rules. But this is another complex step.
For simplicity, let me add it as part of the binarization step:
A → B becomes A → B · Bnew where Bnew → ε... but we can't have ε.

Alternative: just accept unit rules as an additional NF form. But the IsNF definition
doesn't include them. Let me consider handling this differently.

Actually, in the Aho normal form for indexed grammars, unit rules (without flag operations)
are typically eliminated as part of the normalization. Let me handle this by showing
that after flag separation, if we have TerminalsIsolated and FlagsSeparated, any
single-nonterminal-no-push rule is a flag pop rule (has consume). This is because
FlagsSeparated says:
- If consume is Some f: RHS is single nonterminal no push ✓ (flag pop)
- If consume is None: either all nonterminals have no push, or single with push, or terminal

So A → B (consume = none, single nonterminal, no push) falls under the first option
of the consume=none case: "all nonterminals have no push". And since the RHS has
exactly one nonterminal, this is fine. But it's not in NF form.

For the binarization step, I need to handle this case. One approach:
introduce a fresh flag `f_unit` and replace A → B with A → B[f_unit·], B[f_unit·] → B.
This turns the unit rule into a flag push + flag pop pair.

Let me use this approach. The new flag type is `Option g.flag`:
- `some f` for original flags
- `none` for the fresh unit-elimination flag

Actually, this is getting quite complex. Let me take a different approach entirely.

Instead of this complex multi-step decomposition, let me directly show that
an indexed grammar with TerminalsIsolated + FlagsSeparated + NoEpsilon' + StartNotOnRhs'
can be converted to normal form by binarizing long rules and eliminating unit rules.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar

section Binarization

variable (g : IndexedGrammar T)

-- The binarization uses fresh nonterminals of the form Sum.inr (i, j)
-- for rule i, position j in the chain.
-- It also uses an optional fresh flag to eliminate unit rules.

/-- Lift an RHS symbol to the binarized grammar's nonterminal type. -/
def binLiftRhsSym : IRhsSymbol T g.nt g.flag →
    IRhsSymbol T (g.nt ⊕ (Nat × Nat)) (Option g.flag)
  | .terminal t => .terminal t
  | .nonterminal n f => .nonterminal (Sum.inl n) (f.map some)

/-- Binarize a single rule at index i. Given a rule:
  - A → a : already NF, keep it
  - A[f·] → B : flag pop, already NF, keep it
  - A → B[f·] : flag push, already NF, keep it
  - A → B : unit rule, replace with A → B[none·], add B[none·] → B
  - A → B₁ B₂ ... Bₖ (k ≥ 2, no pushes, no consume):
    A → B₁ C₁, C₁ → B₂ C₂, ..., Cₖ₋₂ → Bₖ₋₁ Bₖ -/
noncomputable def binSingleRule (i : Nat) (r : IRule T g.nt g.flag) :
    List (IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag)) :=
  -- Terminal rule
  if r.rhs.any (fun s => match s with | .terminal _ => true | _ => false) && r.rhs.length == 1 then
    [⟨Sum.inl r.lhs, r.consume.map some, r.rhs.map g.binLiftRhsSym⟩]
  -- Flag pop: A[f·] → B (consume = some f, single nonterminal)
  else if h : r.consume.isSome ∧ r.rhs.length = 1 then
    [⟨Sum.inl r.lhs, r.consume.map some, r.rhs.map g.binLiftRhsSym⟩]
  -- Flag push: A → B[f·] (consume = none, single nonterminal with push)
  else if r.consume.isNone ∧ r.rhs.length = 1 ∧
          r.rhs.any (fun s => match s with | .nonterminal _ (some _) => true | _ => false) then
    [⟨Sum.inl r.lhs, none, r.rhs.map g.binLiftRhsSym⟩]
  -- Unit rule: A → B (consume = none, single nonterminal, no push)
  else if r.consume.isNone ∧ r.rhs.length = 1 then
    match r.rhs.head? with
    | some (.nonterminal B none) =>
      -- A → B[none·] and B[none·] → B
      [ ⟨Sum.inl r.lhs, none, [.nonterminal (Sum.inl B) (some none)]⟩,
        ⟨Sum.inl B, some none, [.nonterminal (Sum.inl B) none]⟩ ]
    | _ => [⟨Sum.inl r.lhs, r.consume.map some, r.rhs.map g.binLiftRhsSym⟩]
  -- Multi-nonterminal: A → B₁ ... Bₖ (k ≥ 2, binarize)
  else
    let rhsList := r.rhs.map g.binLiftRhsSym
    match rhsList with
    | [] => []
    | [x] => [⟨Sum.inl r.lhs, r.consume.map some, [x]⟩]
    | x :: y :: rest =>
      let rec binarizeAux (lhs : g.nt ⊕ (Nat × Nat)) (syms : List (IRhsSymbol T (g.nt ⊕ (Nat × Nat)) (Option g.flag))) (idx : Nat) :
          List (IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag)) :=
        match syms with
        | [] => []
        | [s₁, s₂] => [⟨lhs, none, [s₁, s₂]⟩]
        | s :: rest =>
          let freshNt := Sum.inr (i, idx)
          ⟨lhs, none, [s, .nonterminal freshNt none]⟩ :: binarizeAux freshNt rest (idx + 1)
      binarizeAux (Sum.inl r.lhs) (x :: y :: rest) 0

/-- The binarized grammar. -/
noncomputable def binarize : IndexedGrammar T where
  nt := g.nt ⊕ (Nat × Nat)
  flag := Option g.flag  -- none is the fresh unit-elimination flag
  initial := Sum.inl g.initial
  rules := ((g.rules.zipIdx).map fun ⟨r, i⟩ => g.binSingleRule i r).flatten

theorem binarize_generates_iff (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs') :
    ∀ w : List T, w ≠ [] → ((g.binarize).Generates w ↔ g.Generates w) := by
  sorry

theorem binarize_isNormalForm (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs') :
    ∃ _ : DecidableEq (g.binarize).nt, (g.binarize).IsNormalForm := by
  sorry

theorem exists_normalForm_from_separated' (g : IndexedGrammar T)
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs') :
    ∃ g' : IndexedGrammar T,
      (∃ _ : DecidableEq g'.nt, g'.IsNormalForm) ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) :=
  ⟨g.binarize, g.binarize_isNormalForm hne hti hfs hfresh,
   g.binarize_generates_iff hne hti hfs hfresh⟩

end Binarization

end IndexedGrammar
