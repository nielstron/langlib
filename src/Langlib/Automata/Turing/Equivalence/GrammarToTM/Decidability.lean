import Mathlib
import Langlib.Grammars.Unrestricted.Toolbox

/-! # Decidability of Grammar Operations

This file shows that the basic operations of unrestricted grammars are
decidable / computable, which is needed to express grammar membership
as a search procedure.

## Main results

- `applyRuleAt` — computable function that applies a rule at a position
- `applyRuleSeq` — computable function that applies a sequence of rules
- `extractTerminals` — extract the terminal word from a terminal sentential form
- `grammarTest` — the decidable test for grammar membership
- `grammarTest_sound` / `grammarTest_complete` — correctness of the test
-/

open Relation

variable {T : Type} [DecidableEq T]

/-! ### Computable rule application -/

/-- Given a grammar, a sentential form, a rule index, and a position,
attempt to apply the rule at that position. Returns `none` if the rule
doesn't match at that position. -/
def applyRuleAt {N : Type} [DecidableEq N]
    (r : grule T N)
    (sf : List (symbol T N))
    (pos : ℕ) : Option (List (symbol T N)) :=
  let pattern := r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R
  let pfx := sf.take pos
  let rest := sf.drop pos
  if rest.take pattern.length == pattern then
    some (pfx ++ r.output_string ++ rest.drop pattern.length)
  else
    none

/-
`applyRuleAt` is correct: if it returns `some sf'`, then `sf` transforms
to `sf'` via the given rule.
-/
theorem applyRuleAt_correct {N : Type} [DecidableEq N]
    (r : grule T N) (sf sf' : List (symbol T N)) (pos : ℕ)
    (h : applyRuleAt r sf pos = some sf') :
    ∃ u v, sf = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v ∧
           sf' = u ++ r.output_string ++ v := by
  unfold applyRuleAt at h;
  have := List.take_append_drop ( r.input_L.length + ( r.input_R.length + 1 ) ) ( List.drop pos sf ) ; aesop;

/-- Apply a sequence of (rule_index, position) pairs to a sentential form,
starting from a given initial form. Returns `none` if any step fails.

This is the core "derivation simulator": given a sequence of instructions
`[(r₀, p₀), (r₁, p₁), ...]`, it:
1. Starts with `init`
2. Applies rule `rules[rᵢ]` at position `pᵢ`
3. Returns the final sentential form (or `none` if any step fails) -/
def applyRuleSeq {N : Type} [DecidableEq N]
    (rules : List (grule T N))
    (init : List (symbol T N))
    (seq : List (ℕ × ℕ)) : Option (List (symbol T N)) :=
  seq.foldl
    (fun acc step =>
      match acc with
      | none => none
      | some sf =>
        match rules[step.1]? with
        | none => none
        | some r => applyRuleAt r sf step.2)
    (some init)

/-
If `applyRuleSeq` returns `some sf'`, then the grammar derives `sf'`
from `init`.
-/
theorem applyRuleSeq_derives (g : grammar T) [DecidableEq g.nt]
    (init sf' : List (symbol T g.nt))
    (seq : List (ℕ × ℕ))
    (h : applyRuleSeq g.rules init seq = some sf') :
    grammar_derives g init sf' := by
  induction' seq with seq_data seq_tails generalizing init sf';
  · cases h ; exact grammar_deri_self;
  · unfold applyRuleSeq at h;
    rcases h' : g.rules[seq_data.1]? with ( _ | r ) <;> simp_all +decide [ List.foldl ];
    · contrapose! h;
      rw [ show List.foldl _ _ _ = none from _ ];
      · exact?;
      · exact?;
    · obtain ⟨sf_mid, h_mid⟩ : ∃ sf_mid, applyRuleAt r init seq_data.2 = some sf_mid ∧ grammar_derives g init sf_mid := by
        by_cases h'' : applyRuleAt r init seq_data.2 = none;
        · rw [ show List.foldl _ _ _ = none from _ ] at h ; aesop;
          rw [ h'' ];
          exact?;
        · obtain ⟨sf_mid, h_mid⟩ : ∃ sf_mid, applyRuleAt r init seq_data.2 = some sf_mid := by
            exact Option.ne_none_iff_exists'.mp h'';
          exact ⟨ sf_mid, h_mid, Relation.ReflTransGen.single <| by obtain ⟨ u, v, hu, hv ⟩ := applyRuleAt_correct r init sf_mid seq_data.2 h_mid; exact ⟨ r, by
            exact?, u, v, hu, hv ⟩ ⟩;
      convert Relation.ReflTransGen.trans h_mid.2 ( ‹∀ ( init sf' : List ( symbol T g.nt ) ), applyRuleSeq g.rules init seq_tails = some sf' → grammar_derives g init sf'› _ _ _ ) using 1;
      convert h using 1;
      exact h_mid.1.symm ▸ rfl

/-! ### Terminal checking -/

/-- Extract the terminal word from a sentential form, if all symbols
are terminals. Returns `none` if any nonterminal is present. -/
def extractTerminals {N : Type} (sf : List (symbol T N)) : Option (List T) :=
  sf.foldr
    (fun s acc =>
      match s, acc with
      | symbol.terminal t, some ts => some (t :: ts)
      | _, _ => none)
    (some [])

/-
`extractTerminals` returns `some w` iff `sf = w.map symbol.terminal`.
-/
theorem extractTerminals_eq_map_iff {N : Type}
    (sf : List (symbol T N)) (w : List T) :
    extractTerminals sf = some w ↔ sf = w.map symbol.terminal := by
  constructor <;> intro h;
  · induction' sf with s sf ih generalizing w;
    · cases h ; trivial;
    · unfold extractTerminals at h;
      cases s <;> aesop;
  · rw [ h, extractTerminals ];
    clear h;
    induction w <;> simp +decide [ * ]

/-! ### The Grammar Test Function

The key function: given a derivation sequence (encoded as a `List (ℕ × ℕ)`)
and an input word `w`, check whether the derivation produces `w`. -/

/-- The grammar membership test.

Given a grammar `g`, a derivation sequence `seq`, and a target word `w`:
1. Apply the rule sequence starting from `[nonterminal g.initial]`
2. Check if the result is exactly `w.map symbol.terminal`

Returns `true` iff the derivation sequence witnesses `w ∈ grammar_language g`. -/
def grammarTest (g : grammar T) [DecidableEq g.nt]
    (seq : List (ℕ × ℕ)) (w : List T) : Bool :=
  match applyRuleSeq g.rules [symbol.nonterminal g.initial] seq with
  | none => false
  | some sf => extractTerminals sf == some w

/-
Soundness of `grammarTest`: if the test passes, then `w` is in the
grammar's language.
-/
theorem grammarTest_sound (g : grammar T) [DecidableEq g.nt]
    (seq : List (ℕ × ℕ)) (w : List T)
    (h : grammarTest g seq w = true) :
    w ∈ grammar_language g := by
  unfold grammarTest at h;
  obtain ⟨sf, hsf⟩ : ∃ sf, applyRuleSeq g.rules [symbol.nonterminal g.initial] seq = some sf ∧ extractTerminals sf = some w := by
    cases h' : applyRuleSeq g.rules [ symbol.nonterminal g.initial ] seq <;> aesop;
  have := applyRuleSeq_derives g [ symbol.nonterminal g.initial ] sf seq hsf.1;
  exact this.trans ( by rw [ extractTerminals_eq_map_iff ] at hsf; aesop )

/-
Completeness of `grammarTest`: if `w` is in the grammar's language,
then some derivation sequence witnesses it.
-/
theorem grammarTest_complete (g : grammar T) [DecidableEq g.nt]
    (w : List T) (hw : w ∈ grammar_language g) :
    ∃ seq : List (ℕ × ℕ), grammarTest g seq w = true := by
  obtain ⟨seq, hseq⟩ : ∃ seq : List (ℕ × ℕ), ∃ sf : List (symbol T g.nt), applyRuleSeq g.rules [symbol.nonterminal g.initial] seq = some sf ∧ sf = w.map symbol.terminal := by
    have h_deriv : ∀ {v w : List (symbol T g.nt)}, grammar_derives g v w → ∃ seq : List (ℕ × ℕ), ∃ sf : List (symbol T g.nt), applyRuleSeq g.rules v seq = some sf ∧ sf = w := by
      intro v w hvw;
      induction hvw;
      · exact ⟨ [ ], v, rfl, rfl ⟩;
      · rename_i h₁ h₂ h₃;
        obtain ⟨ r, hr₁, u, v, rfl, rfl ⟩ := h₂;
        obtain ⟨ seq, sf, hseq, hsf ⟩ := h₃;
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hr₁;
        use seq ++ [(i.val, u.length)];
        unfold applyRuleSeq at *;
        simp +decide [ hseq, hsf];
        unfold applyRuleAt; simp +decide;
        simp +decide [ ← hi, List.take_append, List.drop_append ];
    exact h_deriv hw;
  unfold grammarTest;
  obtain ⟨sf, hsf₁, hsf₂⟩ := hseq
  use seq
  simp [hsf₁, hsf₂];
  exact?