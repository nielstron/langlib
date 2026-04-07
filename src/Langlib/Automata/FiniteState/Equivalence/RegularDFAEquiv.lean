/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Automata.FiniteState.Definition
import Langlib.Classes.Regular.Definition

open Relation Classical

noncomputable section

variable {T : Type}
/-! # Regular Language Inclusions

This file relates right-regular grammars (Type-3) to:
1. **Mathlib's `Language.IsRegular`** — proved equivalent via DFA ↔ RG conversions.

## Main results

- `is_RG_iff_isRegular` — The Mathlib regular languages are equivalent to the right-regular languages.

## References

* Hopcroft, Motwani, Ullman. *Introduction to Automata Theory, Languages, and Computation*,
  3rd ed. Section 3.3.
-/

-- ============================================================================
-- Part 1: RG → IsRegular (via NFA with finite states)
-- ============================================================================


/-- All nonterminals mentioned in a single RG rule. -/
def RG_rule.nonterminals {N : Type} : RG_rule T N → List N
  | .cons A _ B => [A, B]
  | .single A _ => [A]
  | .epsilon A  => [A]

/-- Finset of all nonterminals appearing in a grammar (including the initial symbol). -/
def RG_grammar.nonterminalFinset (g : RG_grammar T) : Finset g.nt :=
  (g.initial :: (g.rules.flatMap RG_rule.nonterminals)).toFinset

lemma RG_grammar.initial_mem_nonterminalFinset (g : RG_grammar T) :
    g.initial ∈ g.nonterminalFinset := by
  simp [nonterminalFinset]

lemma RG_grammar.rule_nt_mem (g : RG_grammar T) {r : RG_rule T g.nt} (hr : r ∈ g.rules)
    {n : g.nt} (hn : n ∈ r.nonterminals) : n ∈ g.nonterminalFinset := by
  simp only [nonterminalFinset, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    List.mem_flatMap]
  right; exact ⟨r, hr, hn⟩

/-- Finite nonterminal subtype: only those nonterminals that appear in the grammar. -/
abbrev RG_grammar.FinNT (g : RG_grammar T) := { x : g.nt // x ∈ g.nonterminalFinset }

/-- NFA with finite states constructed from a right-regular grammar. -/
def NFA_of_RG (g : RG_grammar T) : NFA T (Option g.FinNT) where
  step
    | none, _ => ∅
    | some ⟨A, _⟩, a =>
      { s | ∃ B, ∃ hB : RG_rule.cons A a B ∈ g.rules,
            s = some ⟨B, g.rule_nt_mem hB (by simp [RG_rule.nonterminals])⟩ } ∪
      (if RG_rule.single A a ∈ g.rules then {none} else ∅)
  start := {some ⟨g.initial, g.initial_mem_nonterminalFinset⟩}
  accept := {none} ∪
    { s | ∃ A, ∃ hA : A ∈ g.nonterminalFinset,
          s = some ⟨A, hA⟩ ∧ RG_rule.epsilon A ∈ g.rules }

/-
PROBLEM
Forward simulation: if `some ⟨B, hB⟩` is reachable from `{some ⟨A, hA⟩}` after reading `w`,
    then the grammar derives `[nt A] →* map terminal w ++ [nt B]`.

PROVIDED SOLUTION
By induction on w using List.reverseRecOn (induction on w by appending elements).

Base case (w = []): evalFrom {some ⟨A, hA⟩} [] = {some ⟨A, hA⟩} by NFA.evalFrom_nil. So some ⟨B, hB⟩ ∈ {some ⟨A, hA⟩} means ⟨B, hB⟩ = ⟨A, hA⟩, i.e., B = A. The derivation is RG_deri_self since map terminal [] ++ [nt A] = [nt A].

Inductive case (w = w' ++ [a]): evalFrom S (w' ++ [a]) = stepSet (evalFrom S w') a by NFA.evalFrom_append_singleton. So some ⟨B, hB⟩ ∈ stepSet (evalFrom {some ⟨A, hA⟩} w') a. By NFA.mem_stepSet, there exists t ∈ evalFrom {some ⟨A, hA⟩} w' such that some ⟨B, hB⟩ ∈ step t a. Since step none _ = ∅, t ≠ none, so t = some ⟨C, hC⟩ for some C. Then some ⟨B, hB⟩ ∈ step (some ⟨C, hC⟩) a. By definition of NFA_of_RG step, this means cons C a B ∈ g.rules (from the first part of the union; the second part only produces none).

By IH, RG_derives g [nt A] (map terminal w' ++ [nt C]). Then apply the cons C a B rule (with u = map terminal w', v = []):
  map terminal w' ++ [nt C] → map terminal w' ++ [terminal a, nt B] = map terminal (w' ++ [a]) ++ [nt B]

So RG_derives g [nt A] (map terminal (w' ++ [a]) ++ [nt B]).
-/
lemma NFA_of_RG_some_forward {g : RG_grammar T}
    (A : g.nt) (hA : A ∈ g.nonterminalFinset)
    (B : g.nt) (hB : B ∈ g.nonterminalFinset)
    (w : List T)
    (h : some ⟨B, hB⟩ ∈ (NFA_of_RG g).evalFrom {some ⟨A, hA⟩} w) :
    RG_derives g [symbol.nonterminal A] (List.map symbol.terminal w ++ [symbol.nonterminal B]) := by
      revert h;
      induction' w using List.reverseRecOn with w a ih generalizing A B;
      · simp +decide [ NFA.evalFrom ];
        rintro rfl; exact RG_deri_self _;
      · simp +decide [ NFA.evalFrom_append ];
        intro h
        obtain ⟨C, hC⟩ : ∃ C : g.FinNT, some ⟨C, C.2⟩ ∈ (NFA_of_RG g).evalFrom {some ⟨A, hA⟩} w ∧ some ⟨B, hB⟩ ∈ (NFA_of_RG g).step (some ⟨C, C.2⟩) a := by
          simp_all +decide [ NFA.stepSet ];
          rcases h with ⟨ i, hi, hi' ⟩ ; rcases i with ( _ | ⟨ C, hC ⟩ ) <;> tauto;
        obtain ⟨hC₁, hC₂⟩ := hC;
        convert RG_deri_of_deri_tran ( ih A hA C C.2 hC₁ ) _ using 1;
        use RG_rule.cons C.val a B;
        unfold NFA_of_RG at hC₂; aesop;

/-
PROBLEM
Forward simulation for `none`: if `none` is reachable from `{some ⟨A, hA⟩}` after reading `w`,
    then `w = w' ++ [a]` and there exists C with cons rules from A to C reading w',
    and single C a ∈ rules. Hence [nt A] →* map terminal w.

PROVIDED SOLUTION
Since step none _ = ∅, none cannot propagate through further steps. So none ∈ evalFrom {some A} w means w = w' ++ [a] for some w' and a, and none ∈ stepSet (evalFrom {some A} w') a (by NFA.evalFrom_append_singleton).

By NFA.mem_stepSet, ∃ t ∈ evalFrom {some A} w' such that none ∈ step t a. Since step none = ∅, t = some ⟨C, hC⟩. And none ∈ step (some C) a means single C a ∈ rules (from the if-then-else in the NFA definition).

By NFA_of_RG_some_forward, RG_derives g [nt A] (map terminal w' ++ [nt C]). Then apply single C a rule:
  map terminal w' ++ [nt C] → map terminal w' ++ [terminal a] = map terminal (w' ++ [a]) = map terminal w.

Base case check: if w = [], evalFrom {some A} [] = {some A} and none ∉ {some A}, contradiction. So w is nonempty, which is needed for the w = w' ++ [a] decomposition.

For w nonempty, use List.exists_append_of_ne_nil or List.append_last to decompose w = w' ++ [a].

Actually, we need to handle the induction more carefully. Let me use induction on w using List.reverseRecOn:
- w = []: evalFrom = {some A}, none ∉ {some A}, contradiction.
- w = w' ++ [a]: as above.
-/
lemma NFA_of_RG_none_forward {g : RG_grammar T}
    (A : g.nt) (hA : A ∈ g.nonterminalFinset)
    (w : List T)
    (h : none ∈ (NFA_of_RG g).evalFrom {some ⟨A, hA⟩} w) :
    RG_derives g [symbol.nonterminal A] (List.map symbol.terminal w) := by
      induction' w using List.reverseRecOn with w' a ih generalizing A hA;
      · simp_all +decide [ NFA.evalFrom ];
      · obtain ⟨C, hC⟩ : ∃ C : g.nt, ∃ hC : C ∈ g.nonterminalFinset, some ⟨C, hC⟩ ∈ (NFA_of_RG g).evalFrom {some ⟨A, hA⟩} w' ∧ none ∈ (NFA_of_RG g).step (some ⟨C, hC⟩) a := by
          have h_step : none ∈ (NFA_of_RG g).stepSet ( (NFA_of_RG g).evalFrom {some ⟨A, hA⟩} w' ) a := by
            convert h using 1;
            simp +decide [ NFA.evalFrom ];
          rw [ NFA.stepSet ] at h_step;
          simp +zetaDelta at *;
          rcases h_step with ⟨ i, hi, hi' ⟩ ; rcases i with ( _ | ⟨ C, hC ⟩ ) <;> tauto;
        obtain ⟨ hC₁, hC₂, hC₃ ⟩ := hC;
        have h_single : RG_rule.single C a ∈ g.rules := by
          unfold NFA_of_RG at hC₃; aesop;
        have h_derive : RG_derives g [symbol.nonterminal A] (List.map symbol.terminal w' ++ [symbol.nonterminal C]) := by
          exact?;
        convert h_derive.trans _ using 1;
        convert ReflTransGen.single _ using 1;
        use RG_rule.single C a, h_single, List.map symbol.terminal w', [] ; aesop

/-
PROBLEM
In an RG grammar, any sentential form reachable from `[nt A]` is either:
    - `map terminal p ++ [nt C]` for some p and C, or
    - `map terminal p` for some p.

PROVIDED SOLUTION
By induction on the derivation h.

Base case (refl): s = [nt A]. Left disjunct with p = [], C = A: [nt A] = map terminal [] ++ [nt A].

Inductive case: RG_derives g [nt A] s' and RG_transforms g s' s. By IH:
- Case 1: s' = map terminal p ++ [nt C]. The transform rewrites some nonterminal in s'. The only nonterminal in s' is C at the end, so the rule has LHS = C, u = map terminal p, v = []. The rule applied is one of:
  - cons C a D: s = map terminal p ++ [terminal a, nt D] = map terminal (p ++ [a]) ++ [nt D]. Left disjunct.
  - single C a: s = map terminal p ++ [terminal a] = map terminal (p ++ [a]). Right disjunct.
  - epsilon C: s = map terminal p. Right disjunct.
- Case 2: s' = map terminal p. s' is all terminals, so no nonterminal to rewrite. RG_transforms requires a nonterminal in s', contradiction.

For the inductive case, the key is showing that when s' = terminals ++ [nt C], the only valid decomposition u ++ [nt r.lhs] ++ v of s' must have u = terminals, r.lhs = C, v = [].
-/
lemma RG_derives_form {g : RG_grammar T} {A : g.nt}
    {s : List (symbol T g.nt)}
    (h : RG_derives g [symbol.nonterminal A] s) :
    (∃ p C, s = List.map symbol.terminal p ++ [symbol.nonterminal C]) ∨
    (∃ p, s = List.map symbol.terminal p) := by
      induction h;
      · exact Or.inl ⟨ [ ], A, rfl ⟩;
      · rename_i h₁ h₂ h₃;
        rcases h₃ with ( ⟨ p, C, rfl ⟩ | ⟨ p, rfl ⟩ );
        · rcases h₂ with ⟨ r, hr, u, v, hu, hv ⟩;
          rcases r with ( _ | _ | _ ) <;> simp_all +decide [ List.append_assoc ];
          · rw [ List.append_eq_append_iff ] at hu;
            rcases hu with ( ⟨ as, rfl, hu ⟩ | ⟨ bs, hu, hv ⟩ ) <;> simp_all +decide [ List.append_assoc ];
            · rcases as with ( _ | ⟨ _, _ | as ⟩ ) <;> simp_all +decide [ List.append_assoc ];
              exact Or.inl ⟨ p ++ [ ‹_› ], ‹_›, by simp +decide [ RG_rule.output ] ⟩;
            · rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.map ];
              · exact Or.inl ⟨ p ++ [ ‹_› ], ‹_›, by aesop ⟩;
              · replace hu := congr_arg List.toFinset hu; rw [ Finset.ext_iff ] at hu; specialize hu b; aesop;
          · rw [ List.append_eq_append_iff ] at hu;
            rcases hu with ( ⟨ as, rfl, hu ⟩ | ⟨ bs, hu, hv ⟩ ) <;> simp_all +decide [ List.append_assoc ];
            · rcases as with ( _ | ⟨ _, _ | as ⟩ ) <;> simp_all +decide [ List.append_assoc ];
              exact Or.inr ⟨ p ++ [ ‹_› ], by simp +decide [ RG_rule.output ] ⟩;
            · rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.map ];
              · exact Or.inr ⟨ p ++ [ ‹_› ], by aesop ⟩;
              · replace hu := congr_arg List.toFinset hu; rw [ Finset.ext_iff ] at hu; specialize hu b; aesop;
          · rw [ List.append_eq_append_iff ] at hu;
            rcases hu with ( ⟨ as, rfl, hu ⟩ | ⟨ bs, hu, hv ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
            · rcases as with ( _ | ⟨ _, _ | as ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
              exact Or.inr ⟨ p, by simp +decide [ RG_rule.output ] ⟩;
            · rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
              · exact Or.inr ⟨ p, by aesop ⟩;
              · cases b <;> simp_all +decide [ List.map ];
                replace hu := congr_arg List.toFinset hu; rw [ Finset.ext_iff ] at hu; specialize hu ( symbol.nonterminal ‹_› ) ; aesop;
        · cases h₂;
          rename_i r hr;
          rcases hr with ⟨ hr₁, u, v, hu, hv ⟩;
          replace hu := congr_arg List.toFinset hu; rw [ Finset.ext_iff ] at hu; specialize hu ( symbol.nonterminal r.lhs ) ; aesop;

/-
An RG transform applied to a sentential form `map terminal p ++ [nt C]`
    must rewrite `C`. This characterizes the three possible outcomes.
-/
lemma RG_transforms_of_terminal_nt {g : RG_grammar T} {p : List T} {C : g.nt}
    {s : List (symbol T g.nt)}
    (h : RG_transforms g (List.map symbol.terminal p ++ [symbol.nonterminal C]) s) :
    (∃ a D, RG_rule.cons C a D ∈ g.rules ∧
        s = List.map symbol.terminal p ++ [symbol.terminal a, symbol.nonterminal D]) ∨
    (∃ a, RG_rule.single C a ∈ g.rules ∧
        s = List.map symbol.terminal p ++ [symbol.terminal a]) ∨
    (RG_rule.epsilon C ∈ g.rules ∧ s = List.map symbol.terminal p) := by
      unfold RG_transforms at h ; rcases h with ⟨ r, hr, u, v, huv ⟩ ; simp_all +decide [ List.append_eq_append_iff ] ;
      rcases huv with ⟨ huv | huv, rfl ⟩;
      · rcases huv with ⟨ as, rfl, h ⟩ ; rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ] ;
        rcases r with ( _ | _ | _ ) <;> aesop;
      · rcases huv with ⟨ bs, h₁, h₂ ⟩ ; rcases bs with ( _ | ⟨ a, bs ⟩ ) <;> simp_all +decide [ List.map ] ;
        · rcases r with ( _ | _ | _ ) <;> aesop;
        · replace h₁ := congr_arg List.toFinset h₁ ; rw [ Finset.ext_iff ] at h₁ ; specialize h₁ a ; aesop;

/-
In an RG grammar, if `[nt A] →* map terminal w ++ [nt B]` with w nonempty,
    then there exists C such that `[nt A] →* map terminal (w.dropLast) ++ [nt C]`
    and `cons C (w.getLast ...) B ∈ rules`.
-/
lemma RG_derives_snoc {g : RG_grammar T} {A B : g.nt}
    {w : List T} (hw : w ≠ [])
    (h : RG_derives g [symbol.nonterminal A]
      (List.map symbol.terminal w ++ [symbol.nonterminal B])) :
    ∃ C, RG_derives g [symbol.nonterminal A]
        (List.map symbol.terminal w.dropLast ++ [symbol.nonterminal C]) ∧
      RG_rule.cons C (w.getLast hw) B ∈ g.rules := by
        revert h w hw;
        -- By definition of `RG_derives`, we can split the derivation into the last step and the rest.
        intro w hw h
        induction' w using List.reverseRecOn with w ih generalizing A B;
        · contradiction;
        · -- By definition of RG_derives, there exists a sequence of transformations from [symbol.nonterminal A] to [symbol.terminal w ++ [symbol.nonterminal B]].
          obtain ⟨s', hs', hs⟩ : ∃ s', RG_derives g [symbol.nonterminal A] s' ∧ RG_transforms g s' (List.map symbol.terminal (w ++ [ih]) ++ [symbol.nonterminal B]) := by
            have h_step : ∀ {u v : List (symbol T g.nt)}, RG_derives g u v → u ≠ v → ∃ s', RG_derives g u s' ∧ RG_transforms g s' v := by
              intros u v huv huv_ne;
              induction huv <;> aesop;
            cases w <;> aesop;
          rcases RG_derives_form hs' with ( ⟨ p, C, rfl ⟩ | ⟨ p, rfl ⟩ ) <;> simp_all +decide [ List.map_append ];
          · rcases RG_transforms_of_terminal_nt hs with ( ⟨ a, D, h₁, h₂ ⟩ | ⟨ a, h₁, h₂ ⟩ | h₁ ) <;> simp_all +decide [ List.map_append ];
            · replace h₂ := congr_arg List.reverse h₂ ; simp_all +decide [ List.reverse_append ];
              grind;
            · replace h₂ := congr_arg List.reverse h₂ ; simp_all +decide [ List.reverse_append ];
            · replace h₁ := congr_arg List.reverse h₁.2 ; simp_all +decide [ List.reverse_append ];
              replace h₁ := congr_arg List.toFinset h₁ ; rw [ Finset.ext_iff ] at h₁ ; specialize h₁ ( symbol.nonterminal B ) ; aesop;
          · rcases hs with ⟨ r, hr, u, v, hu, hv ⟩;
            replace hu := congr_arg List.toFinset hu; simp_all +decide [ Finset.ext_iff ] ;
            specialize hu ( symbol.nonterminal r.lhs ) ; aesop

/-
Backward simulation: if the grammar derives `[nt A] →* map terminal w ++ [nt B]`,
    then `some ⟨B, hB⟩` is reachable from `{some ⟨A, hA⟩}` after reading `w`.
-/
lemma NFA_of_RG_some_backward {g : RG_grammar T}
    (A : g.nt) (hA : A ∈ g.nonterminalFinset)
    (B : g.nt) (hB : B ∈ g.nonterminalFinset)
    (w : List T)
    (h : RG_derives g [symbol.nonterminal A] (List.map symbol.terminal w ++ [symbol.nonterminal B])) :
    some ⟨B, hB⟩ ∈ (NFA_of_RG g).evalFrom {some ⟨A, hA⟩} w := by
      induction' w using List.reverseRecOn with w' a ih generalizing A B;
      · cases h ; aesop;
        rename_i w hw₁ hw₂;
        rcases hw₂ with ⟨ r, hr, u, v, hw₁, hw₂ ⟩;
        rcases u with ( _ | ⟨ _, _ | u ⟩ ) <;> rcases v with ( _ | ⟨ _, _ | v ⟩ ) <;> simp_all +decide [ List.map ];
        · rcases r with ( _ | _ | _ ) <;> cases hw₂;
        · rename_i k hk;
          have := RG_derives_form hk;
          rcases this with ( ⟨ p, C, h ⟩ | ⟨ p, h ⟩ ) <;> rcases p with ( _ | ⟨ _, _ | p ⟩ ) <;> simp_all +decide [ List.map ];
        · rcases r with ( _ | _ | _ ) <;> simp_all +decide [ RG_rule.output ];
        · cases r <;> simp_all +decide [ RG_rule.output ];
          rename_i k hk;
          have := hk;
          have := RG_derives_form this; simp_all +decide [ RG_rule.output ] ;
          rcases this with ( ⟨ p, C, h ⟩ | ⟨ p, h ⟩ ) <;> rcases p with ( _ | ⟨ _, _ | p ⟩ ) <;> simp_all +decide [ List.map ];
      · have := RG_derives_snoc ( show w' ++ [ a ] ≠ [ ] from by aesop ) h; simp_all +decide [ List.map_append ] ;
        obtain ⟨ C, hC₁, hC₂ ⟩ := this; specialize ih A hA C ( g.rule_nt_mem hC₂ ( by simp +decide [ RG_rule.nonterminals ] ) ) hC₁; simp_all +decide [ NFA.stepSet ] ;
        unfold NFA_of_RG; aesop;

/-
If `[nt A] →* map terminal w` (all terminals), the derivation ends with
    either a `single` or `epsilon` rule from some intermediate nonterminal.
-/
lemma RG_generates_last_step {g : RG_grammar T} {A : g.nt} {w : List T}
    (h : RG_derives g [symbol.nonterminal A] (List.map symbol.terminal w)) :
    (∃ C p, RG_derives g [symbol.nonterminal A]
        (List.map symbol.terminal p ++ [symbol.nonterminal C]) ∧
      RG_rule.epsilon C ∈ g.rules ∧ w = p) ∨
    (∃ C p a, RG_derives g [symbol.nonterminal A]
        (List.map symbol.terminal p ++ [symbol.nonterminal C]) ∧
      RG_rule.single C a ∈ g.rules ∧ w = p ++ [a]) := by
        obtain ⟨s', hs'⟩ : ∃ s', RG_derives g [symbol.nonterminal A] s' ∧ RG_transforms g s' (List.map symbol.terminal w) := by
          contrapose! h;
          induction' w with w ih;
          · contrapose! h;
            have := h.cases_tail; aesop;
          · contrapose! h;
            cases h ; tauto;
        rcases RG_derives_form hs'.left with ( ⟨ p, C, rfl ⟩ | ⟨ p, rfl ⟩ );
        · rcases RG_transforms_of_terminal_nt hs'.2 with ( ⟨ a, D, hD, h ⟩ | ⟨ a, hD, h ⟩ | h ) <;> simp_all +decide [ List.map ];
          · replace h := congr_arg List.toFinset h ; rw [ Finset.ext_iff ] at h ; specialize h ( symbol.nonterminal D ) ; aesop;
          · refine Or.inr ⟨ C, p, hs'.1, a, hD, ?_ ⟩;
            exact List.map_injective_iff.mpr ( show Function.Injective symbol.terminal from fun x y hxy => by cases hxy; rfl ) <| by simpa using h;
          · exact Or.inl ⟨ C, hs'.1, h.1 ⟩;
        · rcases hs'.2 with ⟨ r, hr, ⟨ u, v, hu, hv ⟩ ⟩ ; simp_all +decide [ List.map_eq_map_iff ];
          replace hu := congr_arg List.toFinset hu; rw [ Finset.ext_iff ] at hu; specialize hu ( symbol.nonterminal r.lhs ) ; aesop;

/-
The finite NFA from a right-regular grammar accepts exactly the grammar's language.
-/
theorem NFA_of_RG_accepts (g : RG_grammar T) :
    (NFA_of_RG g).accepts = RG_language g := by
      ext w;
      constructor;
      · intro hw
        obtain ⟨q, hq⟩ := hw;
        rcases q with ( _ | ⟨ A, hA ⟩ ) <;> simp_all +decide [ NFA_of_RG ];
        · convert NFA_of_RG_none_forward _ _ _ hq using 1;
        · have h_derives : RG_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w ++ [symbol.nonterminal A]) := by
            apply NFA_of_RG_some_forward;
            exact hq.2;
          have h_derives : RG_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w ++ [symbol.nonterminal A]) → RG_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) := by
            intro h_deriv
            have h_eps : RG_transforms g (List.map symbol.terminal w ++ [symbol.nonterminal A]) (List.map symbol.terminal w) := by
              use RG_rule.epsilon A, by
                exact hq.1, List.map symbol.terminal w, [];
              simp +decide [ RG_rule.lhs, RG_rule.output ]
            exact RG_deri_of_deri_tran h_deriv h_eps;
          exact h_derives ‹_›;
      · intro hw
        obtain ⟨q, hq⟩ : ∃ q ∈ (NFA_of_RG g).accept, q ∈ (NFA_of_RG g).evalFrom {some ⟨g.initial, g.initial_mem_nonterminalFinset⟩} w := by
          have := RG_generates_last_step hw;
          rcases this with ( ⟨ C, p, hp, hC, rfl ⟩ | ⟨ C, p, a, hp, hC, rfl ⟩ );
          · use some ⟨C, by
              exact g.rule_nt_mem hC ( by simp +decide [ RG_rule.nonterminals ] )⟩
            generalize_proofs at *;
            exact ⟨ by unfold NFA_of_RG; aesop, by exact NFA_of_RG_some_backward _ _ _ _ _ hp ⟩;
          · refine' ⟨ none, _, _ ⟩ <;> simp_all +decide [ NFA_of_RG ];
            refine' Set.mem_iUnion₂.mpr ⟨ _, _, _ ⟩;
            exact some ⟨ C, by
              exact g.rule_nt_mem hC ( by simp +decide [ RG_rule.nonterminals ] ) ⟩
            all_goals generalize_proofs at *;
            · apply_rules [ NFA_of_RG_some_backward ];
            · aesop;
        exact ⟨ q, hq.1, hq.2 ⟩

/-- Every right-regular grammar language is Mathlib-regular. -/
theorem isRegular_of_is_RG {L : Language T} (h : is_RG L) : L.IsRegular := by
  obtain ⟨g, rfl⟩ := h
  rw [← NFA_of_RG_accepts g, ← NFA.toDFA_correct]
  exact ⟨_, inferInstance, _, rfl⟩

-- ============================================================================
-- Part 2: IsRegular → RG (via DFA construction)
-- ============================================================================

variable [Fintype T]

/-- Right-regular grammar constructed from a DFA over a finite alphabet. -/
def RG_of_DFA {σ : Type} [Fintype σ] (M : DFA T σ) : RG_grammar T where
  nt := σ
  initial := M.start
  rules :=
    (Finset.univ.product Finset.univ).toList.map
      (fun qa : σ × T => RG_rule.cons qa.1 qa.2 (M.step qa.1 qa.2)) ++
    Finset.univ.toList.filterMap
      (fun q => if q ∈ M.accept then some (RG_rule.epsilon q) else none)

/-
PROBLEM
The transition rule for (q, a) is in the grammar.

PROVIDED SOLUTION
The rule `RG_rule.cons q a (M.step q a)` is in the rules list because it comes from mapping `(q, a)` over the product `Finset.univ.product Finset.univ`. Since `q ∈ Finset.univ` and `a ∈ Finset.univ`, the pair `(q, a)` is in the product, and mapping produces the desired rule. Use `List.mem_append`, `List.mem_map`, `Finset.mem_toList`, `Finset.mem_product`, `Finset.mem_univ`.
-/
lemma RG_of_DFA_cons_mem {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) (a : T) :
    RG_rule.cons q a (M.step q a) ∈ (RG_of_DFA M).rules := by
      unfold RG_of_DFA; aesop;

/-
PROBLEM
The epsilon rule for an accepting state is in the grammar.

PROVIDED SOLUTION
The rule `RG_rule.epsilon q` is in the rules list because it comes from `filterMap` on `Finset.univ.toList`. Since `q ∈ Finset.univ` and `q ∈ M.accept`, the `filterMap` includes `some (RG_rule.epsilon q)`. Unfold `RG_of_DFA`, use `List.mem_append`, `List.mem_filterMap`, `Finset.mem_toList`, `Finset.mem_univ`, and the if-then-else with `hq`.
-/
lemma RG_of_DFA_epsilon_mem {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) (hq : q ∈ M.accept) :
    RG_rule.epsilon q ∈ (RG_of_DFA M).rules := by
      convert List.mem_append_right _ _;
      rw [ List.mem_filterMap ] ; aesop

/-
PROBLEM
An epsilon rule in the grammar implies the state is accepting.

PROVIDED SOLUTION
Forward: if `RG_rule.epsilon q ∈ rules`, unfold `RG_of_DFA` and note the rules are either of the form `RG_rule.cons ...` (from the map) or `RG_rule.epsilon q'` (from the filterMap, where q' ∈ M.accept). Since `RG_rule.cons ... ≠ RG_rule.epsilon q`, the rule must come from the filterMap part, which only includes `RG_rule.epsilon q'` when `q' ∈ M.accept`. By injectivity of the epsilon constructor, `q = q'`.

Backward: use `RG_of_DFA_epsilon_mem`.
-/
lemma RG_of_DFA_epsilon_mem_iff {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) :
    RG_rule.epsilon q ∈ (RG_of_DFA M).rules ↔ q ∈ M.accept := by
      simp [RG_of_DFA]

/-
PROBLEM
A cons rule in the grammar implies it matches the DFA transition.

PROVIDED SOLUTION
Forward: if `RG_rule.cons q a q' ∈ rules`, unfold `RG_of_DFA` and note the rules are either `RG_rule.cons p b (M.step p b)` from the map part, or `RG_rule.epsilon p` from the filterMap part. Since `RG_rule.cons ... ≠ RG_rule.epsilon ...`, the rule must come from the map. By injectivity of the cons constructor, `q = p`, `a = b`, and `q' = M.step p b = M.step q a`.

Backward: if `q' = M.step q a`, then `RG_rule.cons q a q' = RG_rule.cons q a (M.step q a)` which is in the rules by `RG_of_DFA_cons_mem`.
-/
lemma RG_of_DFA_cons_mem_iff {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) (a : T) (q' : σ) :
    RG_rule.cons q a q' ∈ (RG_of_DFA M).rules ↔ q' = M.step q a := by
      constructor <;> intro H;
      · unfold RG_of_DFA at H;
        grind +splitImp;
      · exact H ▸ RG_of_DFA_cons_mem M q a

/-
PROBLEM
Key simulation: starting from nonterminal `q`, the grammar derives
    the terminal string of `w` followed by nonterminal `evalFrom q w`.

PROVIDED SOLUTION
By induction on `w`.

Base case (w = []): We need `RG_derives g [nt q] ([nt (M.evalFrom q [])])` which is `RG_derives g [nt q] [nt q]` since `evalFrom q [] = q`. This is `RG_deri_self`.

Inductive step (w = a :: w'): We have by induction hypothesis:
  `RG_derives g [nt (M.step q a)] (map terminal w' ++ [nt (M.evalFrom (M.step q a) w')])`

Note that `M.evalFrom q (a :: w') = M.evalFrom (M.step q a) w'`.

We first apply the rule `q → a (M.step q a)` (which is `RG_of_DFA_cons_mem`):
  `[nt q] → [t a, nt (M.step q a)]`

Then we apply the induction hypothesis in context (prepend `[t a]`):
  `[t a, nt (M.step q a)] →* [t a] ++ map terminal w' ++ [nt (evalFrom (step q a) w')]`
  = `map terminal (a :: w') ++ [nt (evalFrom q (a :: w'))]`

For the context step, we need to show that RG derivations can be performed with a terminal prefix. This follows since RG_transforms allows arbitrary context u, v.

Use `RG_of_DFA_cons_mem` to get the first step, then show the IH derivation lifts to the prefixed context.
-/
lemma RG_of_DFA_derives_simulation {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) (w : List T) :
    RG_derives (RG_of_DFA M)
      [symbol.nonterminal q]
      (List.map symbol.terminal w ++ [symbol.nonterminal (M.evalFrom q w)]) := by
        cases' w with a w;
        · exact RG_deri_self _;
        · convert RG_deri_of_deri_deri _ _ using 1;
          exact [ symbol.terminal a, symbol.nonterminal ( M.step q a ) ];
          · apply RG_deri_of_tran;
            use RG_rule.cons q a (M.step q a);
            exact ⟨ RG_of_DFA_cons_mem M q a, [ ], [ ], rfl, rfl ⟩;
          · induction' w using List.reverseRecOn with w ih;
            · exact RG_deri_self _;
            · convert RG_deri_of_deri_tran _ _ using 1;
              exact List.map symbol.terminal ( a :: w ) ++ [ symbol.nonterminal ( M.evalFrom q ( a :: w ) ) ];
              · assumption;
              · use RG_rule.cons (M.evalFrom q (a :: w)) ih (M.evalFrom q (a :: (w ++ [ih])));
                simp +decide [ RG_of_DFA_cons_mem ];
                exact ⟨ [ symbol.terminal a ] ++ List.map symbol.terminal w, [ ], by simp +decide [ RG_rule.lhs, RG_rule.output ] ⟩

/-
PROBLEM
There are no `single` rules in the grammar constructed from a DFA.

PROVIDED SOLUTION
Unfold RG_of_DFA. The rules list is a concatenation of two parts:
1. `map ... (cons rules)` — all of the form `RG_rule.cons ...`
2. `filterMap ... (epsilon rules)` — all of the form `RG_rule.epsilon ...`

Since `RG_rule.single q a` is neither a `cons` nor an `epsilon` rule, it cannot appear in either part. Use `List.mem_append`, `List.mem_map`, `List.mem_filterMap`, and the fact that `RG_rule.single` is injectively distinct from `RG_rule.cons` and `RG_rule.epsilon` (by the `RG_rule` constructors being distinct).
-/
lemma RG_of_DFA_no_single {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) (a : T) :
    RG_rule.single q a ∉ (RG_of_DFA M).rules := by
      simp +decide [ RG_of_DFA ]

/-
PROBLEM
Key invariant: in the DFA grammar, any sentential form reachable from `[nt q]`
    is either `map terminal prefix ++ [nt (evalFrom q prefix)]` for some prefix,
    or `map terminal prefix` where `evalFrom q prefix ∈ M.accept`.

PROVIDED SOLUTION
By induction on the derivation `h : RG_derives (RG_of_DFA M) [nt q] s`.

Base case (refl): s = [nt q]. Take p = []. Then s = map terminal [] ++ [nt (evalFrom q [])] = [nt q] since evalFrom q [] = q. Left disjunct holds.

Inductive case: We have `RG_derives g [nt q] s'` and `RG_transforms g s' s`. By induction hypothesis, either:
- Case A: s' = map terminal p ++ [nt (evalFrom q p)] for some p
- Case B: s' = map terminal p and evalFrom q p ∈ accept for some p

In Case B: s' is all terminals, so no RG_transforms can apply (there are no nonterminals to rewrite). This is a contradiction since RG_transforms requires a nonterminal in s'.

In Case A: s' = map terminal p ++ [nt (evalFrom q p)]. The only nonterminal in s' is at the end. Let r be the applied rule, and let q' = evalFrom q p. The transform rewrites the nonterminal q' in context u, v where s' = u ++ [nt q'] ++ v. Since q' is the only nonterminal and it's at position |p|, we must have u = map terminal p and v = []. So:
- If r = cons q' a B: B = M.step q' a by RG_of_DFA_cons_mem_iff. Then s = map terminal p ++ [terminal a, nonterminal B] = map terminal (p ++ [a]) ++ [nt (evalFrom q (p ++ [a]))] since evalFrom q (p ++ [a]) = evalFrom (evalFrom q p) [a] = step q' a = B. Left disjunct holds.
- If r = single q' a: impossible by RG_of_DFA_no_single.
- If r = epsilon q': Then s = map terminal p ++ [] = map terminal p, and q' ∈ accept by RG_of_DFA_epsilon_mem_iff. Right disjunct holds.
-/
lemma RG_of_DFA_derives_inv {σ : Type} [Fintype σ] (M : DFA T σ)
    (q : σ) (s : List (symbol T σ))
    (h : RG_derives (RG_of_DFA M) [symbol.nonterminal q] s) :
    (∃ p : List T, s = List.map symbol.terminal p ++ [symbol.nonterminal (M.evalFrom q p)]) ∨
    (∃ p : List T, s = List.map symbol.terminal p ∧ M.evalFrom q p ∈ M.accept) := by
      induction' h with s' s h ih;
      · exact Or.inl ⟨ [ ], rfl ⟩;
      · rcases ‹_› with ( ⟨ p, rfl ⟩ | ⟨ p, rfl, hp ⟩ ) <;> simp_all +decide [ RG_transforms ];
        · rcases ih with ⟨ r, hr, u, v, hu, rfl ⟩ ; rcases r with ( _ | _ | _ ) <;> simp_all +decide [ RG_rule.lhs, RG_rule.output ] ;
          · rcases List.append_eq_append_iff.mp hu.symm with ( ⟨ x, hx ⟩ | ⟨ x, hx ⟩ ) <;> simp_all +decide [ List.map ];
            · rcases x with ( _ | ⟨ y, x ⟩ ) <;> simp_all +decide [ List.map ];
              · unfold RG_of_DFA at hr; simp_all +decide [ Finset.mem_product ] ;
                exact Or.inl ⟨ p ++ [ ‹_› ], by aesop ⟩;
              · rcases y with ( _ | _ ) <;> simp_all +decide [ List.map ];
                replace hx := congr_arg List.toFinset hx.1; rw [ Finset.ext_iff ] at hx; specialize hx ( symbol.nonterminal ‹_› ) ; aesop;
            · rcases x with ( _ | ⟨ _, _ | x ⟩ ) <;> simp_all +decide [ List.map ];
              refine' Or.inl ⟨ p ++ [ ‹_› ], _ ⟩ ; simp +decide [ hx, DFA.evalFrom ];
              unfold RG_of_DFA at hr; aesop;
          · exact absurd hr ( RG_of_DFA_no_single M _ _ );
          · rw [ List.append_eq_append_iff ] at hu;
            rcases hu with ( ⟨ as, rfl, hu ⟩ | ⟨ bs, hu, hv ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
            · rcases as with ( _ | ⟨ _, _ | as ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
              exact Or.inr ⟨ p, rfl, by simpa [ hu.1 ] using RG_of_DFA_epsilon_mem_iff M _ |>.1 hr ⟩;
            · cases bs <;> simp_all +decide [ List.map ];
              · exact Or.inr ⟨ p, hu.symm, by simpa [ RG_of_DFA_epsilon_mem_iff ] using hr ⟩;
              · replace hu := congr_arg List.toFinset hu; rw [ Finset.ext_iff ] at hu; specialize hu ( symbol.nonterminal ‹_› ) ; aesop;
        · obtain ⟨ r, hr, u, v, huv, rfl ⟩ := ih;
          replace huv := congr_arg List.toFinset huv; rw [ Finset.ext_iff ] at huv; specialize huv ( symbol.nonterminal r.lhs ) ; aesop;

/-
PROBLEM
The RG constructed from a DFA generates exactly the DFA's language.

PROVIDED SOLUTION
We show set equality by showing both inclusions.

Forward (w ∈ RG_language → w ∈ M.accepts):
Suppose RG_derives g [nt M.start] (map terminal w). Apply RG_of_DFA_derives_inv to get either:
- Left: map terminal w = map terminal p ++ [nt (evalFrom M.start p)] for some p. But the LHS is all terminals while the RHS ends with a nonterminal, contradiction. (A nonterminal cannot equal a terminal, so this case is impossible.)
- Right: map terminal w = map terminal p and evalFrom M.start p ∈ M.accept. By injectivity of map terminal, w = p. So evalFrom M.start w ∈ M.accept, which means w ∈ M.accepts.

Backward (w ∈ M.accepts → w ∈ RG_language):
We have M.eval w ∈ M.accept. Use RG_of_DFA_derives_simulation to get:
  [nt M.start] →* map terminal w ++ [nt (evalFrom M.start w)]
Then apply the epsilon rule (evalFrom M.start w ∈ accept ↔ epsilon rule exists, by RG_of_DFA_epsilon_mem) to get:
  map terminal w ++ [nt (evalFrom M.start w)] → map terminal w
So [nt M.start] →* map terminal w.
-/
theorem RG_of_DFA_language {σ : Type} [Fintype σ] (M : DFA T σ) :
    RG_language (RG_of_DFA M) = M.accepts := by
      -- By combining the above results, we conclude the proof.
      apply Set.ext
      intro w
      constructor;
      · intro hw
        obtain ⟨s, hs⟩ := RG_of_DFA_derives_inv M M.start (List.map symbol.terminal w) hw;
        · replace hs := congr_arg List.toFinset hs ; simp_all +decide [ Finset.ext_iff ];
          specialize hs ( symbol.nonterminal ( M.evalFrom M.start s ) ) ; aesop;
        · obtain ⟨ p, hp₁, hp₂ ⟩ := ‹_›;
          rw [ List.map_inj_right ] at hp₁ ; aesop;
          aesop;
      · intro hw;
        apply Relation.ReflTransGen.tail;
        exact RG_of_DFA_derives_simulation M M.start w;
        exact ⟨ RG_rule.epsilon _, RG_of_DFA_epsilon_mem M _ hw, List.map symbol.terminal w, [ ], by aesop ⟩

/-- Every Mathlib-regular language over a finite alphabet is generated by
    a right-regular grammar. -/
theorem is_RG_of_isRegular {L : Language T} (h : L.IsRegular) : is_RG L := by
  obtain ⟨σ, hfin, M, rfl⟩ := h
  exact ⟨RG_of_DFA M, RG_of_DFA_language M⟩

/-- Right-regular grammars generate exactly the Mathlib-regular languages
    (over a finite alphabet). -/
theorem is_RG_iff_isRegular {L : Language T} :
    is_RG L ↔ L.IsRegular :=
  ⟨isRegular_of_is_RG, is_RG_of_isRegular⟩

theorem RG_eq_DFA {T: Type} [Fintype T] :
  (RG : Set (Language T)) = DFA.Class := by
    ext L
    refine Eq.to_iff ?_
    simp only [RG, Set.mem_setOf_eq, DFA.Class, eq_iff_iff]
    exact is_RG_iff_isRegular
