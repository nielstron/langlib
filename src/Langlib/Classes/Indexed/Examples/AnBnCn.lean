import Mathlib
import Langlib.Grammars.Indexed.Definition
import Langlib.Classes.Indexed.Definition
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Inclusion.Indexed

/-! # Strict Inclusion: CF ⊊ Indexed

This file proves that the class of indexed languages strictly contains the class of
context-free languages, by exhibiting a witness: the language `{aⁿbⁿcⁿ | n ∈ ℕ}`
is indexed but not context-free.

The indexed grammar uses a stack-bottom marker to ensure that each nonterminal
consumes exactly as many flags as were pushed.

## Main declarations

- `is_Indexed_lang_eq_eq` — `{aⁿbⁿcⁿ}` is an indexed language
- `CF_strict_subclass_Indexed` — CF ⊊ Indexed
-/

open List

section anbncn

/-- Nonterminals for the aⁿbⁿcⁿ indexed grammar. -/
inductive ANBNCN_NT where
  | S | T | A | B | C
deriving DecidableEq

/-- Flags for the aⁿbⁿcⁿ indexed grammar. -/
inductive ANBNCN_Flag where
  | count | bottom
deriving DecidableEq

def grammar_anbncn_indexed : IndexedGrammar (Fin 3) where
  nt := ANBNCN_NT
  flag := ANBNCN_Flag
  initial := .S
  rules := [
    { lhs := .S, consume := none,
      rhs := [IRhsSymbol.nonterminal .T (some .bottom)] },
    { lhs := .T, consume := none,
      rhs := [IRhsSymbol.nonterminal .T (some .count)] },
    { lhs := .T, consume := none,
      rhs := [IRhsSymbol.nonterminal .A none,
              IRhsSymbol.nonterminal .B none,
              IRhsSymbol.nonterminal .C none] },
    { lhs := .A, consume := some .count,
      rhs := [IRhsSymbol.terminal 0, IRhsSymbol.nonterminal .A none] },
    { lhs := .A, consume := some .bottom, rhs := [] },
    { lhs := .B, consume := some .count,
      rhs := [IRhsSymbol.terminal 1, IRhsSymbol.nonterminal .B none] },
    { lhs := .B, consume := some .bottom, rhs := [] },
    { lhs := .C, consume := some .count,
      rhs := [IRhsSymbol.terminal 2, IRhsSymbol.nonterminal .C none] },
    { lhs := .C, consume := some .bottom, rhs := [] }
  ]

private abbrev G := grammar_anbncn_indexed
private abbrev iS (σ : List ANBNCN_Flag) : G.ISym := .indexed .S σ
private abbrev iT (σ : List ANBNCN_Flag) : G.ISym := .indexed .T σ
private abbrev iA (σ : List ANBNCN_Flag) : G.ISym := .indexed .A σ
private abbrev iB (σ : List ANBNCN_Flag) : G.ISym := .indexed .B σ
private abbrev iC (σ : List ANBNCN_Flag) : G.ISym := .indexed .C σ
private abbrev ia : G.ISym := .terminal 0
private abbrev ib : G.ISym := .terminal 1
private abbrev ic : G.ISym := .terminal 2

private abbrev stk (n : ℕ) : List ANBNCN_Flag := replicate n .count ++ [.bottom]

private lemma stk_succ (n : ℕ) : stk (n + 1) = .count :: stk n := by
  simp [stk, replicate_succ]

-- ==================== Forward direction ====================

private lemma step_S_to_T :
    G.Transforms [iS []] [iT [.bottom]] :=
  ⟨⟨.S, none, [.nonterminal .T (some .bottom)]⟩,
    [], [], [], by simp [G, grammar_anbncn_indexed], rfl, rfl⟩

private lemma push_counts (n : ℕ) :
    G.Derives [iT (stk 0)] [iT (stk n)] := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    apply ih.tail
    refine ⟨⟨.T, none, [.nonterminal .T (some .count)]⟩, [], [], stk n,
      by simp [G, grammar_anbncn_indexed], rfl, ?_⟩
    simp [IndexedGrammar.expandRhs, stk_succ]

private lemma step_T_to_ABC (σ : List ANBNCN_Flag) :
    G.Transforms [iT σ] [iA σ, iB σ, iC σ] :=
  ⟨⟨.T, none, [.nonterminal .A none, .nonterminal .B none, .nonterminal .C none]⟩,
    [], [], σ, by simp [G, grammar_anbncn_indexed], rfl, rfl⟩

private lemma consume_A (n : ℕ) (suffix : List G.ISym) :
    G.Derives ([iA (stk n)] ++ suffix) (replicate n ia ++ suffix) := by
      induction' n with n ih generalizing suffix;
      · convert Relation.ReflTransGen.single _ using 1;
        use ⟨ .A, some .bottom, [ ] ⟩;
        use [], suffix, []
        simp [G];
        exact ⟨ by tauto, rfl ⟩;
      · -- Apply the rule 3 (A consume count): Transforms ([iA (.count :: stk n)] ++ suffix) ([ia, iA (stk n)] ++ suffix).
        have step_A_count : G.Transforms ([iA (.count :: stk n)] ++ suffix) ([ia, iA (stk n)] ++ suffix) := by
          use ⟨ .A, some .count, [IRhsSymbol.terminal 0, IRhsSymbol.nonterminal .A none] ⟩, [], suffix, stk n;
          exact ⟨ by tauto, by tauto ⟩;
        have step_A_count : G.Derives ([ia, iA (stk n)] ++ suffix) (replicate (n + 1) ia ++ suffix) := by
          have step_A_count : G.Derives ([iA (stk n)] ++ suffix) (replicate n ia ++ suffix) := by
            exact ih suffix;
          convert G.deri_with_prefix [ia] step_A_count using 1;
        exact .single ‹_› |> Relation.ReflTransGen.trans <| step_A_count

private lemma consume_B (n : ℕ) (suffix : List G.ISym) :
    G.Derives ([iB (stk n)] ++ suffix) (replicate n ib ++ suffix) := by
      -- We proceed by induction on $n$.
      induction' n with n ih generalizing suffix;
      · exact .single ( by
          use ⟨ .B, some .bottom, [ ] ⟩;
          unfold G; simp +decide [ stk ] ;
          exact ⟨ by simp +decide [ grammar_anbncn_indexed ], [ ], suffix, [ ], rfl, rfl ⟩ );
      · -- Apply rule 5 (B consume count): r = {.B, some .count, [terminal 1, nonterminal .B none]}, u=[], v=suffix, σ=stk n.
        have h_rule5 : G.Transforms ([iB (stk (n + 1))] ++ suffix) ([ib, iB (stk n)] ++ suffix) := by
          use ⟨.B, some .count, [IRhsSymbol.terminal 1, IRhsSymbol.nonterminal .B none]⟩, [], suffix, stk n;
          simp +decide [ grammar_anbncn_indexed ];
          exact ⟨ rfl, rfl ⟩;
        -- By the induction hypothesis, we can derive [ib, iB (stk n)] ++ suffix to replicate n ib ++ suffix.
        have h_ind : G.Derives ([ib, iB (stk n)] ++ suffix) (replicate (n + 1) ib ++ suffix) := by
          convert G.deri_with_prefix [ib] (ih suffix) using 1;
        exact .single h_rule5 |> Relation.ReflTransGen.trans <| h_ind

private lemma consume_C (n : ℕ) :
    G.Derives [iC (stk n)] (replicate n ic) := by
      induction' n with n ih;
      · constructor;
        constructor;
        exists ⟨ .C, some .bottom, [ ] ⟩, [ ], [ ], [ ];
        simp +decide [ G ];
        exact?;
      · -- Apply the transformation from iC (stk (n + 1)) to ic :: iC (stk n).
        have h_transform : G.Transforms [iC (stk (n + 1))] (ic :: iC (stk n) :: []) := by
          use ⟨.C, some .count, [IRhsSymbol.terminal 2, IRhsSymbol.nonterminal .C none]⟩;
          use [], [], stk n;
          simp +decide [ grammar_anbncn_indexed ];
          exact ⟨ rfl, rfl ⟩;
        convert G.deri_of_deri_deri _ _ using 1;
        exact [ ic, iC ( stk n ) ];
        · exact .single h_transform;
        · convert G.deri_with_prefix [ ic ] ih using 1

private lemma anbncn_generates (n : ℕ) :
    replicate n (0 : Fin 3) ++ replicate n 1 ++ replicate n 2 ∈
      G.Language := by
  show G.Generates _
  unfold IndexedGrammar.Generates
  apply IndexedGrammar.deri_of_tran_deri step_S_to_T
  apply IndexedGrammar.deri_of_deri_deri (push_counts n)
  apply IndexedGrammar.deri_of_tran_deri (step_T_to_ABC (stk n))
  apply IndexedGrammar.deri_of_deri_deri (consume_A n [iB (stk n), iC (stk n)])
  apply IndexedGrammar.deri_of_deri_deri
    (IndexedGrammar.deri_with_prefix (replicate n ia) (consume_B n [iC (stk n)]))
  convert IndexedGrammar.deri_with_prefix (replicate n ia ++ replicate n ib) (consume_C n) using 1
  · simp [List.append_assoc]
  · simp [List.map_append, List.map_replicate]

-- ==================== Backward direction ====================

/-- Structural invariant for reachable sentential forms. -/
private inductive GoodForm : List G.ISym → Prop where
  | start : GoodForm [iS []]
  | withT (n : ℕ) : GoodForm [iT (stk n)]
  | withABC (n ja jb jc : ℕ) (doneA doneB doneC : Bool)
      (hja : ja ≤ n) (hjb : jb ≤ n) (hjc : jc ≤ n)
      (hdA : doneA = true → ja = n)
      (hdB : doneB = true → jb = n)
      (hdC : doneC = true → jc = n) :
    GoodForm (replicate ja ia
             ++ (if doneA then [] else [iA (stk (n - ja))])
             ++ replicate jb ib
             ++ (if doneB then [] else [iB (stk (n - jb))])
             ++ replicate jc ic
             ++ (if doneC then [] else [iC (stk (n - jc))]))

/-
Case 1: form = [iS []]
-/
private lemma goodForm_step_case1 {form' : List G.ISym}
    (ht : G.Transforms [iS []] form') : GoodForm form' := by
      cases ht;
      rename_i r hr;
      obtain ⟨ u, v, σ, hr₁, hr₂, rfl ⟩ := hr;
      rcases u with ( _ | ⟨ x, u ⟩ ) <;> rcases v with ( _ | ⟨ y, v ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
      · rcases r with ⟨ _ | _, _ | _, _ | _ ⟩ <;> simp_all +decide [ G ];
        · contradiction;
        · cases hr₁;
          · exact GoodForm.withT 0;
          · contradiction;
      · cases r_consume : r.consume <;> simp_all +decide;
      · cases r : r.consume <;> simp_all +decide;
      · cases r : r.consume <;> simp_all +decide

/-
Case 2: form = [iT (stk n)]
-/
private lemma goodForm_step_case2 {n : ℕ} {form' : List G.ISym}
    (ht : G.Transforms [iT (stk n)] form') : GoodForm form' := by
      obtain ⟨ r, u, v, σ, hr, h₁, h₂ ⟩ := ht;
      rcases r with ⟨ lhs, consume, rhs ⟩;
      rcases u with ( _ | ⟨ _, _ | u ⟩ ) <;> simp_all +decide [ G ];
      · unfold grammar_anbncn_indexed at *;
        rcases consume with ( _ | _ | consume ) <;> simp_all +decide;
        · rcases hr with ( ⟨ rfl, rfl ⟩ | rfl | rfl ) <;> simp_all +decide [ IndexedGrammar.expandRhs ];
          · convert GoodForm.withT ( n + 1 ) using 1;
            aesop;
          · convert GoodForm.withABC n 0 0 0 false false false _ _ _ _ _ _ using 1 <;> simp +decide [ h₁ ];
        · grind;
        · grind;
      · cases consume <;> contradiction;
      · cases consume <;> contradiction

/-
Splitting a list at a unique nonterminal type.
    If both sides split at the first occurrence of an `indexed nt` symbol,
    then the prefixes, the symbol, and the suffixes agree.
-/
private lemma split_unique_nt {nt : ANBNCN_NT}
    {σ₁ σ₂ : List ANBNCN_Flag} {u₁ u₂ v₁ v₂ : List G.ISym}
    (h₁ : ∀ x ∈ u₁, ∀ σ, x ≠ IndexedGrammar.ISym.indexed nt σ)
    (h₂ : ∀ x ∈ u₂, ∀ σ, x ≠ IndexedGrammar.ISym.indexed nt σ)
    (heq : u₁ ++ IndexedGrammar.ISym.indexed nt σ₁ :: v₁ =
           u₂ ++ IndexedGrammar.ISym.indexed nt σ₂ :: v₂) :
    u₁ = u₂ ∧ σ₁ = σ₂ ∧ v₁ = v₂ := by
      induction' u₁ with a u₁ ih generalizing u₂ v₁ v₂ <;> induction' u₂ with b u₂ ih' <;> simp +decide at heq ⊢;
      · tauto;
      · exact h₂ _ ( List.mem_cons_self ) _ heq.1.symm;
      · exact h₁ _ ( List.mem_cons_self ) _ heq.1;
      · grind +ring

/-- Terminals are never indexed symbols. -/
private lemma terminal_ne_indexed (t : Fin 3) (nt : ANBNCN_NT) (σ : List ANBNCN_Flag) :
    (IndexedGrammar.ISym.terminal t : G.ISym) ≠ IndexedGrammar.ISym.indexed nt σ := by
  intro h; cases h

/-- No element of `replicate k (terminal t)` is an indexed symbol. -/
private lemma no_indexed_in_replicate (k : ℕ) (t : Fin 3) (nt : ANBNCN_NT) :
    ∀ x ∈ replicate k (IndexedGrammar.ISym.terminal t : G.ISym),
      ∀ σ, x ≠ IndexedGrammar.ISym.indexed nt σ := by
  intro x hx σ; rw [eq_of_mem_replicate hx]; exact terminal_ne_indexed t nt σ

/-- Distinct nonterminal types give distinct indexed symbols. -/
private lemma indexed_ne_of_nt_ne {nt₁ nt₂ : ANBNCN_NT} (hne : nt₁ ≠ nt₂)
    (σ₁ σ₂ : List ANBNCN_Flag) :
    (IndexedGrammar.ISym.indexed nt₁ σ₁ : G.ISym) ≠ IndexedGrammar.ISym.indexed nt₂ σ₂ := by
  intro h; cases h; exact hne rfl

/-- No A-indexed symbol in `replicate k ia ++ oA_or_empty` when `oA_or_empty` has no A
    (e.g. when doneA = true, or when looking for B/C). -/
private lemma no_A_before_A (ja : ℕ) :
    ∀ x ∈ replicate ja ia, ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.A σ :=
  no_indexed_in_replicate ja 0 .A

/-
No B-indexed symbol in the prefix before B in the form.
-/
private lemma no_B_before_B (ja : ℕ) (doneA : Bool) (n jb : ℕ) (hja : ja ≤ n) :
    ∀ x ∈ replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))]) ++ replicate jb ib,
      ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.B σ := by
        grind

/-
No C-indexed symbol in the prefix before C in the form.
-/
private lemma no_C_before_C (ja : ℕ) (doneA : Bool) (n jb : ℕ) (doneB : Bool)
    (jc : ℕ) (hja : ja ≤ n) (hjb : jb ≤ n) :
    ∀ x ∈ replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))])
          ++ replicate jb ib ++ (if doneB then [] else [iB (stk (n - jb))])
          ++ replicate jc ic,
      ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.C σ := by
        grind

/-
No S-indexed symbol in the ABC form.
-/
private lemma no_S_in_abc_form (ja jb jc : ℕ) (n : ℕ)
    (doneA doneB doneC : Bool) (hja : ja ≤ n) (hjb : jb ≤ n) (hjc : jc ≤ n) :
    ∀ x ∈ replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))])
          ++ replicate jb ib ++ (if doneB then [] else [iB (stk (n - jb))])
          ++ replicate jc ic ++ (if doneC then [] else [iC (stk (n - jc))]),
      ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.S σ := by
        grind

/-
No T-indexed symbol in the ABC form.
-/
private lemma no_T_in_abc_form (ja jb jc : ℕ) (n : ℕ)
    (doneA doneB doneC : Bool) (hja : ja ≤ n) (hjb : jb ≤ n) (hjc : jc ≤ n) :
    ∀ x ∈ replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))])
          ++ replicate jb ib ++ (if doneB then [] else [iB (stk (n - jb))])
          ++ replicate jc ic ++ (if doneC then [] else [iC (stk (n - jc))]),
      ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.T σ := by
        aesop ( simp_config := { singlePass := true } ) ;

/-
Sub-case: an A-type rule fires on the ABC form (doneA = false).
-/
private lemma goodForm_step_on_A {n ja jb jc : ℕ} {doneB doneC : Bool}
    {form' : List G.ISym}
    (hja : ja ≤ n) (hjb : jb ≤ n) (hjc : jc ≤ n)
    (hdB : doneB = true → jb = n) (hdC : doneC = true → jc = n)
    {f : ANBNCN_Flag} {rhs : List (IRhsSymbol (Fin 3) ANBNCN_NT ANBNCN_Flag)}
    {u v : List G.ISym} {σ : List ANBNCN_Flag}
    (hr : ⟨ANBNCN_NT.A, some f, rhs⟩ ∈ G.rules)
    (heq : u ++ IndexedGrammar.ISym.indexed ANBNCN_NT.A (f :: σ) :: v =
           replicate ja ia ++ [iA (stk (n - ja))]
           ++ replicate jb ib ++ (if doneB then [] else [iB (stk (n - jb))])
           ++ replicate jc ic ++ (if doneC then [] else [iC (stk (n - jc))]))
    (hform' : form' = u ++ IndexedGrammar.expandRhs G rhs σ ++ v) :
    GoodForm form' := by
      -- Prove that $u = \text{replicate } ja \, ia$.
      have hu : u = replicate ja ia := by
        have h_u : ∃ a, replicate ja ia = u ++ a ∧ iA (stk (n - ja)) :: replicate jb ib ++ (if doneB = true then [] else [iB (stk (n - jb))]) ++ replicate jc ic ++ (if doneC = true then [] else [iC (stk (n - jc))]) = a ++ IndexedGrammar.ISym.indexed ANBNCN_NT.A (f :: σ) :: v ∨ ∃ a, u = replicate ja ia ++ a ∧ iA (stk (n - ja)) :: replicate jb ib ++ (if doneB = true then [] else [iB (stk (n - jb))]) ++ replicate jc ic ++ (if doneC = true then [] else [iC (stk (n - jc))]) = a ++ IndexedGrammar.ISym.indexed ANBNCN_NT.A (f :: σ) :: v := by
          have h_u : u ++ IndexedGrammar.ISym.indexed ANBNCN_NT.A (f :: σ) :: v = replicate ja ia ++ (iA (stk (n - ja)) :: replicate jb ib ++ (if doneB = true then [] else [iB (stk (n - jb))]) ++ replicate jc ic ++ (if doneC = true then [] else [iC (stk (n - jc))])) := by
            grind;
          rw [ List.append_eq_append_iff ] at h_u;
          rcases h_u with ( ⟨ as, has₁, has₂ ⟩ | ⟨ bs, hbs₁, hbs₂ ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          have h_contra : ∀ x ∈ replicate ja ia, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.A (f :: σ) := by
            intro x hx; rw [ List.eq_of_mem_replicate hx ] ; exact terminal_ne_indexed _ _ _;
          grind;
        obtain ⟨ a, ha ⟩ := h_u;
        rcases ha with ( ⟨ ha₁, ha₂ ⟩ | ⟨ a, rfl, ha₂ ⟩ );
        · replace ha₂ := congr_arg List.reverse ha₂ ; simp_all +decide [ List.reverse_append ];
        · rcases a with ( _ | ⟨ x, a ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          have h_contradiction : ∀ x ∈ replicate jb ib ++ (if doneB = true then [] else [iB (stk (n - jb))]) ++ replicate jc ic ++ (if doneC = true then [] else [iC (stk (n - jc))]), ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.A σ := by
            grind +splitIndPred;
          grind +ring;
      -- Prove that $f :: σ = stk (n - ja)$.
      have hfs : f :: σ = stk (n - ja) := by
        replace heq := congr_arg ( fun x => x.drop ja ) heq ; simp_all +decide [ List.drop_append ] ;
      rcases k : n - ja with ( _ | k ) <;> simp_all +decide [ stk_succ ];
      · unfold G at *; simp_all +decide [ grammar_anbncn_indexed ] ;
        cases hr <;> simp_all +decide [ stk ];
        convert GoodForm.withABC n n jb jc true doneB doneC _ _ _ _ _ _ using 1 <;> norm_num [ Nat.sub_eq_zero_iff_le.mpr hja ];
        · rw [ Nat.sub_eq_iff_eq_add ] at k <;> first | linarith | aesop;
        · linarith;
        · linarith;
        · exact hdB;
        · exact hdC;
      · unfold G at hr; simp_all +decide [ grammar_anbncn_indexed ] ;
        convert GoodForm.withABC n ( ja + 1 ) jb jc Bool.false doneB doneC _ _ _ _ _ _ using 1 <;> norm_num [ Nat.succ_eq_add_one, Nat.add_sub_add_right ];
        all_goals norm_cast;
        · simp +decide [ ← k, List.replicate_add, IndexedGrammar.expandRhs ];
          omega;
        · omega

/-
Sub-case: a B-type rule fires on the ABC form (doneB = false).
-/
private lemma goodForm_step_on_B {n ja jb jc : ℕ} {doneA doneC : Bool}
    {form' : List G.ISym}
    (hja : ja ≤ n) (hjb : jb ≤ n) (hjc : jc ≤ n)
    (hdA : doneA = true → ja = n) (hdC : doneC = true → jc = n)
    {f : ANBNCN_Flag} {rhs : List (IRhsSymbol (Fin 3) ANBNCN_NT ANBNCN_Flag)}
    {u v : List G.ISym} {σ : List ANBNCN_Flag}
    (hr : ⟨ANBNCN_NT.B, some f, rhs⟩ ∈ G.rules)
    (heq : u ++ IndexedGrammar.ISym.indexed ANBNCN_NT.B (f :: σ) :: v =
           replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))])
           ++ replicate jb ib ++ [iB (stk (n - jb))]
           ++ replicate jc ic ++ (if doneC then [] else [iC (stk (n - jc))]))
    (hform' : form' = u ++ IndexedGrammar.expandRhs G rhs σ ++ v) :
    GoodForm form' := by
      have h_split : ∃ u' v', u = replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))]) ++ replicate jb ib ++ u' ∧ v = v' ++ replicate jc ic ++ (if doneC then [] else [iC (stk (n - jc))]) := by
        have h_split : u ++ IndexedGrammar.ISym.indexed ANBNCN_NT.B (f :: σ) :: v = (replicate ja ia ++ if doneA = true then [] else [iA (stk (n - ja))]) ++ replicate jb ib ++ ([iB (stk (n - jb))] ++ replicate jc ic ++ if doneC = true then [] else [iC (stk (n - jc))]) := by
          simpa only [ List.append_assoc ] using heq;
        rw [ List.append_eq_append_iff ] at h_split;
        rcases h_split with ( ⟨ as, has₁, has₂ ⟩ | ⟨ bs, has₁, has₂ ⟩ ) <;> simp_all +decide [ List.append_assoc ];
        · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          have := no_B_before_B ja doneA n jb hja; simp_all +decide [ List.append_assoc ] ;
          exact this _ ( Or.inr <| Or.inl rfl ) _ has₂.1.symm;
        · rcases bs with ( _ | ⟨ x, bs ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          have h_split : ∀ x ∈ replicate jc ic ++ (if doneC then [] else [iC (stk (n - jc))]), ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.B σ := by
            split_ifs <;> simp_all +decide [ List.mem_append, List.mem_replicate ];
            rintro x ( ⟨ _, rfl ⟩ | rfl ) σ <;> simp +decide [ IndexedGrammar.ISym ];
          grind;
      obtain ⟨ u', v', rfl, rfl ⟩ := h_split; simp_all +decide [ List.append_assoc ] ;
      rcases u' with ( _ | ⟨ _, _ | u' ⟩ ) <;> simp_all +decide [ List.append_assoc ] ;
      · rcases n' : n - jb with ( _ | n' ) <;> simp_all +decide [ stk_succ ];
        · unfold G at hr; simp_all +decide [ stk ] ;
          unfold grammar_anbncn_indexed at hr; simp_all +decide [ List.mem_cons ] ;
          convert GoodForm.withABC n ja n jc doneA true doneC _ _ _ _ _ _ using 1 <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
        · rcases hr' : rhs with ( _ | ⟨ x, _ | ⟨ y, rhs ⟩ ⟩ ) <;> simp_all +decide [ G ] ;
          · contradiction;
          · rcases x with ( _ | _ | x ) <;> simp_all +decide [ grammar_anbncn_indexed ];
          · unfold grammar_anbncn_indexed at hr; simp_all +decide ;
            unfold grammar_anbncn_indexed; simp +decide [ IndexedGrammar.expandRhs ] ;
            convert GoodForm.withABC n ja ( jb + 1 ) jc doneA false doneC ( by linarith ) ( by omega ) ( by omega ) ( by aesop ) ( by aesop ) using 1 ; simp +decide [ List.replicate_add ] ; ring;
            rw [ show n - ( 1 + jb ) = n - jb - 1 by rw [ Nat.sub_sub, add_comm ] ] ; simp +decide [ n', heq ] ; aesop;
      · replace heq := congr_arg List.length heq.2 ; simp_all +arith +decide [ List.length_append ] ;
      · replace heq := congr_arg List.length heq.2 ; simp_all +arith +decide;

/-
Sub-case: a C-type rule fires on the ABC form (doneC = false).
-/
private lemma goodForm_step_on_C {n ja jb jc : ℕ} {doneA doneB : Bool}
    {form' : List G.ISym}
    (hja : ja ≤ n) (hjb : jb ≤ n) (hjc : jc ≤ n)
    (hdA : doneA = true → ja = n) (hdB : doneB = true → jb = n)
    {f : ANBNCN_Flag} {rhs : List (IRhsSymbol (Fin 3) ANBNCN_NT ANBNCN_Flag)}
    {u v : List G.ISym} {σ : List ANBNCN_Flag}
    (hr : ⟨ANBNCN_NT.C, some f, rhs⟩ ∈ G.rules)
    (heq : u ++ IndexedGrammar.ISym.indexed ANBNCN_NT.C (f :: σ) :: v =
           replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))])
           ++ replicate jb ib ++ (if doneB then [] else [iB (stk (n - jb))])
           ++ replicate jc ic ++ [iC (stk (n - jc))])
    (hform' : form' = u ++ IndexedGrammar.expandRhs G rhs σ ++ v) :
    GoodForm form' := by
      have h_split : u = replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))]) ++ replicate jb ib ++ (if doneB then [] else [iB (stk (n - jb))]) ++ replicate jc ic := by
        have hu : ∀ x ∈ u, ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.C σ := by
          rw [ List.append_eq_append_iff ] at heq;
          rcases heq with ( ⟨ as, has₁, has₂ ⟩ | ⟨ bs, rfl, hbs ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          · have := no_C_before_C ja doneA n jb doneB jc hja hjb; aesop;
          · cases bs <;> aesop;
        apply (split_unique_nt ?_ ?_ heq).left;
        · assumption;
        · apply_rules [ no_C_before_C ];
      rcases f with ( _ | _ ) <;> simp_all +decide [ G ];
      · rcases k : n - jc with ( _ | k ) <;> simp_all +decide [ stk ];
        simp_all +decide [ replicate ];
        convert GoodForm.withABC n ja jb ( jc + 1 ) doneA doneB false _ _ _ _ _ _ using 1 <;> simp_all +decide [ Nat.sub_succ ];
        · simp_all +decide [ replicate_add, grammar_anbncn_indexed, IndexedGrammar.expandRhs ];
        · omega;
      · rcases k : n - jc with ( _ | _ | k ) <;> simp_all +decide [ stk ];
        · unfold grammar_anbncn_indexed at hr; simp_all +decide ;
          split_ifs <;> simp_all +decide [ GoodForm ];
          · convert GoodForm.withABC n n n n Bool.true Bool.true Bool.true _ _ _ _ _ _ using 1 <;> simp +decide [ * ];
            rw [ Nat.sub_eq_iff_eq_add ] at k <;> aesop;
          · convert GoodForm.withABC n n jb jc doneA doneB true _ _ _ _ _ _ using 1 <;> simp +decide [ *, Nat.sub_eq_iff_eq_add' hjc ];
            omega;
          · convert GoodForm.withABC n ja n jc doneA true true _ _ _ _ _ _ using 1 <;> simp +decide [ *, Nat.sub_eq_iff_eq_add ];
            omega;
          · convert GoodForm.withABC n ja jb jc doneA doneB true _ _ _ _ _ _ using 1 <;> simp +decide [ *, Nat.sub_eq_iff_eq_add ];
            omega;
        · cases heq.1

/-
Case 3: ABC form
-/
set_option maxHeartbeats 400000 in
private lemma goodForm_step_case3 {n ja jb jc : ℕ} {doneA doneB doneC : Bool}
    {form' : List G.ISym}
    (hja : ja ≤ n) (hjb : jb ≤ n) (hjc : jc ≤ n)
    (hdA : doneA = true → ja = n)
    (hdB : doneB = true → jb = n)
    (hdC : doneC = true → jc = n)
    (ht : G.Transforms (replicate ja ia
             ++ (if doneA then [] else [iA (stk (n - ja))])
             ++ replicate jb ib
             ++ (if doneB then [] else [iB (stk (n - jb))])
             ++ replicate jc ic
             ++ (if doneC then [] else [iC (stk (n - jc))])) form') :
    GoodForm form' := by
      obtain ⟨ r, u, v, σ, hr, heq, rfl ⟩ := ht;
      by_cases hA : r.lhs = .A;
      · rcases r_consume : r.consume with ( _ | _ | _ ) <;> simp_all +decide;
        · rcases r with ⟨ lhs, consume, rhs ⟩ ; simp_all +decide [ grammar_anbncn_indexed ] ;
        · by_cases hdoneA : doneA = true;
          · replace heq := congr_arg ( fun x => ∀ y ∈ x, ∀ σ : List ANBNCN_Flag, y ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.A σ ) heq ; simp_all +decide [ List.mem_append, List.mem_replicate ];
            grind;
          · convert goodForm_step_on_A hja hjb hjc hdB hdC _ _ _;
            exact ANBNCN_Flag.count;
            exact r.rhs;
            exact u;
            exact v;
            exact σ;
            · cases r ; aesop;
            · grind;
            · rw [ List.append_assoc ];
        · rcases doneA with ( _ | _ | _ ) <;> simp_all +decide [ add_assoc ];
          · apply goodForm_step_on_A hja hjb hjc hdB hdC;
            rotate_left;
            convert heq.symm using 1;
            grind;
            rw [ List.append_assoc ];
            cases r ; aesop;
          · replace heq := congr_arg ( fun x => x.map ( fun y => y ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.A ( ANBNCN_Flag.bottom :: σ ) ) ) heq ; simp_all +decide [ List.map_append, List.map_replicate ];
            replace heq := congr_arg List.toFinset heq ; rw [ Finset.ext_iff ] at heq ; specialize heq False ; aesop;
      · by_cases hB : r.lhs = .B;
        · by_cases hC : doneB = true;
          · have h_no_B : ∀ x ∈ replicate ja ia ++ (if doneA then [] else [iA (stk (n - ja))]) ++ replicate jb ib ++ (if doneB then [] else [iB (stk (n - jb))]) ++ replicate jc ic ++ (if doneC then [] else [iC (stk (n - jc))]), ∀ σ, x ≠ IndexedGrammar.ISym.indexed ANBNCN_NT.B σ := by
              grind +splitIndPred;
            cases r_consume : r.consume <;> simp_all +decide;
            · exact False.elim <| h_no_B _ ( Or.inr <| Or.inl rfl ) _ rfl;
            · exact False.elim <| h_no_B _ ( Or.inr <| Or.inl rfl ) _ rfl;
          · cases r_consume : r.consume <;> simp_all +decide;
            · unfold G at hr; simp_all +decide [ grammar_anbncn_indexed ] ;
              rcases hr with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp_all +decide;
            · convert goodForm_step_on_B hja hjb hjc hdA hdC _ _ _;
              exact ‹G.flag›;
              exact r.rhs;
              exact u;
              exact v;
              exact σ;
              · cases r ; aesop;
              · grind;
              · rw [ List.append_assoc ];
        · by_cases hC : r.lhs = .C;
          · by_cases hC' : doneC = true <;> simp_all +decide;
            · cases r_consume : r.consume <;> simp_all +decide;
              · unfold G at hr; simp_all +decide [ grammar_anbncn_indexed ] ;
                rcases hr with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp_all +decide;
              · have := no_C_before_C ja doneA n jb doneB jc hja hjb; simp_all +decide [ List.mem_append, List.mem_replicate ] ;
                exact False.elim <| this _ ( Or.inr <| Or.inl rfl ) _ rfl;
            · cases r_consume : r.consume <;> simp_all +decide [ G ];
              · unfold grammar_anbncn_indexed at hr; aesop;
              · apply goodForm_step_on_C hja hjb hjc hdA hdB;
                rotate_left;
                convert heq.symm using 1;
                grind;
                rw [ List.append_assoc ];
                cases r ; aesop;
          · rcases r with ⟨ lhs, consume, rhs ⟩;
            cases lhs <;> cases consume <;> simp_all +decide [ G ];
            · have := no_S_in_abc_form ja jb jc n doneA doneB doneC hja hjb hjc; simp_all +decide [ List.mem_append, List.mem_replicate ] ;
              exact False.elim <| this _ ( Or.inr <| Or.inl rfl ) _ rfl;
            · cases hr;
              contradiction;
            · have := no_T_in_abc_form ja jb jc n doneA doneB doneC hja hjb hjc;
              simp_all +decide [List.mem_append, List.mem_replicate];
              exact False.elim <| this _ (Or.inr <| Or.inl rfl) _ rfl;
            · cases hr;
              contradiction

private lemma goodForm_step {form form' : List G.ISym}
    (hg : GoodForm form) (ht : G.Transforms form form') : GoodForm form' := by
  cases hg with
  | start => exact goodForm_step_case1 ht
  | withT n => exact goodForm_step_case2 ht
  | withABC n ja jb jc doneA doneB doneC hja hjb hjc hdA hdB hdC =>
    exact goodForm_step_case3 hja hjb hjc hdA hdB hdC ht

private lemma goodForm_derives {form : List G.ISym}
    (hd : G.Derives [iS []] form) : GoodForm form := by
  induction hd with
  | refl => exact GoodForm.start
  | tail _ ht ih => exact goodForm_step ih ht

private lemma goodForm_terminal {w : List (Fin 3)}
    (hg : GoodForm (w.map IndexedGrammar.ISym.terminal)) :
    ∃ n, w = replicate n 0 ++ replicate n 1 ++ replicate n 2 := by
      contrapose hg;
      -- By cases on hg, we can derive a contradiction with the assumption that w is not of the form replicate n 0 ++ replicate n 1 ++ replicate n 2.
      intro h
      obtain ⟨n, hn⟩ : ∃ n : ℕ, w = List.replicate n 0 ++ List.replicate n 1 ++ List.replicate n 2 := by
        have h_form : ∀ {w : List G.ISym}, GoodForm w → (∀ s ∈ w, s ∈ Set.range (fun t : Fin 3 => IndexedGrammar.ISym.terminal t)) → ∃ n : ℕ, w = List.map (fun t : Fin 3 => IndexedGrammar.ISym.terminal t) (List.replicate n 0 ++ List.replicate n 1 ++ List.replicate n 2) := by
          intros w hw hw_terminal
          induction' hw with w hw ih;
          · cases hw_terminal _ ( List.mem_singleton_self _ );
            cases ‹_›;
          · cases hw_terminal _ ( List.mem_singleton_self _ ) ; aesop;
          · split_ifs at hw_terminal <;> simp_all +decide [ Set.range ];
            grind;
            any_goals have := hw_terminal _ ( Or.inr <| Or.inr <| Or.inr <| rfl ) ; obtain ⟨ y, hy ⟩ := this; cases y ; cases hy;
            any_goals have := hw_terminal _ ( Or.inr <| Or.inl rfl ) ; obtain ⟨ y, hy ⟩ := this; cases y ; cases hy;
            · have := hw_terminal _ ( Or.inr <| Or.inr <| Or.inl rfl ) ; obtain ⟨ y, hy ⟩ := this; cases y ; cases hy;
            · have := hw_terminal _ ( Or.inr <| Or.inr <| Or.inl rfl ) ; obtain ⟨ y, hy ⟩ := this; cases y ; cases hy;
        obtain ⟨ n, hn ⟩ := h_form h ( by aesop );
        exact ⟨ n, by simpa using List.map_injective_iff.mpr ( show Function.Injective ( fun t : Fin 3 => IndexedGrammar.ISym.terminal t ) from fun a b h => by cases a ; cases b ; cases h ; trivial ) hn ⟩;
      exact hg ⟨ n, hn ⟩

theorem is_Indexed_lang_eq_eq : is_Indexed lang_eq_eq := by
  refine ⟨G, ?_⟩
  ext w; constructor
  · intro hw
    exact goodForm_terminal (goodForm_derives hw)
  · intro hw
    obtain ⟨n, rfl⟩ := hw
    exact anbncn_generates n

end anbncn
