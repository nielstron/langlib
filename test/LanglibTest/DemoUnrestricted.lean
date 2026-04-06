import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Utilities.ListUtils
import Langlib.Utilities.WrittenByOthers.TrimAssoc

/-! # Unrestricted Grammar Examples

This file contains larger unrestricted-grammar examples used as executable demonstrations.

## Main declarations

- `alphabet`
- `inner`
-/

inductive alphabet
  | _a : alphabet
  | _b : alphabet
  | _c : alphabet

inductive inner
  | _S : inner
  | _L : inner
  | _R : inner
  | _X : inner
  | _B : inner
  | _M : inner
  | _E : inner
  | _C : inner
  | _K : inner

private def a_ := alphabet._a
private def b_ := alphabet._b
private def c_ := alphabet._c

private def S_ := inner._S
private def L_ := inner._L
private def R_ := inner._R
private def X_ := inner._X
private def B_ := inner._B
private def M_ := inner._M
private def E_ := inner._E
private def C_ := inner._C
private def K_ := inner._K

private def my_char : Type := symbol alphabet inner

private def a : my_char := symbol.terminal a_
private def b : my_char := symbol.terminal b_
private def c : my_char := symbol.terminal c_

private def S : my_char := symbol.nonterminal S_
private def L : my_char := symbol.nonterminal L_
private def R : my_char := symbol.nonterminal R_
private def X : my_char := symbol.nonterminal X_
private def B : my_char := symbol.nonterminal B_
private def M : my_char := symbol.nonterminal M_
private def E : my_char := symbol.nonterminal E_
private def C : my_char := symbol.nonterminal C_
private def K : my_char := symbol.nonterminal K_

/-
Grammar for unary multiplication
{ a^m . b^n . c^(m*n) | m n ∈ ℕ }
example   2 * 3 = 6

          S
S → LR
          LR
L → aLX
          aaLXXR
R → BR
          aaLXXBBBR
L → M
          aaMXXBBBR
R → E
          aaMXXBBBE
XB → BCX
CB → BC
XC → CX
          aaMBBBCCCCCCXXE
XE → E
          aaMBBBCCCCCCE
MB → bM
          aabbbMCCCCCCE
M → K
          aabbbKCCCCCCE
KC → cK
          aabbbccccccKE
KE → ∅
          aabbbcccccc
-/

private def my_rule : Type := grule alphabet inner

private def S_LR   : my_rule := grule.mk  [] S_ [] [L, R]
private def L_aLX  : my_rule := grule.mk  [] L_ [] [a, L, X]
private def R_BR   : my_rule := grule.mk  [] R_ [] [B, R]
private def L_M    : my_rule := grule.mk  [] L_ [] [M]
private def R_E    : my_rule := grule.mk  [] R_ [] [E]
private def XB_BCX : my_rule := grule.mk [X] B_ [] [B, C, X]
private def CB_BC  : my_rule := grule.mk [C] B_ [] [B, C]
private def XC_CX  : my_rule := grule.mk [X] C_ [] [C, X]
private def XE_E   : my_rule := grule.mk [X] E_ [] [E]      -- shortens the word
private def MB_bM  : my_rule := grule.mk [M] B_ [] [b, M]
private def M_K    : my_rule := grule.mk  [] M_ [] [K]
private def KC_cK  : my_rule := grule.mk [K] C_ [] [c, K]
private def KE_nil : my_rule := grule.mk [K] E_ [] []       -- shortens the word

private def gr_mul : grammar alphabet :=
  grammar.mk inner S_
    [S_LR, L_aLX, R_BR, L_M, R_E, XB_BCX, CB_BC, XC_CX, XE_E, MB_bM, M_K, KC_cK, KE_nil]

-- grammar_transforms: ∃ r ∈ g.rules, ∃ u v, eq₁ ∧ eq₂
-- After `use rule`: `rule ∈ g.rules ∧ ∃ u v, eq₁ ∧ eq₂`
-- So: refine ⟨rule, ?mem, pref, post, ?eq₁, ?eq₂⟩
macro "grammar_step" rule:term "," pref:term "," post:term : tactic =>
  `(tactic| (
    apply grammar_deri_of_tran_deri
    · refine ⟨$rule, ?_, $pref, $post, ?_, ?_⟩
      · simp [gr_mul]
      · rfl
      · rfl
  ))


-- example 0 * 0 = 0
example : grammar_generates gr_mul [] := by
  grammar_step S_LR, [], []
  grammar_step L_M, [], [R]
  grammar_step R_E, [M], []
  grammar_step M_K, [], [E]
  grammar_step KE_nil, [], []
  apply grammar_deri_self

-- example 1 * 1 = 1
example : grammar_generates gr_mul [a_, b_, c_] := by
  grammar_step S_LR, [], []
  grammar_step L_aLX, [], [R]
  grammar_step R_BR, [a, L, X], []
  grammar_step L_M, [a], [X, B, R]
  grammar_step R_E, [a, M, X, B], []
  grammar_step XB_BCX, [a, M], [E]
  grammar_step XE_E, [a, M, B, C], []
  grammar_step MB_bM, [a], [C, E]
  grammar_step M_K, [a, b], [C, E]
  grammar_step KC_cK, [a, b], [E]
  grammar_step KE_nil, [a, b, c], []
  apply grammar_deri_self

-- example 2 * 1 = 2
example : grammar_generates gr_mul [a_, a_, b_, c_, c_] := by
  grammar_step S_LR, [], []
  grammar_step L_aLX, [], [R]
  grammar_step R_BR, [a, L, X], []
  grammar_step L_aLX, [a], [X, B, R]
  grammar_step L_M, [a, a], [X, X, B, R]
  grammar_step R_E, [a, a, M, X, X, B], []
  grammar_step XB_BCX, [a, a, M, X], [E]
  grammar_step XE_E, [a, a, M, X, B, C], []
  grammar_step XB_BCX, [a, a, M], [C, E]
  grammar_step XC_CX, [a, a, M, B, C], [E]
  grammar_step XE_E, [a, a, M, B, C, C], []
  grammar_step MB_bM, [a, a], [C, C, E]
  grammar_step M_K, [a, a, b], [C, C, E]
  grammar_step KC_cK, [a, a, b], [C, E]
  grammar_step KC_cK, [a, a, b, c], [E]
  grammar_step KE_nil, [a, a, b, c, c], []
  apply grammar_deri_self

-- example 3 * 3 = 9
example : grammar_generates gr_mul
    [a_, a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_, c_, c_, c_] := by
  grammar_step S_LR, [], []
  grammar_step L_aLX, [], [R]
  grammar_step L_aLX, [a], [X, R]
  grammar_step L_aLX, [a, a], [X, X, R]
  grammar_step R_BR, [a, a, a, L, X, X, X], []
  grammar_step R_BR, [a, a, a, L, X, X, X, B], []
  grammar_step R_BR, [a, a, a, L, X, X, X, B, B], []
  grammar_step L_M, [a, a, a], [X, X, X, B, B, B, R]
  grammar_step R_E, [a, a, a, M, X, X, X, B, B, B], []
  grammar_step XB_BCX, [a, a, a, M, X, X], [B, B, E]
  grammar_step XB_BCX, [a, a, a, M, X, X, B, C], [B, E]
  grammar_step XB_BCX, [a, a, a, M, X, X, B, C, B, C], [E]
  grammar_step CB_BC, [a, a, a, M, X, X, B], [C, B, C, X, E]
  grammar_step CB_BC, [a, a, a, M, X, X, B, B, C], [C, X, E]
  grammar_step CB_BC, [a, a, a, M, X, X, B, B], [C, C, X, E]
  grammar_step XB_BCX, [a, a, a, M, X], [B, B, C, C, C, X, E]
  grammar_step XB_BCX, [a, a, a, M, X, B, C], [B, C, C, C, X, E]
  grammar_step XB_BCX, [a, a, a, M, X, B, C, B, C], [C, C, C, X, E]
  grammar_step XC_CX, [a, a, a, M, X, B, C, B, C, B, C], [C, C, X, E]
  grammar_step XC_CX, [a, a, a, M, X, B, C, B, C, B, C, C], [C, X, E]
  grammar_step XC_CX, [a, a, a, M, X, B, C, B, C, B, C, C, C], [X, E]
  grammar_step CB_BC, [a, a, a, M, X, B], [C, B, C, C, C, C, X, X, E]
  grammar_step CB_BC, [a, a, a, M, X, B, B, C], [C, C, C, C, X, X, E]
  grammar_step CB_BC, [a, a, a, M, X, B, B], [C, C, C, C, C, X, X, E]
  grammar_step XB_BCX, [a, a, a, M], [B, B, C, C, C, C, C, C, X, X, E]
  grammar_step XB_BCX, [a, a, a, M, B, C], [B, C, C, C, C, C, C, X, X, E]
  grammar_step XB_BCX, [a, a, a, M, B, C, B, C], [C, C, C, C, C, C, X, X, E]
  grammar_step XC_CX, [a, a, a, M, B, C, B, C, B, C], [C, C, C, C, C, X, X, E]
  grammar_step XC_CX, [a, a, a, M, B, C, B, C, B, C, C], [C, C, C, C, X, X, E]
  grammar_step XC_CX, [a, a, a, M, B, C, B, C, B, C, C, C], [C, C, C, X, X, E]
  grammar_step XC_CX, [a, a, a, M, B, C, B, C, B, C, C, C, C], [C, C, X, X, E]
  grammar_step XC_CX, [a, a, a, M, B, C, B, C, B, C, C, C, C, C], [C, X, X, E]
  grammar_step XC_CX, [a, a, a, M, B, C, B, C, B, C, C, C, C, C, C], [X, X, E]
  grammar_step CB_BC, [a, a, a, M, B], [C, B, C, C, C, C, C, C, C, X, X, X, E]
  grammar_step CB_BC, [a, a, a, M, B, B, C], [C, C, C, C, C, C, C, X, X, X, E]
  grammar_step CB_BC, [a, a, a, M, B, B], [C, C, C, C, C, C, C, C, X, X, X, E]
  -- a^3.M.B^3.C^9.X^3.E
  apply grammar_deri_of_deri_deri
  · show grammar_derives gr_mul
        ([a, a, a, M, B, B, B, C, C, C, C, C, C, C, C, C] ++ [X, X, X, E])
        ([a, a, a, M, B, B, B, C, C, C, C, C, C, C, C, C] ++ [E])
    apply grammar_deri_with_prefix
    grammar_step XE_E, [X, X], []
    grammar_step XE_E, [X], []
    grammar_step XE_E, [], []
    apply grammar_deri_self
  show grammar_derives gr_mul
      ([a, a, a] ++ [M, B, B, B, C, C, C, C, C, C, C, C, C, E])
      ([a, a, a] ++ [b, b, b, c, c, c, c, c, c, c, c, c])
  apply grammar_deri_with_prefix
  grammar_step MB_bM, [], [B, B, C, C, C, C, C, C, C, C, C, E]
  grammar_step MB_bM, [b], [B, C, C, C, C, C, C, C, C, C, E]
  grammar_step MB_bM, [b, b], [C, C, C, C, C, C, C, C, C, E]
  show grammar_derives gr_mul
      ([b, b, b] ++ [M, C, C, C, C, C, C, C, C, C, E])
      ([b, b, b] ++ [c, c, c, c, c, c, c, c, c])
  apply grammar_deri_with_prefix
  grammar_step M_K, [], [C, C, C, C, C, C, C, C, C, E]
  grammar_step KC_cK, [], [C, C, C, C, C, C, C, C, E]
  grammar_step KC_cK, [c], [C, C, C, C, C, C, C, E]
  grammar_step KC_cK, [c, c], [C, C, C, C, C, C, E]
  grammar_step KC_cK, [c, c, c], [C, C, C, C, C, E]
  grammar_step KC_cK, [c, c, c, c], [C, C, C, C, E]
  grammar_step KC_cK, [c, c, c, c, c], [C, C, C, E]
  grammar_step KC_cK, [c, c, c, c, c, c], [C, C, E]
  grammar_step KC_cK, [c, c, c, c, c, c, c], [C, E]
  grammar_step KC_cK, [c, c, c, c, c, c, c, c], [E]
  grammar_step KE_nil, [c, c, c, c, c, c, c, c, c], []
  apply grammar_deri_self


private lemma sub_suc_suc {m n : ℕ} (n_lt_m : n < m) : m - n = (m - n.succ).succ := by
  omega

private lemma steps_L_aLX (m : ℕ) :
    grammar_derives gr_mul [L, R]
      (List.replicate m a ++ [L] ++ List.replicate m X ++ [R]) := by
  induction m with
  | zero => apply grammar_deri_self
  | succ k ih =>
    apply grammar_deri_of_deri_tran ih
    refine ⟨L_aLX, ?_, List.replicate k a, List.replicate k X ++ [R], ?_, ?_⟩
    · simp [gr_mul]
    · simp [L, L_aLX, List.append_nil, List.append_assoc]
    · rw [List.replicate_succ_eq_append_singleton a]
      rw [List.replicate_succ_eq_singleton_append X]
      simp [L, L_aLX, List.append_assoc]

private lemma steps_R_BR (m n : ℕ) :
    grammar_derives gr_mul
      (List.replicate m a ++ [L] ++ List.replicate m X ++ [R])
      (List.replicate m a ++ [L] ++ List.replicate m X ++ List.replicate n B ++ [R]) := by
  induction n with
  | zero =>
    rw [List.replicate_zero, List.append_nil]
    apply grammar_deri_self
  | succ k ih =>
    apply grammar_deri_of_deri_tran ih
    refine ⟨R_BR, ?_,
      List.replicate m a ++ [L] ++ List.replicate m X ++ List.replicate k B, [], ?_, ?_⟩
    · simp [gr_mul]
    · simp [R, R_BR, List.append_nil]
    · rw [List.replicate_succ_eq_append_singleton B]
      simp [R, R_BR, List.append_nil, List.append_assoc]

/-
PROBLEM
`[X] ++ C^k` derives to `C^k ++ [X]` using XC_CX.

PROVIDED SOLUTION
Induct on k. Base: trivial. Step: the word is [X] ++ [C] ++ C^k. Apply XC_CX with u=[], v=C^k to get [C,X] ++ C^k = [C] ++ [X] ++ C^k. Then use grammar_deri_with_prefix [C] on the IH to get [C] ++ C^k ++ [X] = C^(k+1) ++ [X].
-/
private lemma aux_XC_skip (k : ℕ) :
    grammar_derives gr_mul ([X] ++ List.replicate k C) (List.replicate k C ++ [X]) := by
  induction' k with k ih;
  · constructor;
  · -- For the inductive step, we can use the rule XC_CX to replace X with CX.
    have h_step : grammar_transforms gr_mul ([X] ++ [C] ++ List.replicate k C) ([C] ++ [X] ++ List.replicate k C) := by
      use XC_CX, by
        simp +decide [ gr_mul ], [], List.replicate k C
      generalize_proofs at *;
      aesop;
    -- Apply the induction hypothesis to the remaining part of the word.
    have h_ind : grammar_derives gr_mul ([C] ++ [X] ++ List.replicate k C) ([C] ++ List.replicate k C ++ [X]) := by
      convert grammar_deri_with_prefix _ ih using 1;
      all_goals rw [ List.append_assoc ] ;
    simpa [ List.replicate ] using Relation.ReflTransGen.trans ( Relation.ReflTransGen.single h_step ) h_ind

/-
PROBLEM
`C^z ++ [B]` derives to `[B] ++ C^z` by repeatedly applying CB_BC.

PROVIDED SOLUTION
Induct on z. Base (z=0): trivial, grammar_deri_self. Step (z+1): We have C^(z+1) ++ [B]. Using List.replicate_succ_eq_singleton_append, rewrite this as C^z ++ [C] ++ [B] = C^z ++ [C, B]. Wait, actually List.replicate (z+1) C = [C] ++ C^z. So the word is [C] ++ C^z ++ [B].

By IH: C^z ++ [B] derives to [B] ++ C^z. Using grammar_deri_with_prefix [C], we get [C] ++ C^z ++ [B] derives to [C] ++ [B] ++ C^z = [C, B] ++ C^z. Then apply CB_BC (which is grule.mk [C] B_ [] [B, C]) with u=[] and v=C^z to transform [C, B] ++ C^z to [B, C] ++ C^z = [B] ++ [C] ++ C^z = [B] ++ C^(z+1).

For CB_BC: grammar_transforms requires ∃ r ∈ g.rules, ∃ u v, w1 = u ++ r.input_L ++ [nonterminal r.input_N] ++ r.input_R ++ v ∧ w2 = u ++ r.output_string ++ v. For CB_BC (input_L=[C], input_N=B_, input_R=[], output=[B,C]): w1 = u ++ [C] ++ [nonterminal B_] ++ [] ++ v = u ++ [C, B] ++ v.
-/
private lemma aux_CB_bubble (z : ℕ) :
    grammar_derives gr_mul (List.replicate z C ++ [B]) ([B] ++ List.replicate z C) := by
  induction' z with z ih;
  · constructor;
  · have h_step : grammar_derives gr_mul ([C] ++ List.replicate z C ++ [B]) ([C, B] ++ List.replicate z C) := by
      have h_step : grammar_derives gr_mul (List.replicate z C ++ [B]) ([B] ++ List.replicate z C) := by
        assumption;
      have h_step : grammar_derives gr_mul ([C] ++ List.replicate z C ++ [B]) ([C] ++ [B] ++ List.replicate z C) := by
        have := h_step
        convert grammar_deri_with_prefix _ this using 1;
        all_goals rw [ List.append_assoc ] ;
      aesop;
    have h_step2 : grammar_derives gr_mul ([C, B] ++ List.replicate z C) ([B, C] ++ List.replicate z C) := by
      apply grammar_deri_of_tran_deri;
      use CB_BC;
      exact ⟨ by simp +decide [ gr_mul ], [ ], List.replicate z C, rfl, rfl ⟩;
      exact Relation.ReflTransGen.refl;
    convert h_step.trans h_step2 using 1

/-
PROBLEM
`[B,C]^n` derives to `B^n ++ C^n` by bubble-sorting.

PROVIDED SOLUTION
Induct on n. Base: trivial. Step: [B,C]^(n+1) = [B,C] ++ [B,C]^n. By IH, [B,C]^n derives to B^n ++ C^n. So [B,C] ++ [B,C]^n derives to [B,C] ++ B^n ++ C^n via grammar_deri_with_prefix [B,C].

Now we need to show [B,C] ++ B^n ++ C^n derives to B^(n+1) ++ C^(n+1).
Rewrite as [B] ++ [C] ++ B^n ++ C^n = [B] ++ (C^1 ++ B^n) ++ C^n.
Use aux_CB_bubble with appropriate prefix/postfix:
- C^1 ++ B^n: induct (or use aux_CB_bubble) to show [C] ++ B^n derives to...

Wait, aux_CB_bubble shows C^z ++ [B] → [B] ++ C^z. We need to bubble one B past n C's. Actually we need to bubble n B's past one C.

Different approach: We need [C] ++ B^n → B^n ++ [C]. This follows from n applications of CB_BC (which transforms CB → BC). Show: [C] ++ B^n → B^1 ++ [C] ++ B^(n-1) → ... → B^n ++ [C].

Actually let me define this more carefully. We can show by induction on n that C ++ B^n derives to B^n ++ C:
- Base n=0: trivial
- Step: [C,B] ++ B^n. Apply CB_BC with u=[], v=B^n to get [B,C] ++ B^n = [B] ++ [C] ++ B^n. By IH, [C] ++ B^n → B^n ++ [C]. Use prefix [B]: [B] ++ [C] ++ B^n → [B] ++ B^n ++ [C] = B^(n+1) ++ [C].

Then for the main step: [B, C] ++ B^n ++ C^n = [B] ++ ([C] ++ B^n) ++ C^n. Using the above, [C] ++ B^n → B^n ++ [C]. So [B] ++ C ++ B^n ++ C^n → [B] ++ B^n ++ [C] ++ C^n = B^(n+1) ++ C^(n+1).

Use grammar_deri_with_prefix [B] and grammar_deri_with_postfix C^n.
-/
private lemma aux_BC_sort (n : ℕ) :
    grammar_derives gr_mul ([B, C] ^ n) (List.replicate n B ++ List.replicate n C) := by
  -- By induction on $n$, we can show that $[C] ++ B^n$ derives to $B^n ++ [C]$.
  have h_ind : ∀ n : ℕ, grammar_derives gr_mul ([C] ++ List.replicate n B) (List.replicate n B ++ [C]) := by
    intro n;
    induction n <;> simp_all +decide [ List.replicate_succ' ];
    · constructor;
    · rename_i n ih;
      apply grammar_deri_of_deri_deri;
      convert grammar_deri_with_postfix _ ih using 1;
      convert grammar_deri_with_prefix _ ( aux_CB_bubble 1 ) using 1 ; simp +decide [ List.replicate ];
  induction n <;> simp_all +decide [ ← List.append_assoc, List.n_times ];
  · constructor;
  · rename_i n ih;
    -- By the induction hypothesis, we can derive $B^n ++ C^n$ from $[B, C]^n$.
    have h_step : grammar_derives gr_mul ([B, C] ++ (List.replicate n [B, C]).flatten) ([B, C] ++ (List.replicate n B ++ List.replicate n C)) := by
      apply grammar_deri_with_prefix; assumption;
    -- Apply the induction hypothesis to derive $B^n ++ C^n ++ [C]$ from $[C] ++ B^n ++ C^n$.
    have h_step2 : grammar_derives gr_mul ([B] ++ ([C] ++ (List.replicate n B ++ List.replicate n C))) ([B] ++ (List.replicate n B ++ [C] ++ List.replicate n C)) := by
      apply grammar_deri_with_prefix;
      convert grammar_deri_with_postfix _ ( h_ind n ) using 1;
    convert h_step.trans ( h_step2 ) using 1;
    exact Nat.recOn n ( by trivial ) fun n ih => by simp_all +decide [ List.replicate ] ;

/-
PROBLEM
`[X] ++ B^n` derives to `[B,C]^n ++ [X]` using XB_BCX.

PROVIDED SOLUTION
Induct on n. Base: trivial. Step: [X] ++ B^(n+1) = [X] ++ [B] ++ B^n. Apply XB_BCX (input_L=[X], input_N=B_, input_R=[], output=[B,C,X]) with u=[] and v=B^n to get [B,C,X] ++ B^n. Then use grammar_deri_with_prefix [B,C] on the IH to get [B,C] ++ [B,C]^n ++ [X] = [B,C]^(n+1) ++ [X].

Note: [B,C] ^ n means List.n_times [B, C] n = (List.replicate n [B, C]).flatten. And [B,C] ^ (n+1) = [B,C] ++ [B,C]^n. Check: List.n_times uses (List.replicate n l).flatten, so List.n_times [B,C] (n+1) = (List.replicate (n+1) [B,C]).flatten = ([B,C] :: List.replicate n [B,C]).flatten = [B,C] ++ (List.replicate n [B,C]).flatten = [B,C] ++ [B,C]^n.
-/
private lemma aux_XB_expand (n : ℕ) :
    grammar_derives gr_mul ([X] ++ List.replicate n B) ([B, C] ^ n ++ [X]) := by
  induction' n with n ih <;> simp_all +decide [ List.replicate_succ ];
  · exact?;
  · -- Apply `XB_BCX` to get `[B, C, X] ++ B^n`.
    have h_trans_XB_BCX : grammar_derives gr_mul ([X] ++ B :: List.replicate n B) ([B, C, X] ++ List.replicate n B) := by
      apply grammar_deri_of_deri_tran;
      apply grammar_deri_self;
      refine' ⟨ XB_BCX, _, _ ⟩ <;> simp +decide [ gr_mul ];
      exists [ ], List.replicate n B;
    -- Apply `grammar_deri_with_prefix` to get `[B, C] ++ [B, C]^n ++ [X]`.
    have h_trans_prefix : grammar_derives gr_mul ([B, C] ++ X :: List.replicate n B) ([B, C] ++ [B, C] ^ n ++ [X]) := by
      apply grammar_deri_with_prefix; assumption;
    convert h_trans_XB_BCX.trans h_trans_prefix using 1

/-
PROBLEM
The core of steps_quadratic: `X^m ++ B^n` derives to `B^n ++ C^(m*n) ++ X^m`.

PROVIDED SOLUTION
Induct on m. Base m=0: trivial (zero_mul, deri_self). Step m+1: X^(m+1) ++ B^n = [X] ++ X^m ++ B^n.

By IH: X^m ++ B^n derives to B^n ++ C^(m*n) ++ X^m. Use grammar_deri_with_prefix [X]:
[X] ++ X^m ++ B^n derives to [X] ++ B^n ++ C^(m*n) ++ X^m.

Now apply aux_XB_expand with prefix [] and postfix C^(m*n) ++ X^m:
[X] ++ B^n ++ C^(m*n) ++ X^m derives to [B,C]^n ++ [X] ++ C^(m*n) ++ X^m.
(Use grammar_deri_with_postfix for the C^(m*n) ++ X^m part.)

Then apply aux_BC_sort with postfix [X] ++ C^(m*n) ++ X^m:
[B,C]^n ++ [X] ++ C^(m*n) ++ X^m derives to B^n ++ C^n ++ [X] ++ C^(m*n) ++ X^m.
(Use grammar_deri_with_postfix.)

Then apply aux_XC_skip (m*n) with prefix B^n ++ C^n and postfix X^m:
B^n ++ C^n ++ [X] ++ C^(m*n) ++ X^m derives to B^n ++ C^n ++ C^(m*n) ++ [X] ++ X^m.
(Use grammar_deri_with_prefix and grammar_deri_with_postfix.)

Finally: B^n ++ C^n ++ C^(m*n) ++ [X] ++ X^m = B^n ++ C^((m+1)*n) ++ X^(m+1).
(Use (m+1)*n = n + m*n and List.replicate_add, and X^(m+1) = [X] ++ X^m = List.replicate (m+1) X.)
-/
private lemma aux_quadratic_core (m n : ℕ) :
    grammar_derives gr_mul
      (List.replicate m X ++ List.replicate n B)
      (List.replicate n B ++ List.replicate (m * n) C ++ List.replicate m X) := by
  induction' m with m ih generalizing n <;> simp_all +decide [ Nat.succ_mul, add_assoc ];
  · exact Relation.ReflTransGen.refl;
  · -- Apply the induction hypothesis to the first part of the list.
    have h_ind : grammar_derives gr_mul ([X] ++ List.replicate m X ++ List.replicate n B) ([X] ++ List.replicate n B ++ List.replicate (m * n) C ++ List.replicate m X) := by
      convert grammar_deri_with_prefix _ ( ih n ) using 1;
      rw [ ← List.append_assoc ];
      rw [ ← List.append_assoc, ← List.append_assoc ];
    -- Apply the rule `XB_BCX` to get `[B, C]^n ++ [X] ++ C^(m*n) ++ X^m`.
    have h_expand : grammar_derives gr_mul ([X] ++ List.replicate n B ++ List.replicate (m * n) C ++ List.replicate m X) ([B, C] ^ n ++ [X] ++ List.replicate (m * n) C ++ List.replicate m X) := by
      have h_expand : grammar_derives gr_mul ([X] ++ List.replicate n B) ([B, C] ^ n ++ [X]) := by
        exact?;
      apply_rules [ grammar_deri_with_postfix, grammar_deri_with_prefix ];
    -- Apply the rule `CB_BC` to get `B^n ++ C^n ++ [X] ++ C^(m*n) ++ X^m`.
    have h_sort : grammar_derives gr_mul ([B, C] ^ n ++ [X] ++ List.replicate (m * n) C ++ List.replicate m X) (List.replicate n B ++ List.replicate n C ++ [X] ++ List.replicate (m * n) C ++ List.replicate m X) := by
      have h_sort : grammar_derives gr_mul ([B, C] ^ n) (List.replicate n B ++ List.replicate n C) := by
        exact?;
      apply_rules [ grammar_deri_with_postfix ];
    -- Apply the rule `XC_CX` to get `B^n ++ C^n ++ C^(m*n) ++ [X] ++ X^m`.
    have h_skip : grammar_derives gr_mul (List.replicate n B ++ List.replicate n C ++ [X] ++ List.replicate (m * n) C ++ List.replicate m X) (List.replicate n B ++ List.replicate n C ++ List.replicate (m * n) C ++ [X] ++ List.replicate m X) := by
      have h_skip : grammar_derives gr_mul ([X] ++ List.replicate (m * n) C) (List.replicate (m * n) C ++ [X]) := by
        exact?;
      convert grammar_deri_with_prefix _ ( grammar_deri_with_postfix _ h_skip ) using 1 ; simp +decide [ List.append_assoc ];
      rotate_left;
      rotate_left;
      exact List.replicate n B ++ List.replicate n C;
      exact List.replicate m X;
      · rw [ List.append_assoc ];
      · grind;
    grind +suggestions

/-
PROVIDED SOLUTION
Use grammar_deri_with_prefix (for List.replicate m a ++ [M]) and grammar_deri_with_postfix (for [E]) to reduce to aux_quadratic_core m n. The key is just reassociating the list appends to match the shape.
-/
private lemma steps_quadratic (m n : ℕ) :
    grammar_derives gr_mul
      (List.replicate m a ++ [M] ++ List.replicate m X ++ List.replicate n B ++ [E])
      (List.replicate m a ++ [M] ++ List.replicate n B ++ List.replicate (m * n) C ++
        List.replicate m X ++ [E]) := by
  -- Apply the lemma `aux_quadratic_core` with $m$ and $n$.
  have h_aux : grammar_derives gr_mul (List.replicate m X ++ List.replicate n B) (List.replicate n B ++ List.replicate (m * n) C ++ List.replicate m X) := by
    exact?;
  -- Apply the lemma `grammar_deri_with_prefix` with $pᵣ = List.replicate m a ++ [M]$ and `ass = h_aux`.
  have h_prefix : grammar_derives gr_mul (List.replicate m a ++ [M] ++ List.replicate m X ++ List.replicate n B) (List.replicate m a ++ [M] ++ List.replicate n B ++ List.replicate (m * n) C ++ List.replicate m X) := by
    convert grammar_deri_with_prefix _ h_aux using 1;
    all_goals rw [ ← List.append_assoc ] ;
    rw [ ← List.append_assoc ];
  -- Apply the lemma `grammar_deri_with_postfix` with `po = [E]` and `ass = h_prefix`.
  apply grammar_deri_with_postfix; assumption

/-
PROVIDED SOLUTION
Same pattern as steps_KC_cK and steps_MB_bM. First use grammar_deri_with_prefix (for the prefix List.replicate m a ++ [M] ++ List.replicate n B ++ List.replicate (m*n) C) to reduce to showing List.replicate m X ++ [E] derives to [E]. Induct on k ≤ m: at step k, the word is List.replicate (m-k) X ++ [E], and we apply XE_E to consume one X, getting List.replicate (m-k-1) X ++ [E]. At k=m we get [E].
-/
private lemma steps_XE_E (m n : ℕ) :
    grammar_derives gr_mul
      (List.replicate m a ++ [M] ++ List.replicate n B ++ List.replicate (m * n) C ++
        List.replicate m X ++ [E])
      (List.replicate m a ++ [M] ++ List.replicate n B ++ List.replicate (m * n) C ++ [E]) := by
  -- Apply the lemma `steps_XE_E` with `k = m`.
  have h_derive : grammar_derives gr_mul (List.replicate m X ++ [E]) [E] := by
    induction' m with m ih;
    · constructor;
    · -- Apply the rule XE_E to transform [X] ++ [E] into [E].
      have h_step : grammar_derives gr_mul ([X] ++ (List.replicate m X ++ [E])) [E] := by
        apply grammar_deri_of_deri_deri;
        apply grammar_deri_with_prefix;
        exact ih;
        constructor;
        constructor;
        exact ⟨ XE_E, by simp +decide [ gr_mul ], [ ], [ ], rfl, rfl ⟩;
      exact h_step;
  convert grammar_deri_with_prefix _ h_derive using 1;
  simp +decide [ List.append_assoc ]

/-
PROVIDED SOLUTION
Use grammar_deri_with_postfix twice (for C^(m*n) and [E]) and grammar_deri_with_prefix (for a^m) to reduce to showing [M] ++ List.replicate n B derives to List.replicate n b ++ [M]. Then induct on n: each step applies MB_bM to turn the leftmost B into b and shift M right. At step k, the word is List.replicate k b ++ [M] ++ List.replicate (n-k) B. Use sub_suc_suc and List.replicate_succ_eq_append_singleton/List.replicate_succ_eq_singleton_append for index arithmetic.
-/
private lemma steps_MB_bM (m n : ℕ) :
    grammar_derives gr_mul
      (List.replicate m a ++ [M] ++ List.replicate n B ++ List.replicate (m * n) C ++ [E])
      (List.replicate m a ++ List.replicate n b ++ [M] ++ List.replicate (m * n) C ++ [E]) := by
  -- The first step is to apply the MB_bM rule to the leftmost B in the string.
  have h_step1 : ∀ k : ℕ, k < n → grammar_derives gr_mul (List.replicate m a ++ List.replicate k b ++ [M] ++ List.replicate (n - k) B ++ List.replicate (m * n) C ++ [E]) (List.replicate m a ++ List.replicate (k + 1) b ++ [M] ++ List.replicate (n - (k + 1)) B ++ List.replicate (m * n) C ++ [E]) := by
    intro k hk
    have h_step1 : grammar_transforms gr_mul (List.replicate m _root_.a ++ List.replicate k b ++ [M] ++ List.replicate (n - k) B ++ List.replicate (m * n) C ++ [E]) (List.replicate m _root_.a ++ List.replicate (k + 1) b ++ [M] ++ List.replicate (n - (k + 1)) B ++ List.replicate (m * n) C ++ [E]) := by
      use MB_bM
      generalize_proofs at *;
      unfold gr_mul; simp +decide [ MB_bM ] ;
      refine' ⟨ List.replicate m a ++ List.replicate k b, List.replicate ( n - ( k + 1 ) ) B ++ List.replicate ( m * n ) C ++ [ E ], _, _ ⟩ <;> simp +decide [ ← List.append_assoc, Nat.sub_sub ] ; ring!; (
      rw [ show n - k = 1 + ( n - ( 1 + k ) ) by omega, List.replicate_add ] ; aesop;);
      grind +suggestions
    generalize_proofs at *;
    exact .single h_step1
  generalize_proofs at *;
  -- By induction on $k$, we can apply the MB_bM rule $n$ times to transform the string.
  have h_ind : ∀ k : ℕ, k ≤ n → grammar_derives gr_mul (List.replicate m a ++ [M] ++ List.replicate n B ++ List.replicate (m * n) C ++ [E]) (List.replicate m a ++ List.replicate k b ++ [M] ++ List.replicate (n - k) B ++ List.replicate (m * n) C ++ [E]) := by
    intro k hk; induction' k with k ih <;> simp_all +decide ;
    · constructor;
    · exact grammar_deri_of_deri_deri ( ih hk.le ) ( h_step1 k hk );
  simpa using h_ind n le_rfl

/-
PROVIDED SOLUTION
Same pattern as steps_MB_bM. Use grammar_deri_with_postfix (for [E]) and grammar_deri_with_prefix (for a^m ++ b^n) to reduce to showing [K] ++ List.replicate (m*n) C derives to List.replicate (m*n) c ++ [K]. Induct: at step k, word is List.replicate k c ++ [K] ++ List.replicate (m*n - k) C. Apply KC_cK to get List.replicate (k+1) c ++ [K] ++ List.replicate (m*n - k - 1) C.
-/
private lemma steps_KC_cK (m n : ℕ) :
    grammar_derives gr_mul
      (List.replicate m a ++ List.replicate n b ++ [K] ++ List.replicate (m * n) C ++ [E])
      (List.replicate m a ++ List.replicate n b ++ List.replicate (m * n) c ++ [K] ++ [E]) := by
  -- By induction on $k$, we can show that $K C^k$ derives to $c^k K$.
  have h_ind : ∀ k : ℕ, grammar_derives gr_mul ([K] ++ List.replicate k C) (List.replicate k c ++ [K]) := by
    intro k
    induction' k with k ih
    · exact grammar_deri_self
    ·
      -- Apply the KC_cK rule to the first C in the list.
      have h_step : grammar_transforms gr_mul ([K] ++ List.replicate (k + 1) C) (List.replicate 1 c ++ [K] ++ List.replicate k C) := by
        use KC_cK; simp [gr_mul];
        exact ⟨ [ ], List.replicate k C, rfl, rfl ⟩;
      have h_step : grammar_derives gr_mul (List.replicate 1 c ++ [K] ++ List.replicate k C) (List.replicate 1 c ++ List.replicate k c ++ [K]) := by
        have h_step : grammar_derives gr_mul ([K] ++ List.replicate k C) (List.replicate k c ++ [K]) := by
          assumption;
        convert grammar_deri_with_prefix _ h_step using 1;
        all_goals rw [ List.append_assoc ] ;
      convert grammar_deri_of_deri_deri _ _ using 1;
      exact List.replicate 1 c ++ [ K ] ++ List.replicate k C;
      · exact?;
      · convert h_step using 1;
  convert grammar_deri_with_prefix _ ( grammar_deri_with_postfix _ ( h_ind ( m * n ) ) ) using 1;
  rotate_left;
  rotate_left;
  exacts [ List.replicate m a ++ List.replicate n b, [ E ], by simp +decide [ List.append_assoc ], by simp +decide [ List.append_assoc ] ]

-- example 3 * 3 = 9 reproved using the new lemmata
example : grammar_generates gr_mul
    [a_, a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_, c_, c_, c_] := by
  grammar_step S_LR, [], []
  apply grammar_deri_of_deri_deri (steps_L_aLX 3)
  apply grammar_deri_of_deri_deri (steps_R_BR 3 3)
  grammar_step L_M, [a, a, a], [X, X, X, B, B, B, R]
  grammar_step R_E, [a, a, a, M, X, X, X, B, B, B], []
  apply grammar_deri_of_deri_deri (steps_quadratic 3 3)
  apply grammar_deri_of_deri_deri (steps_XE_E 3 3)
  apply grammar_deri_of_deri_deri (steps_MB_bM 3 3)
  grammar_step M_K, [a, a, a, b, b, b], [C, C, C, C, C, C, C, C, C, E]
  apply grammar_deri_of_deri_deri (steps_KC_cK 3 3)
  apply grammar_deri_of_tran
  · refine ⟨KE_nil, ?_, [a, a, a, b, b, b, c, c, c, c, c, c, c, c, c], [], ?_, ?_⟩
    · simp [gr_mul]
    · rfl
    · rfl

-- example 7 * 11 = 77
example : grammar_generates gr_mul
    (List.replicate 7 a_ ++ List.replicate 11 b_ ++ List.replicate 77 c_) := by
  grammar_step S_LR, [], []
  apply grammar_deri_of_deri_deri (steps_L_aLX 7)
  apply grammar_deri_of_deri_deri (steps_R_BR 7 11)
  grammar_step L_M, (List.replicate 7 a), (List.replicate 7 X ++ List.replicate 11 B ++ [R])
  grammar_step R_E, (List.replicate 7 a ++ [M] ++ List.replicate 7 X ++ List.replicate 11 B), []
  apply grammar_deri_of_deri_deri (steps_quadratic 7 11)
  apply grammar_deri_of_deri_deri (steps_XE_E 7 11)
  apply grammar_deri_of_deri_deri (steps_MB_bM 7 11)
  grammar_step M_K, (List.replicate 7 a ++ List.replicate 11 b), (List.replicate 77 C ++ [E])
  apply grammar_deri_of_deri_deri (steps_KC_cK 7 11)
  apply grammar_deri_of_tran
  · refine ⟨KE_nil, ?_,
      (List.replicate 7 a ++ List.replicate 11 b ++ List.replicate 77 c), [], ?_, ?_⟩
    · simp [gr_mul]
    · rfl
    · rfl

/-
PROVIDED SOLUTION
Follow these steps:
1. Apply S_LR with u=[], v=[] to get [L, R]
2. Apply grammar_deri_of_deri_deri (steps_L_aLX m) to get a^m ++ [L] ++ X^m ++ [R]
3. Apply grammar_deri_of_deri_deri (steps_R_BR m n) to get a^m ++ [L] ++ X^m ++ B^n ++ [R]
4. Apply L_M with u=a^m, v=X^m ++ B^n ++ [R] to get a^m ++ [M] ++ X^m ++ B^n ++ [R]
5. Apply R_E with u=a^m ++ [M] ++ X^m ++ B^n, v=[] to get a^m ++ [M] ++ X^m ++ B^n ++ [E]
6. Apply grammar_deri_of_deri_deri (steps_quadratic m n) to get a^m ++ [M] ++ B^n ++ C^(m*n) ++ X^m ++ [E]
7. Apply grammar_deri_of_deri_deri (steps_XE_E m n) to get a^m ++ [M] ++ B^n ++ C^(m*n) ++ [E]
8. Apply grammar_deri_of_deri_deri (steps_MB_bM m n) to get a^m ++ b^n ++ [M] ++ C^(m*n) ++ [E]
9. Apply M_K with u=a^m ++ b^n, v=C^(m*n) ++ [E] to get a^m ++ b^n ++ [K] ++ C^(m*n) ++ [E]
10. Apply grammar_deri_of_deri_deri (steps_KC_cK m n) to get a^m ++ b^n ++ c^(m*n) ++ [K] ++ [E]
11. Apply KE_nil with u=a^m ++ b^n ++ c^(m*n), v=[] to finish.

For steps 4, 5, 9, 11: use grammar_deri_of_tran_deri or grammar_deri_of_tran with refine ⟨rule, ?_, pref, post, ?_, ?_⟩ and simp [gr_mul] for membership, rfl for the equations. Some steps may need simp for list reassociation.
-/
private theorem multiplication_complete (m n : ℕ) :
    grammar_generates gr_mul
      (List.replicate m a_ ++ List.replicate n b_ ++ List.replicate (m * n) c_) := by
  have h_rules : grammar_derives gr_mul [S] (List.replicate m a ++ [M] ++ List.replicate m X ++ List.replicate n B ++ [E]) := by
    -- Apply the rules in sequence to derive the target string.
    have h_seq : grammar_derives gr_mul [S] (List.replicate m a ++ [L] ++ List.replicate m X ++ [R]) := by
      -- Apply the step_L_aLX lemma with m to get the desired derivation.
      have h_step1 : grammar_derives gr_mul [S] (List.replicate m a ++ [L] ++ List.replicate m X ++ [R]) := by
        have h_step1 : grammar_derives gr_mul [S] [L, R] := by
          apply Relation.ReflTransGen.single;
          use S_LR; simp +decide [gr_mul] ;
          exists [ ], [ ]
        exact h_step1.trans ( steps_L_aLX m )
      generalize_proofs at *; (
      assumption);
    have h_seq2 : grammar_derives gr_mul (List.replicate m a ++ [L] ++ List.replicate m X ++ [R]) (List.replicate m a ++ [L] ++ List.replicate m X ++ List.replicate n B ++ [R]) := by
      exact?;
    have h_seq3 : grammar_derives gr_mul (List.replicate m a ++ [L] ++ List.replicate m X ++ List.replicate n B ++ [R]) (List.replicate m a ++ [M] ++ List.replicate m X ++ List.replicate n B ++ [R]) := by
      apply grammar_deri_of_tran;
      use L_M; simp [gr_mul];
      exact ⟨ List.replicate m a, List.replicate m X ++ ( List.replicate n B ++ [ R ] ), rfl, rfl ⟩;
    have h_seq4 : grammar_derives gr_mul (List.replicate m a ++ [M] ++ List.replicate m X ++ List.replicate n B ++ [R]) (List.replicate m a ++ [M] ++ List.replicate m X ++ List.replicate n B ++ [E]) := by
      apply grammar_deri_of_tran_deri
      use R_E
      simp [gr_mul];
      rotate_right;
      exact List.replicate m a ++ [ M ] ++ List.replicate m X ++ List.replicate n B ++ [ E ];
      · exists List.replicate m a ++ [ M ] ++ List.replicate m X ++ List.replicate n B, [ ];
        aesop;
      · constructor;
    exact h_seq.trans ( h_seq2.trans ( h_seq3.trans h_seq4 ) );
  have h_rules : grammar_derives gr_mul (List.replicate m a ++ [M] ++ List.replicate m X ++ List.replicate n B ++ [E]) (List.replicate m a ++ List.replicate n b ++ [M] ++ List.replicate (m * n) C ++ [E]) := by
    apply grammar_deri_of_deri_deri (steps_quadratic m n)
    apply grammar_deri_of_deri_deri (steps_XE_E m n)
    apply steps_MB_bM m n;
  have h_rules : grammar_derives gr_mul (List.replicate m a ++ List.replicate n b ++ [M] ++ List.replicate (m * n) C ++ [E]) (List.replicate m a ++ List.replicate n b ++ List.replicate (m * n) c ++ [K] ++ [E]) := by
    have h_rules : grammar_derives gr_mul (List.replicate m a ++ List.replicate n b ++ [K] ++ List.replicate (m * n) C ++ [E]) (List.replicate m a ++ List.replicate n b ++ List.replicate (m * n) c ++ [K] ++ [E]) := by
      exact?;
    apply grammar_deri_of_deri_deri;
    rotate_right;
    exact List.replicate m a ++ List.replicate n b ++ [K] ++ List.replicate ( m * n ) C ++ [ E ];
    · apply grammar_deri_of_tran;
      use M_K;
      simp +decide [ gr_mul ];
      exact ⟨ List.replicate m a ++ List.replicate n b, List.replicate ( m * n ) C ++ [ E ], by aesop ⟩;
    · assumption;
  have h_rules : grammar_derives gr_mul (List.replicate m a ++ List.replicate n b ++ List.replicate (m * n) c ++ [K] ++ [E]) (List.replicate m a ++ List.replicate n b ++ List.replicate (m * n) c) := by
    apply grammar_deri_of_tran_deri
    use KE_nil
    simp [gr_mul];
    rotate_right;
    exact List.replicate m a ++ List.replicate n b ++ List.replicate ( m * n ) c;
    · exists List.replicate m a ++ List.replicate n b ++ List.replicate ( m * n ) c, [ ];
      aesop;
    · apply grammar_deri_self;
  convert Relation.ReflTransGen.trans ‹grammar_derives gr_mul [ S ] _› ( Relation.ReflTransGen.trans ‹_› ( Relation.ReflTransGen.trans ‹_› ‹_› ) ) using 1;
  unfold grammar_generates; aesop;

-- example 3 * 3 = 9 reproved using the new theorem
example : grammar_generates gr_mul
    [a_, a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_, c_, c_, c_] := by
  exact multiplication_complete 3 3

-- example 1001 * 587 = 587587
example : grammar_generates gr_mul
    (List.replicate 1001 a_ ++ List.replicate 587 b_ ++ List.replicate 587587 c_) := by
  have pe : 587587 = 1001 * 587 := by norm_num
  rw [pe]
  apply multiplication_complete