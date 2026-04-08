import Langlib.Grammars.ContextFree.Toolbox
import Mathlib
import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

/-! # Intersection of Context-Free and Regular Languages

This file proves that the intersection of a context-free language with a regular language
is context-free. This is a classic result in formal language theory, proved via the
product construction of a CFG and a DFA.

## Main declarations

- `CF_of_CF_inter_regular` : the main theorem
- `productGrammar` : the product CFG×DFA grammar construction
-/

open Classical

noncomputable section

variable {T : Type}

-- ============================================================================
-- Step-counted derivations for CF_grammar
-- ============================================================================

/-- `CF_derivesIn g n w₁ w₂` means `g` transforms `w₁` to `w₂` in exactly `n` steps.
    Uses tail convention (matching ReflTransGen). -/
inductive CF_derivesIn (g : CF_grammar T) :
    ℕ → List (symbol T g.nt) → List (symbol T g.nt) → Prop
  | refl (w) : CF_derivesIn g 0 w w
  | tail {n w₁ w₂ w₃} :
      CF_derivesIn g n w₁ w₂ → CF_transforms g w₂ w₃ → CF_derivesIn g (n + 1) w₁ w₃

variable {g : CF_grammar T}

lemma CF_derivesIn_of_derives {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_derives g w₁ w₂) : ∃ n, CF_derivesIn g n w₁ w₂ := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | tail _ htran ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .tail hn htran⟩

/-
PROVIDED SOLUTION
By induction on h. Base case (refl): reflexivity. Tail case: use ih and then apply the transform step using CF_deri_of_deri_tran.
-/
lemma CF_derives_of_derivesIn {n : ℕ} {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_derivesIn g n w₁ w₂) : CF_derives g w₁ w₂ := by
  induction' h with n w₁ w₂ h ih;
  · constructor;
  · exact?

/-
PROVIDED SOLUTION
By induction on h₂. Base case: h₁ with n+0=n. Tail case: apply tail to ih and the transform step, adjusting the step count.
-/
lemma CF_derivesIn_trans {n m : ℕ} {w₁ w₂ w₃ : List (symbol T g.nt)}
    (h₁ : CF_derivesIn g n w₁ w₂) (h₂ : CF_derivesIn g m w₂ w₃) :
    CF_derivesIn g (n + m) w₁ w₃ := by
  induction h₂;
  · exact h₁;
  · rename_i k w₁ w₂ w₃ h₁ h₂ ih; exact ih h₁ |> fun h => h.tail ( by tauto ) ;

/-
PROBLEM
Head extraction: an (n+1)-step derivation starts with one step.

PROVIDED SOLUTION
By induction on n. For n=0, the derivation must be tail of a 0-step (refl) derivation followed by a transform. For n+1, use the inductive hypothesis to extract the first step from the (n+1)-step prefix, then reattach the last step.
-/
lemma CF_derivesIn_head {n : ℕ} {w₁ w₃ : List (symbol T g.nt)}
    (h : CF_derivesIn g (n + 1) w₁ w₃) :
    ∃ w₂, CF_transforms g w₁ w₂ ∧ CF_derivesIn g n w₂ w₃ := by
  revert h;
  induction' n with n ih generalizing w₁ w₃;
  · rintro ⟨ w₂, h₂ ⟩;
    rename_i h₁ h₂;
    cases h₁;
    exact ⟨ _, h₂, CF_derivesIn.refl _ ⟩;
  · rintro ⟨ w₂, hw₂ ⟩;
    obtain ⟨ w₂, hw₂₁, hw₂₂ ⟩ := ih ‹_›;
    exact ⟨ w₂, hw₂₁, by exact CF_derivesIn.tail hw₂₂ ‹_› ⟩

/-
PROBLEM
Adding a prefix preserves step count.

PROVIDED SOLUTION
By induction on h. Base (refl): use refl. Tail: use ih, then apply the transform with the prefix prepended to u and v (same as CF_deri_with_prefix pattern).
-/
lemma CF_derivesIn_append_left {n : ℕ} {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_derivesIn g n w₁ w₂) (pfx : List (symbol T g.nt)) :
    CF_derivesIn g n (pfx ++ w₁) (pfx ++ w₂) := by
  induction' h with pfx hw₁ hw₂ hpfx hw₁ hw₂ hpfx' hw₁' hw₂' ih;
  · constructor;
  · obtain ⟨ r, u, v, hr, rfl, rfl ⟩ := hpfx';
    exact CF_derivesIn.tail hw₁' ⟨ r, pfx ++ u, v, hr, by simp +decide [ List.append_assoc ], by simp +decide [ List.append_assoc ] ⟩

/-
PROBLEM
Adding a postfix preserves step count.

PROVIDED SOLUTION
By induction on h. Base (refl): use refl. Tail: use ih, then apply the transform with the suffix appended (same as CF_deri_with_postfix pattern).
-/
lemma CF_derivesIn_append_right {n : ℕ} {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_derivesIn g n w₁ w₂) (sfx : List (symbol T g.nt)) :
    CF_derivesIn g n (w₁ ++ sfx) (w₂ ++ sfx) := by
  induction' n with n ih generalizing w₁ w₂ sfx;
  · cases h ; tauto;
  · rcases h with ⟨ w₃, h₁, h₂ ⟩;
    obtain ⟨ r, u, v, hr, rfl, rfl ⟩ := ‹CF_transforms g _ _›;
    exact CF_derivesIn.tail ( ih ‹_› sfx ) ( by unfold CF_transforms; aesop )

/-
PROBLEM
Key splitting lemma: a derivation from `p ++ q` can be split into
    independent derivations from `p` and `q` with step counts adding up.

PROVIDED SOLUTION
By induction on n.
Base case (n=0): h gives p ++ q = w, so w = p ++ q. Use n₁=0, n₂=0, x=p, y=q with refl derivations.
Step case (n=k+1): By h, we have CF_derivesIn g k (p++q) w' and CF_transforms g w' w for some w'.
By the induction hypothesis, w' = x' ++ y' with p ⇒^n₁' x' and q ⇒^n₂' y' and k = n₁' + n₂'.
The transform w' → w applies a rule at some position in w' = x' ++ y'. The rule replaces a nonterminal at some position. This position is either in x' (left part) or y' (right part).
- If the rule position is in x' (the nonterminal being replaced is in x'), then the transform produces x'' from x' and y remains y'. So w = x'' ++ y', with p ⇒^(n₁'+1) x'' and q ⇒^n₂' y'.
- If the rule position is in y', similarly w = x' ++ y'', with p ⇒^n₁' x' and q ⇒^(n₂'+1) y''.
To determine which side, check if the position of the replaced nonterminal (given by u in the transform) has length < x'.length. Use List.append_eq_append_iff or similar to split the append.

This is exactly the same pattern as the existing head_tail_split proof in Splitting.lean and DerivesIn.append_split in CountingSteps.lean. Follow the same case analysis on whether the rule application falls in the left or right part of the concatenation.
-/
lemma CF_derivesIn_append_split {n : ℕ} {p q w : List (symbol T g.nt)}
    (h : CF_derivesIn g n (p ++ q) w) :
    ∃ x y n₁ n₂, w = x ++ y ∧
      CF_derivesIn g n₁ p x ∧ CF_derivesIn g n₂ q y ∧ n = n₁ + n₂ := by
  revert h;
  induction' n with n ih generalizing p q w;
  · rintro ⟨ ⟩;
    exact ⟨ p, q, 0, 0, rfl, CF_derivesIn.refl _, CF_derivesIn.refl _, rfl ⟩;
  · intro h;
    obtain ⟨w', hw'⟩ : ∃ w' : List (symbol T g.nt), CF_derivesIn g n (p ++ q) w' ∧ CF_transforms g w' w := by
      cases h ; aesop;
    obtain ⟨ x, y, n₁, n₂, hw', hx, hy, hn ⟩ := ih hw'.1;
    obtain ⟨ r, u, v, hr, hw₁, hw₂ ⟩ := ‹CF_derivesIn g n ( p ++ q ) w' ∧ CF_transforms g w' w›.2;
    by_cases h : u.length < x.length;
    · -- Since $u.length < x.length$, we can split $x$ into $u$ and some remainder $x'$.
      obtain ⟨x', hx'⟩ : ∃ x', x = u ++ [symbol.nonterminal r.1] ++ x' := by
        simp_all +decide [ List.append_assoc ];
        rw [ List.append_eq_append_iff ] at hw';
        rcases hw' with ( ⟨ as, rfl, h ⟩ | ⟨ bs, rfl, h ⟩ ) <;> simp_all +decide [ List.append_assoc ];
        cases as <;> aesop;
      use u ++ r.2 ++ x', y, n₁ + 1, n₂;
      simp_all +decide [ List.append_assoc ];
      exact ⟨ by exact CF_derivesIn.tail hx ( by exact ⟨ r, u, x', hr, by aesop ⟩ ), by ring ⟩;
    · -- Since $u.length \geq x.length$, we can write $u = x ++ u'$ for some $u'$.
      obtain ⟨u', hu'⟩ : ∃ u' : List (symbol T g.nt), u = x ++ u' := by
        rw [hw'] at hw₁;
        rw [ List.append_assoc ] at hw₁;
        rw [ List.append_eq_append_iff ] at hw₁ ; aesop;
      simp_all +decide [ List.append_assoc ];
      refine' ⟨ x, u' ++ ( r.2 ++ v ), rfl, n₁, hx, n₂ + 1, _, _ ⟩ <;> simp_all +decide [ Nat.add_assoc ];
      convert CF_derivesIn.tail hy _ using 1;
      exact ⟨ r, u', v, hr, by aesop ⟩

-- ============================================================================
-- Product Grammar Construction
-- ============================================================================

variable {σ : Type} [Fintype σ]

/-- Thread DFA states through a list of symbols, enumerating all valid
    annotated symbol lists with their ending DFA states. -/
noncomputable def threadSymbols (M : DFA T σ)
    {N : Type} (syms : List (symbol T N)) (p : σ) :
    List (List (symbol T (Option (σ × N × σ))) × σ) :=
  match syms with
  | [] => [([], p)]
  | symbol.terminal a :: rest =>
      (threadSymbols M rest (M.step p a)).map fun ⟨out, q⟩ =>
        (symbol.terminal a :: out, q)
  | symbol.nonterminal B :: rest =>
      Finset.univ.toList.flatMap fun qmid =>
        (threadSymbols M rest qmid).map fun ⟨out, q⟩ =>
          (symbol.nonterminal (some (p, B, qmid)) :: out, q)

/-- The product grammar of a CFG `g` and a DFA `M`. -/
noncomputable def productGrammar (g : CF_grammar T) (M : DFA T σ) : CF_grammar T where
  nt := Option (σ × g.nt × σ)
  initial := none
  rules :=
    -- Start rules: for each accept state f
    ((Finset.univ.filter (· ∈ M.accept)).toList.map fun f =>
      (none, [symbol.nonterminal (some (M.start, g.initial, f))]))
    ++
    -- Body rules: for each original rule and valid state threading
    (g.rules.flatMap fun rule =>
      Finset.univ.toList.flatMap fun p =>
        (threadSymbols M rule.2 p).map fun ⟨out, q⟩ =>
          (some (p, rule.1, q), out))

-- ============================================================================
-- Properties of threadSymbols
-- ============================================================================

@[simp]
lemma threadSymbols_nil (M : DFA T σ) {N : Type} (p : σ) :
    threadSymbols M ([] : List (symbol T N)) p = [([], p)] := rfl

@[simp]
lemma threadSymbols_terminal (M : DFA T σ) {N : Type} (a : T)
    (rest : List (symbol T N)) (p : σ) :
    threadSymbols M (symbol.terminal a :: rest) p =
      (threadSymbols M rest (M.step p a)).map fun ⟨out, q⟩ =>
        (symbol.terminal a :: out, q) := rfl

@[simp]
lemma threadSymbols_nonterminal (M : DFA T σ) {N : Type} (B : N)
    (rest : List (symbol T N)) (p : σ) :
    threadSymbols M (symbol.nonterminal B :: rest) p =
      Finset.univ.toList.flatMap fun qmid =>
        (threadSymbols M rest qmid).map fun ⟨out, q⟩ =>
          (symbol.nonterminal (some (p, B, qmid)) :: out, q) := rfl

/-
PROBLEM
threadSymbols is non-empty.

PROVIDED SOLUTION
By induction on syms. Base case: the list is [([], p)], which has length 1 > 0. Terminal case: map preserves length, and the recursive call is nonempty. Nonterminal case: Finset.univ is nonempty (since σ has Fintype), so flatMap over a nonempty list with nonempty results gives nonempty list.
-/
lemma threadSymbols_nonempty (M : DFA T σ) {N : Type}
    (syms : List (symbol T N)) (p : σ) :
    (threadSymbols M syms p).length > 0 := by
  induction' syms with sym syms ih generalizing p <;> simp_all +decide;
  cases sym <;> simp +decide [ *, List.length ];
  exact Finset.sum_pos ( fun _ _ => ih _ ) ⟨ p, Finset.mem_univ _ ⟩

/-
PROBLEM
============================================================================
Forward Direction
============================================================================

Project a body rule back: if a triple-nonterminal rule is in the product grammar,
    there's a corresponding original rule.

PROVIDED SOLUTION
Unfold productGrammar and look at h. The rules of productGrammar g M are a concatenation of start rules and body rules. Since the LHS is `some (p, A, q)` (not `none`), it can't come from a start rule (those have `none` as LHS). So it must be in the body rules: g.rules.flatMap fun rule => Finset.univ.toList.flatMap fun p => (threadSymbols M rule.2 p).map .... Unpack the membership to find the original rule and the threadSymbols entry.
-/
lemma productGrammar_body_rule_mem {M : DFA T σ}
    {p : σ} {A : g.nt} {q : σ}
    {out : List (symbol T (Option (σ × g.nt × σ)))}
    (h : (some (p, A, q), out) ∈ (productGrammar g M).rules) :
    ∃ rhs : List (symbol T g.nt),
      (A, rhs) ∈ g.rules ∧ (out, q) ∈ threadSymbols M rhs p := by
  unfold productGrammar at h; aesop;

/-
PROBLEM
A terminal-only derivation has 0 steps.

PROVIDED SOLUTION
If n > 0, then CF_derivesIn_head gives a first step CF_transforms g' [terminal a] w₂. But CF_transforms requires finding a nonterminal in the sentential form to rewrite, and [terminal a] has no nonterminals. So this is impossible. Hence n = 0, and by CF_derivesIn.refl, w = [terminal a].
-/
lemma CF_derivesIn_terminal_zero {g' : CF_grammar T} {n : ℕ} {a : T}
    {w : List (symbol T g'.nt)}
    (h : CF_derivesIn g' n [symbol.terminal a] w) :
    n = 0 ∧ w = [symbol.terminal a] := by
  by_contra h_contra
  obtain ⟨h_step, h_contra⟩ : ∃ n', CF_derivesIn g' n' [symbol.terminal a] w ∧ n' > 0 := by
    refine' ⟨ n, h, Nat.pos_of_ne_zero fun hn => h_contra ⟨ hn, _ ⟩ ⟩;
    cases h <;> aesop;
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, CF_transforms g' [symbol.terminal a] w₂ ∧ CF_derivesIn g' (h_step - 1) w₂ w := by
    have := CF_derivesIn_head ( show CF_derivesIn g' ( h_step - 1 + 1 ) [ symbol.terminal a ] w from by cases h_step <;> tauto ) ; aesop;
  obtain ⟨ r, u, v, hr, hu, hv ⟩ := hw₂.1;
  rcases u with ( _ | ⟨ u₁, u₂ ⟩ ) <;> rcases v with ( _ | ⟨ v₁, v₂ ⟩ ) <;> simp +decide at hu ⊢

/-
PROBLEM
If a concatenation of symbols equals a map of terminals, both parts are terminal maps.

PROVIDED SOLUTION
By induction on u.
Base case u = []: w₁ = [], w₂ = w, trivial.
Step case u = symbol.terminal a :: u' (u can't start with nonterminal because w.map terminal has only terminals): w must be a :: w', and u' ++ v = w'.map terminal. By IH, get w₁', w₂' with u' = w₁'.map terminal, v = w₂'.map terminal, w' = w₁' ++ w₂'. Then w₁ = a :: w₁', w₂ = w₂'.
Actually, need to show u starts with a terminal. Since u ++ v = w.map terminal and w.map terminal starts with terminal, the first element of u (if non-empty) must be terminal.
-/
lemma append_eq_map_terminal {N : Type}
    {u v : List (symbol T N)} {w : List T}
    (h : u ++ v = w.map symbol.terminal) :
    ∃ w₁ w₂, u = w₁.map symbol.terminal ∧ v = w₂.map symbol.terminal ∧ w = w₁ ++ w₂ := by
  induction' u with u hu generalizing v w;
  · aesop;
  · rcases w with ( _ | ⟨ a, w ⟩ ) <;> simp_all +decide [ List.map ];
    rename_i ih; obtain ⟨ w₁, hw₁, w₂, hw₂, hw₃ ⟩ := ih h.2; use a :: w₁; aesop;

/-
PROBLEM
Helper: process annotated symbols from threadSymbols, projecting out
    the original grammar derivation and DFA evaluation.
    By induction on `syms`.

PROVIDED SOLUTION
By induction on `syms`, generalizing out, p, q, w, n.

Case syms = []:
  hthread gives out = [] and q = p. hder gives n = 0 and w = []. Both conclusions hold trivially (CF_deri_self for g and DFA.evalFrom M p [] = p = q).

Case syms = symbol.terminal a :: rest:
  hthread: from threadSymbols_terminal, (out, q) ∈ (threadSymbols M rest (M.step p a)).map (...). So out = symbol.terminal a :: out_rest and (out_rest, q) ∈ threadSymbols M rest (M.step p a).
  hder: CF_derivesIn ... n (symbol.terminal a :: out_rest) (w.map symbol.terminal).
  View as [symbol.terminal a] ++ out_rest. Use CF_derivesIn_append_split to get:
    ∃ x y n₁ n₂, w.map terminal = x ++ y, [terminal a] ⇒^n₁ x, out_rest ⇒^n₂ y, n = n₁ + n₂.
  By CF_derivesIn_terminal_zero on [terminal a] ⇒^n₁ x: n₁ = 0 and x = [terminal a].
  So y = w'.map terminal for some w' with w = a :: w', and n₂ = n.
  Apply induction hypothesis on rest, out_rest, M.step p a, q, w', n₂:
    Get CF_derives g rest (w'.map terminal) and DFA.evalFrom M (M.step p a) w' = q.
  Then CF_derives g (terminal a :: rest) (a :: w').map terminal (by prepending the terminal using CF_deri_with_prefix).
  And DFA.evalFrom M p (a :: w') = DFA.evalFrom M (M.step p a) w' = q.

Case syms = symbol.nonterminal B :: rest:
  hthread: from threadSymbols_nonterminal, ∃ qmid, out = nonterminal (some (p, B, qmid)) :: out_rest and (out_rest, q) ∈ threadSymbols M rest qmid.
  hder: CF_derivesIn ... n (nonterminal (some (p, B, qmid)) :: out_rest) (w.map terminal).
  View as [nonterminal (some (p, B, qmid))] ++ out_rest. Use CF_derivesIn_append_split:
    ∃ x y n₁ n₂, w.map terminal = x ++ y, [nonterminal (some (p, B, qmid))] ⇒^n₁ x, out_rest ⇒^n₂ y, n = n₁ + n₂.
  By append_eq_map_terminal: x = w₁.map terminal and y = w₂.map terminal with w = w₁ ++ w₂.
  Use ih (the strong induction hypothesis from forward_key) with k = n₁ < N_bound (since n₁ ≤ n < N_bound):
    Get CF_derives g [nonterminal B] (w₁.map terminal) and DFA.evalFrom M p w₁ = qmid.
  Apply list induction hypothesis on rest, out_rest, qmid, q, w₂, n₂ (n₂ ≤ n < N_bound):
    Get CF_derives g rest (w₂.map terminal) and DFA.evalFrom M qmid w₂ = q.
  Combine: CF_derives g (nonterminal B :: rest) (w.map terminal) by CF_deri_with_prefix/postfix.
  And DFA.evalFrom M p w = DFA.evalFrom M p (w₁ ++ w₂) = DFA.evalFrom M (DFA.evalFrom M p w₁) w₂ = DFA.evalFrom M qmid w₂ = q (using DFA.evalFrom_of_append).
-/
lemma forward_thread {M : DFA T σ} (N_bound : ℕ)
    (syms : List (symbol T g.nt))
    (out : List (symbol T (Option (σ × g.nt × σ))))
    (p q : σ) (w : List T) (n : ℕ)
    (hn : n < N_bound)
    (hthread : (out, q) ∈ threadSymbols M syms p)
    (hder : CF_derivesIn (productGrammar g M) n out (w.map symbol.terminal))
    (ih : ∀ k < N_bound, ∀ (p' : σ) (A' : g.nt) (q' : σ) (w' : List T),
      CF_derivesIn (productGrammar g M) k
        [symbol.nonterminal (some (p', A', q'))] (w'.map symbol.terminal) →
      CF_derives g [symbol.nonterminal A'] (w'.map symbol.terminal) ∧
      DFA.evalFrom M p' w' = q') :
    CF_derives g syms (w.map symbol.terminal) ∧
    DFA.evalFrom M p w = q := by
  -- By induction on the length of `syms`, we can show that the length of the derivation `n` equals the length of `syms`.
  induction' syms with sym syms ih generalizing out p q w n;
  · -- In the base case, when `syms` is empty, `out` must also be empty, and `w` must be empty as well.
    have h_empty : out = [] ∧ w = [] := by
      cases n <;> cases w <;> simp_all +decide [ threadSymbols ];
      · grind +splitIndPred;
      · -- Since the empty list cannot derive a non-empty list in one step, this leads to a contradiction.
        have h_contra : ¬∃ w₂, CF_transforms (productGrammar g M) [] w₂ ∧ CF_derivesIn (productGrammar g M) ‹_› w₂ (symbol.terminal ‹_› :: List.map symbol.terminal ‹_›) := by
          simp [CF_transforms];
        exact h_contra <| by rcases CF_derivesIn_head hder with ⟨ w₂, hw₂₁, hw₂₂ ⟩ ; exact ⟨ w₂, hw₂₁, hw₂₂ ⟩ ;
    -- Since `out` is empty and `w` is empty, the CF_derives relation holds trivially.
    simp [h_empty] at *;
    exact ⟨ by exact Relation.ReflTransGen.refl, hthread.symm ⟩;
  · cases' sym with a B;
    · simp +zetaDelta at *;
      rcases hthread with ⟨ out', hthread', rfl ⟩;
      -- Apply the induction hypothesis to out' and w.
      obtain ⟨w', hw', hw''⟩ : ∃ w', w = a :: w' ∧ CF_derivesIn (productGrammar g M) n out' (List.map symbol.terminal w') := by
        obtain ⟨w', hw'⟩ : ∃ w', w = a :: w' ∧ CF_derivesIn (productGrammar g M) n out' (List.map symbol.terminal w') := by
          have h_split : ∃ x y n₁ n₂, List.map symbol.terminal w = x ++ y ∧ CF_derivesIn (productGrammar g M) n₁ [symbol.terminal a] x ∧ CF_derivesIn (productGrammar g M) n₂ out' y ∧ n = n₁ + n₂ := by
            exact?
          obtain ⟨ x, y, n₁, n₂, h₁, h₂, h₃, rfl ⟩ := h_split;
          have := CF_derivesIn_terminal_zero h₂;
          rcases w with ( _ | ⟨ a', w ⟩ ) <;> simp_all +decide [ List.map ];
        use w';
      have := ih out' ( M.step p a ) q w' n hn hthread' hw''; simp_all +decide [ DFA.evalFrom ] ;
      -- Apply the CF_deri_with_prefix lemma to the induction hypothesis.
      have := CF_deri_with_prefix (symbol.terminal a :: []) this.left; aesop;
    · -- By definition of `threadSymbols`, we know that `out = nonterminal (some (p, B, qmid)) :: out_rest` for some `qmid` and `out_rest`.
      obtain ⟨qmid, out_rest, hthread_out⟩ : ∃ qmid : σ, ∃ out_rest : List (symbol T (Option (σ × g.nt × σ))), out = symbol.nonterminal (some (p, B, qmid)) :: out_rest ∧ (out_rest, q) ∈ threadSymbols M syms qmid := by
        grind +suggestions;
      -- By definition of `CF_derivesIn`, we know that `CF_derivesIn (productGrammar g M) n (symbol.nonterminal (some (p, B, qmid)) :: out_rest) (List.map symbol.terminal w)`.
      have hder_split : ∃ x y n₁ n₂, List.map symbol.terminal w = x ++ y ∧ CF_derivesIn (productGrammar g M) n₁ [symbol.nonterminal (some (p, B, qmid))] x ∧ CF_derivesIn (productGrammar g M) n₂ out_rest y ∧ n = n₁ + n₂ := by
        have := CF_derivesIn_append_split ( show CF_derivesIn ( productGrammar g M ) n ( [ symbol.nonterminal ( some ( p, B, qmid ) ) ] ++ out_rest ) ( List.map symbol.terminal w ) from by simpa only [ hthread_out ] using hder ) ; aesop;
      obtain ⟨ x, y, n₁, n₂, hxy, hx, hy, rfl ⟩ := hder_split
      have hxy_map : ∃ w₁ w₂, x = List.map symbol.terminal w₁ ∧ y = List.map symbol.terminal w₂ ∧ w = w₁ ++ w₂ := by
        have := append_eq_map_terminal hxy.symm; aesop;
      obtain ⟨ w₁, w₂, hx_map, hy_map, rfl ⟩ := hxy_map
      have h_ind : CF_derives g [symbol.nonterminal B] (List.map symbol.terminal w₁) ∧ M.evalFrom p w₁ = qmid := by
        exact ‹∀ k < N_bound, ∀ ( p' : σ ) ( A' : g.nt ) ( q' : σ ) ( w' : List T ), CF_derivesIn ( productGrammar g M ) k [ symbol.nonterminal ( some ( p', A', q' ) ) ] ( List.map symbol.terminal w' ) → CF_derives g [ symbol.nonterminal A' ] ( List.map symbol.terminal w' ) ∧ M.evalFrom p' w' = q'› n₁ ( by linarith ) p B qmid w₁ ( by simpa [ hx_map ] using hx ) |> fun h => ⟨ h.1, h.2 ⟩
      have h_ind' : CF_derives g syms (List.map symbol.terminal w₂) ∧ M.evalFrom qmid w₂ = q := by
        exact ih out_rest qmid q w₂ n₂ ( by linarith ) hthread_out.2 ( by simpa only [ hy_map ] using hy ) |> fun h => ⟨ h.1, h.2 ⟩
      have h_final : CF_derives g (symbol.nonterminal B :: syms) (List.map symbol.terminal (w₁ ++ w₂)) := by
        convert CF_deri_with_prefix _ h_ind'.1 |> CF_deri_of_deri_deri <| CF_deri_with_postfix _ h_ind.1 using 1 ; aesop ( simp_config := { singlePass := true } ) ;
      have h_final' : M.evalFrom p (w₁ ++ w₂) = q := by
        rw [ DFA.evalFrom_of_append, h_ind.2, h_ind'.2 ]
      exact ⟨ h_final, h_final' ⟩

/-
PROBLEM
Key forward lemma:
    If `(p, A, q)` derives a terminal string `w` in the product grammar in `n` steps,
    then `A` derives `w` in `g` and `M.evalFrom p w = q`.
    Proved by strong induction on `n`, using `forward_thread` for the recursive structure.

PROVIDED SOLUTION
By strong induction on n using Nat.strongRecOn.

n = 0: CF_derivesIn ... 0 [nonterminal (some (p, A, q))] (w.map terminal). By CF_derivesIn.refl, [nonterminal (some (p, A, q))] = w.map terminal. But the LHS has a nonterminal, so this is impossible (w.map terminal only has terminals).

n = k+1: Use CF_derivesIn_head to get: ∃ w₂, CF_transforms (productGrammar g M) [nonterminal (some (p, A, q))] w₂ ∧ CF_derivesIn ... k w₂ (w.map terminal).

The transform on [nonterminal X] means: ∃ (r, u, v), r ∈ (productGrammar g M).rules, [nonterminal X] = u ++ [nonterminal r.1] ++ v, w₂ = u ++ r.2 ++ v.
Since [nonterminal X] has length 1, u = [] and v = [], so r.1 = some (p, A, q) and w₂ = r.2.

By productGrammar_body_rule_mem: ∃ rhs ∈ g.rules, (w₂, q) ∈ threadSymbols M rhs p.

Apply forward_thread with N_bound = k+1, syms = rhs, out = w₂, and the strong induction hypothesis as ih.
This gives: CF_derives g rhs (w.map terminal) and DFA.evalFrom M p w = q.

For the grammar part: since (A, rhs) ∈ g.rules, [nonterminal A] ⇒₁ rhs ⇒* w.map terminal, so CF_derives g [nonterminal A] (w.map terminal).
-/
lemma forward_key {M : DFA T σ} (n : ℕ) (p : σ) (A : g.nt) (q : σ) (w : List T)
    (hder : CF_derivesIn (productGrammar g M) n
      [symbol.nonterminal (some (p, A, q))] (w.map symbol.terminal)) :
    CF_derives g [symbol.nonterminal A] (w.map symbol.terminal) ∧
    DFA.evalFrom M p w = q := by
  revert hder;
  induction' n using Nat.strong_induction_on with n ih generalizing p A q w;
  rcases n with ( _ | n );
  · cases w <;> simp +decide [ CF_derivesIn ];
    · rintro ⟨ ⟩;
    · rintro ⟨ ⟩;
  · intro h;
    obtain ⟨w₂, hw₂⟩ : ∃ w₂, CF_transforms (productGrammar g M) [symbol.nonterminal (some (p, A, q))] w₂ ∧ CF_derivesIn (productGrammar g M) n w₂ (w.map symbol.terminal) := by
      exact?;
    rcases hw₂ with ⟨ ⟨ r, u, v, hr, hu, hv ⟩, hw₂ ⟩;
    rcases u with ( _ | ⟨ _, _ ⟩ ) <;> rcases v with ( _ | ⟨ _, _ ⟩ ) <;> simp_all +decide;
    -- By definition of `productGrammar`, we know that `r.2` is a valid derivation in `g`.
    obtain ⟨rhs, hrhs⟩ : ∃ rhs : List (symbol T g.nt), (A, rhs) ∈ g.rules ∧ (r.2, q) ∈ threadSymbols M rhs p := by
      grind +locals;
    have := forward_thread ( n + 1 ) rhs r.2 p q w n ( Nat.lt_succ_self _ ) hrhs.2 hw₂;
    exact ⟨ by simpa using CF_deri_of_deri_deri ( CF_deri_of_tran ( show CF_transforms g [ symbol.nonterminal A ] rhs from by
                                                                      exact ⟨ ⟨ A, rhs ⟩, [ ], [ ], hrhs.1, by simp +decide, by simp +decide ⟩ ) ) ( this ( fun k hk p' A' q' w' hw' => ih k ( Nat.le_of_lt_succ hk ) p' A' q' w' hw' ) |>.1 ), this ( fun k hk p' A' q' w' hw' => ih k ( Nat.le_of_lt_succ hk ) p' A' q' w' hw' ) |>.2 ⟩

/-
PROBLEM
============================================================================
Backward Direction
============================================================================

backward_thread base case: empty symbol list.

PROVIDED SOLUTION
If n > 0, by CF_derivesIn_head there's a first step CF_transforms g [] w₂. But CF_transforms requires ∃ r ∈ g.rules, ∃ u v, [] = u ++ [nonterminal r.1] ++ v, which is impossible since [] is empty. So n = 0, and by CF_derivesIn.refl, [] = w.map terminal, so w = [].
-/
lemma backward_thread_nil {M : DFA T σ} (w : List T) (p : σ) (n : ℕ)
    (hder : CF_derivesIn g n [] (w.map symbol.terminal)) :
    w = [] ∧ n = 0 := by
  induction' n with n ih generalizing w p;
  · rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | w ⟩ ⟩ ) <;> cases hder;
    trivial;
  · obtain ⟨ w₂, hw₂ ⟩ := CF_derivesIn_head hder;
    obtain ⟨ r, u, v, hr, hu, hv ⟩ := hw₂.1;
    cases u <;> cases v <;> cases hu

/-
PROBLEM
backward_thread: process a sentential form symbol by symbol.

PROVIDED SOLUTION
By induction on `syms`, generalizing w, p, n.

Case syms = []:
  By backward_thread_nil, w = [] and n = 0.
  Use out = [], q = p. ([], p) ∈ threadSymbols M [] p = [([], p)] trivially.
  DFA.evalFrom M p [] = p. CF_derives (productGrammar g M) [] [] by refl.

Case syms = terminal a :: rest:
  View syms as [terminal a] ++ rest. Use CF_derivesIn_append_split:
    ∃ x y n₁ n₂, w.map terminal = x ++ y, [terminal a] ⇒^n₁ x, rest ⇒^n₂ y, n = n₁ + n₂.
  By CF_derivesIn_terminal_zero: n₁ = 0, x = [terminal a].
  So w.map terminal = [terminal a] ++ y. By append_eq_map_terminal on the right or by simple analysis, w starts with a: w = a :: w₂ and y = w₂.map terminal. Actually [terminal a] ++ y = w.map terminal, so [terminal a] ++ y = (a :: w₂).map terminal for some w₂, giving w = a :: w₂ and y = w₂.map terminal.
  n₂ = n (since n₁ = 0).
  By list IH on rest, w₂, M.step p a, n₂ (n₂ ≤ n < N_bound):
    ∃ out_rest q_rest ∈ threadSymbols M rest (M.step p a), q_rest = DFA.evalFrom M (M.step p a) w₂, CF_derives ... out_rest (w₂.map terminal).
  Use out = terminal a :: out_rest, q = q_rest.
  (terminal a :: out_rest, q_rest) ∈ threadSymbols M (terminal a :: rest) p: by definition of threadSymbols_terminal, this is the map of (out_rest, q_rest) which is in threadSymbols M rest (M.step p a).
  DFA.evalFrom M p (a :: w₂) = DFA.evalFrom M (M.step p a) w₂ = q_rest.
  CF_derives (productGrammar g M) (terminal a :: out_rest) ((a :: w₂).map terminal): prepend terminal a to the derivation of out_rest using CF_deri_with_prefix with prefix [terminal a].

Case syms = nonterminal B :: rest:
  View as [nonterminal B] ++ rest. Use CF_derivesIn_append_split:
    ∃ x y n₁ n₂, w.map terminal = x ++ y, [nonterminal B] ⇒^n₁ x, rest ⇒^n₂ y, n = n₁ + n₂.
  By append_eq_map_terminal: x = w₁.map terminal, y = w₂.map terminal, w = w₁ ++ w₂.
  Let qmid := DFA.evalFrom M p w₁.
  Use ih (strong IH from backward_key) with k = n₁, since n₁ ≤ n < N_bound:
    ih n₁ (by omega) B w₁ p qmid (...) rfl
    gives CF_derives (productGrammar g M) [nonterminal (some (p, B, qmid))] (w₁.map terminal).
  By list IH on rest, w₂, qmid, n₂ (n₂ ≤ n < N_bound):
    ∃ out_rest q_rest ∈ threadSymbols M rest qmid, q_rest = DFA.evalFrom M qmid w₂, CF_derives ... out_rest ....
  Use out = nonterminal (some (p, B, qmid)) :: out_rest, q = q_rest.
  Membership in threadSymbols: by threadSymbols_nonterminal, since qmid ∈ Finset.univ and (out_rest, q_rest) ∈ threadSymbols M rest qmid.
  DFA.evalFrom M p (w₁ ++ w₂) = DFA.evalFrom M qmid w₂ = q_rest (by DFA.evalFrom_of_append).
  CF_derives: combine [nonterminal (some (p, B, qmid))] ⇒* w₁.map terminal and out_rest ⇒* w₂.map terminal.
  Use CF_deri_with_postfix on the first to get [nonterminal (some (p, B, qmid))] ++ out_rest ⇒* w₁.map terminal ++ out_rest.
  Then CF_deri_with_prefix on the second to get w₁.map terminal ++ out_rest ⇒* w₁.map terminal ++ w₂.map terminal.
  Compose with CF_deri_of_deri_deri.
-/
set_option maxHeartbeats 800000 in
lemma backward_thread {M : DFA T σ} (N_bound : ℕ)
    (syms : List (symbol T g.nt)) (w : List T) (p : σ) (n : ℕ)
    (hn : n < N_bound)
    (hder : CF_derivesIn g n syms (w.map symbol.terminal))
    (ih : ∀ k < N_bound, ∀ (B : g.nt) (w' : List T) (p' q' : σ),
      CF_derivesIn g k [symbol.nonterminal B] (w'.map symbol.terminal) →
      DFA.evalFrom M p' w' = q' →
      CF_derives (productGrammar g M)
        [symbol.nonterminal (some (p', B, q'))] (w'.map symbol.terminal)) :
    ∃ (out : List (symbol T (Option (σ × g.nt × σ)))) (q : σ),
      (out, q) ∈ threadSymbols M syms p ∧
      q = DFA.evalFrom M p w ∧
      CF_derives (productGrammar g M) out (w.map symbol.terminal) := by
  -- By induction on the length of syms, we can construct the required out and q.
  induction' syms with sym syms ih generalizing p w n;
  · have := @backward_thread_nil T g σ _ M w p n hder;
    use [], p; simp_all +decide [ threadSymbols ] ;
    constructor;
  · rcases sym with ( a | B ) <;> simp_all +decide [ CF_derivesIn_append_split ];
    · -- By definition of CF_derivesIn, we can split the derivation into two parts: one for the terminal symbol and one for the rest of the symbols.
      obtain ⟨w₁, w₂, hw₁, hw₂, hw⟩ : ∃ w₁ w₂ : List T, w = w₁ ++ w₂ ∧ CF_derivesIn g 0 [symbol.terminal a] (w₁.map symbol.terminal) ∧ CF_derivesIn g n syms (w₂.map symbol.terminal) := by
        have h_split : ∃ w₁ w₂ : List T, w = w₁ ++ w₂ ∧ CF_derivesIn g 0 [symbol.terminal a] (w₁.map symbol.terminal) ∧ CF_derivesIn g n syms (w₂.map symbol.terminal) := by
          have h_split : CF_derivesIn g n (symbol.terminal a :: syms) (List.map symbol.terminal w) := hder
          obtain ⟨w₁, w₂, hw₁, hw₂, hw⟩ : ∃ w₁ w₂ : List T, w = w₁ ++ w₂ ∧ CF_derivesIn g 0 [symbol.terminal a] (w₁.map symbol.terminal) ∧ CF_derivesIn g n syms (w₂.map symbol.terminal) := by
            have h_split : ∃ x y n₁ n₂, w.map symbol.terminal = x ++ y ∧ CF_derivesIn g n₁ [symbol.terminal a] x ∧ CF_derivesIn g n₂ syms y ∧ n = n₁ + n₂ := by
              exact CF_derivesIn_append_split h_split |> fun ⟨ x, y, n₁, n₂, hxy, hx, hy, hn ⟩ => ⟨ x, y, n₁, n₂, hxy, hx, hy, hn ⟩
            obtain ⟨ x, y, n₁, n₂, h₁, h₂, h₃, rfl ⟩ := h_split; rcases n₁ with ( _ | n₁ ) <;> simp_all +decide [ CF_derivesIn_terminal_zero ] ;
            · rcases x with ( _ | ⟨ _, _ | x ⟩ ) <;> simp_all +decide [ CF_derivesIn_terminal_zero ] ; (
              grind +splitIndPred);
              · rcases w with ( _ | ⟨ a, w ⟩ ) <;> simp_all +decide [ List.map ] ; (
                use [a], w; aesop;);
              · grind +splitIndPred;
            · exact absurd ( CF_derivesIn_terminal_zero h₂ ) ( by aesop )
          generalize_proofs at *; (
          use w₁, w₂)
        generalize_proofs at *; (
        exact h_split)
      generalize_proofs at *; (
      obtain ⟨ out, hout₁, hout₂ ⟩ := ih w₂ ( M.step p a ) n hn hw; use out; simp_all +decide [ List.map_append ] ;
      -- Apply the CF_deri_with_prefix lemma to get the desired result.
      have h_prefix : CF_derives (productGrammar g M) (symbol.terminal a :: out) (symbol.terminal a :: List.map symbol.terminal w₂) := by
        have h_prefix : ∀ {u v : List (symbol T (Option (σ × g.nt × σ)))}, CF_derives (productGrammar g M) u v → CF_derives (productGrammar g M) (symbol.terminal a :: u) (symbol.terminal a :: v) := by
          intros u v huv; exact (by
          have h_prefix : ∀ {u v : List (symbol T (Option (σ × g.nt × σ)))}, CF_derives (productGrammar g M) u v → CF_derives (productGrammar g M) (symbol.terminal a :: u) (symbol.terminal a :: v) := by
            intros u v huv; exact (by
              have h_prefix : ∀ {u v : List (symbol T (Option (σ × g.nt × σ)))}, CF_transforms (productGrammar g M) u v → CF_transforms (productGrammar g M) (symbol.terminal a :: u) (symbol.terminal a :: v) := by
                intros u v huv; exact (by
                  obtain ⟨ r, u', v', hr, hu, hv ⟩ := huv;
                  exact ⟨ r, symbol.terminal a :: u', v', hr, by simp [hu], by simp [hv] ⟩
                )
              induction huv <;> [ tauto; exact Relation.ReflTransGen.tail ‹_› ( h_prefix ‹_› ) ] ;
            )
          generalize_proofs at *; (
          exact h_prefix huv))
        generalize_proofs at *; (
        exact h_prefix hout₂)
      generalize_proofs at *; (
      have := CF_derivesIn_terminal_zero hw₂; aesop;));
    · obtain ⟨x, y, n₁, n₂, hw, hx, hy, hn_eq⟩ : ∃ x y n₁ n₂, w.map symbol.terminal = x ++ y ∧ CF_derivesIn g n₁ [symbol.nonterminal B] x ∧ CF_derivesIn g n₂ syms y ∧ n = n₁ + n₂ := by
        -- Apply the lemma CF_derivesIn_append_split to hder.
        apply CF_derivesIn_append_split hder |> fun ⟨x, y, n₁, n₂, hw, hx, hy, hn_eq⟩ => ⟨x, y, n₁, n₂, hw, hx, hy, hn_eq⟩
      generalize_proofs at *; (
      -- By the properties of the map function and the concatenation of lists, we can split w into w₁ and w₂ such that x = w₁.map symbol.terminal and y = w₂.map symbol.terminal.
      obtain ⟨w₁, w₂, hw₁, hw₂⟩ : ∃ w₁ w₂ : List T, x = w₁.map symbol.terminal ∧ y = w₂.map symbol.terminal ∧ w = w₁ ++ w₂ := by
        have := append_eq_map_terminal hw.symm; aesop;
      generalize_proofs at *; (
      -- By the induction hypothesis, we have that there exists an out and q such that (out, q) is in the threadSymbols of syms and q is the evaluation of M from p on w₂.
      obtain ⟨out, q, hq, hout⟩ : ∃ out q, (out, q) ∈ threadSymbols M syms (M.evalFrom p w₁) ∧ q = M.evalFrom (M.evalFrom p w₁) w₂ ∧ CF_derives (productGrammar g M) out (w₂.map symbol.terminal) := by
        exact Exists.elim ( ih w₂ ( M.evalFrom p w₁ ) n₂ ( by linarith ) ( by simpa [ hw₂ ] using hy ) ) fun out hout => ⟨ out, _, hout.1, rfl, hout.2 ⟩ ;
      generalize_proofs at *; (
      use M.evalFrom p w₁, out; simp_all +decide [ DFA.evalFrom_of_append ] ;
      have h_combined : CF_derives (productGrammar g M) (symbol.nonterminal (some (p, B, M.evalFrom p w₁)) :: out) (w₁.map symbol.terminal ++ out) := by
        have h_combined : CF_derives (productGrammar g M) [symbol.nonterminal (some (p, B, M.evalFrom p w₁))] (w₁.map symbol.terminal) := by
          exact ‹∀ k < N_bound, ∀ ( B : g.nt ) ( w' : List T ) ( p' : σ ), CF_derivesIn g k [ symbol.nonterminal B ] ( List.map symbol.terminal w' ) → CF_derives ( productGrammar g M ) [ symbol.nonterminal ( some ( p', B, M.evalFrom p' w' ) ) ] ( List.map symbol.terminal w' ) › n₁ ( by linarith ) B w₁ p hx |> fun h => by simpa using h;
        generalize_proofs at *; (
        have h_combined : CF_derives (productGrammar g M) (symbol.nonterminal (some (p, B, M.evalFrom p w₁)) :: out) (w₁.map symbol.terminal ++ out) := by
          have h_append : ∀ {u v : List (symbol T (Option (σ × g.nt × σ)))}, CF_derives (productGrammar g M) u v → ∀ {w : List (symbol T (Option (σ × g.nt × σ)))}, CF_derives (productGrammar g M) (u ++ w) (v ++ w) := by
            grind +suggestions
          exact h_append h_combined |> fun h => by simpa using h;
        generalize_proofs at *; (
        exact h_combined))
      generalize_proofs at *; (
      grind +suggestions))))

/-
PROBLEM
Key backward lemma:
    If `A` derives `w` in `g` and `M.evalFrom p w = q`,
    then `(p, A, q)` derives `w` in the product grammar.

PROVIDED SOLUTION
By strong induction on n using Nat.strong_induction_on.

n = 0: CF_derivesIn g 0 [nonterminal A] (w.map terminal). By refl, [nonterminal A] = w.map terminal, which is impossible (nonterminal ≠ terminal).

n = k + 1: Use CF_derivesIn_head to get:
∃ w₂, CF_transforms g [nonterminal A] w₂ ∧ CF_derivesIn g k w₂ (w.map terminal).

The transform on [nonterminal A] means: ∃ (r, u, v) with r ∈ g.rules, [nonterminal A] = u ++ [nonterminal r.1] ++ v, w₂ = u ++ r.2 ++ v.
Since |[nonterminal A]| = 1, we must have u = [], v = [], r.1 = A, w₂ = r.2.
So there's a rule (A, rhs) ∈ g.rules and rhs ⇒^k w.map terminal.

Apply backward_thread with N_bound = k+1, syms = rhs, w, p, k, hn = Nat.lt_succ_self k:
Need ih : ∀ j < k+1, ∀ B w' p' q', CF_derivesIn g j [nonterminal B] (w'.map terminal) → evalFrom p' w' = q' → CF_derives (productGrammar g M) [nonterminal (some (p', B, q'))] (w'.map terminal).
This is exactly the strong induction hypothesis (since j < k+1 means j ≤ k < n = k+1).

Get ∃ out q_out, (out, q_out) ∈ threadSymbols M rhs p ∧ q_out = DFA.evalFrom M p w ∧ CF_derives (productGrammar g M) out (w.map terminal).

Since heval : DFA.evalFrom M p w = q, we have q_out = q.

Now construct the product grammar derivation:
1. (some (p, A, q), out) is in (productGrammar g M).rules (as a body rule, since (A, rhs) ∈ g.rules and (out, q) ∈ threadSymbols M rhs p).
2. [nonterminal (some (p, A, q))] ⇒₁ out in the product grammar.
3. out ⇒* w.map terminal.
Compose with CF_deri_of_tran_deri.
-/
lemma backward_key {M : DFA T σ} (n : ℕ) (A : g.nt) (w : List T) (p q : σ)
    (hder : CF_derivesIn g n [symbol.nonterminal A] (w.map symbol.terminal))
    (heval : DFA.evalFrom M p w = q) :
    CF_derives (productGrammar g M)
      [symbol.nonterminal (some (p, A, q))] (w.map symbol.terminal) := by
  induction' n using Nat.strong_induction_on with n ih generalizing A w p q;
  rcases n with ( _ | n ) <;> simp_all +decide [ CF_derivesIn ];
  · cases w <;> cases hder;
  · -- By definition of CF_derivesIn, there exists some w₂ such that CF_transforms g [symbol.nonterminal A] w₂ and CF_derivesIn g n w₂ (w.map symbol.terminal).
    obtain ⟨w₂, hw₂⟩ : ∃ w₂, CF_transforms g [symbol.nonterminal A] w₂ ∧ CF_derivesIn g n w₂ (w.map symbol.terminal) := by
      exact?;
    -- Since $w₂$ is derived from $A$ in $g$, we have $w₂ = rhs$ for some $rhs$ such that $(A, rhs) \in g.rules$.
    obtain ⟨rhs, hrhs⟩ : ∃ rhs : List (symbol T g.nt), (A, rhs) ∈ g.rules ∧ w₂ = rhs := by
      obtain ⟨ r, u, v, hr, hu, hv ⟩ := hw₂.1;
      rcases u with ( _ | ⟨ _, _ | u ⟩ ) <;> rcases v with ( _ | ⟨ _, _ | v ⟩ ) <;> simp_all +decide [ List.append_assoc ];
    -- Apply the backward_thread lemma with N_bound = n+1, syms = rhs, w, p, n, hn = Nat.lt_succ_self n.
    obtain ⟨out, q_out, hout, hq_out, hder⟩ : ∃ out : List (symbol T (Option (σ × g.nt × σ))), ∃ q_out : σ, (out, q_out) ∈ threadSymbols M rhs p ∧ q_out = DFA.evalFrom M p w ∧ CF_derives (productGrammar g M) out (w.map symbol.terminal) := by
      apply backward_thread (n + 1) rhs w p n (Nat.lt_succ_self n) (by
      grind +locals) (by
      exact fun k hk B w' p' q' hder heval => by simpa [ heval ] using ih k ( Nat.le_of_lt_succ hk ) B w' p' hder;);
    -- Since $(some (p, A, q), out)$ is in the rules of the product grammar, we can apply the CF_deri_of_tran_deri lemma.
    have h_rule : (some (p, A, q), out) ∈ (productGrammar g M).rules := by
      unfold productGrammar; aesop;
    exact CF_deri_of_tran_deri ( by exact ⟨ ( some ( p, A, q ), out ), [ ], [ ], h_rule, by aesop ⟩ ) hder

/-
PROBLEM
============================================================================
Main Theorem
============================================================================

The product grammar generates exactly the intersection of the CFG language
    and the DFA language.

PROVIDED SOLUTION
We prove set equality by showing both inclusions.

(⊆) Let w ∈ CF_language (productGrammar g M).
Then CF_derives (productGrammar g M) [nonterminal none] (w.map terminal).
The first step must use a start rule (since none is the initial nonterminal).
A start rule maps none to [nonterminal (some (M.start, g.initial, f))] for some f ∈ M.accept.
So CF_derives (productGrammar g M) [nonterminal (some (M.start, g.initial, f))] (w.map terminal).
Convert to CF_derivesIn (using CF_derivesIn_of_derives) to get some n.
By forward_key: CF_derives g [nonterminal g.initial] (w.map terminal) and DFA.evalFrom M M.start w = f.
Since f ∈ M.accept and M.eval w = DFA.evalFrom M M.start w = f, w ∈ M.accepts.
Also w ∈ CF_language g.

(⊇) Let w ∈ CF_language g ∧ w ∈ M.accepts.
CF_derives g [nonterminal g.initial] (w.map terminal).
Convert to CF_derivesIn to get some n.
DFA.evalFrom M M.start w ∈ M.accept. Let f = DFA.evalFrom M M.start w = M.eval w.
By backward_key with n, g.initial, w, M.start, f:
CF_derives (productGrammar g M) [nonterminal (some (M.start, g.initial, f))] (w.map terminal).
Now apply the start rule: none → [nonterminal (some (M.start, g.initial, f))] which is in (productGrammar g M).rules (since f ∈ M.accept).
CF_transforms (productGrammar g M) [nonterminal none] [nonterminal (some (M.start, g.initial, f))].
Compose: CF_derives (productGrammar g M) [nonterminal none] (w.map terminal).
So w ∈ CF_language (productGrammar g M).
-/
theorem productGrammar_language (g : CF_grammar T) (M : DFA T σ) :
    CF_language (productGrammar g M) = CF_language g ⊓ DFA.accepts M := by
  ext w
  constructor
  intro hw
  obtain ⟨n, hn⟩ := CF_derivesIn_of_derives hw
  have h_forward : ∃ f ∈ M.accept, CF_derives g [symbol.nonterminal g.initial] (w.map symbol.terminal) ∧ DFA.evalFrom M M.start w = f := by
    -- By definition of product grammar, if there's a derivation from [symbol.nonterminal none] to w.map symbol.terminal, then there must be a start rule that transforms none into [symbol.nonterminal (some (M.start, g.initial, f))] for some f in M.accept.
    obtain ⟨f, hf⟩ : ∃ f ∈ M.accept, CF_derivesIn (productGrammar g M) (n - 1) [symbol.nonterminal (some (M.start, g.initial, f))] (w.map symbol.terminal) := by
      rcases n with ( _ | n ) <;> simp_all +decide [ CF_derivesIn ];
      · cases w <;> cases hn;
      · obtain ⟨ u, hu ⟩ := CF_derivesIn_head hn;
        rcases hu with ⟨ ⟨ r, u, v, hr, hu, hv ⟩, hu' ⟩ ; simp_all +decide [ productGrammar ] ;
        rcases hr with ( ⟨ f, hf, rfl ⟩ | ⟨ a, b, hab, a', b', c', hc', rfl ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ] ;
        · cases u <;> aesop;
        · cases u <;> cases v <;> aesop ( simp_config := { decide := true } ) ;
    exact ⟨ f, hf.1, forward_key _ _ _ _ _ hf.2 |>.1, forward_key _ _ _ _ _ hf.2 |>.2 ⟩
  obtain ⟨f, hf1, hf2, hf3⟩ := h_forward
  exact ⟨hf2, by
    aesop⟩
  intro hw
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨n, hn⟩ := CF_derivesIn_of_derives hw1
  have h_backward : CF_derives (productGrammar g M) [symbol.nonterminal (some (M.start, g.initial, DFA.evalFrom M M.start w))] (w.map symbol.terminal) := by
    exact?
  have h_start : CF_derives (productGrammar g M) [symbol.nonterminal none] (w.map symbol.terminal) := by
    convert CF_deri_of_deri_deri _ _ using 1;
    exact [ symbol.nonterminal ( some ( M.start, g.initial, M.evalFrom M.start w ) ) ];
    · have h_start : (none, [symbol.nonterminal (some (M.start, g.initial, M.evalFrom M.start w))]) ∈ (productGrammar g M).rules := by
        unfold productGrammar; aesop;
      exact .single ⟨ ( none, [ symbol.nonterminal ( some ( M.start, g.initial, M.evalFrom M.start w ) ) ] ), [ ], [ ], h_start, rfl, rfl ⟩;
    · assumption
  exact h_start

/-
PROBLEM
The class of context-free languages is closed under intersection with regular languages.

PROVIDED SOLUTION
From h₁ : is_CF L₁, get ⟨g, hg⟩ with CF_language g = L₁.
From h₂ : L₂.IsRegular, get ⟨σ, _, M, hM⟩ with M.accepts = L₂.
Use the product grammar: is_CF (L₁ ⊓ L₂) by exhibiting productGrammar g M.
CF_language (productGrammar g M) = CF_language g ⊓ M.accepts (by productGrammar_language).
= L₁ ⊓ L₂ (by hg and hM).
-/
theorem CF_of_CF_inter_regular {L₁ L₂ : Language T}
    (h₁ : is_CF L₁) (h₂ : L₂.IsRegular) :
    is_CF (L₁ ⊓ L₂) := by
  revert h₂;
  rintro ⟨ σ, _, M, rfl ⟩;
  obtain ⟨g, hg⟩ := is_CF_implies_is_CF_via_cfg h₁
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨productGrammar g M, ?_⟩
  rw [← hg, productGrammar_language]

end
