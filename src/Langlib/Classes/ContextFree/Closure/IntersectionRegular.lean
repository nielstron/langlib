import Langlib.Grammars.ContextFree.Toolbox
import Mathlib
import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Utilities.ClosurePredicates

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

lemma CF_derives_of_derivesIn {n : ℕ} {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_derivesIn g n w₁ w₂) : CF_derives g w₁ w₂ := by
  induction' h with n w₁ w₂ h ih;
  · constructor;
  · exact?

lemma CF_derivesIn_trans {n m : ℕ} {w₁ w₂ w₃ : List (symbol T g.nt)}
    (h₁ : CF_derivesIn g n w₁ w₂) (h₂ : CF_derivesIn g m w₂ w₃) :
    CF_derivesIn g (n + m) w₁ w₃ := by
  induction h₂;
  · exact h₁;
  · rename_i k w₁ w₂ w₃ h₁ h₂ ih; exact ih h₁ |> fun h => h.tail ( by tauto ) ;

/-
Head extraction: an (n+1)-step derivation starts with one step.
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
Adding a prefix preserves step count.
-/
lemma CF_derivesIn_append_left {n : ℕ} {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_derivesIn g n w₁ w₂) (pfx : List (symbol T g.nt)) :
    CF_derivesIn g n (pfx ++ w₁) (pfx ++ w₂) := by
  induction' h with pfx hw₁ hw₂ hpfx hw₁ hw₂ hpfx' hw₁' hw₂' ih;
  · constructor;
  · obtain ⟨ r, u, v, hr, rfl, rfl ⟩ := hpfx';
    exact CF_derivesIn.tail hw₁' ⟨ r, pfx ++ u, v, hr, by simp +decide [ List.append_assoc ], by simp +decide [ List.append_assoc ] ⟩

/-
Adding a postfix preserves step count.
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
Key splitting lemma: a derivation from `p ++ q` can be split into
    independent derivations from `p` and `q` with step counts adding up.
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
threadSymbols is non-empty.
-/
lemma threadSymbols_nonempty (M : DFA T σ) {N : Type}
    (syms : List (symbol T N)) (p : σ) :
    (threadSymbols M syms p).length > 0 := by
  induction' syms with sym syms ih generalizing p <;> simp_all +decide;
  cases sym <;> simp +decide [ *, List.length ];
  exact Finset.sum_pos ( fun _ _ => ih _ ) ⟨ p, Finset.mem_univ _ ⟩

/-
============================================================================
Forward Direction
============================================================================

Project a body rule back: if a triple-nonterminal rule is in the product grammar,
    there's a corresponding original rule.
-/
lemma productGrammar_body_rule_mem {M : DFA T σ}
    {p : σ} {A : g.nt} {q : σ}
    {out : List (symbol T (Option (σ × g.nt × σ)))}
    (h : (some (p, A, q), out) ∈ (productGrammar g M).rules) :
    ∃ rhs : List (symbol T g.nt),
      (A, rhs) ∈ g.rules ∧ (out, q) ∈ threadSymbols M rhs p := by
  unfold productGrammar at h; aesop;

/-
A terminal-only derivation has 0 steps.
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
If a concatenation of symbols equals a map of terminals, both parts are terminal maps.
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
Helper: process annotated symbols from threadSymbols, projecting out
    the original grammar derivation and DFA evaluation.
    By induction on `syms`.
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
Key forward lemma:
    If `(p, A, q)` derives a terminal string `w` in the product grammar in `n` steps,
    then `A` derives `w` in `g` and `M.evalFrom p w = q`.
    Proved by strong induction on `n`, using `forward_thread` for the recursive structure.
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
============================================================================
Backward Direction
============================================================================

backward_thread base case: empty symbol list.
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
backward_thread: process a sentential form symbol by symbol.
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
Key backward lemma:
    If `A` derives `w` in `g` and `M.evalFrom p w = q`,
    then `(p, A, q)` derives `w` in the product grammar.
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
============================================================================
Main Theorem
============================================================================

The product grammar generates exactly the intersection of the CFG language
    and the DFA language.
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
The class of context-free languages is closed under intersection with regular languages.
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

/-- The class of context-free languages is closed under intersection with regular languages. -/
theorem CF_closedUnderIntersectionWithRegular :
    ClosedUnderIntersectionWithRegular (α := T) is_CF :=
  fun L hL R hR => CF_of_CF_inter_regular hL hR

end
