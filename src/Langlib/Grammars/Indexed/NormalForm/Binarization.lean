import Mathlib
import Langlib.Grammars.Indexed.Definition

/-! # Binarization for Indexed Grammars

This file constructs a binarization transformation for indexed grammars.
Given an indexed grammar with no ε-productions, isolated terminals, separated flags,
and a fresh start symbol, it produces an equivalent grammar in normal form.

This is Step 5 of Aho's Normal Form theorem.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar

section Binarization

variable (g : IndexedGrammar T)

/-- Lift an RHS symbol to the binarized grammar's nonterminal type. -/
def binLiftRhsSym : IRhsSymbol T g.nt g.flag →
    IRhsSymbol T (g.nt ⊕ (Nat × Nat)) (Option g.flag)
  | .terminal t => .terminal t
  | .nonterminal n f => .nonterminal (Sum.inl n) (f.map some)

/-- The auxiliary binarization function. -/
noncomputable def binarizeChain (i : Nat)
    (lhs : g.nt ⊕ (Nat × Nat))
    (syms : List (IRhsSymbol T (g.nt ⊕ (Nat × Nat)) (Option g.flag)))
    (idx : Nat) :
    List (IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag)) :=
  match syms with
  | [] => []
  | [s₁, s₂] => [⟨lhs, none, [s₁, s₂]⟩]
  | s :: rest =>
    let freshNt := Sum.inr (i, idx)
    ⟨lhs, none, [s, .nonterminal freshNt none]⟩ :: binarizeChain i freshNt rest (idx + 1)

/-- Binarize a single rule at index i. -/
noncomputable def binSingleRule (i : Nat) (r : IRule T g.nt g.flag) :
    List (IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag)) :=
  -- Terminal rule
  if r.rhs.any (fun s => match s with | .terminal _ => true | _ => false) && r.rhs.length == 1 then
    [⟨Sum.inl r.lhs, r.consume.map some, r.rhs.map g.binLiftRhsSym⟩]
  -- Flag pop: A[f·] → B (consume = some f, single nonterminal)
  else if r.consume.isSome ∧ r.rhs.length = 1 then
    [⟨Sum.inl r.lhs, r.consume.map some, r.rhs.map g.binLiftRhsSym⟩]
  -- Flag push: A → B[f·] (consume = none, single nonterminal with push)
  else if r.consume.isNone ∧ r.rhs.length = 1 ∧
          r.rhs.any (fun s => match s with | .nonterminal _ (some _) => true | _ => false) then
    [⟨Sum.inl r.lhs, none, r.rhs.map g.binLiftRhsSym⟩]
  -- Unit rule: A → B (consume = none, single nonterminal, no push)
  else if r.consume.isNone ∧ r.rhs.length = 1 then
    match r.rhs.head? with
    | some (.nonterminal B none) =>
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
      g.binarizeChain i (Sum.inl r.lhs) (x :: y :: rest) 0

/-- The binarized grammar. -/
noncomputable def binarize : IndexedGrammar T where
  nt := g.nt ⊕ (Nat × Nat)
  flag := Option g.flag
  initial := Sum.inl g.initial
  rules := ((g.rules.zipIdx).map fun ⟨r, i⟩ => g.binSingleRule i r).flatten

/-! ### Classification of rules under hypotheses -/

/-
Under the hypotheses, every rule falls into one of five categories.
-/
private lemma rule_classification
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (r : IRule T g.nt g.flag) (hr : r ∈ g.rules) :
    (∃ a : T, r.rhs = [IRhsSymbol.terminal a] ∧ r.consume = none) ∨
    (∃ f : g.flag, ∃ B : g.nt, r.consume = some f ∧ r.rhs = [IRhsSymbol.nonterminal B none]) ∨
    (∃ f : g.flag, ∃ B : g.nt, r.consume = none ∧ r.rhs = [IRhsSymbol.nonterminal B (some f)]) ∨
    (∃ B : g.nt, r.consume = none ∧ r.rhs = [IRhsSymbol.nonterminal B none]) ∨
    (r.consume = none ∧ r.rhs.length ≥ 2 ∧ ∀ s ∈ r.rhs, ∃ n : g.nt, s = IRhsSymbol.nonterminal n none) := by
  have := hfs r hr; rcases r with ⟨ lhs, consume, rhs ⟩ ; rcases consume with ( _ | f ) <;> simp_all +decide ;
  · rcases rhs with ( _ | ⟨ s, _ | ⟨ t, rhs ⟩ ⟩ ) <;> simp_all +decide [ IRule.FlagsSeparated ];
    · exact hne _ hr rfl;
    · grind +ring;
  · cases this ; aesop

/-! ### Helper lemmas for IsNormalForm -/

open Classical in
/-- Every rule produced by `binarizeChain` is in normal form. -/
private lemma binarizeChain_isNF (i : Nat)
    (lhs : g.nt ⊕ (Nat × Nat))
    (syms : List (IRhsSymbol T (g.nt ⊕ (Nat × Nat)) (Option g.flag)))
    (idx : Nat)
    (h_all_nt : ∀ s ∈ syms, ∃ n, s = IRhsSymbol.nonterminal (Sum.inl n) none ∧ n ≠ g.initial)
    (h_len : syms.length ≥ 2)
    (h_lhs : lhs ≠ Sum.inl g.initial)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binarizeChain i lhs syms idx) :
    @IRule.IsNF _ _ _ (instDecidableEq) r' (Sum.inl g.initial) := by
  induction' syms with s syms ih generalizing lhs idx;
  · contradiction;
  · rcases syms with ( _ | ⟨ t, _ | ⟨ u, syms ⟩ ⟩ ) <;> simp_all +decide [ binarizeChain ];
    · unfold IRule.IsNF; aesop;
    · rcases hr' with ( rfl | hr' );
      · exact Or.inl ⟨ rfl, by aesop ⟩;
      · exact ih.2 _ _ _ hr'

/-
binSingleRule for terminal rules produces NF rules.
-/
private lemma binSingleRule_isNF_terminal
    (a : T) (r : IRule T g.nt g.flag)
    (ha : r.rhs = [IRhsSymbol.terminal a]) (hc : r.consume = none)
    (i : Nat)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r) :
    @IRule.IsNF _ _ _ (instDecidableEq) r' (Sum.inl g.initial) := by
  unfold binSingleRule at hr';
  split_ifs at hr' <;> simp_all +decide [ IRule.IsNF ];
  exact Or.inr ⟨ a, rfl ⟩

/-
binSingleRule for flag pop rules produces NF rules.
-/
private lemma binSingleRule_isNF_flagPop
    (f : g.flag) (B : g.nt) (r : IRule T g.nt g.flag)
    (hc : r.consume = some f) (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (hfresh : ∀ s ∈ r.rhs, match s with | .nonterminal n _ => n ≠ g.initial | .terminal _ => True)
    (i : Nat)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r) :
    @IRule.IsNF _ _ _ (instDecidableEq) r' (Sum.inl g.initial) := by
  unfold IndexedGrammar.binSingleRule at hr';
  split_ifs at hr' <;> simp_all +decide [ IRule.IsNF ];
  exact Or.inl ⟨ B, rfl, hfresh ⟩

/-
binSingleRule for flag push rules produces NF rules.
-/
private lemma binSingleRule_isNF_flagPush
    (f : g.flag) (B : g.nt) (r : IRule T g.nt g.flag)
    (hc : r.consume = none) (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (hfresh : ∀ s ∈ r.rhs, match s with | .nonterminal n _ => n ≠ g.initial | .terminal _ => True)
    (i : Nat)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r) :
    @IRule.IsNF _ _ _ (instDecidableEq) r' (Sum.inl g.initial) := by
  unfold IndexedGrammar.binSingleRule at hr';
  split_ifs at hr' <;> simp_all +decide;
  refine' Or.inr <| Or.inr <| Or.inl _;
  exact ⟨ rfl, Sum.inl B, some f, rfl, by simpa using hfresh ⟩

/-
binSingleRule for unit rules produces NF rules.
-/
private lemma binSingleRule_isNF_unit
    (B : g.nt) (r : IRule T g.nt g.flag)
    (hc : r.consume = none) (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (hfresh : ∀ s ∈ r.rhs, match s with | .nonterminal n _ => n ≠ g.initial | .terminal _ => True)
    (i : Nat)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r) :
    @IRule.IsNF _ _ _ (instDecidableEq) r' (Sum.inl g.initial) := by
  unfold IndexedGrammar.binSingleRule at hr';
  split_ifs at hr' <;> simp_all +decide [ IRule.IsNF ];
  rcases hr' with ( rfl | rfl ) <;> simp +decide [ hfresh ]

/-
binSingleRule for multi-nonterminal rules produces NF rules.
-/
private lemma binSingleRule_isNF_multi
    (r : IRule T g.nt g.flag)
    (hc : r.consume = none) (hlen : r.rhs.length ≥ 2)
    (hall : ∀ s ∈ r.rhs, ∃ n : g.nt, s = IRhsSymbol.nonterminal n none)
    (hfresh : ∀ s ∈ r.rhs, match s with | .nonterminal n _ => n ≠ g.initial | .terminal _ => True)
    (i : Nat)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r) :
    @IRule.IsNF _ _ _ (instDecidableEq) r' (Sum.inl g.initial) := by
  unfold IndexedGrammar.binSingleRule at hr';
  rcases h : r.rhs with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp +decide [ h ] at hr' ⊢;
  · simp +decide [ h ] at hlen ⊢;
  · apply Classical.byContradiction
    intro h_contra;
    exact h_contra <| binarizeChain_isNF g i ( Sum.inl r.lhs ) ( g.binLiftRhsSym x :: g.binLiftRhsSym y :: map g.binLiftRhsSym l ) 0 ( by
      intro s hs; rcases List.mem_cons.mp hs with ( rfl | hs ) <;> simp_all +decide [ IndexedGrammar.binLiftRhsSym ] ;
      · rcases hall.1 with ⟨ n, rfl ⟩ ; exact ⟨ n, rfl, hfresh.1 ⟩ ;
      · rcases hs with ( rfl | ⟨ a, ha, rfl ⟩ );
        · rcases hall.2.1 with ⟨ n, rfl ⟩ ; exact ⟨ n, rfl, hfresh.2.1 ⟩ ;
        · rcases hall.2.2 a ha with ⟨ n, rfl ⟩ ; exact ⟨ n, rfl, hfresh.2.2 _ ha ⟩ ) ( by
      simp +arith +decide [ h ] at hlen ⊢ ) ( by
      intro h_eq;
      exact h_contra <| by
        induction' l with z l ih generalizing r' <;> simp +decide [ binarizeChain ] at hr' ⊢;
        · cases hall x ( by simp +decide [ h ] ) ; cases hall y ( by simp +decide [ h ] ) ; simp +decide [ *, IRule.IsNF ] at *;
          exact Or.inl ⟨ _, Or.inl ⟨ _, ⟨ rfl, rfl ⟩, hfresh ⟩ ⟩;
        · rcases hr' with ( rfl | hr' );
          · unfold IndexedGrammar.binLiftRhsSym; simp +decide [ h_eq ] ;
            exact Or.inl ⟨ rfl, by
              rcases x with ( _ | ⟨ n, f ⟩ ) <;> simp +decide [ * ] at *;
              exact ⟨ hall.1, hfresh.1 ⟩ ⟩;
          · apply binarizeChain_isNF g i (Sum.inr (i, 0)) (g.binLiftRhsSym y :: g.binLiftRhsSym z :: map g.binLiftRhsSym l) 1 (by
            simp +decide [ IndexedGrammar.binLiftRhsSym ];
            refine' ⟨ _, _, _ ⟩;
            · rcases y with ( _ | ⟨ n, f ⟩ ) <;> simp +decide [ * ] at *;
              tauto;
            · rcases z with ( _ | ⟨ n, f ⟩ ) <;> simp +decide [ * ] at *;
              tauto;
            · intro a ha; specialize hall a ( by rw [ h ] ; simp +decide [ ha ] ) ; rcases hall with ⟨ n, rfl ⟩ ; simp +decide [ hfresh ] ;
              grind) (by
            simp +arith +decide) (by
            lia) r' hr' ) r' hr'

open Classical in
/-- Under the grammar hypotheses, every rule produced by `binSingleRule` is in NF. -/
private lemma binSingleRule_isNF
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    (r : IRule T g.nt g.flag) (hr : r ∈ g.rules)
    (i : Nat)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r) :
    @IRule.IsNF _ _ _ (instDecidableEq) r' (Sum.inl g.initial) := by
  have hclass := rule_classification g hne hti hfs r hr
  rcases hclass with ⟨a, ha, hc⟩ | ⟨f, B, hc, hrhs⟩ | ⟨f, B, hc, hrhs⟩ | ⟨B, hc, hrhs⟩ | ⟨hc, hlen, hall⟩
  · exact binSingleRule_isNF_terminal g a r ha hc i r' hr'
  · exact binSingleRule_isNF_flagPop g f B r hc hrhs (hfresh r hr) i r' hr'
  · exact binSingleRule_isNF_flagPush g f B r hc hrhs (hfresh r hr) i r' hr'
  · exact binSingleRule_isNF_unit g B r hc hrhs (hfresh r hr) i r' hr'
  · exact binSingleRule_isNF_multi g r hc hlen hall (hfresh r hr) i r' hr'

open Classical in
theorem binarize_isNormalForm (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs') :
    ∃ _ : DecidableEq (g.binarize).nt, (g.binarize).IsNormalForm := by
  unfold IndexedGrammar.IsNormalForm;
  unfold IndexedGrammar.binarize; simp +decide [ List.mem_flatten ] ;
  exact ⟨ inferInstance, fun r r' i hi hr => binSingleRule_isNF g hne hti hfs hfresh r' ( by simpa using List.mem_iff_getElem.mp hi |> fun ⟨ j, hj ⟩ => by aesop ) i r hr ⟩

/-! ### Helper lemmas for generates_iff -/

/-- Lift a sentential-form symbol from `g` to `g.binarize`. -/
def liftBinISym : g.ISym → (g.binarize).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed (Sum.inl n) (σ.map some)

/-
`expandRhs` commutes with the lifting map.
-/
private lemma expandRhs_liftBin (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    (expandRhs g rhs σ).map g.liftBinISym =
    expandRhs g.binarize (rhs.map g.binLiftRhsSym) (σ.map some) := by
  unfold IndexedGrammar.expandRhs;
  induction' rhs with s rhs ih;
  · rfl;
  · cases s <;> simp +decide [ * ];
    · rfl;
    · cases ‹Option g.flag› <;> rfl

/-
Terminal words lift correctly.
-/
private lemma map_liftBinISym_terminal (w : List T) :
    w.map (ISym.terminal (g := g.binarize)) =
    (w.map (ISym.terminal (g := g))).map g.liftBinISym := by
  induction w <;> aesop

/-
The rule at index i in g.rules corresponds to binSingleRule rules in g.binarize.
-/
private lemma binSingleRule_rules_mem (r : IRule T g.nt g.flag) (i : Nat)
    (hr : g.rules[i]? = some r)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r) :
    r' ∈ g.binarize.rules := by
  unfold IndexedGrammar.binarize; simp +decide [ hr' ] ;
  grind

/-
binarizeChain applied to sentential form simulates multi-nonterminal expansion.
-/
private lemma binarizeChain_simulates (i : Nat)
    (syms : List (IRhsSymbol T g.nt g.flag))
    (σ : List g.flag)
    (h_all : ∀ s ∈ syms, ∃ n : g.nt, s = IRhsSymbol.nonterminal n none)
    (h_len : syms.length ≥ 2)
    (lhs : g.nt ⊕ (Nat × Nat))
    (idx : Nat)
    (u v : List (g.binarize).ISym)
    (h_rules : ∀ r' ∈ g.binarizeChain i lhs (syms.map g.binLiftRhsSym) idx,
               r' ∈ g.binarize.rules) :
    (g.binarize).Derives
      (u ++ [ISym.indexed lhs (σ.map some)] ++ v)
      (u ++ (expandRhs g.binarize (syms.map g.binLiftRhsSym) (σ.map some)) ++ v) := by
  induction' syms with s syms ih generalizing lhs σ idx u v;
  · contradiction;
  · rcases syms with ( _ | ⟨ s', _ | ⟨ s'', syms ⟩ ⟩ ) <;> simp_all +decide;
    · apply deri_of_tran;
      use ⟨ lhs, none, [ g.binLiftRhsSym s, g.binLiftRhsSym s' ] ⟩;
      use u, v, σ.map some;
      exact ⟨ h_rules _ ( by simp +decide [ IndexedGrammar.binarizeChain ] ), by simp +decide [ List.append_assoc ], by simp +decide [ List.append_assoc ] ⟩;
    · obtain ⟨ n, rfl ⟩ := h_all.1;
      convert deri_of_tran_deri _ _ using 1;
      exact u ++ [ ISym.indexed ( Sum.inl n ) ( map some σ ), ISym.indexed ( Sum.inr ( i, idx ) ) ( map some σ ) ] ++ v;
      · use ⟨ lhs, none, [ IRhsSymbol.nonterminal ( Sum.inl n ) none, IRhsSymbol.nonterminal ( Sum.inr ( i, idx ) ) none ] ⟩, u, v, σ.map some;
        simp +decide [ IndexedGrammar.expandRhs ];
        convert h_rules _ _ using 1;
        unfold IndexedGrammar.binLiftRhsSym; simp +decide [ IndexedGrammar.binarizeChain ] ;
      · convert ih σ |>.2 i idx ( idx + 1 ) ( u ++ [ ISym.indexed ( Sum.inl n ) ( map some σ ) ] ) v _ using 1;
        · simp +decide [ List.append_assoc ];
        · unfold IndexedGrammar.binLiftRhsSym; simp +decide [ IndexedGrammar.expandRhs ] ;
        · grind +locals

/-
One-step transform in g can be simulated by multi-step derive in g.binarize.
-/
private lemma binarize_forward_transforms
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    {w₁ w₂ : List g.ISym}
    (h : g.Transforms w₁ w₂) :
    (g.binarize).Derives (w₁.map g.liftBinISym) (w₂.map g.liftBinISym) := by
  obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := h;
  -- By rule_classification, r falls into one of five cases.
  obtain h | h | h | h | h := rule_classification g hne hti hfs r hr;
  · rcases h with ⟨ a, ha₁, ha₂ ⟩ ; simp_all +decide [ IndexedGrammar.expandRhs ] ;
    apply_rules [ deri_of_tran ];
    use ⟨ Sum.inl r.lhs, none, [ IRhsSymbol.terminal a ] ⟩, map g.liftBinISym u, map g.liftBinISym v, σ.map some;
    simp +decide [ IndexedGrammar.binarize, List.mem_flatten, List.mem_map ];
    refine' ⟨ _, _, _ ⟩;
    · obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hr;
      use r, i.val;
      simp +decide [ ha₁, ha₂, IndexedGrammar.binSingleRule ];
      exact ⟨ by rw [ List.mem_iff_get ] ; exact ⟨ ⟨ i, by simp ⟩, by aesop ⟩, rfl ⟩;
    · rfl;
    · rfl;
  · obtain ⟨ f, B, hf, hB ⟩ := h;
    have h_transform : (g.binarize).Transforms (u.map g.liftBinISym ++ [ISym.indexed (Sum.inl r.lhs) (some f :: σ.map some)] ++ v.map g.liftBinISym) (u.map g.liftBinISym ++ [ISym.indexed (Sum.inl B) (σ.map some)] ++ v.map g.liftBinISym) := by
      use ⟨Sum.inl r.lhs, some (some f), [IRhsSymbol.nonterminal (Sum.inl B) none]⟩;
      refine' ⟨ _, _, _, _, rfl, _ ⟩;
      · obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hr;
        convert binSingleRule_rules_mem g r i _ _ _;
        · aesop;
        · unfold IndexedGrammar.binSingleRule; aesop;
      · unfold IndexedGrammar.expandRhs; aesop;
    convert deri_of_tran _ using 1;
    cases r ; aesop;
  · rcases h with ⟨ f, B, hf, hB ⟩ ; simp_all +decide ;
    convert deri_of_tran _ using 1;
    use ⟨ Sum.inl r.lhs, none, [ IRhsSymbol.nonterminal ( Sum.inl B ) ( some ( some f ) ) ] ⟩, map g.liftBinISym u, map g.liftBinISym v, σ.map some; simp +decide [ *, IndexedGrammar.expandRhs ] ;
    exact ⟨ by
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hr;
      convert binSingleRule_rules_mem g r i _ _ _ using 1;
      · aesop;
      · unfold IndexedGrammar.binSingleRule; aesop;, rfl, rfl ⟩;
  · rcases h with ⟨ B, hB₁, hB₂ ⟩ ; simp_all +decide [ List.map_append ] ;
    -- Apply the first rule to get indexed (Sum.inl B) (none :: σ.map some).
    have h_step1 : g.binarize.Transforms (u.map g.liftBinISym ++ [ISym.indexed (Sum.inl r.lhs) (σ.map some)] ++ v.map g.liftBinISym) (u.map g.liftBinISym ++ [ISym.indexed (Sum.inl B) (none :: σ.map some)] ++ v.map g.liftBinISym) := by
      use ⟨Sum.inl r.lhs, none, [IRhsSymbol.nonterminal (Sum.inl B) (some none)]⟩, u.map g.liftBinISym, v.map g.liftBinISym, σ.map some;
      simp +decide [ IndexedGrammar.binarize, IndexedGrammar.expandRhs ];
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hr; use r, i; simp_all +decide [ IndexedGrammar.binSingleRule ] ;
      grind;
    -- Apply the second rule to get indexed (Sum.inl B) (σ.map some).
    have h_step2 : g.binarize.Transforms (u.map g.liftBinISym ++ [ISym.indexed (Sum.inl B) (none :: σ.map some)] ++ v.map g.liftBinISym) (u.map g.liftBinISym ++ [ISym.indexed (Sum.inl B) (σ.map some)] ++ v.map g.liftBinISym) := by
      use ⟨ Sum.inl B, some none, [IRhsSymbol.nonterminal (Sum.inl B) none] ⟩, u.map g.liftBinISym, v.map g.liftBinISym, σ.map some;
      simp +decide [ IndexedGrammar.binarize, IndexedGrammar.expandRhs ];
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hr; use r, i; simp_all +decide [ List.get ] ;
      grind +locals;
    convert deri_of_tran_deri h_step1 ( deri_of_tran h_step2 ) using 1;
    · simp +decide [ List.map_append ];
      rfl;
    · simp +decide [ IndexedGrammar.expandRhs ];
      rfl;
  · obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hr;
    have h_rules : ∀ r' ∈ g.binarizeChain i (Sum.inl r.lhs) (r.rhs.map g.binLiftRhsSym) 0, r' ∈ g.binarize.rules := by
      intro r' hr'
      have h_rules : r' ∈ g.binSingleRule i r := by
        unfold IndexedGrammar.binSingleRule;
        rcases r_rhs : r.rhs with ( _ | ⟨ x, _ | ⟨ y, rest ⟩ ⟩ ) <;> simp_all +decide;
      exact binSingleRule_rules_mem g r i ( by simpa [ hi ] ) r' h_rules;
    convert binarizeChain_simulates g i ( r.rhs ) σ h.2.2 h.2.1 ( Sum.inl r.lhs ) 0 ( u.map g.liftBinISym ) ( v.map g.liftBinISym ) h_rules using 1;
    · cases h : r.consume <;> aesop;
    · simp +decide [ hw₂, expandRhs_liftBin ]

/-
Multi-step derive in g lifts to multi-step derive in g.binarize.
-/
private lemma binarize_forward_derives
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    {w₁ w₂ : List g.ISym}
    (h : g.Derives w₁ w₂) :
    (g.binarize).Derives (w₁.map g.liftBinISym) (w₂.map g.liftBinISym) := by
  have h_ind : ∀ {w₁ w₂ : List g.ISym}, g.Derives w₁ w₂ → (g.binarize).Derives (w₁.map g.liftBinISym) (w₂.map g.liftBinISym) := by
    intros w₁ w₂ h; induction h;
    · exact deri_self g.binarize (map g.liftBinISym w₁);
    · rename_i h₁ h₂ h₃;
      exact h₃.trans ( binarize_forward_transforms g hne hti hfs hfresh h₂ );
  exact h_ind h

/-
Forward: g.Generates w → g.binarize.Generates w
-/
private lemma binarize_generates_forward
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    {w : List T} (hw : w ≠ []) (h : g.Generates w) :
    (g.binarize).Generates w := by
  convert binarize_forward_derives g hne hti hfs hfresh h;
  unfold IndexedGrammar.Generates; aesop;

/-! #### Backward direction: g.binarize generates w → g generates w -/

/-- Strip `none` values from a flag stack, recovering a stack for the original grammar. -/
def stripStack : List (Option g.flag) → List g.flag :=
  List.filterMap id

/-- Unbinarize a single sentential-form symbol. Maps:
- `terminal t` to `[terminal t]`
- `indexed (Sum.inl n) σ` to `[indexed n (stripStack σ)]`
- `indexed (Sum.inr (i, j)) σ` to the remaining nonterminals of the i-th rule from
  position j+1 onward, each with stack `stripStack σ`. -/
noncomputable def unbinarizeSym : (g.binarize).ISym → List g.ISym
  | .terminal t => [.terminal t]
  | .indexed (Sum.inl n) σ => [.indexed n (g.stripStack σ)]
  | .indexed (Sum.inr (i, _j)) σ =>
    match g.rules[i]? with
    | some r => (r.rhs.drop (_j + 1)).filterMap fun s =>
        match s with
        | .nonterminal n _ => some (.indexed n (g.stripStack σ))
        | .terminal _ => none
    | none => []

/-- Unbinarize a sentential form by flatMapping each symbol. -/
noncomputable def unbinarizeSF (w : List (g.binarize).ISym) : List g.ISym :=
  w.flatMap (g.unbinarizeSym)

/-
The initial sentential form unbinarizes correctly.
-/
private lemma unbinarize_initial :
    g.unbinarizeSF [.indexed (Sum.inl g.initial) []] = [.indexed g.initial []] := by
  rfl

/-
Terminal words unbinarize correctly.
-/
private lemma unbinarize_terminal (w : List T) :
    g.unbinarizeSF (w.map (.terminal (g := g.binarize))) = w.map (.terminal (g := g)) := by
  induction w <;> simp +decide [ *, List.map ];
  · rfl;
  · unfold IndexedGrammar.unbinarizeSF at *; aesop;

/-
unbinarizeSF distributes over append.
-/
private lemma unbinarizeSF_append (u v : List (g.binarize).ISym) :
    g.unbinarizeSF (u ++ v) = g.unbinarizeSF u ++ g.unbinarizeSF v := by
  unfold IndexedGrammar.unbinarizeSF; aesop;

/-
stripStack of (some f :: σ) = f :: stripStack σ.
-/
private lemma stripStack_some (f : g.flag) (σ : List (Option g.flag)) :
    g.stripStack (some f :: σ) = f :: g.stripStack σ := by
  exact toList_toArray

/-
stripStack of (none :: σ) = stripStack σ.
-/
private lemma stripStack_none (σ : List (Option g.flag)) :
    g.stripStack (none :: σ) = g.stripStack σ := by
  exact toList_toArray

/-
For a multi-nonterminal rule r (all nonterminals, no push),
    expandRhs in the binarized grammar unbinarizes to expandRhs in the original grammar.
-/
private lemma unbinarize_expandRhs_nonterminals
    (r : IRule T g.nt g.flag)
    (hall : ∀ s ∈ r.rhs, ∃ n : g.nt, s = IRhsSymbol.nonterminal n none)
    (σ : List (Option g.flag)) :
    g.unbinarizeSF (expandRhs g.binarize (r.rhs.map g.binLiftRhsSym) σ) =
    expandRhs g r.rhs (g.stripStack σ) := by
  unfold IndexedGrammar.unbinarizeSF IndexedGrammar.expandRhs;
  rw [ List.flatMap_map ];
  rw [ List.flatMap_map ];
  rw [ List.map_eq_flatMap ];
  refine' List.flatMap_congr fun x hx => _;
  rcases hall x hx with ⟨ n, rfl ⟩ ; rfl

/-
For a Sum.inr(i, j) nonterminal, unbinarizeSym gives the remaining nonterminals of rule i
    from position j+1 onward, each with stripped stack.
-/
private lemma unbinarizeSym_chain_nonterminal
    (r : IRule T g.nt g.flag) (i j : Nat) (hi : g.rules[i]? = some r)
    (hall : ∀ s ∈ r.rhs, ∃ n : g.nt, s = IRhsSymbol.nonterminal n none)
    (σ : List (Option g.flag)) :
    g.unbinarizeSym (.indexed (Sum.inr (i, j)) σ) =
    (r.rhs.drop (j + 1)).map fun s =>
      match s with
      | .nonterminal n _ => .indexed n (g.stripStack σ)
      | .terminal t => .terminal t := by
  unfold IndexedGrammar.unbinarizeSym;
  rw [ ← List.filterMap_eq_map ];
  rw [ filterMap_congr ];
  rotate_right;
  use fun s => match s with | IRhsSymbol.nonterminal n _ => some (ISym.indexed n (g.stripStack σ)) | IRhsSymbol.terminal _ => none;
  · grind;
  · intro x hx; specialize hall x ( List.mem_of_mem_drop hx ) ; rcases hall with ⟨ n, rfl ⟩ ; rfl;

/-
For a chain step rule with LHS = Sum.inr(i,j), consuming nothing, and RHS having
    either two binLifted nonterminals (end case) or one binLifted plus one Sum.inr (intermediate),
    the unbinarize is unchanged.
-/
private lemma unbinarize_chain_step_eq
    (i j : Nat) (r : IRule T g.nt g.flag) (hi : g.rules[i]? = some r)
    (hall : ∀ s ∈ r.rhs, ∃ n : g.nt, s = IRhsSymbol.nonterminal n none)
    (n : g.nt) (hn : r.rhs.drop (j + 1) = (.nonterminal n none) :: (r.rhs.drop (j + 2)))
    (σ : List (Option g.flag))
    (rhs_tail : List (IRhsSymbol T (g.nt ⊕ (Nat × Nat)) (Option g.flag)))
    -- rhs_tail is either [binLift next_nt] (end) or [Sum.inr(i,j+1)] (intermediate)
    (h_rhs_tail : (rhs_tail = (r.rhs.drop (j + 2)).map g.binLiftRhsSym) ∨
                  (rhs_tail = [IRhsSymbol.nonterminal (Sum.inr (i, j + 1)) none])) :
    g.unbinarizeSym (.indexed (Sum.inr (i, j)) σ) =
    g.unbinarizeSF (expandRhs g.binarize
      (IRhsSymbol.nonterminal (Sum.inl n) none :: rhs_tail) σ) := by
  rcases h_rhs_tail with ( rfl | rfl );
  · rw [ unbinarizeSym_chain_nonterminal ];
    rotate_left;
    exact r;
    · exact hi;
    · assumption;
    · unfold IndexedGrammar.unbinarizeSF IndexedGrammar.expandRhs;
      rw [ hn ];
      rw [ List.map_cons, List.map_cons ];
      rw [ List.flatMap_cons, List.flatMap_map ];
      rw [ List.flatMap_map ];
      rw [ List.map_eq_flatMap ];
      congr! 1;
      refine' List.flatMap_congr fun x hx => _;
      rcases hall x ( List.mem_of_mem_drop hx ) with ⟨ n, rfl ⟩ ; rfl;
  · unfold IndexedGrammar.unbinarizeSym IndexedGrammar.unbinarizeSF;
    unfold IndexedGrammar.unbinarizeSym IndexedGrammar.expandRhs; simp +decide [ hi ] ;
    rw [ hn ] ; rfl;

/-
Helper: a rule in g.binarize.rules came from binSingleRule of some original rule.
-/
private lemma mem_binarize_rules_origin
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binarize.rules) :
    ∃ (i : Nat) (r : IRule T g.nt g.flag), g.rules[i]? = some r ∧ r' ∈ g.binSingleRule i r := by
  unfold IndexedGrammar.binarize at hr';
  grind +suggestions

/-- unbinarize_rule_step for a specific binSingleRule output r' given original rule r. -/
private lemma unbinarize_rule_step_of
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    (i : Nat) (r : IRule T g.nt g.flag) (hi : g.rules[i]? = some r)
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binSingleRule i r)
    (σ : List (Option g.flag)) :
    g.Derives
      (g.unbinarizeSym (match r'.consume with
        | none => .indexed r'.lhs σ
        | some f => .indexed r'.lhs (f :: σ)))
      (g.unbinarizeSF (expandRhs g.binarize r'.rhs σ)) := by
  sorry

/-- For a rule from binSingleRule, unbinarizeSym of the LHS symbol gets derived to
    unbinarizeSF of the expandRhs of the RHS. -/
private lemma unbinarize_rule_step
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    (r' : IRule T (g.nt ⊕ (Nat × Nat)) (Option g.flag))
    (hr' : r' ∈ g.binarize.rules)
    (σ : List (Option g.flag)) :
    g.Derives
      (g.unbinarizeSym (match r'.consume with
        | none => .indexed r'.lhs σ
        | some f => .indexed r'.lhs (f :: σ)))
      (g.unbinarizeSF (expandRhs g.binarize r'.rhs σ)) := by
  obtain ⟨i, r, hi, hr⟩ := mem_binarize_rules_origin g r' hr'
  exact unbinarize_rule_step_of g hne hti hfs hfresh i r hi r' hr σ

/-- Key simulation: one step in g.binarize corresponds to zero or one steps in g. -/
private lemma unbinarize_transforms
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    {w₁ w₂ : List (g.binarize).ISym}
    (h : (g.binarize).Transforms w₁ w₂) :
    g.Derives (g.unbinarizeSF w₁) (g.unbinarizeSF w₂) := by
  obtain ⟨r', u, v, σ, hr', hw₁, hw₂⟩ := h
  have key := unbinarize_rule_step g hne hti hfs hfresh r' hr' σ
  have sf_single : ∀ (s : (g.binarize).ISym), g.unbinarizeSF [s] = g.unbinarizeSym s := by
    intro s; simp [unbinarizeSF, List.flatMap]
  cases hc : r'.consume with
  | none =>
    rw [hc] at hw₁ key; simp only at hw₁ key
    rw [hw₁, hw₂]; simp only [unbinarizeSF_append]
    have : g.unbinarizeSF [ISym.indexed r'.lhs σ] = g.unbinarizeSym (.indexed r'.lhs σ) := sf_single _
    rw [this]; exact deri_with_suffix _ (deri_with_prefix _ key)
  | some f =>
    rw [hc] at hw₁ key; simp only at hw₁ key
    rw [hw₁, hw₂]; simp only [unbinarizeSF_append]
    have : g.unbinarizeSF [ISym.indexed r'.lhs (f :: σ)] = g.unbinarizeSym (.indexed r'.lhs (f :: σ)) := sf_single _
    rw [this]; exact deri_with_suffix _ (deri_with_prefix _ key)

/-
Simulation lifts to multi-step derivations.
-/
private lemma unbinarize_derives
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    {w₁ w₂ : List (g.binarize).ISym}
    (h : (g.binarize).Derives w₁ w₂) :
    g.Derives (g.unbinarizeSF w₁) (g.unbinarizeSF w₂) := by
  induction h;
  · constructor;
  · apply IndexedGrammar.deri_of_deri_deri; assumption; exact IndexedGrammar.unbinarize_transforms g hne hti hfs hfresh ‹_›;

/-
Backward: g.binarize.Generates w → g.Generates w
-/
private lemma binarize_generates_backward
    (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs')
    {w : List T} (hw : w ≠ []) (h : (g.binarize).Generates w) :
    g.Generates w := by
  convert unbinarize_derives g hne hti hfs hfresh h;
  -- By definition of `Generates`, we have that `g.Generates w` means `g.Derives [ISym.indexed g.initial []] (w.map ISym.terminal)`.
  rw [IndexedGrammar.Generates];
  convert Iff.rfl;
  convert unbinarize_terminal g w

/-! ### Main theorems -/

theorem binarize_generates_iff (hne : g.NoEpsilon') (hti : g.TerminalsIsolated)
    (hfs : g.FlagsSeparated) (hfresh : g.StartNotOnRhs') :
    ∀ w : List T, w ≠ [] → ((g.binarize).Generates w ↔ g.Generates w) := by
  intro w hw
  exact ⟨binarize_generates_backward g hne hti hfs hfresh hw,
         binarize_generates_forward g hne hti hfs hfresh hw⟩

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