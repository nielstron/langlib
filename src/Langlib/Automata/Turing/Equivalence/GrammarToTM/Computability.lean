import Mathlib
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Automata.Turing.Equivalence.GrammarToTM.Decidability
import Langlib.Utilities.PrimrecHelpers

/-! # Computability of Grammar Operations

This file establishes that the `grammarTest` function is `Computable₂`.

## Key results

- `grammarTest_computable₂` — the grammar test function is `Computable₂`

## Structure

1. `Primcodable` instances for `symbol` and `grule`
2. Primrec lemmas for symbol constructors and grule field projections
3. `primrec_applyRuleAt` — `applyRuleAt` is primitive recursive
4. `computable_extractTerminals` — `extractTerminals` is computable
5. `primrec_applyRuleSeq_step` / `computable_applyRuleSeq` — rule sequence application
6. `grammarTest_computable₂` — the final result
-/

variable {T : Type} [DecidableEq T]

/-! ### Primcodable instances -/

noncomputable def symbolEquiv (T N : Type) : symbol T N ≃ T ⊕ N where
  toFun s := match s with
    | .terminal t => Sum.inl t
    | .nonterminal n => Sum.inr n
  invFun s := match s with
    | Sum.inl t => .terminal t
    | Sum.inr n => .nonterminal n
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

noncomputable instance symbolPrimcodable {T N : Type}
    [Primcodable T] [Primcodable N] : Primcodable (symbol T N) :=
  Primcodable.ofEquiv (T ⊕ N) (symbolEquiv T N)

noncomputable def gruleEquiv (T N : Type) :
    grule T N ≃ List (symbol T N) × N × List (symbol T N) × List (symbol T N) where
  toFun r := (r.input_L, r.input_N, r.input_R, r.output_string)
  invFun p := { input_L := p.1, input_N := p.2.1, input_R := p.2.2.1, output_string := p.2.2.2 }
  left_inv r := by cases r; rfl
  right_inv p := by obtain ⟨a, b, c, d⟩ := p; rfl

noncomputable instance grulePrimcodable {T N : Type}
    [Primcodable T] [Primcodable N] : Primcodable (grule T N) :=
  Primcodable.ofEquiv _ (gruleEquiv T N)

/-! ### Symbol constructors are primrec -/

theorem primrec_symbol_nonterminal {N : Type} [Primcodable T] [Primcodable N] :
    Primrec (symbol.nonterminal : N → symbol T N) := by
  convert Primrec.of_eq _ _
  exact fun n => (symbolEquiv T N).symm (Sum.inr n)
  · exact Primrec.of_equiv_symm.comp Primrec.sumInr
  · aesop

theorem primrec_symbol_terminal {N : Type} [Primcodable T] [Primcodable N] :
    Primrec (symbol.terminal : T → symbol T N) := by
  convert Primrec.of_eq _ _
  exact fun t => (symbolEquiv T N).symm (Sum.inl t)
  · exact Primrec.of_equiv_symm.comp Primrec.sumInl
  · aesop

/-- Case analysis on `symbol` is primrec. -/
theorem primrec_symbol_casesOn {N σ : Type} [Primcodable T] [Primcodable N] [Primcodable σ]
    {α : Type} [Primcodable α]
    {f : α → symbol T N} {g : α → T → σ} {h : α → N → σ}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => match f a with
      | .terminal t => g a t
      | .nonterminal n => h a n) := by
  convert Primrec.sumCasesOn (Primrec.of_equiv.comp hf) hg hh using 1
  exact funext fun x => by cases f x <;> rfl

/-! ### grule field projections are primrec -/

theorem primrec_grule_inputL {N : Type} [Primcodable T] [Primcodable N] :
    Primrec (fun (r : grule T N) => r.input_L) :=
  Primrec.fst.comp Primrec.of_equiv

theorem primrec_grule_inputN {N : Type} [Primcodable T] [Primcodable N] :
    Primrec (fun (r : grule T N) => r.input_N) :=
  (Primrec.fst.comp Primrec.snd).comp Primrec.of_equiv

theorem primrec_grule_inputR {N : Type} [Primcodable T] [Primcodable N] :
    Primrec (fun (r : grule T N) => r.input_R) :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp Primrec.of_equiv

theorem primrec_grule_outputString {N : Type} [Primcodable T] [Primcodable N] :
    Primrec (fun (r : grule T N) => r.output_string) :=
  (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp Primrec.of_equiv

/-! ### applyRuleAt is primrec -/

theorem primrec_applyRuleAt {N : Type} [DecidableEq N]
    [Primcodable T] [Primcodable N] :
    Primrec (fun (args : grule T N × List (symbol T N) × ℕ) =>
      applyRuleAt args.1 args.2.1 args.2.2) := by
        convert Primrec.ite _ _ _ using 1;
        · have h_conj : Primrec (fun (args : grule T N × List (symbol T N) × ℕ) => List.take (args.1.input_L ++ [symbol.nonterminal args.1.input_N] ++ args.1.input_R).length (List.drop args.2.2 args.2.1)) := by
            have h_conj : Primrec (fun (args : grule T N × List (symbol T N) × ℕ) => (args.1.input_L ++ [symbol.nonterminal args.1.input_N] ++ args.1.input_R).length) := by
              simp +zetaDelta at *;
              convert Primrec.nat_add.comp ( Primrec.list_length.comp ( primrec_grule_inputL.comp ( Primrec.fst ) ) ) ( Primrec.nat_add.comp ( Primrec.list_length.comp ( primrec_grule_inputR.comp ( Primrec.fst ) ) ) ( Primrec.const 1 ) ) using 1;
              · infer_instance;
              · infer_instance;
            have h_conj : Primrec (fun (args : grule T N × List (symbol T N) × ℕ) => List.drop args.2.2 args.2.1) := by
              convert primrec₂_list_drop.comp _ _ using 1;
              · exact Primrec.snd.comp ( Primrec.snd );
              · exact Primrec.fst.comp ( Primrec.snd );
            convert Primrec₂.comp _ _ _ using 1;
            all_goals try infer_instance;
            · exact?;
            · assumption;
            · exact h_conj;
          convert Primrec.eq.comp h_conj _ using 1;
          rotate_left;
          exact fun args => args.1.input_L ++ [ symbol.nonterminal args.1.input_N ] ++ args.1.input_R;
          · convert Primrec.list_append.comp ( Primrec.list_append.comp ( primrec_grule_inputL.comp ( Primrec.fst ) ) ( Primrec.list_cons.comp ( primrec_symbol_nonterminal.comp ( primrec_grule_inputN.comp ( Primrec.fst ) ) ) ( Primrec.const [ ] ) ) ) ( primrec_grule_inputR.comp ( Primrec.fst ) ) using 1;
            · infer_instance;
            · infer_instance;
            · infer_instance;
            · infer_instance;
          · grind;
        · convert Primrec.option_some.comp _ using 1;
          convert Primrec.list_append.comp _ _ using 1;
          · exact Primrec.list_append.comp ( primrec₂_list_take.comp ( Primrec.snd.comp Primrec.snd ) ( Primrec.fst.comp Primrec.snd ) ) ( primrec_grule_outputString.comp Primrec.fst );
          · convert primrec₂_list_drop.comp _ _ using 1;
            · convert Primrec.comp ( Primrec.list_length ) ( Primrec.list_append.comp ( Primrec.list_append.comp ( primrec_grule_inputL.comp ( Primrec.fst ) ) ( Primrec.list_cons.comp ( primrec_symbol_nonterminal.comp ( primrec_grule_inputN.comp ( Primrec.fst ) ) ) ( Primrec.const [] ) ) ) ( primrec_grule_inputR.comp ( Primrec.fst ) ) ) using 1;
              · infer_instance;
              · infer_instance;
              · infer_instance;
              · infer_instance;
            · exact primrec₂_list_drop.comp ( Primrec.snd.comp ( Primrec.snd ) ) ( Primrec.fst.comp ( Primrec.snd ) );
        · exact Primrec.const none

/-! ### extractTerminals is computable -/

theorem computable_extractTerminals {N : Type}
    [Primcodable T] [Primcodable N] :
    Computable (extractTerminals (T := T) (N := N)) := by
      convert Primrec.to_comp _;
      convert Primrec.list_foldr _ _ _ using 1;
      rotate_left;
      exact symbol T N;
      exact?;
      exact fun l => l;
      exact fun _ => some [];
      exact fun l p => match p.1 with | .terminal t => Option.map ( t :: · ) p.2 | .nonterminal _ => none;
      · exact Primrec.id;
      · exact Primrec.const _;
      · convert primrec_symbol_casesOn _ _ _ using 1;
        all_goals try infer_instance;
        · exact Primrec.fst.comp ( Primrec.snd );
        · convert Primrec.option_map _ _ using 1;
          exact?;
          · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) );
          · exact Primrec.list_cons.comp ( Primrec.snd.comp Primrec.fst ) Primrec.snd;
        · exact Primrec.const none;
      · unfold extractTerminals;
        congr! 2;
        exact funext fun x => funext fun y => by cases x <;> cases y <;> rfl;

/-! ### applyRuleSeq with fixed args is computable -/

private theorem step_eq_bind {N : Type} [DecidableEq N]
    (rules : List (grule T N))
    (p : Option (List (symbol T N)) × (ℕ × ℕ)) :
    (match p.1 with
      | none => none
      | some sf =>
        match rules[p.2.1]? with
        | none => none
        | some r => applyRuleAt r sf p.2.2) =
    p.1.bind (fun sf => (rules[p.2.1]?).bind (fun r => applyRuleAt r sf p.2.2)) := by
  cases p.1 <;> simp [Option.bind]
  rename_i sf
  cases rules[p.2.1]? <;> simp [Option.bind]

theorem primrec_applyRuleSeq_step {N : Type} [DecidableEq N]
    [Primcodable T] [Primcodable N]
    (rules : List (grule T N)) :
    Primrec (fun (p : Option (List (symbol T N)) × (ℕ × ℕ)) =>
      match p.1 with
      | none => none
      | some sf =>
        match rules[p.2.1]? with
        | none => none
        | some r => applyRuleAt r sf p.2.2) := by
          simp [step_eq_bind];
          apply Primrec.option_bind;
          · exact Primrec.fst;
          · have h_step : Primrec (fun (p : (Option (List (symbol T N)) × (ℕ × ℕ)) × List (symbol T N)) => (rules[p.1.2.1]?).bind (fun r => applyRuleAt r p.2 p.1.2.2)) := by
              have h_step : Primrec (fun (p : (Option (List (symbol T N)) × (ℕ × ℕ)) × List (symbol T N)) => (rules[p.1.2.1]?)) := by
                convert Primrec.list_getElem? |> Primrec.comp <| Primrec.const rules |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd.comp Primrec.fst ) using 1;
              have h_step : Primrec (fun (p : (Option (List (symbol T N)) × (ℕ × ℕ)) × List (symbol T N) × grule T N) => applyRuleAt p.2.2 p.2.1 p.1.2.2) := by
                convert primrec_applyRuleAt.comp _ using 1;
                rotate_left;
                all_goals try infer_instance;
                exact fun p => ( p.2.2, p.2.1, p.1.2.2 );
                · exact Primrec.pair ( Primrec.snd.comp ( Primrec.snd ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) );
                · rfl;
              convert Primrec.option_bind _ _ using 1;
              all_goals try infer_instance;
              · grind;
              · convert h_step.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1;
            exact?

theorem computable_applyRuleSeq {N : Type} [DecidableEq N]
    [Primcodable T] [Primcodable N]
    (rules : List (grule T N)) (init : List (symbol T N)) :
    Computable (fun seq => applyRuleSeq rules init seq) := by
      apply Computable.of_eq;
      convert Primrec.to_comp _;
      exact fun seq => List.foldl ( fun acc step => match acc with | none => none | some sf => match rules[step.1]? with | none => none | some r => applyRuleAt r sf step.2 ) ( some init ) seq;
      · convert Primrec.list_foldl _ _ _;
        rotate_left;
        exact?;
        exact fun _ p => match p.1 with | none => none | some sf => match rules[p.2.1]? with | none => none | some r => applyRuleAt r sf p.2.2;
        · exact Primrec.id;
        · exact Primrec.const _;
        · convert primrec_applyRuleSeq_step rules |> Primrec.comp <| Primrec.snd using 1;
        · rfl;
      · exact fun _ => rfl

/-! ### Main result -/

theorem grammarTest_computable₂ (g : grammar T)
    [DecidableEq g.nt] [Primcodable T] [Primcodable g.nt] :
    Computable₂ (grammarTest g) := by
      apply Computable₂.mk;
      -- By definition of `grammarTest`, we can rewrite it as a composition of computable functions.
      have h_comp : Computable (fun p : (List (ℕ × ℕ)) × List T =>
        match applyRuleSeq g.rules [symbol.nonterminal g.initial] p.1 with
        | none => false
        | some sf => extractTerminals sf == some p.2) := by
          convert Computable.option_casesOn ( computable_applyRuleSeq g.rules [ symbol.nonterminal g.initial ] |> Computable.comp <| Computable.fst ) ( Computable.const false ) _ using 1;
          rotate_left;
          exact fun p sf => extractTerminals sf == some p.2;
          · apply Computable₂.mk;
            convert Computable.comp ( show Computable ( fun p : Option ( List T ) × Option ( List T ) => p.1 == p.2 ) from ?_ ) ( Computable.pair ( computable_extractTerminals.comp ( Computable.snd ) ) ( Computable.option_some.comp ( Computable.snd.comp ( Computable.fst ) ) ) ) using 1;
            -- The function that checks if two options are equal is primitive recursive.
            have h_option_eq_primrec : Primrec (fun p : Option (List T) × Option (List T) => p.1 == p.2) := by
              convert Primrec.eq;
              rotate_left;
              exact Option ( List T );
              exact?;
              constructor <;> intro h <;> simp_all +decide [ PrimrecRel ];
              · use inferInstance;
                grind;
              · convert h using 1;
                constructor <;> intro h <;> simp_all +decide [ PrimrecPred ];
                grind +revert;
            exact h_option_eq_primrec.to_comp;
          · exact funext fun p => by cases applyRuleSeq g.rules [ symbol.nonterminal g.initial ] p.1 <;> rfl;
      exact h_comp