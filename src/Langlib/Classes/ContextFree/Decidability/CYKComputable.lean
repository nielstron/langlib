import Mathlib
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Langlib.Classes.ContextFree.Pumping.ParseTree
import Langlib.Classes.ContextFree.Decidability.PrimrecHelpers
import Langlib.Classes.ContextFree.Decidability.Membership

/-! # Computable CYK

This file shows that the CYK decision procedure for context-free grammars
yields a `ComputablePred`.

## Strategy

We define a bitvector-based CYK table computation where nonterminal sets are
encoded as natural numbers (bitvectors). The table is built bottom-up by
`Nat.rec` on substring length. Each step is shown to be `Primrec` by composing
primitive recursive building blocks.

Correctness is established by showing the bitvector CYK agrees with the existing
`cykDecideAux` (which is already proven correct via `cykDecideAux_iff_canDerive`).

## Main results

- `cf_membership_computable` — membership in a CF language is `ComputablePred`.
-/

open List

/-! ## Bitvector operations -/

section BitvectorOps

/-- Check if bit `idx` is set in `bv`. -/
def ntInSet (bv : ℕ) (idx : ℕ) : Bool := Nat.testBit bv idx

/-- Set bit `idx` in `bv`. -/
def ntSetBit (bv : ℕ) (idx : ℕ) : ℕ := bv ||| (1 <<< idx)

lemma ntInSet_ntSetBit_self (bv : ℕ) (idx : ℕ) :
    ntInSet (ntSetBit bv idx) idx = true := by
  simp [ntInSet, ntSetBit, Nat.testBit_or, Nat.testBit_shiftLeft]

lemma ntInSet_ntSetBit_of_true (bv : ℕ) (idx idx' : ℕ)
    (h : ntInSet bv idx = true) :
    ntInSet (ntSetBit bv idx') idx = true := by
  simp [ntInSet, ntSetBit, Nat.testBit_or] at *
  exact Or.inl h

lemma ntInSet_zero (idx : ℕ) : ntInSet 0 idx = false := by
  simp [ntInSet]

end BitvectorOps

/-! ## Primrec proofs for bitvector operations -/

section BitvectorPrimrec

lemma primrec₂_ntInSet : Primrec₂ (fun bv idx => ntInSet bv idx) := by
  have h_div : Primrec₂ (fun (bv : ℕ) (idx : ℕ) => bv / 2 ^ idx) := by
    have h_div : Primrec₂ (fun (bv : ℕ) (idx : ℕ) => bv / 2 ^ idx) := by
      have h_exp : Primrec₂ (fun (idx : ℕ) (bv : ℕ) => 2 ^ idx) := by
        have h_exp : Primrec (fun (idx : ℕ) => 2 ^ idx) := by
          rw [ show ( fun idx => 2 ^ idx : ℕ → ℕ ) = fun idx => Nat.recOn idx 1 fun n ih => 2 * ih by funext n; induction n <;> simp +decide [ *, pow_succ' ] ];
          have h_pow : Primrec₂ (fun (n : ℕ) (ih : ℕ) => 2 * ih) := by
            exact Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd );
          field_simp;
          exact?;
        exact h_exp.comp ( Primrec.fst )
      exact Primrec.nat_div.comp ( Primrec.fst ) ( h_exp.comp ( Primrec.snd ) ( Primrec.fst ) );
    exact h_div;
  have h_mod : Primrec₂ (fun (n : ℕ) (m : ℕ) => n % m) := by
    exact?;
  have h_mod : Primrec₂ (fun (bv : ℕ) (idx : ℕ) => (bv / 2 ^ idx) % 2) := by
    exact h_mod.comp₂ h_div ( Primrec₂.const 2 );
  have h_eq : Primrec₂ (fun (n : ℕ) (m : ℕ) => decide (n = m)) := by
    convert Primrec.eq using 1;
    exact?;
  convert h_eq.comp₂ h_mod ( Primrec₂.const 1 ) using 1;
  ext; simp [ntInSet];
  exact?

lemma primrec₂_ntSetBit : Primrec₂ (fun bv idx => ntSetBit bv idx) := by
  unfold ntSetBit;
  refine' Primrec.of_eq _ _;
  exact fun n => if Nat.testBit n.1 n.2 then n.1 else n.1 + 2 ^ n.2;
  · convert Primrec.cond _ _ _ using 1;
    rotate_left;
    exact fun n => Nat.testBit n.1 n.2;
    exact fun n => n.1;
    exact fun n => n.1 + 2 ^ n.2;
    · convert primrec₂_ntInSet using 1;
    · exact Primrec.fst;
    · have h_primrec_exp : Primrec (fun (n : ℕ) => 2 ^ n) := by
        have h_pow_two_primrec : Primrec (fun n => 2 ^ n) := by
          have : ∀ n, 2 ^ n = Nat.rec 1 (fun _ m => 2 * m) n := by
            exact fun n => by induction n <;> simp +decide [ *, pow_succ' ] ;
          rw [ show ( fun n => 2 ^ n ) = _ from funext this ];
          convert Primrec.nat_rec₁ _ _ using 1;
          exact Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd );
        exact h_pow_two_primrec;
      exact Primrec.nat_add.comp ( Primrec.fst ) ( h_primrec_exp.comp ( Primrec.snd ) );
    · grind;
  · intro n; split_ifs <;> simp_all +decide [ Nat.testBit, Nat.shiftLeft_eq ] ;
    · refine' Eq.symm ( Nat.eq_of_testBit_eq fun i => _ );
      by_cases hi : i = n.2 <;> simp_all +decide [ Nat.testBit_two_pow ];
      · simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
      · aesop;
    · -- Since $n.1$ and $2^n.2$ have no overlapping 1s in their binary representations, their bitwise OR is equal to their sum.
      have h_no_overlap : ∀ (m n : ℕ), (m &&& n = 0) → (m ||| n = m + n) := by
        intro m n h; induction' m using Nat.binaryRec with m ih generalizing n <;> induction' n using Nat.binaryRec with n ih' <;> simp_all +decide [ Nat.shiftLeft, Nat.shiftRight ] ;
        cases m <;> cases n <;> simp_all +decide [ Nat.bit ];
        · ring;
        · ring;
        · ring;
      rw [ h_no_overlap ];
      refine' Nat.eq_of_testBit_eq fun i => _;
      by_cases hi : i = n.2 <;> simp_all +decide [ Nat.testBit_two_pow ];
      · simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
      · grind

end BitvectorPrimrec

/-! ## Fold over fixed lists is Primrec -/

section FoldFixed

variable {α σ : Type} [Primcodable α] [Primcodable σ]

/-- Folding over a fixed list with a Primrec step function is Primrec. -/
lemma primrec_foldl_fixed {β : Type} (l : List β)
    (step : β → (α → σ → σ))
    (h_step : ∀ b : β, Primrec₂ (step b)) :
    Primrec₂ (fun (a : α) (init : σ) => l.foldl (fun acc b => step b a acc) init) := by
  induction l with
  | nil => exact Primrec.snd
  | cons hd tl ih =>
    simp only [List.foldl]
    show Primrec₂ fun a init => tl.foldl (fun acc b => step b a acc) (step hd a init)
    exact ih.comp Primrec.fst ((h_step hd).comp Primrec.fst Primrec.snd)

end FoldFixed

/-! ## CYK Table Definitions (Bitvector-based) -/

section CYKDefs

variable {T : Type} [DecidableEq T]

/-- Bitvector lookup for terminal rules: given terminal `t`, compute the bitvector
    of nonterminals with leaf rule `nt → t`. -/
def cykLeafBV (leafData : List (ℕ × T)) (t : T) : ℕ :=
  leafData.foldl (fun bv p => if p.2 == t then ntSetBit bv p.1 else bv) 0

/-- Build the CYK table bottom-up.

    The result is a flat `List ℕ` where entry at index `l * n + i`
    (with `n = w.length`) is the bitvector of nonterminals that derive
    the substring `w[i .. i+l]` (length `l+1` starting at position `i`).

    `extraRows` is the number of rows beyond the base row. -/
def cykBuildTable (leafData : List (ℕ × T)) (nodeData : List (ℕ × ℕ × ℕ))
    (w : List T) : ℕ → List ℕ
  | 0 => w.map (cykLeafBV leafData)
  | k + 1 =>
    let prev := cykBuildTable leafData nodeData w k
    let n := w.length
    prev ++ (List.range n).map fun i =>
      if i + k + 2 > n then 0
      else (List.range (k + 1)).foldl (fun bv j =>
        nodeData.foldl (fun bv' r =>
          if ntInSet (prev.getD (j * n + i) 0) r.2.1 &&
             ntInSet (prev.getD ((k - j) * n + (i + j + 1)) 0) r.2.2
          then ntSetBit bv' r.1 else bv') bv
      ) 0

/-- Full membership check via CYK bitvector table. -/
def cykMemCheck (leafData : List (ℕ × T)) (nodeData : List (ℕ × ℕ × ℕ))
    (startIdx : ℕ) (w : List T) : Bool :=
  match w with
  | [] => false
  | _ => ntInSet ((cykBuildTable leafData nodeData w (w.length - 1)).getD
            ((w.length - 1) * w.length) 0) startIdx

end CYKDefs

/-! ## CYK Bitvector is Primitive Recursive -/

section CYKPrimrec

variable {T : Type} [DecidableEq T] [Primcodable T]

/-
`cykLeafBV` with fixed leaf data is Primrec.
-/
lemma primrec_cykLeafBV (ld : List (ℕ × T)) :
    Primrec (fun t : T => cykLeafBV ld t) := by
  have h_foldl : ∀ (l : List (ℕ × T)), Primrec (fun t => List.foldl (fun bv p => if p.2 == t then ntSetBit bv p.1 else bv) 0 l) := by
    intro l
    induction' l using List.reverseRecOn with p l ih;
    · exact Primrec.const 0;
    · simp +zetaDelta at *;
      convert Primrec.ite _ _ _ using 1;
      · exact Primrec.eq.comp ( Primrec.const _ ) ( Primrec.id );
      · exact Primrec.comp ( primrec₂_ntSetBit.comp ( Primrec.fst ) ( Primrec.snd ) ) ( ih.pair ( Primrec.const _ ) );
      · exact ih;
  exact h_foldl ld

/-
The innermost rule step is Primrec₂.
    Context: `(table, n, i, k, j)`. Accumulator: bitvector.
-/
lemma primrec₂_ruleStep (ntR lR rR : ℕ) :
    Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) =>
      if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR &&
         ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 +
            (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR
      then ntSetBit bv ntR else bv) := by
  have h_primrec : Primrec (fun ctx : List ℕ × ℕ × ℕ × ℕ × ℕ => ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) := by
    have h_getD : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l.getD i 0) := by
      convert Primrec.list_getD 0 using 1;
    exact h_getD.comp ( Primrec.fst ) ( by exact Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ) ( Primrec.fst.comp ( Primrec.snd ) ) ) ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) );
  have h_primrec : Primrec (fun ctx : List ℕ × ℕ × ℕ × ℕ × ℕ => ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) := by
    convert Primrec.list_getD 0 |> Primrec.comp <| Primrec.fst.comp ( Primrec.id ) |> Primrec.pair <| _ using 1;
    apply_rules [ Primrec.nat_add.comp, Primrec.nat_mul.comp, Primrec.nat_sub.comp, Primrec.fst, Primrec.snd ];
    all_goals try { exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) };
    · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) ) );
    · exact Primrec.fst.comp ( Primrec.snd );
    · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) );
    · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) ) );
    · exact Primrec.const 1;
  have h_primrec : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR && ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR then ntSetBit bv ntR else bv) := by
    have h_cond : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR && ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR then true else false) := by
      have h_cond : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR) := by
        have h_cond : Primrec₂ (fun (x : ℕ) (y : ℕ) => ntInSet x y) := by
          exact?;
        convert h_cond.comp ( ‹Primrec fun ctx : List ℕ × ℕ × ℕ × ℕ × ℕ => ctx.1.getD ( ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1 ) 0›.comp ( Primrec.fst ) ) ( Primrec.const lR ) using 1;
      have h_cond : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR) := by
        convert Primrec₂.comp ( primrec₂_ntInSet ) ( h_primrec.comp ( Primrec.fst ) ) ( Primrec.const rR ) using 1;
      simp +zetaDelta at *;
      exact Primrec₂.comp ( Primrec.and ) ‹_› ‹_›
    convert Primrec.cond h_cond ( show Primrec₂ ( fun ( ctx : List ℕ × ℕ × ℕ × ℕ × ℕ ) ( bv : ℕ ) => ntSetBit bv ntR ) from ?_ ) ( show Primrec₂ ( fun ( ctx : List ℕ × ℕ × ℕ × ℕ × ℕ ) ( bv : ℕ ) => bv ) from ?_ ) using 1;
    · simp +decide [ Primrec₂ ];
      grind;
    · exact Primrec₂.comp ( primrec₂_ntSetBit ) ( Primrec.snd ) ( Primrec.const _ );
    · exact Primrec.snd;
  exact h_primrec

/-- The fold over all rules (fixed `nodeData`) is Primrec₂. -/
lemma primrec₂_allRulesStep (nd : List (ℕ × ℕ × ℕ)) :
    Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) =>
      nd.foldl (fun bv' r =>
        if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) r.2.1 &&
           ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 +
              (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv) := by
  apply primrec_foldl_fixed
  intro ⟨ntR, lR, rR⟩
  exact primrec₂_ruleStep ntR lR rR

/-
The split-point fold is Primrec.
-/
lemma primrec_splitFold (nd : List (ℕ × ℕ × ℕ)) :
    Primrec (fun (ctx : List ℕ × ℕ × ℕ × ℕ) =>
      (List.range (ctx.2.2.2 + 1)).foldl (fun bv j =>
        nd.foldl (fun bv' r =>
          if ntInSet (ctx.1.getD (j * ctx.2.1 + ctx.2.2.1) 0) r.2.1 &&
             ntInSet (ctx.1.getD ((ctx.2.2.2 - j) * ctx.2.1 +
                (ctx.2.2.1 + j + 1)) 0) r.2.2
          then ntSetBit bv' r.1 else bv') bv
      ) 0) := by
  have h_split_point_fold : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ) (bv : ℕ) =>
    List.range (ctx.2.2.2 + 1) |>.foldl (fun bv' j =>
      nd.foldl (fun bv'' r =>
        if ntInSet (ctx.1.getD (ctx.2.2.1 + j * ctx.2.1) 0) r.2.1 &&
           ntInSet (ctx.1.getD (ctx.2.2.1 + j + 1 + (ctx.2.2.2 - j) * ctx.2.1) 0) r.2.2
        then ntSetBit bv'' r.1 else bv'') bv') bv) := by
          apply_rules [ Primrec₂.comp, Primrec₂.mk ];
          have := @primrec₂_allRulesStep;
          specialize this nd;
          convert Primrec.list_foldl _ _ _ using 1;
          rotate_left;
          exact ℕ;
          exact?;
          exact fun p => List.range ( p.1.2.2.2 + 1 );
          exact fun p => p.2;
          exact fun p q => foldl ( fun bv' r => if ( ntInSet ( p.1.1.getD ( p.1.2.2.1 + q.2 * p.1.2.1 ) 0 ) r.2.1 && ntInSet ( p.1.1.getD ( p.1.2.2.1 + q.2 + 1 + ( p.1.2.2.2 - q.2 ) * p.1.2.1 ) 0 ) r.2.2 ) = true then ntSetBit bv' r.1 else bv' ) q.1 nd;
          · have h_range : Primrec (fun (n : ℕ) => List.range (n + 1)) := by
              exact Primrec.list_range.comp ( Primrec.succ );
            exact h_range.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) );
          · exact Primrec.snd;
          · convert this using 1;
            constructor <;> intro h <;> simp_all +decide [ Primrec₂ ];
            convert this.comp _ using 1;
            rotate_left;
            exact fun p => ⟨ ⟨ p.1.1.1, p.1.1.2.1, p.1.1.2.2.1, p.1.1.2.2.2, p.2.2 ⟩, p.2.1 ⟩;
            · exact Primrec.pair ( Primrec.pair ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ) ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ) ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) ) ) ) ) ) ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.id ) ) );
            · grind;
          · lia;
  convert h_split_point_fold.comp ( Primrec.id ) ( Primrec.const 0 ) using 1;
  grind

/-
The cell computation is Primrec₂.
    First arg: `(table, n, k)`. Second arg: `i`.
-/
lemma primrec₂_cellValue (nd : List (ℕ × ℕ × ℕ)) :
    Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ) (i : ℕ) =>
      if i + ctx.2.2 + 2 > ctx.2.1 then 0
      else (List.range (ctx.2.2 + 1)).foldl (fun bv j =>
        nd.foldl (fun bv' r =>
          if ntInSet (ctx.1.getD (j * ctx.2.1 + i) 0) r.2.1 &&
             ntInSet (ctx.1.getD ((ctx.2.2 - j) * ctx.2.1 + (i + j + 1)) 0) r.2.2
          then ntSetBit bv' r.1 else bv') bv
      ) 0) := by
  refine' Primrec.ite _ _ _;
  · refine' ⟨ _, _ ⟩;
    infer_instance;
    convert Primrec.nat_lt.comp _ _ using 1;
    exact?;
    · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) );
    · exact Primrec.nat_add.comp ( Primrec.nat_add.comp ( Primrec.snd ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ( Primrec.const 2 );
  · exact Primrec.const 0;
  · convert primrec_splitFold nd |> Primrec.comp <| _ using 1;
    rotate_left;
    exact fun p => ( p.1.1, p.1.2.1, p.2, p.1.2.2 );
    · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ( Primrec.pair ( Primrec.snd ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) );
    · grind +revert

/-
The step function for Nat.rec is Primrec₂.
-/
lemma primrec₂_cykStep (nd : List (ℕ × ℕ × ℕ)) :
    Primrec₂ (fun (w : List T) (p : ℕ × List ℕ) =>
      p.2 ++ (List.range w.length).map fun i =>
        if i + p.1 + 2 > w.length then 0
        else (List.range (p.1 + 1)).foldl (fun bv j =>
          nd.foldl (fun bv' r =>
            if ntInSet (p.2.getD (j * w.length + i) 0) r.2.1 &&
               ntInSet (p.2.getD ((p.1 - j) * w.length + (i + j + 1)) 0) r.2.2
            then ntSetBit bv' r.1 else bv') bv
        ) 0) := by
  apply_rules [ Primrec₂.comp, Primrec₂.pair, Primrec₂.const ];
  all_goals try apply_rules [ Primrec.fst, Primrec.snd, Primrec.list_map ];
  · exact?;
  · exact Primrec.snd.comp ( Primrec.snd );
  · exact Primrec.list_range.comp ( Primrec.list_length.comp ( Primrec.fst ) );
  · convert primrec₂_cellValue nd using 1;
    constructor <;> intro h;
    · convert primrec₂_cellValue nd using 1;
    · convert h.comp ( Primrec.snd.comp ( Primrec.snd.comp Primrec.fst ) |> Primrec.pair <| Primrec.list_length.comp ( Primrec.fst.comp Primrec.fst ) |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd.comp Primrec.fst ) ) ( Primrec.snd ) using 1

/-
The full CYK table build is Primrec.
-/
lemma primrec_cykBuildTable (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ)) :
    Primrec (fun w : List T =>
      cykBuildTable ld nd w (w.length - 1)) := by
  have h_primrec : Primrec (fun w : List T => w.map (cykLeafBV ld)) := by
    have h_primrec : Primrec (fun t : T => cykLeafBV ld t) := by
      exact?;
    convert Primrec.list_map _ _;
    all_goals try infer_instance;
    · exact Primrec.id;
    · exact Primrec.comp h_primrec ( Primrec.snd );
  have h_primrec_step : Primrec₂ (fun (w : List T) (p : ℕ × List ℕ) => p.2 ++ (List.range w.length).map fun i =>
    if i + p.1 + 2 > w.length then 0
    else (List.range (p.1 + 1)).foldl (fun bv j =>
      nd.foldl (fun bv' r =>
        if ntInSet (p.2.getD (j * w.length + i) 0) r.2.1 &&
           ntInSet (p.2.getD ((p.1 - j) * w.length + (i + j + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv
    ) 0) := by
      exact?;
  have := @Primrec.nat_rec;
  convert this h_primrec ( h_primrec_step ) |> Primrec.comp <| Primrec.pair ( Primrec.id ) ( Primrec.nat_sub.comp ( Primrec.list_length ) ( Primrec.const 1 ) ) using 1;
  funext w; exact (by
  induction' w.length - 1 with k ih generalizing w <;> simp +decide [ *, cykBuildTable ])

/-- The full membership check is Primrec. -/
lemma cykMemCheck_eq (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ)) (si : ℕ)
    (w : List T) :
    cykMemCheck ld nd si w =
    ntInSet ((cykBuildTable ld nd w (w.length - 1)).getD
      ((w.length - 1) * w.length) 0) si := by
  cases w with
  | nil => simp [cykMemCheck, cykBuildTable, ntInSet]
  | cons h t => simp [cykMemCheck]

/-- The full membership check is Primrec. -/
lemma primrec_cykMemCheck (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ)) (si : ℕ) :
    Primrec (fun w : List T => cykMemCheck ld nd si w) := by
  have : Primrec (fun w : List T =>
      ntInSet ((cykBuildTable ld nd w (w.length - 1)).getD
        ((w.length - 1) * w.length) 0) si) := by
    exact (primrec₂_ntInSet.comp
      ((Primrec.list_getD 0).comp (primrec_cykBuildTable ld nd)
        (Primrec.nat_mul.comp
          (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
          Primrec.list_length))
      (Primrec.const si))
  exact this.of_eq (fun w => (cykMemCheck_eq ld nd si w).symm)

end CYKPrimrec

/-! ## CYK Bitvector Correctness -/

section CYKCorrectness

variable {T : Type} [DecidableEq T]

/-
Setting a different bit doesn't affect the queried bit.
-/
lemma ntInSet_ntSetBit_ne (bv idx idx' : ℕ) (h : idx ≠ idx') :
    ntInSet (ntSetBit bv idx') idx = ntInSet bv idx := by
  unfold ntSetBit;
  unfold ntInSet; rw [ Nat.shiftLeft_eq ] ;
  grind

/-
`cykLeafBV` correctly tracks membership: bit `idx` is set iff
    `leafData` contains `(idx, t)`.
-/
lemma cykLeafBV_correct (leafData : List (ℕ × T)) (t : T) (idx : ℕ) :
    ntInSet (cykLeafBV leafData t) idx = true ↔ (idx, t) ∈ leafData := by
  induction' leafData using List.reverseRecOn with leafData p ih generalizing idx;
  · simp +decide [ cykLeafBV, ntInSet ];
  · by_cases h : p.2 = t <;> simp_all +decide [ cykLeafBV ];
    · by_cases h' : idx = p.1 <;> simp_all +decide [ ntInSet_ntSetBit_self, ntInSet_ntSetBit_of_true, ntInSet_ntSetBit_ne ];
      · lia;
      · grind;
    · aesop

/-
The CYK table has the expected length.
-/
lemma cykBuildTable_length (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (k : ℕ) :
    (cykBuildTable ld nd w k).length = (k + 1) * w.length := by
  induction' k with k ih generalizing w;
  · simp [cykBuildTable];
  · unfold cykBuildTable;
    grind

/-
Entries from earlier rows are preserved when adding a new row.
-/
lemma cykBuildTable_getD_prev (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (k : ℕ) (idx : ℕ) (h : idx < (k + 1) * w.length) :
    (cykBuildTable ld nd w (k + 1)).getD idx 0 =
    (cykBuildTable ld nd w k).getD idx 0 := by
  rw [cykBuildTable];
  rw [ List.getD_append ];
  rw [ cykBuildTable_length ] ; exact h

/-
Generalized stability: entries are preserved across all later rows.
-/
lemma cykBuildTable_getD_stable (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (k k' : ℕ) (hk : k ≤ k') (idx : ℕ) (h : idx < (k + 1) * w.length) :
    (cykBuildTable ld nd w k').getD idx 0 =
    (cykBuildTable ld nd w k).getD idx 0 := by
  induction' hk with k' hk ih;
  · rfl;
  · rw [ ← ih, cykBuildTable_getD_prev ];
    nlinarith [ Nat.succ_le_succ hk ]

/-
Characterization of the nodeData fold: bit `idx` is set in the result iff
    it was set in `init` or there's a matching rule in `nd`.
-/
lemma foldl_rules_ntInSet (nd : List (ℕ × ℕ × ℕ)) (left_bv right_bv init : ℕ) (idx : ℕ) :
    ntInSet (nd.foldl (fun bv' r =>
      if ntInSet left_bv r.2.1 && ntInSet right_bv r.2.2
      then ntSetBit bv' r.1 else bv') init) idx = true ↔
    (ntInSet init idx = true ∨
     ∃ r ∈ nd, r.1 = idx ∧ ntInSet left_bv r.2.1 = true ∧ ntInSet right_bv r.2.2 = true) := by
  induction' nd using List.reverseRecOn with nd hd ih generalizing init;
  · aesop;
  · by_cases h : ntInSet left_bv hd.2.1 && ntInSet right_bv hd.2.2 <;> simp_all +decide [ List.foldl_append ];
    · by_cases h' : idx = hd.1 <;> simp_all +decide [ ntInSet_ntSetBit_self, ntInSet_ntSetBit_of_true, ntInSet_ntSetBit_ne ];
      · exact Or.inr ⟨ _, _, Or.inr rfl, h ⟩;
      · grind;
    · grind

/-
Characterization of the double fold: bit `idx` is set iff there's a matching
    split point and rule.
-/
lemma foldl_splits_ntInSet (nd : List (ℕ × ℕ × ℕ)) (table : List ℕ)
    (n i k : ℕ) (idx : ℕ) :
    ntInSet ((List.range (k + 1)).foldl (fun bv j =>
      nd.foldl (fun bv' r =>
        if ntInSet (table.getD (j * n + i) 0) r.2.1 &&
           ntInSet (table.getD ((k - j) * n + (i + j + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv
    ) 0) idx = true ↔
    ∃ j ∈ List.range (k + 1), ∃ r ∈ nd,
      r.1 = idx ∧
      ntInSet (table.getD (j * n + i) 0) r.2.1 = true ∧
      ntInSet (table.getD ((k - j) * n + (i + j + 1)) 0) r.2.2 = true := by
  simp +decide [ foldl_rules_ntInSet ];
  constructor <;> intro h;
  · contrapose! h;
    -- By induction on the range, we can show that the bit at `idx` is not set after each step of the fold.
    have h_ind : ∀ (j : ℕ) (hj : j ≤ k + 1), ntInSet (List.foldl (fun bv j => List.foldl (fun bv' r => if ntInSet (table[j * n + i]?.getD 0) r.2.1 = true ∧ ntInSet (table[(k - j) * n + (i + j + 1)]?.getD 0) r.2.2 = true then ntSetBit bv' r.1 else bv') bv nd) 0 (List.range j)) idx = false := by
      intro j hj; induction' j with j ih <;> simp_all +decide [ List.range_succ ] ;
      · exact?;
      · convert foldl_rules_ntInSet nd _ _ _ _ using 1;
        rotate_left;
        exact table[j * n + i]?.getD 0;
        exact table[(k - j) * n + (i + j + 1)]?.getD 0;
        exact foldl ( fun bv j => foldl ( fun bv' r => if ntInSet ( table[j * n + i]?.getD 0 ) r.2.1 = true ∧ ntInSet ( table[( k - j ) * n + ( i + j + 1 ) ]?.getD 0 ) r.2.2 = true then ntSetBit bv' r.1 else bv' ) bv nd ) 0 ( range j );
        exact idx;
        grind;
    exact ne_of_eq_of_ne ( h_ind _ le_rfl ) ( by decide );
  · -- By definition of `foldl`, if there exists a `j` in the range such that the condition holds, then the bit at `idx` will be set to `true` after processing all `j`'s.
    have h_foldl : ∀ (l : List ℕ) (j : ℕ) (hj : j ∈ l), (∃ r ∈ nd, r.1 = idx ∧ ntInSet (table[j * n + i]?.getD 0) r.2.1 ∧ ntInSet (table[(k - j) * n + (i + j + 1)]?.getD 0) r.2.2) → ntInSet (List.foldl (fun bv j => List.foldl (fun bv' r => if ntInSet (table[j * n + i]?.getD 0) r.2.1 ∧ ntInSet (table[(k - j) * n + (i + j + 1)]?.getD 0) r.2.2 then ntSetBit bv' r.1 else bv') bv nd) 0 l) idx := by
      intro l j hj h; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl_append ] ;
      by_cases h : j ∈ l <;> simp_all +decide [ foldl_rules_ntInSet ];
      · have h_foldl_rules : ∀ (bv : ℕ) (idx : ℕ), ntInSet bv idx = true → ∀ (nd : List (ℕ × ℕ × ℕ)), ntInSet (List.foldl (fun bv' r => if ntInSet (table[ih * n + i]?.getD 0) r.2.1 ∧ ntInSet (table[(k - ih) * n + (i + ih + 1)]?.getD 0) r.2.2 then ntSetBit bv' r.1 else bv') bv nd) idx = true := by
          intros bv idx hbv nd; induction' nd using List.reverseRecOn with nd ih <;> simp_all +decide [ List.foldl_append ] ;
          split_ifs <;> simp_all +decide [ ntInSet_ntSetBit_self, ntInSet_ntSetBit_of_true ];
        exact h_foldl_rules _ _ ‹_› _;
      · rename_i h₁ h₂;
        obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := h₂;
        convert foldl_rules_ntInSet nd _ _ _ _ |>.2 _ using 1;
        congr! 1;
        congr! 1;
        rotate_left;
        exact table[ih * n + i]?.getD 0;
        exact table[(k - ih) * n + (i + ih + 1)]?.getD 0;
        · exact Or.inr ⟨ _, h₁, rfl, h₂, h₃ ⟩;
        · grind;
    obtain ⟨ j, hj₁, hj₂ ⟩ := h; specialize h_foldl ( List.range ( k + 1 ) ) j; aesop;

open ChomskyNormalFormGrammar in
/-- Base case of CYK correctness: single characters. -/
lemma cykBuildTable_correct_base
    (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (enc : g.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔
        ChomskyNormalFormRule.leaf nt t ∈ g.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (w : List T) (hw : w ≠ [])
    (i : ℕ) (hi : i < w.length)
    (nt : g.NT) :
    ntInSet ((cykBuildTable leafData nodeData w 0).getD i 0) (enc nt) =
    cykDecideAux (g.rules.toList) nt (w.drop i |>.take 1) := by
  convert cykLeafBV_correct leafData ( w[i] ) ( enc nt ) using 1;
  rw [ show cykBuildTable leafData nodeData w 0 = w.map ( cykLeafBV leafData ) from rfl ] ; simp +decide [ List.getElem?_map, hi ] ;
  rw [ show drop i w = w[i] :: drop ( i + 1 ) w from ?_, List.take ] <;> norm_num [ hi ];
  rw [ cykDecideAux ];
  rw [ List.any_eq ];
  by_cases h : ( enc nt, w[i] ) ∈ leafData <;> simp +decide [ h, h_leaf ];
  · rw [ decide_eq_true ];
    exact ⟨ ChomskyNormalFormRule.leaf nt ( w[i] ), h_leaf nt ( w[i] ) |>.1 h, by simp +decide ⟩;
  · rw [ decide_eq_false ];
    contrapose! h;
    rcases h with ⟨ x, hx₁, hx₂ ⟩ ; rcases x with ( _ | _ ) <;> simp_all +decide ;

/-
The table entry at row (l+1), column i unfolds to the fold expression.
-/
lemma cykBuildTable_entry_step (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (l i : ℕ) (hi : i + l + 2 ≤ w.length) :
    (cykBuildTable ld nd w (l + 1)).getD ((l + 1) * w.length + i) 0 =
    (List.range (l + 1)).foldl (fun bv j =>
      nd.foldl (fun bv' r =>
        if ntInSet ((cykBuildTable ld nd w l).getD (j * w.length + i) 0) r.2.1 &&
           ntInSet ((cykBuildTable ld nd w l).getD ((l - j) * w.length + (i + j + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv
    ) 0 := by
  rw [ cykBuildTable ];
  simp +zetaDelta at *;
  rw [ List.getElem?_append ] ; norm_num;
  rw [ cykBuildTable_length ];
  grind

open ChomskyNormalFormGrammar in
/-- cykDecideAux on a word of length ≥ 2 checks split points and node rules. -/
lemma cykDecideAux_long {NT : Type} [DecidableEq NT]
    (rules : List (ChomskyNormalFormRule T NT))
    (nt : NT) (w : List T) (hw : w.length ≥ 2) :
    cykDecideAux rules nt w =
    (List.finRange (w.length - 1)).any fun ⟨j, hj⟩ =>
      rules.any fun r =>
        match r with
        | ChomskyNormalFormRule.node n' c₁ c₂ =>
          decide (n' = nt) && cykDecideAux rules c₁ (w.take (j + 1)) &&
            cykDecideAux rules c₂ (w.drop (j + 1))
        | _ => false := by
  rcases w with ( _ | ⟨ h₁, _ | ⟨ h₂, w ⟩ ⟩ ) <;> simp +arith +decide at hw ⊢;
  rw [ cykDecideAux ];
  congr! 2

set_option maxHeartbeats 800000 in
open ChomskyNormalFormGrammar in
/-- Step case of CYK correctness: longer substrings.
    Requires `h_node_range` to ensure all nodeData entries are in range of enc. -/
lemma cykBuildTable_correct_step
    (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (enc : g.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔
        ChomskyNormalFormRule.leaf nt t ∈ g.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (h_node : ∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔
        ChomskyNormalFormRule.node nt l r ∈ g.rules)
    (h_node_range : ∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r'))
    (h_leaf_range : ∀ p ∈ leafData, ∃ nt, p.1 = enc nt)
    (w : List T) (hw : w ≠ [])
    (l : ℕ) (i : ℕ) (hi : i + l + 2 ≤ w.length)
    (nt : g.NT)
    (ih : ∀ l' < l + 1, ∀ i' : ℕ, i' + l' + 1 ≤ w.length → ∀ nt' : g.NT,
      ntInSet ((cykBuildTable leafData nodeData w l').getD
        (l' * w.length + i') 0) (enc nt') =
      cykDecideAux (g.rules.toList) nt'
        (w.drop i' |>.take (l' + 1))) :
    ntInSet ((cykBuildTable leafData nodeData w (l + 1)).getD
      ((l + 1) * w.length + i) 0) (enc nt) =
    cykDecideAux (g.rules.toList) nt
      (w.drop i |>.take (l + 2)) := by
  have h_LHS : ntInSet ((cykBuildTable leafData nodeData w (l + 1)).getD ((l + 1) * w.length + i) 0) (enc nt) = true ↔ ∃ j ∈ List.range (l + 1), ∃ r ∈ nodeData, r.1 = enc nt ∧ ntInSet ((cykBuildTable leafData nodeData w l).getD (j * w.length + i) 0) r.2.1 ∧ ntInSet ((cykBuildTable leafData nodeData w l).getD ((l - j) * w.length + (i + j + 1)) 0) r.2.2 := by
    rw [ cykBuildTable_entry_step ];
    · convert foldl_splits_ntInSet nodeData ( cykBuildTable leafData nodeData w l ) w.length i l ( enc nt ) using 1;
    · linarith;
  have h_LHS_simplified : ntInSet ((cykBuildTable leafData nodeData w (l + 1)).getD ((l + 1) * w.length + i) 0) (enc nt) = true ↔ ∃ j ∈ List.range (l + 1), ∃ c₁ c₂ : g.NT, ChomskyNormalFormRule.node nt c₁ c₂ ∈ g.rules ∧ cykDecideAux g.rules.toList c₁ (take (j + 1) (drop i w)) ∧ cykDecideAux g.rules.toList c₂ (take (l - j + 1) (drop (i + j + 1) w)) := by
    constructor <;> intro h;
    · obtain ⟨ j, hj, r, hr, hr', hr'', hr''' ⟩ := h_LHS.mp h;
      obtain ⟨ nt', l', r', rfl ⟩ := h_node_range r hr; simp_all +decide [ enc_inj.eq_iff ] ;
      use j, hj, l', r';
      have := ih j hj i ( by linarith ) l'; have := ih ( l - j ) ( Nat.sub_le _ _ ) ( i + j + 1 ) ( by omega ) r'; simp_all +decide [ Nat.sub_add_comm hj ] ;
      have h_stable : ∀ (k k' : ℕ) (hk : k ≤ k') (idx : ℕ) (h : idx < (k + 1) * w.length), (cykBuildTable leafData nodeData w k').getD idx 0 = (cykBuildTable leafData nodeData w k).getD idx 0 :=
        fun k k' hk idx hidx => cykBuildTable_getD_stable leafData nodeData w k k' hk idx hidx;
      have := h_stable j l hj ( j * w.length + i ) ( by nlinarith ) ; have := h_stable ( l - j ) l ( Nat.sub_le _ _ ) ( ( l - j ) * w.length + ( i + j + 1 ) ) ( by nlinarith [ Nat.sub_add_cancel hj ] ) ; aesop;
    · obtain ⟨ j, hj₁, c₁, c₂, h₁, h₂, h₃ ⟩ := h;
      refine' h_LHS.mpr ⟨ j, hj₁, _, _, _, _, _ ⟩;
      exact ( enc nt, enc c₁, enc c₂ );
      · exact h_node nt c₁ c₂ |>.2 h₁;
      · rfl;
      · specialize ih j (by
        linarith [ List.mem_range.mp hj₁ ]) i (by
        linarith [ List.mem_range.mp hj₁ ]) c₁;
        grind +suggestions;
      · convert ih ( l - j ) ( by linarith [ Nat.sub_add_cancel ( show j ≤ l from by linarith [ List.mem_range.mp hj₁ ] ) ] ) ( i + j + 1 ) ( by linarith [ Nat.sub_add_cancel ( show j ≤ l from by linarith [ List.mem_range.mp hj₁ ] ) ] ) c₂ using 1;
        · rw [ cykBuildTable_getD_stable ];
          · exact Nat.sub_le _ _;
          · nlinarith [ Nat.sub_add_cancel ( show j ≤ l from by linarith [ List.mem_range.mp hj₁ ] ) ];
        · exact h₃.symm;
  have h_RHS : cykDecideAux g.rules.toList nt (take (l + 2) (drop i w)) = true ↔ ∃ j < l + 1, ∃ c₁ c₂ : g.NT, ChomskyNormalFormRule.node nt c₁ c₂ ∈ g.rules ∧ cykDecideAux g.rules.toList c₁ (take (j + 1) (drop i w)) ∧ cykDecideAux g.rules.toList c₂ (take (l - j + 1) (drop (i + j + 1) w)) := by
    rw [cykDecideAux_long];
    · simp +decide [ List.any_eq_true, List.finRange ];
      constructor;
      · rintro ⟨ a, x, hx, hx' ⟩;
        rcases x with ( _ | ⟨ n', c₁, c₂ ⟩ ) <;> simp +decide at hx' ⊢;
        refine' ⟨ a, _, c₁, c₂, _, _, _ ⟩;
        · exact Nat.le_of_lt_succ ( lt_of_lt_of_le a.2 ( Nat.sub_le_of_le_add <| by omega ) );
        · lia;
        · grind;
        · convert hx'.2 using 2;
          rw [ List.drop_take ];
          rw [ show l + 2 - ( a + 1 ) = l - a + 1 by omega ] ; simp +decide [ add_assoc, List.drop_drop ] ;
      · rintro ⟨ j, hj, c₁, c₂, h₁, h₂, h₃ ⟩;
        use ⟨ j, by
          omega ⟩
        generalize_proofs at *;
        use ChomskyNormalFormRule.node nt c₁ c₂;
        simp_all +decide [ List.take_take, List.drop_take ];
        exact ⟨ by rw [ min_eq_left ( by linarith ) ] ; exact h₂, by rw [ show l + 1 - j = l - j + 1 by omega ] ; exact h₃ ⟩;
    · grind +revert;
  simp_all +decide [ List.mem_range ];
  convert h_LHS_simplified using 1;
  convert Bool.eq_iff_iff using 1;
  convert Iff.rfl using 2;
  convert foldl_splits_ntInSet nodeData ( cykBuildTable leafData nodeData w l ) w.length i l ( enc nt ) using 1;
  · congr! 1;
    congr! 1;
    convert cykBuildTable_entry_step leafData nodeData w l i ( by linarith ) using 1;
  · simp +decide [ List.mem_range, Nat.lt_succ_iff ]

open ChomskyNormalFormGrammar in
/-- Key correctness lemma: CYK bitvector table entries correspond to `cykDecideAux`.
    Proved by strong induction on `l`. -/
lemma cykBuildTable_correct
    (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (enc : g.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔
        ChomskyNormalFormRule.leaf nt t ∈ g.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (h_node : ∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔
        ChomskyNormalFormRule.node nt l r ∈ g.rules)
    (h_node_range : ∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r'))
    (h_leaf_range : ∀ p ∈ leafData, ∃ nt, p.1 = enc nt)
    (w : List T) (hw : w ≠ [])
    (k l : ℕ) (hl : l ≤ k) (hk : k < w.length)
    (i : ℕ) (hi : i + l + 1 ≤ w.length)
    (nt : g.NT) :
    ntInSet ((cykBuildTable leafData nodeData w k).getD
      (l * w.length + i) 0) (enc nt) =
    cykDecideAux (g.rules.toList) nt
      (w.drop i |>.take (l + 1)) := by
  -- First reduce to l = k via stability
  rw [cykBuildTable_getD_stable leafData nodeData w l k hl
    (l * w.length + i) (by nlinarith)]
  -- Now induct on l
  induction l using Nat.strongRecOn generalizing k i nt with
  | _ l ih_strong =>
    match l with
    | 0 =>
      -- Base case
      simp only [zero_mul, zero_add]
      exact cykBuildTable_correct_base g enc enc_inj leafData h_leaf nodeData w hw i (by omega) nt
    | l + 1 =>
      -- Step case: use cykBuildTable_correct_step
      apply cykBuildTable_correct_step g enc enc_inj leafData h_leaf nodeData h_node h_node_range h_leaf_range w hw l i hi nt
      intro l' hl' i' hi' nt'
      exact ih_strong l' hl' l' (le_refl l') (by omega) i' hi' nt'

end CYKCorrectness

/-! ## Main theorem: CF membership is ComputablePred -/

section CFComputablePred

variable {T : Type} [Fintype T] [DecidableEq T]

-- Helper: the CYK membership check correctly decides CNF language membership
open ChomskyNormalFormGrammar in
lemma cykMemCheck_correct_cnf
    {T : Type} [DecidableEq T] [Primcodable T]
    (cnf : ChomskyNormalFormGrammar.{0, 0} T) [DecidableEq cnf.NT]
    (enc : cnf.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔ ChomskyNormalFormRule.leaf nt t ∈ cnf.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (h_node : ∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔ ChomskyNormalFormRule.node nt l r ∈ cnf.rules)
    (h_node_range : ∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r'))
    (h_leaf_range : ∀ p ∈ leafData, ∃ nt, p.1 = enc nt)
    (w : List T) (hw : w ≠ []) :
    cykMemCheck leafData nodeData (enc cnf.initial) w = true ↔ w ∈ cnf.language := by
  rw [cykMemCheck_eq]
  have hlen : 0 < w.length := by cases w <;> simp_all
  have hcorr := @cykBuildTable_correct T _ cnf _ enc enc_inj leafData h_leaf nodeData h_node
    h_node_range h_leaf_range w hw (w.length - 1) (w.length - 1) (le_refl _)
    (by omega) 0 (by omega) cnf.initial
  simp only [List.drop_zero, Nat.sub_add_cancel hlen, List.take_length, Nat.add_zero] at hcorr
  rw [hcorr]
  have h_cyk := cykDecideAux_iff_canDerive cnf cnf.rules.toList (fun r => Finset.mem_toList) cnf.initial w
  have h_cd := canDerive_iff_derives cnf cnf.initial w
  rw [mem_language_iff]
  unfold Generates
  exact h_cyk.trans h_cd

set_option maxHeartbeats 800000 in
/-- Membership in a context-free language is a computable predicate. -/
theorem cf_membership_computable
    (g : CF_grammar T) [Fintype g.nt] [DecidableEq g.nt]
    [Primcodable T] :
    ComputablePred (fun w : List T => w ∈ CF_language g) := by
  obtain ⟨enc, enc_inj⟩ : ∃ enc : (mathlib_cfg_of_cfg g).toCNF.NT → ℕ, Function.Injective enc := by
    have h_encodable : Encodable (mathlib_cfg_of_cfg g).toCNF.NT := by
      have h_encodable : Encodable ((g.nt ⊕ T) ⊕ (r : ContextFreeRule T (g.nt ⊕ T)) × Fin (r.output.length - 2)) := by
        have h_encodable : Countable ((g.nt ⊕ T) ⊕ (r : ContextFreeRule T (g.nt ⊕ T)) × Fin (r.output.length - 2)) := by
          have h_countable : Countable (ContextFreeRule T (g.nt ⊕ T)) := by
            have h_countable : Countable ((g.nt ⊕ T) × List (Symbol T (g.nt ⊕ T))) := by
              infer_instance;
            exact ( Equiv.ofBijective ( fun x => ( x.input, x.output ) ) ⟨ fun x y h => by cases x; cases y; aesop, fun x => by cases x; exact ⟨ ⟨ _, _ ⟩, rfl ⟩ ⟩ ) |> fun h => h.countable_iff.mpr h_countable;
          infer_instance;
        exact Encodable.ofCountable _;
      exact h_encodable;
    exact ⟨ _, Encodable.encode_injective ⟩;
  obtain ⟨leafData, nodeData, h_leaf, h_node, h_node_range, h_leaf_range⟩ : ∃ leafData : List (ℕ × T), ∃ nodeData : List (ℕ × ℕ × ℕ),
    (∀ nt t, (enc nt, t) ∈ leafData ↔ ChomskyNormalFormRule.leaf nt t ∈ (mathlib_cfg_of_cfg g).toCNF.rules) ∧
    (∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔ ChomskyNormalFormRule.node nt l r ∈ (mathlib_cfg_of_cfg g).toCNF.rules) ∧
    (∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r')) ∧
    (∀ p ∈ leafData, ∃ nt, p.1 = enc nt) := by
      refine' ⟨ _, _, _, _, _, _ ⟩;
      exact (mathlib_cfg_of_cfg g).toCNF.rules.toList.filterMap (fun r => match r with | ChomskyNormalFormRule.leaf nt t => some (enc nt, t) | _ => none);
      exact (mathlib_cfg_of_cfg g).toCNF.rules.toList.filterMap (fun r => match r with | ChomskyNormalFormRule.node nt l r => some (enc nt, enc l, enc r) | _ => none);
      · intro nt t; simp +decide [ ChomskyNormalFormRule.leaf ] ;
        constructor <;> intro h;
        · obtain ⟨ a, ha, ha' ⟩ := h; rcases a with ( _ | _ | a ) <;> simp_all +decide ;
          grind;
        · exact ⟨ _, h, rfl ⟩;
      · intro nt l r;
        rw [ List.mem_filterMap ];
        constructor;
        · rintro ⟨ a, ha, ha' ⟩;
          cases a <;> simp_all +decide [ enc_inj.eq_iff ];
        · exact fun h => ⟨ ChomskyNormalFormRule.node nt l r, by simpa using h, rfl ⟩;
      · grind;
      · grind;
  obtain ⟨emptyVal, h_empty⟩ : ∃ emptyVal : Bool, [] ∈ CF_language g ↔ emptyVal = true := by
    by_cases h : [] ∈ CF_language g <;> [ exact ⟨ Bool.true, by simpa ⟩ ; exact ⟨ Bool.false, by simpa ⟩ ];
  obtain ⟨f, hf⟩ : ∃ f : List T → Bool, Computable f ∧ ∀ w, w ∈ CF_language g ↔ f w = true := by
    refine' ⟨ fun w => if w = [] then emptyVal else cykMemCheck leafData nodeData ( enc ( ( mathlib_cfg_of_cfg g ).toCNF.initial ) ) w, _, _ ⟩;
    · convert Computable.cond _ _ _ using 1;
      rotate_left;
      exact fun w => w = [];
      exact fun _ => emptyVal;
      exact fun w => cykMemCheck leafData nodeData ( enc ( ( mathlib_cfg_of_cfg g ).toCNF.initial ) ) w;
      · convert Computable.of_eq _ _;
        exact fun w => w.length = 0;
        · convert Computable.of_eq _ _;
          exact fun w => Nat.recOn w.length ( Bool.true ) fun _ _ => Bool.false;
          · convert Computable.nat_casesOn _ _ _ using 1;
            · exact Computable.list_length;
            · exact Computable.const Bool.true;
            · exact Computable.const Bool.false;
          · intro n; cases n <;> simp +decide ;
        · aesop;
      · exact Computable.const _;
      · exact Primrec.to_comp ( primrec_cykMemCheck _ _ _ );
      · grind;
    · intro w; by_cases hw : w = [] <;> simp +decide [ hw, h_empty ] ;
      rw [ CF_language_eq_mathlib_language ];
      convert cykMemCheck_correct_cnf ( mathlib_cfg_of_cfg g |> ContextFreeGrammar.toCNF ) enc enc_inj leafData h_leaf nodeData h_node h_node_range h_leaf_range w hw |> Iff.symm using 1;
      · rw [ ← ContextFreeGrammar.toCNF_correct ];
        grind;
      · exact?;
  convert hf.1 using 1;
  constructor <;> intro h <;> rw [ ComputablePred ] at * <;> aesop

end CFComputablePred