import Mathlib
import Langlib.Classes.ContextFree.Decidability.UniformMembership

/-! # Primitive Recursiveness of Saturation Step

This file proves that the saturation step function `satStep` is primitive recursive,
which is needed for the computability proof of context-free membership.
-/

open List

variable {T : Type} [DecidableEq T] [Primcodable T]

/-! ## Triple list membership is Primrec -/

private lemma triple_list_mem_primrec :
    Primrec₂ (fun (t : ℕ × ℕ × ℕ) (S : List (ℕ × ℕ × ℕ)) => (decide (t ∈ S) : Bool)) := by
  refine' Primrec.of_eq _ _;
  exact fun p => List.any p.2 fun x => x == p.1;
  · convert primrec_list_any _ _;
    all_goals try infer_instance;
    · exact Primrec.snd;
    · -- The equality function is primitive recursive, so we can use the fact that it is computable.
      have h_eq_primrec : Primrec₂ (fun (x y : ℕ × ℕ × ℕ) => x == y) := by
        convert Primrec.eq.comp ( Primrec.fst ) ( Primrec.snd ) using 1;
        any_goals exact ℕ × ℕ × ℕ;
        all_goals try infer_instance;
        constructor <;> intro h;
        · convert Primrec.eq;
        · convert h using 1;
          constructor <;> intro h <;> rw [ PrimrecPred ] at * <;> simp_all +decide [ Primrec₂ ];
          grind +splitIndPred;
      convert h_eq_primrec.comp _ _ using 1;
      · exact Primrec.snd;
      · exact Primrec.fst.comp ( Primrec.fst );
  · grind

/-! ## matchOneSym helper is Primrec -/

/-
The core matching function for a single nonterminal symbol: given (k, nc, S, pos),
    returns the list of end positions from S matching (k % nc, pos, _).
-/
private lemma nonterminal_match_primrec :
    Primrec (fun (p : (ℕ × ℕ × List (ℕ × ℕ × ℕ)) × ℕ) =>
      (p.1.2.2.flatMap (fun trip =>
        if trip.1 == p.1.1 % p.1.2.1 && trip.2.1 == p.2 then [trip.2.2] else []))) := by
  have h_primrec : Primrec (fun (p : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ × ℕ)) => (p.2.1 == p.1.1.1 && p.2.2.1 == p.1.2.2)) := by
    have h_primrec : Primrec (fun (p : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ × ℕ)) => (p.2.1 == p.1.1.1)) := by
      have h_primrec : Primrec (fun (p : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ × ℕ)) => (p.2.1, p.1.1.1)) := by
        exact Primrec.pair ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) );
      have h_primrec : Primrec (fun (p : ℕ × ℕ) => (p.1 == p.2)) := by
        convert Primrec.eq.comp ( Primrec.fst ) ( Primrec.snd ) using 1;
        exact?;
      convert h_primrec.comp ‹Primrec fun p : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ × ℕ) => (p.2.1, p.1.1.1)› using 1;
    convert Primrec.and.comp ( h_primrec ) ( show Primrec ( fun p : ( ( ℕ × ℕ ) × List ( ℕ × ℕ × ℕ ) × ℕ ) × ( ℕ × ℕ × ℕ ) => p.2.2.1 == p.1.2.2 ) from ?_ ) using 1;
    convert Primrec.beq.comp ( show Primrec ( fun p : ( ( ℕ × ℕ ) × List ( ℕ × ℕ × ℕ ) × ℕ ) × ( ℕ × ℕ × ℕ ) => p.2.2.1 ) from ?_ ) ( show Primrec ( fun p : ( ( ℕ × ℕ ) × List ( ℕ × ℕ × ℕ ) × ℕ ) × ( ℕ × ℕ × ℕ ) => p.1.2.2 ) from ?_ ) using 1;
    · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) );
    · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) );
  have h_primrec : Primrec (fun (p : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ) × List (ℕ × ℕ × ℕ)) => p.2.flatMap (fun trip => if (trip.1 == p.1.1.1 && trip.2.1 == p.1.2.2) then [trip.2.2] else [])) := by
    have h_primrec : Primrec (fun (p : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ) × (ℕ × ℕ × ℕ)) => if (p.2.1 == p.1.1.1 && p.2.2.1 == p.1.2.2) then [p.2.2.2] else []) := by
      convert Primrec.cond _ _ _ using 1;
      rotate_left;
      exact fun p => p.2.1 == p.1.1.1 && p.2.2.1 == p.1.2.2;
      exact fun p => [ p.2.2.2 ];
      exact fun p => [];
      · exact h_primrec;
      · exact Primrec.list_cons.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ( Primrec.const [ ] );
      · exact Primrec.const [];
      · grind;
    convert Primrec.list_flatMap _ _ using 1;
    all_goals try infer_instance;
    · exact Primrec.snd;
    · convert h_primrec.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1;
  convert h_primrec.comp _ using 1;
  rotate_left;
  exact fun p => ( ( ( p.1.1 % p.1.2.1, p.2 ), p.1.2.2, p.2 ), p.1.2.2 );
  · convert Primrec.pair _ _ using 1;
    · exact Primrec.pair ( Primrec.pair ( Primrec.nat_mod.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ( Primrec.snd ) ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ( Primrec.snd ) );
    · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) );
  · grind

/-
The core matching function for a single terminal symbol: given (w, t, pos),
    returns [pos + 1] if w[pos] = t, else [].
-/
private lemma terminal_match_primrec :
    Primrec (fun (p : (List T × T) × ℕ) =>
      match p.1.1[p.2]? with
      | some c => if c == p.1.2 then [p.2 + 1] else []
      | none => ([] : List ℕ)) := by
  have h_list_getElem?_primrec : Primrec (fun (p : List T × ℕ) => p.1[p.2]?) := by
    convert Primrec.list_getElem? using 1;
  have h_option_filterMap : Primrec (fun (p : Option T × T × ℕ) => match p.1 with | some c => if c == p.2.1 then [p.2.2 + 1] else [] | none => []) := by
    have h_match : Primrec (fun (p : Option T × T × ℕ) => if p.1 = some p.2.1 then [p.2.2 + 1] else []) := by
      convert Primrec.cond _ _ _;
      rotate_left;
      exact fun p => p.1 = some p.2.1;
      · convert Primrec.eq.comp ( Primrec.fst ) ( Primrec.option_some.comp ( Primrec.fst.comp ( Primrec.snd ) ) ) using 1;
        exact?;
      · exact Primrec.list_cons.comp ( Primrec.succ.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ( Primrec.const [] );
      · exact Primrec.const [];
      · grind;
    grind;
  convert h_option_filterMap.comp ( h_list_getElem?_primrec.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) |> Primrec.pair <| Primrec.snd.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1

set_option maxHeartbeats 1600000 in
/-- matchOneSym is Primrec when we express it as a function of bundled parameters.
    Context: (nc, w, S). Input: (sym, pos). -/
private lemma matchOneSym_primrec_bundled :
    Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × (ℕ ⊕ T) × ℕ) =>
      matchOneSym p.1.2.1 p.1.1 p.1.2.2 p.2.1 p.2.2) := by
  have heq : (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × (ℕ ⊕ T) × ℕ) =>
      matchOneSym p.1.2.1 p.1.1 p.1.2.2 p.2.1 p.2.2) =
    (fun p => Sum.casesOn p.2.1
      (fun k => p.1.2.2.flatMap (fun trip => if trip.1 == k % p.1.1 && trip.2.1 == p.2.2 then [trip.2.2] else []))
      (fun t => match p.1.2.1[p.2.2]? with | some c => if c == t then [p.2.2 + 1] else [] | none => [])) := by
    funext p; cases p.2.1 with
    | inl k =>
      simp [matchOneSym]
      induction p.1.2.2 with
      | nil => simp
      | cons hd tl ih =>
        obtain ⟨a, b, c⟩ := hd
        simp only [List.filter_cons, List.flatMap_cons, decide_eq_true_eq, Bool.and_eq_true]
        by_cases h1 : a = k % p.1.1 <;> by_cases h2 : b = p.2.2 <;> simp_all
    | inr t => rfl
  rw [heq]
  apply Primrec.sumCasesOn
  · exact Primrec.fst.comp Primrec.snd
  · exact nonterminal_match_primrec.comp
      (Primrec.pair
        (Primrec.pair Primrec.snd
          (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  · exact terminal_match_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

/-! ## matchRHS is Primrec -/

/-
matchRHS is Primrec as a function of bundled parameters.
    Takes (nc, w, S, rhs, startPos) bundled appropriately.
-/
private lemma matchRHS_primrec_bundled :
    Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × List (ℕ ⊕ T) × ℕ) =>
      matchRHS p.1.2.1 p.1.1 p.1.2.2 p.2.1 p.2.2) := by
  have h_foldl : Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × List (ℕ ⊕ T) × List ℕ) => p.2.1.foldl (fun positions sym => positions.flatMap (fun pos => matchOneSym p.1.2.1 p.1.1 p.1.2.2 sym pos)) p.2.2) := by
    have h_foldl : Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × List (ℕ ⊕ T) × List ℕ) => List.foldl (fun (positions : List ℕ) (sym : ℕ ⊕ T) => List.flatMap (fun (pos : ℕ) => matchOneSym p.1.2.1 p.1.1 p.1.2.2 sym pos) positions) p.2.2 p.2.1) := by
      have h_step : Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × List ℕ × (ℕ ⊕ T)) => List.flatMap (fun (pos : ℕ) => matchOneSym p.1.2.1 p.1.1 p.1.2.2 p.2.2 pos) p.2.1) := by
        have h_step : Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × (ℕ ⊕ T) × ℕ) => matchOneSym p.1.2.1 p.1.1 p.1.2.2 p.2.1 p.2.2) := by
          exact?;
        have h_flatMap : Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ)) × List ℕ × (ℕ ⊕ T)) => List.flatMap (fun (pos : ℕ) => matchOneSym p.1.2.1 p.1.1 p.1.2.2 p.2.2 pos) p.2.1) := by
          have h_flatMap : Primrec (fun (p : List ℕ × (ℕ × List T × List (ℕ × ℕ × ℕ)) × (ℕ ⊕ T)) => List.flatMap (fun (pos : ℕ) => matchOneSym p.2.1.2.1 p.2.1.1 p.2.1.2.2 p.2.2 pos) p.1) := by
            convert Primrec.list_flatMap _ _ using 1;
            all_goals try infer_instance;
            · exact Primrec.fst;
            · convert h_step.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1;
              constructor <;> intro h;
              · convert h_step.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1;
              · convert h.comp ( Primrec.snd.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1
          convert h_flatMap.comp ( show Primrec ( fun p : ( ℕ × List T × List ( ℕ × ℕ × ℕ ) ) × List ℕ × ( ℕ ⊕ T ) => ( p.2.1, p.1, p.2.2 ) ) from ?_ ) using 1;
          exact Primrec.pair ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.pair ( Primrec.fst ) ( Primrec.snd.comp ( Primrec.snd ) ) );
        exact h_flatMap
      convert Primrec.list_foldl _ _ _;
      rotate_left;
      exact inferInstance;
      exact fun p q => flatMap ( fun pos => matchOneSym p.1.2.1 p.1.1 p.1.2.2 q.2 pos ) q.1;
      · exact Primrec.fst.comp ( Primrec.snd );
      · exact Primrec.snd.comp ( Primrec.snd );
      · convert h_step.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1;
      · rfl;
    exact h_foldl;
  convert h_foldl.comp _ using 1;
  rotate_left;
  exact fun p => ⟨ p.1, p.2.1, [ p.2.2 ] ⟩;
  · exact Primrec.pair ( Primrec.fst ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.list_cons.comp ( Primrec.snd.comp ( Primrec.snd ) ) ( Primrec.const [ ] ) ) );
  · exact?

/-! ## satStep is Primrec -/

/-
The innermost conditional-append step of satStep is Primrec.
    Given (ruleIdx_mod_nc, startPos) as context and (S''', endPos) as input,
    conditionally appends the triple (ruleIdx_mod_nc, startPos, endPos) to S'''.
-/
private lemma condAppend_primrec :
    Primrec₂ (fun (ctx : ℕ × ℕ) (pair : List (ℕ × ℕ × ℕ) × ℕ) =>
      let triple := (ctx.1, ctx.2, pair.2)
      if decide (triple ∈ pair.1) then pair.1 else pair.1 ++ [triple]) := by
  unfold Primrec₂;
  simp +zetaDelta at *;
  convert Primrec.cond _ _ _;
  rotate_left;
  exact fun x => decide ( ( x.1.1, x.1.2, x.2.2 ) ∈ x.2.1 );
  · convert Primrec₂.comp ( triple_list_mem_primrec ) _ _ using 1;
    · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.fst ) ) ( Primrec.snd.comp ( Primrec.snd ) ) );
    · exact Primrec.fst.comp ( Primrec.snd );
  · exact Primrec.fst.comp ( Primrec.snd );
  · exact Primrec.list_append.comp ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.list_cons.comp ( Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.fst ) ) ( Primrec.snd.comp ( Primrec.snd ) ) ) ) ( Primrec.const [] ) );
  · grind

/-
The innermost foldl of satStep: fold over endPos list, conditionally appending triples.
-/
private lemma innerFoldl_primrec :
    Primrec (fun (p : (ℕ × ℕ) × List ℕ × List (ℕ × ℕ × ℕ)) =>
      p.2.1.foldl (fun S''' endPos =>
        let triple := (p.1.1, p.1.2, endPos)
        if decide (triple ∈ S''') then S''' else S''' ++ [triple]) p.2.2) := by
  have h_condAppend_primrec : Primrec₂ (fun (ctx : ℕ × ℕ) (pair : List (ℕ × ℕ × ℕ) × ℕ) =>
    let triple := (ctx.1, ctx.2, pair.2)
    if decide (triple ∈ pair.1) then pair.1 else pair.1 ++ [triple]) := by
      exact?;
  convert Primrec.list_foldl _ _ _;
  rotate_left;
  exact?;
  exact fun p q => if decide ( ( p.1.1, p.1.2, q.2 ) ∈ q.1 ) = true then q.1 else q.1 ++ [ ( p.1.1, p.1.2, q.2 ) ];
  · exact Primrec.fst.comp ( Primrec.snd );
  · exact Primrec.snd.comp ( Primrec.snd );
  · convert h_condAppend_primrec.comp _ _ using 1;
    · exact Primrec.fst.comp ( Primrec.fst );
    · exact Primrec.snd;
  · rfl

/-
The step function of the middle foldl: given context and (S'', startPos),
    compute matchRHS and apply innerFoldl.
-/
private lemma middleStep_primrec :
    Primrec₂ (fun (ctx : ℕ × List T × List (ℕ × ℕ × ℕ) × ℕ × List (ℕ ⊕ T))
                 (pair : List (ℕ × ℕ × ℕ) × ℕ) =>
      (matchRHS ctx.2.1 ctx.1 ctx.2.2.1 ctx.2.2.2.2 pair.2).foldl (fun S''' endPos =>
        let triple := (ctx.2.2.2.1 % ctx.1, pair.2, endPos)
        if decide (triple ∈ S''') then S''' else S''' ++ [triple]) pair.1) := by
  apply Primrec.of_eq;
  convert innerFoldl_primrec.comp ( Primrec.pair _ _ ) using 1;
  exact fun n => ( n.1.2.2.2.1 % n.1.1, n.2.2 );
  exact fun n => ( matchRHS n.1.2.1 n.1.1 n.1.2.2.1 n.1.2.2.2.2 n.2.2, n.2.1 );
  · exact Primrec.pair ( Primrec.nat_mod.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ) ( Primrec.fst.comp ( Primrec.fst ) ) ) ( Primrec.snd.comp ( Primrec.snd ) );
  · convert Primrec.pair ( matchRHS_primrec_bundled.comp ( Primrec.pair _ _ ) ) ( Primrec.fst.comp ( Primrec.snd ) ) using 1;
    congr! 1;
    rotate_left;
    bv_omega;
    all_goals try infer_instance;
    exact fun x => ( x.1.1, x.1.2.1, x.1.2.2.1 );
    exact fun x => ( x.1.2.2.2.2, x.2.2 );
    · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) );
    · exact Primrec.pair ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ) ( Primrec.snd.comp ( Primrec.snd ) );
    · rfl;
  · aesop

/-
The middle foldl of satStep: fold over range(w.length+1), computing matchRHS and applying innerFoldl.
    Context: (nc, w, S_orig, ruleIdx, ruleRHS). Input: S'.
-/
private lemma middleFoldl_primrec :
    Primrec (fun (p : (ℕ × List T × List (ℕ × ℕ × ℕ) × ℕ × List (ℕ ⊕ T)) × List (ℕ × ℕ × ℕ)) =>
      (List.range (p.1.2.1.length + 1)).foldl (fun S'' startPos =>
        (matchRHS p.1.2.1 p.1.1 p.1.2.2.1 p.1.2.2.2.2 startPos).foldl (fun S''' endPos =>
          let triple := (p.1.2.2.2.1 % p.1.1, startPos, endPos)
          if decide (triple ∈ S''') then S''' else S''' ++ [triple]) S'') p.2) := by
  convert Primrec.list_foldl _ _ _ using 1;
  rotate_left;
  exact ℕ;
  all_goals try infer_instance;
  exact fun p => List.range ( p.1.2.1.length + 1 );
  exact fun p => p.2;
  exact fun p q => p.1.2.2.2.2 |> fun ruleRHS => matchRHS p.1.2.1 p.1.1 p.1.2.2.1 ruleRHS q.2 |> fun endPos => endPos.foldl ( fun S''' endPos => let triple := ( p.1.2.2.2.1 % p.1.1, q.2, endPos ) ; if decide ( triple ∈ S''' ) then S''' else S''' ++ [ triple ] ) q.1;
  · convert Primrec.list_range.comp _ using 1;
    convert Primrec.nat_add.comp ( Primrec.list_length.comp _ ) ( Primrec.const 1 ) using 1;
    bv_omega;
    exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) );
  · exact Primrec.snd;
  · convert middleStep_primrec.comp _ _ using 1;
    all_goals try infer_instance;
    · exact Primrec.fst.comp ( Primrec.fst );
    · exact Primrec.snd;
  · exact funext fun p => by rfl;

set_option maxHeartbeats 1600000 in
/-- satStep is Primrec as a function of bundled parameters. -/
lemma satStep_primrec_full :
    Primrec (fun (p : (ℕ × List (ℕ × List (ℕ ⊕ T)) × List T) × List (ℕ × ℕ × ℕ)) =>
      satStep p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  convert Primrec.list_foldl (β := ℕ × List (ℕ ⊕ T)) (σ := List (ℕ × ℕ × ℕ))
    (f := fun p : (ℕ × List (ℕ × List (ℕ ⊕ T)) × List T) × List (ℕ × ℕ × ℕ) => p.1.2.1)
    (g := fun p => p.2)
    (h := fun p pair =>
      (List.range (p.1.2.2.length + 1)).foldl (fun S'' startPos =>
        (matchRHS p.1.2.2 p.1.1 p.2 pair.2.2 startPos).foldl (fun S''' endPos =>
          let triple := (pair.2.1 % p.1.1, startPos, endPos)
          if decide (triple ∈ S''') then S''' else S''' ++ [triple]) S'') pair.1)
    ?_ ?_ ?_ using 1
  · exact Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  · exact Primrec.snd
  · apply Primrec.of_eq
    exact middleFoldl_primrec.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair (Primrec.snd.comp Primrec.fst)
            (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
      (Primrec.fst.comp Primrec.snd))
    intro x; rfl

/-! ## Iteration of satStep is Primrec -/

set_option maxHeartbeats 800000 in
private lemma satFixpoint_primrec :
    Primrec₂ (fun (ctx : ℕ × List (ℕ × List (ℕ ⊕ T)) × List T) (n : ℕ) =>
      (satStep ctx.1 ctx.2.1 ctx.2.2)^[n] ([] : List (ℕ × ℕ × ℕ))) := by
  have h_step : Primrec₂ (fun (ctx : ℕ × List (ℕ × List (ℕ ⊕ T)) × List T)
      (pair : ℕ × List (ℕ × ℕ × ℕ)) => satStep ctx.1 ctx.2.1 ctx.2.2 pair.2) := by
    unfold Primrec₂
    exact satStep_primrec_full.comp (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  have h_nat_rec := Primrec.nat_rec (Primrec.const ([] : List (ℕ × ℕ × ℕ))) h_step
  apply Primrec.of_eq h_nat_rec
  intro ⟨ctx, n⟩; simp only
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show (fun n IH => satStep ctx.1 ctx.2.1 ctx.2.2 (n, IH).2) =
         (fun _ IH => satStep ctx.1 ctx.2.1 ctx.2.2 IH) from rfl] at *
    dsimp only [Nat.rec]; rw [ih]
    exact (Function.iterate_succ_apply' _ n _).symm

/-! ## checkMembershipEncoded is Computable -/

set_option maxHeartbeats 1600000 in
theorem checkMembershipEncoded_computable' [Fintype T] :
    Computable (checkMembershipEncoded : EncodedCFG T × List T → Bool) := by
  apply Primrec.to_comp
  show Primrec (fun p : (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))) × List T =>
    checkMembershipEncoded p)
  apply Primrec.of_eq
  · show Primrec (fun p : (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))) × List T =>
      decide ((p.1.2.1 % (p.1.1 + 1), 0, p.2.length) ∈
        (satStep (p.1.1 + 1) p.1.2.2 p.2)^[(p.1.1 + 1) * (p.2.length + 1) * (p.2.length + 1) + 1] []))
    have h_triple : Primrec (fun p : (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))) × List T =>
        (p.1.2.1 % (p.1.1 + 1), (0 : ℕ), p.2.length)) :=
      Primrec.pair
        (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair (Primrec.const 0) (Primrec.list_length.comp Primrec.snd))
    have h_ctx : Primrec (fun p : (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))) × List T =>
        (p.1.1 + 1, p.1.2.2, p.2)) :=
      Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    have h_bound : Primrec (fun p : (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))) × List T =>
        (p.1.1 + 1) * (p.2.length + 1) * (p.2.length + 1) + 1) :=
      Primrec.succ.comp
        (Primrec.nat_mul.comp
          (Primrec.nat_mul.comp
            (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd)))
          (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd)))
    have h_sat : Primrec (fun p : (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))) × List T =>
        (satStep (p.1.1 + 1) p.1.2.2 p.2)^[
          (p.1.1 + 1) * (p.2.length + 1) * (p.2.length + 1) + 1] []) :=
      Primrec₂.comp satFixpoint_primrec h_ctx h_bound
    exact Primrec₂.comp triple_list_mem_primrec h_triple h_sat
  · intro p
    simp [checkMembershipEncoded, EncodedCFG.ntCount, EncodedCFG.numNT,
          EncodedCFG.initialIdx, EncodedCFG.rawRules, satFixpoint]