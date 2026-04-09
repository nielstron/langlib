import Mathlib

/-! # Primitive Recursive Helpers

This file provides helper lemmas establishing that various list operations
are primitive recursive, needed for showing that the CYK algorithm is computable. -/

open List

section PrimrecListOps

variable {α : Type} [Primcodable α]

/-
`List.take` is primitive recursive (as a function of both arguments).
-/
lemma primrec₂_list_take : Primrec₂ (fun (n : ℕ) (l : List α) => l.take n) := by
  -- We can show that `List.take` is primitive recursive using `Primrec.list_foldl.` The initial state `(n, [])` is primitive recursive.
  have h_take : Primrec (fun pl : ℕ × List α => (pl.2.foldl (fun (s : ℕ × List α) (x : α) => if s.1 = 0 then (0, s.2) else (s.1 - 1, s.2 ++ [x])) (pl.1, [])).2) := by
    have h_take : Primrec₂ (fun (s : ℕ × List α) (x : α) => if s.1 = 0 then (0, s.2) else (s.1 - 1, s.2 ++ [x])) := by
      refine' Primrec.ite _ _ _;
      · exact Primrec.eq.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.const 0 );
      · exact Primrec.pair ( Primrec.const _ ) ( Primrec.snd.comp ( Primrec.fst ) );
      · refine' Primrec.pair _ _;
        · exact Primrec.nat_sub.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.const 1 );
        · have h_concat : Primrec₂ (fun (l : List α) (x : α) => l ++ [x]) := by
            convert Primrec.list_concat using 1;
          exact h_concat.comp ( Primrec.snd.comp ( Primrec.fst ) ) ( Primrec.snd );
    have h_foldl : Primrec (fun (pl : ℕ × List α) => List.foldl (fun (s : ℕ × List α) (x : α) => if s.1 = 0 then (0, s.2) else (s.1 - 1, s.2 ++ [x])) (pl.1, []) pl.2) := by
      convert Primrec.list_foldl _ _ _ using 1;
      rotate_left;
      exact α;
      assumption;
      exact fun pl => pl.2;
      exact fun pl => ( pl.1, [] );
      exact fun pl s => if s.1.1 = 0 then ( 0, s.1.2 ) else ( s.1.1 - 1, s.1.2 ++ [ s.2 ] );
      · exact Primrec.snd;
      · exact Primrec.pair ( Primrec.fst ) ( Primrec.const _ );
      · convert h_take.comp _ _ using 1;
        · exact Primrec.fst.comp ( Primrec.snd );
        · exact Primrec.snd.comp ( Primrec.snd );
      · rfl;
    exact Primrec.snd.comp h_foldl;
  have h_take_eq : ∀ n l, (l.foldl (fun (s : ℕ × List α) (x : α) => if s.1 = 0 then (0, s.2) else (s.1 - 1, s.2 ++ [x])) (n, [])).2 = take n l := by
    intro n l; induction' l using List.reverseRecOn with x l ih generalizing n <;> simp_all +decide [ List.take ] ;
    split_ifs <;> simp_all +decide [ List.take_append ];
    · have h_foldl_zero : ∀ (l : List α) (n : ℕ), (List.foldl (fun (s : ℕ × List α) (x : α) => if s.1 = 0 then (0, s.2) else (s.1 - 1, s.2 ++ [x])) (n, []) l).1 = n - l.length := by
        intro l n; induction' l using List.reverseRecOn with x l ih generalizing n <;> simp_all +decide [ List.length ] ;
        grind +splitImp;
      rw [ ← h_foldl_zero, ‹ ( foldl ( fun s x => if s.1 = 0 then ( 0, s.2 ) else ( s.1 - 1, s.2 ++ [ x ] ) ) ( n, [] ) x ).1 = 0 › ];
    · -- By definition of `foldl`, if the first component of the result is not zero, then `n` must be greater than the length of `x`.
      have h_foldl : ∀ (n : ℕ) (x : List α), (foldl (fun s x => if s.1 = 0 then (0, s.2) else (s.1 - 1, s.2 ++ [x])) (n, []) x).1 = n - x.length := by
        intro n x; induction' x using List.reverseRecOn with x l ih <;> simp_all +decide [ List.take ] ;
        lia;
      exact h_foldl n x ▸ Nat.pos_of_ne_zero ‹_›;
  simpa only [ ← h_take_eq ] using h_take.comp ( Primrec.fst.pair Primrec.snd )

/-
`List.drop` is primitive recursive (as a function of both arguments).
-/
lemma primrec₂_list_drop : Primrec₂ (fun (n : ℕ) (l : List α) => l.drop n) := by
  -- We'll use induction on $n$ to prove that `drop` is primitive recursive.
  have h_ind : ∀ n : ℕ,
      Primrec (fun (l : List α) => drop n l) := by
        intro n;
        induction' n with n ih;
        · exact Primrec.id;
        · -- The function `drop (n + 1)` can be expressed as `drop n ∘ List.tail`.
          have h_drop_succ : ∀ (l : List α), drop (n + 1) l = drop n (List.tail l) := by
            aesop;
          simpa only [ h_drop_succ ] using ih.comp ( Primrec.list_tail );
  convert Primrec.nat_rec ( h_ind 0 ) _;
  rotate_left;
  exact fun l p => drop 1 p.2;
  · exact Primrec.comp ( h_ind 1 ) ( Primrec.snd.comp ( Primrec.snd ) );
  · constructor <;> intro h <;> simp_all +decide [ Primrec₂ ];
    · convert h.comp ( show Primrec ( fun p : List α × ℕ => ( p.2, p.1 ) ) from ?_ ) using 1;
      · exact funext fun p => by induction p.2 <;> simp +decide [ *, Nat.rec ] ;
      · exact Primrec.pair ( Primrec.snd ) ( Primrec.fst );
    · convert h.comp ( show Primrec ( fun p : ℕ × List α => ( p.2, p.1 ) ) from ?_ ) using 1;
      · ext ⟨ n, l ⟩ ; induction n <;> simp +decide [ *, List.drop ] ;
        rename_i k hk;
        rw [ show ( Nat.rec l ( fun n IH => IH.tail ) k : List α ) = l.drop k from ?_ ];
        · grind;
        · exact Nat.recOn k rfl fun n IH => by simp +decide [ IH, List.drop ] ;
      · exact Primrec.pair ( Primrec.snd ) ( Primrec.fst )

end PrimrecListOps

section PrimrecListAny

variable {α : Type} [Primcodable α]

/-
`List.any` with a fixed predicate is primitive recursive.
-/
lemma primrec_list_any {f : α → List β} {p : α → β → Bool}
    [Primcodable β]
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).any (p a)) := by
  -- Use the given `Primrec₂` hypothesis plus `Primrec.fst` and `Primrec.snd` to make a `Primrec` function from `α × β × Bool` to `Bool`.
  have hp_step : Primrec (fun (ab : α × (β × Bool)) => p ab.1 ab.2.1 || ab.2.2) := by
    have hp_step : Primrec (fun (ab : α × β) => p ab.1 ab.2) := by
      exact?;
    convert Primrec.cond ?_ ?_ ?_ using 1;
    · exact hp_step.comp ( Primrec.fst.pair ( Primrec.fst.comp Primrec.snd ) );
    · exact Primrec.const Bool.true;
    · exact Primrec.snd.comp ( Primrec.snd );
  convert Primrec.list_foldr _ _ _ (f := fun a => f a) using 2;
  rotate_left;
  exact fun _ => Bool.false;
  exact fun a b => p a b.1 || b.2;
  · exact hf;
  · exact Primrec.const Bool.false;
  · exact hp_step;
  · induction ( f ‹_› ) <;> simp +decide [ * ]

end PrimrecListAny