module

public import Langlib.Classes.ContextFree.Decidability.UniformMembership
public import Mathlib.Computability.Partrec
import Langlib.Utilities.PrimrecHelpers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
set_option backward.isDefEq.respectTransparency false
@[expose]
public section



/-! # Primitive Recursiveness of Saturation Step

This file proves that the saturation step function `satStep` is primitive recursive,
which is needed for the computability proof of context-free membership.
-/

open List

variable {T : Type} [DecidableEq T] [Primcodable T]

/-! ## Triple list membership is Primrec -/

private lemma triple_list_mem_primrec :
    Primrec₂ (fun (t : ℕ × ℕ × ℕ) (S : List (ℕ × ℕ × ℕ)) => (decide (t ∈ S) : Bool)) := by
  have hp : Primrec₂ (fun (p : (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ))
      (trip : ℕ × ℕ × ℕ) =>
        trip.1 == p.1.1 && trip.2.1 == p.1.2.1 && trip.2.2 == p.1.2.2) := by
    have h₁ : Primrec₂ (fun (p : (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ))
        (trip : ℕ × ℕ × ℕ) => trip.1 == p.1.1) :=
      Primrec.beq.comp₂
        (Primrec.fst.comp₂ Primrec₂.right)
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
    have h₂ : Primrec₂ (fun (p : (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ))
        (trip : ℕ × ℕ × ℕ) => trip.2.1 == p.1.2.1) :=
      Primrec.beq.comp₂
        (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
        (Primrec.fst.comp₂ (Primrec.snd.comp₂
          (Primrec.fst.comp₂ Primrec₂.left)))
    have h₃ : Primrec₂ (fun (p : (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ))
        (trip : ℕ × ℕ × ℕ) => trip.2.2 == p.1.2.2) :=
      Primrec.beq.comp₂
        (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
        (Primrec.snd.comp₂ (Primrec.snd.comp₂
          (Primrec.fst.comp₂ Primrec₂.left)))
    exact Primrec.and.comp₂ h₁ (Primrec.and.comp₂ h₂ h₃)
  apply Primrec.of_eq (primrec_list_any (f := Prod.snd) Primrec.snd hp)
  intro p
  simp

/-! ## matchOneSym helper is Primrec -/

/-
The core matching function for a single nonterminal symbol: given (k, nc, S, pos),
    returns the list of end positions from S matching (k % nc, pos, _).
-/
private lemma nonterminal_match_primrec :
    Primrec (fun (p : (ℕ × ℕ × List (ℕ × ℕ × ℕ)) × ℕ) =>
      (p.1.2.2.flatMap (fun trip =>
        if trip.1 == p.1.1 % p.1.2.1 && trip.2.1 == p.2 then [trip.2.2] else []))) := by
  let P := (ℕ × ℕ × List (ℕ × ℕ × ℕ)) × ℕ
  have hfirst : Primrec₂ (fun (p : P) (trip : ℕ × ℕ × ℕ) =>
      trip.1 == p.1.1 % p.1.2.1) :=
    Primrec.beq.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.nat_mod.comp₂
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        (Primrec.fst.comp₂ (Primrec.snd.comp₂
          (Primrec.fst.comp₂ Primrec₂.left))))
  have hsecond : Primrec₂ (fun (p : P) (trip : ℕ × ℕ × ℕ) =>
      trip.2.1 == p.2) :=
    Primrec.beq.comp₂
      (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.left)
  have hcond : Primrec₂ (fun (p : P) (trip : ℕ × ℕ × ℕ) =>
      trip.1 == p.1.1 % p.1.2.1 && trip.2.1 == p.2) :=
    Primrec.and.comp₂ hfirst hsecond
  have hthen : Primrec₂ (fun (_ : P) (trip : ℕ × ℕ × ℕ) => [trip.2.2]) :=
    Primrec.list_cons.comp₂
      (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
      (Primrec₂.const ([] : List ℕ))
  have hbody : Primrec₂ (fun (p : P) (trip : ℕ × ℕ × ℕ) =>
      if trip.1 == p.1.1 % p.1.2.1 && trip.2.1 == p.2 then [trip.2.2] else []) := by
    apply Primrec.of_eq (Primrec.cond hcond hthen (Primrec₂.const ([] : List ℕ)))
    intro ⟨p, trip⟩
    simp
  exact Primrec.list_flatMap
    (f := fun p : P => p.1.2.2)
    (g := fun p trip => if trip.1 == p.1.1 % p.1.2.1 && trip.2.1 == p.2 then
      [trip.2.2] else [])
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hbody

/-
The core matching function for a single terminal symbol: given (w, t, pos),
    returns [pos + 1] if w[pos] = t, else [].
-/
private lemma terminal_match_primrec :
    Primrec (fun (p : (List T × T) × ℕ) =>
      match p.1.1[p.2]? with
      | some c => if c == p.1.2 then [p.2 + 1] else []
      | none => ([] : List ℕ)) := by
  let P := (List T × T) × ℕ
  have hget : Primrec (fun (p : P) => p.1.1[p.2]?) :=
    Primrec₂.comp Primrec.list_getElem?
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hcond : Primrec₂ (fun (p : P) (c : T) => c == p.1.2) :=
    Primrec.beq.comp₂ Primrec₂.right
      (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
  have hthen : Primrec₂ (fun (p : P) (_ : T) => [p.2 + 1]) :=
    Primrec.list_cons.comp₂
      (Primrec.succ.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
      (Primrec₂.const ([] : List ℕ))
  have hsome : Primrec₂ (fun (p : P) (c : T) =>
      if c == p.1.2 then [p.2 + 1] else []) := by
    apply Primrec.of_eq (Primrec.cond hcond hthen (Primrec₂.const ([] : List ℕ)))
    intro ⟨p, c⟩
    simp
  apply Primrec.of_eq
    (Primrec.option_casesOn hget (Primrec.const ([] : List ℕ)) hsome)
  intro p
  cases h : p.1.1[p.2]? <;> simp [h]

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
  let C := ℕ × List T × List (ℕ × ℕ × ℕ)
  let P := C × List (ℕ ⊕ T) × ℕ
  let D := P × (List ℕ × (ℕ ⊕ T))
  have hleft : Primrec₂ (fun (x : D) (_ : ℕ) => x) := Primrec₂.left
  have hp : Primrec₂ (fun (x : D) (_ : ℕ) => x.1) :=
    Primrec.fst.comp₂ hleft
  have hctx : Primrec₂ (fun (x : D) (_ : ℕ) => x.1.1) :=
    Primrec.fst.comp₂ hp
  have hsym : Primrec₂ (fun (x : D) (_ : ℕ) => x.2.2) :=
    Primrec.snd.comp₂ (Primrec.snd.comp₂ hleft)
  have hsympos : Primrec₂ (fun (x : D) (pos : ℕ) => (x.2.2, pos)) :=
    Primrec.pair hsym Primrec₂.right
  have hargs : Primrec₂ (fun (x : D) (pos : ℕ) =>
      (x.1.1, x.2.2, pos)) :=
    Primrec.pair hctx hsympos
  have hmatch : Primrec₂ (fun (x : D) (pos : ℕ) =>
      matchOneSym x.1.1.2.1 x.1.1.1 x.1.1.2.2 x.2.2 pos) :=
    matchOneSym_primrec_bundled.comp₂ hargs
  have hstep : Primrec (fun (x : D) =>
      x.2.1.flatMap (fun pos =>
        matchOneSym x.1.1.2.1 x.1.1.1 x.1.1.2.2 x.2.2 pos)) :=
    Primrec.list_flatMap
      (f := fun x : D => x.2.1)
      (g := fun x pos => matchOneSym x.1.1.2.1 x.1.1.1 x.1.1.2.2 x.2.2 pos)
      (Primrec.fst.comp Primrec.snd) hmatch
  apply Primrec.of_eq
  · exact Primrec.list_foldl
      (f := fun p : P => p.2.1)
      (g := fun p : P => [p.2.2])
      (h := fun p q => q.1.flatMap (fun pos =>
        matchOneSym p.1.2.1 p.1.1 p.1.2.2 q.2 pos))
      (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.const ([] : List ℕ)))
      hstep
  · intro p
    rfl

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
  have htriple : Primrec (fun (x : (ℕ × ℕ) × (List (ℕ × ℕ × ℕ) × ℕ)) =>
      (x.1.1, x.1.2, x.2.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  have hlist : Primrec (fun (x : (ℕ × ℕ) × (List (ℕ × ℕ × ℕ) × ℕ)) =>
      x.2.1) := Primrec.fst.comp Primrec.snd
  have hcond := Primrec₂.comp triple_list_mem_primrec htriple hlist
  have happend : Primrec (fun (x : (ℕ × ℕ) × (List (ℕ × ℕ × ℕ) × ℕ)) =>
      x.2.1 ++ [(x.1.1, x.1.2, x.2.2)]) :=
    Primrec.list_append.comp hlist
      (Primrec.list_cons.comp htriple (Primrec.const []))
  apply Primrec.of_eq (Primrec.cond hcond hlist happend)
  intro x
  simp

/-
The innermost foldl of satStep: fold over endPos list, conditionally appending triples.
-/
private lemma innerFoldl_primrec :
    Primrec (fun (p : (ℕ × ℕ) × List ℕ × List (ℕ × ℕ × ℕ)) =>
      p.2.1.foldl (fun S''' endPos =>
        let triple := (p.1.1, p.1.2, endPos)
        if decide (triple ∈ S''') then S''' else S''' ++ [triple]) p.2.2) := by
  exact Primrec.list_foldl
    (f := fun p : (ℕ × ℕ) × List ℕ × List (ℕ × ℕ × ℕ) => p.2.1)
    (g := fun p : (ℕ × ℕ) × List ℕ × List (ℕ × ℕ × ℕ) => p.2.2)
    (h := fun p q =>
      let triple := (p.1.1, p.1.2, q.2)
      if decide (triple ∈ q.1) then q.1 else q.1 ++ [triple])
    (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)
    (condAppend_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

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
  let P := (ℕ × List T × List (ℕ × ℕ × ℕ) × ℕ × List (ℕ ⊕ T)) ×
    List (ℕ × ℕ × ℕ)
  have hrange : Primrec (fun p : P => List.range (p.1.2.1.length + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp (Primrec.list_length.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  exact Primrec.list_foldl
    (f := fun p : P => List.range (p.1.2.1.length + 1))
    (g := fun p : P => p.2)
    (h := fun p q =>
      (matchRHS p.1.2.1 p.1.1 p.1.2.2.1 p.1.2.2.2.2 q.2).foldl
        (fun S''' endPos =>
          let triple := (p.1.2.2.2.1 % p.1.1, q.2, endPos)
          if decide (triple ∈ S''') then S''' else S''' ++ [triple]) q.1)
    hrange Primrec.snd
    (middleStep_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

set_option maxHeartbeats 1600000 in
/-- satStep is Primrec as a function of bundled parameters. -/
lemma satStep_primrec_full :
    Primrec (fun (p : (ℕ × List (ℕ × List (ℕ ⊕ T)) × List T) × List (ℕ × ℕ × ℕ)) =>
      satStep p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let P := (ℕ × List (ℕ × List (ℕ ⊕ T)) × List T) × List (ℕ × ℕ × ℕ)
  let R := ℕ × List (ℕ ⊕ T)
  have hctx : Primrec₂ (fun (p : P) (pair : List (ℕ × ℕ × ℕ) × R) =>
      (p.1.1, p.1.2.2, p.2, pair.2.1, pair.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
      (Primrec.pair
        (Primrec.snd.comp₂ (Primrec.snd.comp₂
          (Primrec.fst.comp₂ Primrec₂.left)))
        (Primrec.pair
          (Primrec.snd.comp₂ Primrec₂.left)
          (Primrec.pair
            (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
            (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.right)))))
  have hargs : Primrec₂ (fun (p : P) (pair : List (ℕ × ℕ × ℕ) × R) =>
      ((p.1.1, p.1.2.2, p.2, pair.2.1, pair.2.2), pair.1)) :=
    Primrec.pair hctx (Primrec.fst.comp₂ Primrec₂.right)
  exact Primrec.list_foldl
    (f := fun p : P => p.1.2.1)
    (g := fun p : P => p.2)
    (h := fun p pair =>
      (List.range (p.1.2.2.length + 1)).foldl (fun S'' startPos =>
        (matchRHS p.1.2.2 p.1.1 p.2 pair.2.2 startPos).foldl
          (fun S''' endPos =>
            let triple := (pair.2.1 % p.1.1, startPos, endPos)
            if decide (triple ∈ S''') then S''' else S''' ++ [triple]) S'') pair.1)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    (middleFoldl_primrec.comp₂ hargs)

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
public theorem checkMembershipEncoded_computable' [Fintype T] :
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
