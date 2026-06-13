module

public import Mathlib.Computability.PostTuringMachine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-! # TM0 Reverse Block Machine

The machine is parameterized by a separator `sep` that marks the right end of
the block. It works on any separator as long as block elements are distinct
from both `default` (the tape blank) and `sep`.

## Key results

- `RevBlock.MSep`: the separator-parametric reverse-block TM0 machine.
- `RevBlock.full_reaches`: the machine reaches a reversed block plus suffix.
- `RevBlock.full_reaches_default`: blank-delimited specialization.
-/

open Turing

namespace RevBlock

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ]

/-! ### State type -/

public inductive CarryPhase where | carryRight | shifting | returning deriving DecidableEq
public inductive NoCarryPhase where | grab | advance | rewind | rewindDone deriving DecidableEq

public instance : Fintype CarryPhase where
  elems := {.carryRight, .shifting, .returning}; complete x := by cases x <;> simp

public instance : Fintype NoCarryPhase where
  elems := {.grab, .advance, .rewind, .rewindDone}; complete x := by cases x <;> simp

@[expose]
public abbrev RSt (Γ : Type) := (Γ × CarryPhase) ⊕ NoCarryPhase
@[expose]
public instance [Inhabited Γ] : Inhabited (RSt Γ) := ⟨Sum.inr .grab⟩

/-! ### Machine definition -/

/-- Reverse-block machine parameterized by separator `sep`.

* **grab / shifting / returning** use `sep` to detect the right block boundary
  and as the temporary "erased" marker when a cell is grabbed.
* **rewind** uses `default` to find the left edge of the tape. -/
@[expose]
public noncomputable def MSep (Γ : Type) [Inhabited Γ] [DecidableEq Γ] (sep : Γ) :
    @TM0.Machine Γ (RSt Γ) ⟨Sum.inr .grab⟩ :=
  fun q a => match q with
    | Sum.inr .grab =>
      if a = sep then some (Sum.inr .rewind, TM0.Stmt.move Dir.left)
      else some (Sum.inl (a, .carryRight), TM0.Stmt.write sep)
    | Sum.inl (g, .carryRight) => some (Sum.inl (g, .shifting), TM0.Stmt.move Dir.right)
    | Sum.inl (g, .shifting) =>
      if a = sep then some (Sum.inl (g, .returning), TM0.Stmt.move Dir.left)
      else some (Sum.inl (a, .carryRight), TM0.Stmt.write g)
    | Sum.inl (g, .returning) =>
      if a = sep then some (Sum.inr .advance, TM0.Stmt.write g)
      else some (Sum.inl (g, .returning), TM0.Stmt.move Dir.left)
    | Sum.inr .advance => some (Sum.inr .grab, TM0.Stmt.move Dir.right)
    | Sum.inr .rewind =>
      if a = default then some (Sum.inr .rewindDone, TM0.Stmt.move Dir.right)
      else some (Sum.inr .rewind, TM0.Stmt.move Dir.left)
    | Sum.inr .rewindDone => none

/-- The original machine with `default` as separator. -/
noncomputable def M (Γ : Type) [Inhabited Γ] [DecidableEq Γ] :
    @TM0.Machine Γ (RSt Γ) ⟨Sum.inr .grab⟩ :=
  MSep Γ default

/-! ### Tape.mk₂ helpers -/

omit [DecidableEq Γ] in
private theorem listBlank_mk_headI_tail (R : List Γ) :
    ListBlank.mk (R.headI :: R.tail) = ListBlank.mk R := by
  apply ListBlank.ext; intro i; simp only [ListBlank.nth_mk]
  cases R with | nil => cases i <;> simp [List.getI, List.getD, List.headI] | cons _ _ => rfl

omit [DecidableEq Γ] in
public theorem mk₂_move_right (L : List Γ) (x : Γ) (R : List Γ) :
    Tape.move Dir.right (Tape.mk₂ L (x :: R)) = Tape.mk₂ (x :: L) R := by
  simp [Tape.mk₂, Tape.mk', Tape.move, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

omit [DecidableEq Γ] in
public theorem mk₂_move_left (x : Γ) (L R : List Γ) :
    Tape.move Dir.left (Tape.mk₂ (x :: L) R) = Tape.mk₂ L (x :: R) := by
  simp only [Tape.mk₂, Tape.mk', Tape.move, ListBlank.head_mk, ListBlank.tail_mk,
    ListBlank.cons_mk, List.headI, List.tail_cons]
  congr 1; exact listBlank_mk_headI_tail R

omit [DecidableEq Γ] in
theorem mk₂_write (a : Γ) (L : List Γ) (x : Γ) (R : List Γ) :
    Tape.write a (Tape.mk₂ L (x :: R)) = Tape.mk₂ L (a :: R) := by
  simp [Tape.mk₂, Tape.mk', Tape.write, ListBlank.tail_mk]

omit [DecidableEq Γ] in
public theorem mk₂_head (L : List Γ) (x : Γ) (R : List Γ) :
    (Tape.mk₂ L (x :: R)).head = x := by
  simp [Tape.mk₂, Tape.mk', ListBlank.head_mk]

omit [DecidableEq Γ] in
public theorem mk₂_nil_eq_mk₁ (R : List Γ) : Tape.mk₂ [] R = Tape.mk₁ R := by
  simp [Tape.mk₂, Tape.mk₁, Tape.mk']

/-! ### Return loop -/

variable (sep : Γ)

/-- Return loop: from returning(carry), move left through non-sep head elements.
    Each step pops from the left and pushes the old head onto the right. -/
theorem return_loop (carry h : Γ) (elems L_orig R : List Γ)
    (hh : h ≠ sep) (helems : ∀ y ∈ elems, y ≠ sep) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inl (carry, .returning), Tape.mk₂ (elems ++ sep :: L_orig) (h :: R)⟩
      ⟨Sum.inl (carry, .returning), Tape.mk₂ L_orig (sep :: elems.reverse ++ h :: R)⟩ := by
  induction' elems with e elems ih generalizing L_orig R h;
  · refine' Relation.ReflTransGen.single _;
    unfold MSep; simp +decide ;
    unfold TM0.step;
    simp +decide [ hh, Tape.mk₂ ];
  · refine' Relation.ReflTransGen.head _ _;
    exact ⟨ Sum.inl ( carry, CarryPhase.returning ), Tape.mk₂ ( elems ++ sep :: L_orig ) ( e :: h :: R ) ⟩;
    · unfold TM0.step MSep; simp +decide ;
      rw [ if_neg ];
      · exact ⟨ _, rfl, mk₂_move_left _ _ _ ⟩;
      · exact?;
    · convert ih e L_orig ( h :: R ) ( helems e ( by simp +decide ) ) ( fun y hy => helems y ( by simp +decide [ hy ] ) ) using 1;
      simp +decide [ List.reverse_cons ]

/-! ### Shift-to-grab -/

/-- Base case: rest = [], shifted = []. -/
private theorem shift_to_grab_nil_nil (carry : Γ) (L_orig suffix : List Γ) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inl (carry, .shifting),
       Tape.mk₂ (sep :: L_orig) (sep :: suffix)⟩
      ⟨Sum.inr .grab,
       Tape.mk₂ (carry :: L_orig) (sep :: suffix)⟩ := by
  have h1 : TM0.step (MSep Γ sep) ⟨Sum.inl (carry, CarryPhase.shifting), Tape.mk₂ (sep :: L_orig) (sep :: suffix)⟩ = some ⟨Sum.inl (carry, CarryPhase.returning), Tape.mk₂ L_orig (sep :: sep :: suffix)⟩ := by
    unfold MSep; simp +decide [ TM0.step ] ;
    exact ⟨ _, if_pos ( mk₂_head _ _ _ ), mk₂_move_left _ _ _ ⟩;
  have h2 : TM0.step (MSep Γ sep) ⟨Sum.inl (carry, CarryPhase.returning), Tape.mk₂ L_orig (sep :: sep :: suffix)⟩ = some ⟨Sum.inr NoCarryPhase.advance, Tape.mk₂ L_orig (carry :: sep :: suffix)⟩ := by
    unfold TM0.step;
    unfold MSep; simp +decide [ Tape.mk₂ ] ;
  have h3 : TM0.step (MSep Γ sep) ⟨Sum.inr NoCarryPhase.advance, Tape.mk₂ L_orig (carry :: sep :: suffix)⟩ = some ⟨Sum.inr NoCarryPhase.grab, Tape.mk₂ (carry :: L_orig) (sep :: suffix)⟩ := by
    unfold TM0.step MSep; simp +decide [ Tape.mk₂ ] ;
  exact Relation.ReflTransGen.head h1 ( Relation.ReflTransGen.head h2 ( Relation.ReflTransGen.head h3 ( Relation.ReflTransGen.refl ) ) )

/-- Base case: rest = [], shifted = x :: xs. -/
private theorem shift_to_grab_nil_cons (carry x : Γ) (xs L_orig suffix : List Γ)
    (hx : x ≠ sep) (hxs : ∀ y ∈ xs, y ≠ sep) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inl (carry, .shifting),
       Tape.mk₂ (x :: xs ++ sep :: L_orig) (sep :: suffix)⟩
      ⟨Sum.inr .grab,
       Tape.mk₂ (carry :: L_orig) (xs.reverse ++ x :: sep :: suffix)⟩ := by
  have h_shift : Reaches (TM0.step (MSep Γ sep)) ⟨Sum.inl (carry, .shifting), Tape.mk₂ (x :: xs ++ sep :: L_orig) (sep :: suffix)⟩ ⟨Sum.inl (carry, .returning), Tape.mk₂ L_orig (sep :: xs.reverse ++ x :: sep :: suffix)⟩ := by
    have h_step : TM0.step (MSep Γ sep) ⟨Sum.inl (carry, .shifting), Tape.mk₂ (x :: xs ++ sep :: L_orig) (sep :: suffix)⟩ = some ⟨Sum.inl (carry, .returning), Tape.mk₂ (xs ++ sep :: L_orig) (x :: sep :: suffix)⟩ := by
      unfold MSep;
      simp +decide [ TM0.step, Tape.mk₂ ];
    have := return_loop sep carry x xs L_orig (sep :: suffix) hx hxs;
    exact Relation.ReflTransGen.head h_step this;
  have h_return : TM0.step (MSep Γ sep) ⟨Sum.inl (carry, .returning), Tape.mk₂ L_orig (sep :: xs.reverse ++ x :: sep :: suffix)⟩ = some ⟨Sum.inr .advance, Tape.mk₂ L_orig (carry :: xs.reverse ++ x :: sep :: suffix)⟩ := by
    unfold MSep;
    simp +decide [ TM0.step, Tape.mk₂ ];
  have h_advance : TM0.step (MSep Γ sep) ⟨Sum.inr .advance, Tape.mk₂ L_orig (carry :: xs.reverse ++ x :: sep :: suffix)⟩ = some ⟨Sum.inr .grab, Tape.mk₂ (carry :: L_orig) (xs.reverse ++ x :: sep :: suffix)⟩ := by
    unfold TM0.step MSep; aesop;
  exact h_shift.trans ( Relation.ReflTransGen.single h_return ) |> Relation.ReflTransGen.trans <| Relation.ReflTransGen.single h_advance

/-
From shifting(carry) to grab: complete shift + return + deposit + advance.
    Note: `hsuf` is not needed because the machine never accesses the suffix.
-/
public theorem shift_to_grab (carry : Γ) (rest shifted L_orig suffix : List Γ)
    (hcarry : carry ≠ sep) (hrest : ∀ y ∈ rest, y ≠ sep)
    (hshifted : ∀ y ∈ shifted, y ≠ sep) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inl (carry, .shifting),
       Tape.mk₂ (shifted ++ sep :: L_orig) (rest ++ sep :: suffix)⟩
      ⟨Sum.inr .grab,
       Tape.mk₂ ((carry :: rest).getLast (by simp) :: L_orig)
         (shifted.reverse ++ (carry :: rest).dropLast ++ sep :: suffix)⟩ := by
  induction' rest with r rest ih generalizing carry shifted; simp_all +decide [ List.getLast, List.dropLast ] ;
  · cases shifted <;> simp_all +decide [  ];
    · exact?;
    · exact shift_to_grab_nil_cons _ _ _ _ _ _ hshifted.1 hshifted.2;
  · have h1 : Reaches (TM0.step (MSep Γ sep)) ⟨Sum.inl (carry, .shifting), Tape.mk₂ (shifted ++ sep :: L_orig) (r :: rest ++ sep :: suffix)⟩ ⟨Sum.inl (r, .carryRight), Tape.mk₂ (shifted ++ sep :: L_orig) (carry :: rest ++ sep :: suffix)⟩ := by
      constructor;
      constructor;
      unfold MSep; simp +decide ;
      unfold TM0.step;
      simp +decide [ hrest, Tape.mk₂ ]
    generalize_proofs at *; (
    have h2 : Reaches (TM0.step (MSep Γ sep)) ⟨Sum.inl (r, .carryRight), Tape.mk₂ (shifted ++ sep :: L_orig) (carry :: rest ++ sep :: suffix)⟩ ⟨Sum.inl (r, .shifting), Tape.mk₂ (carry :: shifted ++ sep :: L_orig) (rest ++ sep :: suffix)⟩ := by
      apply Relation.ReflTransGen.single; simp [TM0.step, MSep];
      convert mk₂_move_right _ _ _ using 1
    generalize_proofs at *; (
    convert h1.trans ( h2.trans ( ih r ( carry :: shifted ) ( by aesop ) ( by aesop ) ( by aesop ) ) ) using 1;
    simp +decide [ List.getLast, List.dropLast ]))

/-! ### One iteration -/

public theorem one_iteration (x : Γ) (rest L_orig suffix : List Γ)
    (hx : x ≠ sep) (hrest : ∀ y ∈ rest, y ≠ sep) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inr .grab, Tape.mk₂ L_orig ((x :: rest) ++ sep :: suffix)⟩
      ⟨Sum.inr .grab,
       Tape.mk₂ ((x :: rest).getLast (by simp) :: L_orig)
         ((x :: rest).dropLast ++ sep :: suffix)⟩ := by
  have h_shift : Reaches (TM0.step (MSep Γ sep)) ⟨Sum.inl (x, .shifting), Tape.mk₂ (sep :: L_orig) (rest ++ sep :: suffix)⟩ ⟨Sum.inr .grab, Tape.mk₂ ((x :: rest).getLast (by simp) :: L_orig) ((x :: rest).dropLast ++ sep :: suffix)⟩ := by
    convert shift_to_grab sep x rest [] L_orig suffix hx hrest ( by simp ) using 1;
  have h_carryRight : Reaches (TM0.step (MSep Γ sep)) ⟨Sum.inr .grab, Tape.mk₂ L_orig (x :: rest ++ sep :: suffix)⟩ ⟨Sum.inl (x, .carryRight), Tape.mk₂ L_orig (sep :: rest ++ sep :: suffix)⟩ := by
    refine' Relation.ReflTransGen.single _;
    unfold MSep; simp +decide ;
    unfold TM0.step; simp +decide ;
    rw [ if_neg ];
    · exact ⟨ TM0.Stmt.write sep, rfl, by rw [ Tape.mk₂ ] ; rfl ⟩;
    · unfold Tape.mk₂; simp +decide [ hx ] ;
  have h_shifting : Reaches (TM0.step (MSep Γ sep)) ⟨Sum.inl (x, .carryRight), Tape.mk₂ L_orig (sep :: rest ++ sep :: suffix)⟩ ⟨Sum.inl (x, .shifting), Tape.mk₂ (sep :: L_orig) (rest ++ sep :: suffix)⟩ := by
    apply_rules [ Relation.ReflTransGen.single ];
  exact h_carryRight.trans h_shifting |> Relation.ReflTransGen.trans <| h_shift

/-! ### Iteration loop -/

public theorem iteration_loop (block suffix : List Γ)
    (hblock : ∀ y ∈ block, y ≠ sep) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inr .grab, Tape.mk₂ [] (block ++ sep :: suffix)⟩
      ⟨Sum.inr .grab, Tape.mk₂ block (sep :: suffix)⟩ := by
  have h_ind : ∀ (block L suffix : List Γ), (∀ y ∈ block, y ≠ sep) → Reaches (TM0.step (MSep Γ sep)) ⟨Sum.inr .grab, Tape.mk₂ L (block ++ sep :: suffix)⟩ ⟨Sum.inr .grab, Tape.mk₂ (block ++ L) (sep :: suffix)⟩ := by
    intro block L suffix hblock; induction' block using List.reverseRecOn with init last ih generalizing L; simp_all +decide [  ] ;
    · constructor;
    · by_cases hinit : init = [] <;> simp_all +decide [ List.append_assoc ];
      · convert one_iteration sep last [] L suffix hblock ( by simp +decide ) using 1;
      · obtain ⟨x, rest, hx⟩ : ∃ x rest, init = x :: rest := List.exists_cons_of_ne_nil hinit;
        have := one_iteration sep x ( rest ++ [ last ] ) L suffix ; simp_all +decide [ List.append_assoc ] ;
        simp_all +decide [ List.dropLast ];
        exact this ( by aesop ) |> fun h => h.trans ( ih _ );
  simpa using h_ind block [] suffix hblock

/-! ### Rewind loop -/

/-- Rewind uses `default` (not `sep`) to find the left tape edge. -/
public theorem rewind_loop (s : Γ) (rest R_rest : List Γ)
    (hs : s ≠ default) (hrest : ∀ y ∈ rest, y ≠ default) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inr .rewind, Tape.mk₂ rest (s :: R_rest)⟩
      ⟨Sum.inr .rewind, Tape.mk₂ [] (default :: rest.reverse ++ s :: R_rest)⟩ := by
  induction' rest with x rest ih generalizing s R_rest <;> simp_all +decide [ Tape.mk₂ ];
  · constructor;
    constructor;
    unfold TM0.step; simp +decide [ hs, MSep ] ;
  · have h_step : TM0.step (MSep Γ sep) ⟨Sum.inr .rewind, Tape.mk₂ (x :: rest) (s :: R_rest)⟩ = some ⟨Sum.inr .rewind, Tape.mk₂ rest (x :: s :: R_rest)⟩ := by
      unfold TM0.step; unfold MSep; aesop;
    exact Relation.ReflTransGen.head h_step ( by simpa using ih x ( s :: R_rest ) hrest.1 )

/-! ### Rewind phase -/

public theorem rewind_phase (block suffix : List Γ)
    (hblock_nd : ∀ y ∈ block, y ≠ default)
    (hblock_nsep : ∀ y ∈ block, y ≠ sep) :
    Reaches (TM0.step (MSep Γ sep))
      ⟨Sum.inr .grab, Tape.mk₂ block (sep :: suffix)⟩
      ⟨Sum.inr .rewindDone, Tape.mk₂ [] (block.reverse ++ sep :: suffix)⟩ := by
  constructor;
  rotate_right;
  exact ⟨ Sum.inr NoCarryPhase.rewind, Tape.mk₂ [] ( default :: block.reverse ++ sep :: suffix ) ⟩;
  · cases block <;> simp_all +decide [ Tape.mk₂ ];
    · refine' .single _;
      unfold TM0.step; simp +decide [ MSep ] ;
    · rename_i k hk;
      have := @RevBlock.rewind_loop Γ _ _ sep;
      convert Relation.ReflTransGen.trans _ ( this k hk ( sep :: suffix ) hblock_nd.1 hblock_nd.2 ) using 1;
      apply_rules [ Relation.ReflTransGen.single ];
      unfold MSep; simp +decide ;
      unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
  · unfold TM0.step; unfold MSep; simp +decide [ Tape.mk₂ ] ;
    simp [Tape.mk'];
    ext i; simp [ListBlank.mk];
    cases i <;> simp +decide [ ListBlank.nth ]

/-! ### Full computation -/

public theorem full_reaches (block suffix : List Γ)
    (hblock_nd : ∀ y ∈ block, y ≠ default)
    (hblock_nsep : ∀ y ∈ block, y ≠ sep) :
    Reaches (TM0.step (MSep Γ sep))
      (TM0.init (block ++ sep :: suffix))
      ⟨Sum.inr .rewindDone, Tape.mk₁ (block.reverse ++ sep :: suffix)⟩ := by
  unfold TM0.init
  rw [← mk₂_nil_eq_mk₁, ← mk₂_nil_eq_mk₁]
  exact (iteration_loop sep block suffix hblock_nsep).trans
    (rewind_phase sep block suffix hblock_nd hblock_nsep)

public theorem step_rewindDone (T : Tape Γ) :
    TM0.step (MSep Γ sep) ⟨Sum.inr .rewindDone, T⟩ = none := by
  simp [TM0.step, MSep]

/-! ### Backward compatibility wrappers -/

theorem full_reaches_default (block suffix : List Γ)
    (hblock : ∀ y ∈ block, y ≠ default) (_hsuf : ∀ y ∈ suffix, y ≠ default) :
    Reaches (TM0.step (M Γ))
      (TM0.init (block ++ default :: suffix))
      ⟨Sum.inr .rewindDone, Tape.mk₁ (block.reverse ++ default :: suffix)⟩ :=
  full_reaches default block suffix hblock hblock

theorem step_rewindDone_default (T : Tape Γ) :
    TM0.step (M Γ) ⟨Sum.inr .rewindDone, T⟩ = none :=
  step_rewindDone default T

end RevBlock
