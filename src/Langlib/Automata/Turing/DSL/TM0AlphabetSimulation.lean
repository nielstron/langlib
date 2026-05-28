module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.PostTuringMachine
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

@[expose] public section

/-! # Alphabet Simulation for TM0

This file proves that a TM0 machine over a finite alphabet `Γ₁` can be
simulated by a TM0 machine over another finite alphabet `Γ₂`, provided
there exists an injection from `Γ₁` to `Γ₂` that maps default to default.

## Main results

- `TM0AlphabetSim.lift_eval_dom` — evaluation preserves Dom under alphabet embedding
-/

open Turing

namespace TM0AlphabetSim

variable {Γ₁ Γ₂ : Type} [Inhabited Γ₁] [Inhabited Γ₂]
variable {Λ : Type} [Inhabited Λ]

/-- Lift a TM0 machine from alphabet Γ₁ to Γ₂ via an embedding/inverse pair.
    The inverse maps Γ₂ symbols back to Γ₁ (left inverse of emb). -/
noncomputable def liftMachine (M : TM0.Machine Γ₁ Λ)
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁) :
    TM0.Machine Γ₂ Λ :=
  fun q a =>
    match M q (inv a) with
    | some (q', stmt) =>
      some (q', match stmt with
        | TM0.Stmt.move d => TM0.Stmt.move d
        | TM0.Stmt.write a' => TM0.Stmt.write (emb a'))
    | none => none

/-- The PointedMap from the embedding function. -/
noncomputable def embPM (emb : Γ₁ → Γ₂) (hemb_default : emb default = default) :
    PointedMap Γ₁ Γ₂ :=
  ⟨emb, hemb_default⟩

/-- The relation between Γ₁ configs and Γ₂ configs under the alphabet lift. -/
def liftRel (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a)
    (hemb_default : emb default = default) :
    TM0.Cfg Γ₁ Λ → TM0.Cfg Γ₂ Λ → Prop :=
  fun c₁ c₂ => c₁.q = c₂.q ∧ c₂.Tape = c₁.Tape.map (embPM emb hemb_default)

/-
The lifted machine respects the original via the alphabet relation.
-/
theorem lift_respects (M : TM0.Machine Γ₁ Λ)
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a)
    (hemb_default : emb default = default) :
    Respects
      (TM0.step M)
      (TM0.step (liftMachine M emb inv))
      (liftRel emb inv hemb hemb_default) := by
  unfold Respects liftRel;
  unfold TM0.step liftMachine;
  rintro ⟨ q, T ⟩ ⟨ q', T' ⟩ ⟨ hq, hT ⟩ ; rcases h : M q T.head with ( _ | ⟨ q'', stmt ⟩ ) <;> simp_all +decide [ Reaches₁ ] ;
  · unfold embPM; aesop;
  · refine' ⟨ ⟨ q'', _ ⟩, _, _ ⟩;
    exact ( match stmt with | TM0.Stmt.move d => Tape.move d | TM0.Stmt.write a => Tape.write ( emb a ) ) ( Tape.map ( embPM emb hemb_default ) T );
    · cases stmt <;> simp +decide [ *, Tape.map_move, Tape.map_write ];
      rfl;
    · refine' Relation.TransGen.single ⟨ q'', _, _, _ ⟩;
      exact match stmt with | TM0.Stmt.move d => TM0.Stmt.move d | TM0.Stmt.write a => TM0.Stmt.write ( emb a );
      · rw [ show inv ( Tape.map ( embPM emb hemb_default ) T ).head = T.head from ?_ ];
        · cases stmt <;> aesop;
        · cases T ; aesop;
      · cases stmt <;> rfl

/-
Initial configs are related under the alphabet lift.
-/
theorem lift_init_rel (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a)
    (hemb_default : emb default = default)
    (l : List Γ₁) :
    liftRel emb inv hemb hemb_default
      (@TM0.init Γ₁ Λ _ _ l)
      (@TM0.init Γ₂ Λ _ _ (l.map emb)) := by
  constructor;
  · rfl;
  · simp [TM0.init];
    unfold Tape.mk₁;
    simp +decide [ Tape.map, Tape.mk₂ ];
    cases l <;> aesop

/-- Evaluation preserves Dom under alphabet lift. -/
theorem lift_eval_dom (M : TM0.Machine Γ₁ Λ)
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a)
    (hemb_default : emb default = default)
    (l : List Γ₁) :
    (TM0.eval M l).Dom ↔
    (TM0.eval (liftMachine M emb inv) (l.map emb)).Dom := by
  simp only [TM0.eval]
  exact tr_eval_dom (lift_respects M emb inv hemb hemb_default)
    (lift_init_rel emb inv hemb hemb_default l) |>.symm

/-! ## Inverse-default-fiber-preserving lift -/

/-- The PointedMap from an inverse function. -/
noncomputable def invPM (inv : Γ₂ → Γ₁) (hinv_default : inv default = default) :
    PointedMap Γ₂ Γ₁ :=
  ⟨inv, hinv_default⟩

/-- Write translation for the inverse-relation lift.

When the source writes `default`, target symbols that already map to `default`
are preserved. This lets the target alphabet carry protected symbols that the
source machine observes as blanks. -/
noncomputable def liftWritePreserveDefaultFiber
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁) [DecidableEq Γ₁]
    (current : Γ₂) (a : Γ₁) : Γ₂ :=
  if a = default then
    if inv current = default then current else emb default
  else
    emb a

/-- Lift a TM0 machine while preserving target symbols in the inverse-default
fiber whenever the source writes `default`. -/
noncomputable def liftMachinePreserveDefaultFiber
    [DecidableEq Γ₁] (M : TM0.Machine Γ₁ Λ)
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁) :
    TM0.Machine Γ₂ Λ :=
  fun q a =>
    match M q (inv a) with
    | some (q', stmt) =>
      some (q', match stmt with
        | TM0.Stmt.move d => TM0.Stmt.move d
        | TM0.Stmt.write a' =>
            TM0.Stmt.write (liftWritePreserveDefaultFiber emb inv a a'))
    | none => none

/-- Inverse-form relation between source and target configurations.

The target tape may contain symbols outside the embedding image; the source
tape only has to be recovered by mapping target symbols through `inv`. -/
def liftInvRel (inv : Γ₂ → Γ₁) (hinv_default : inv default = default) :
    TM0.Cfg Γ₁ Λ → TM0.Cfg Γ₂ Λ → Prop :=
  fun c₁ c₂ => c₁.q = c₂.q ∧ c₁.Tape = c₂.Tape.map (invPM inv hinv_default)

theorem inv_liftWritePreserveDefaultFiber
    [DecidableEq Γ₁]
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a)
    (current : Γ₂) (a : Γ₁) :
    inv (liftWritePreserveDefaultFiber emb inv current a) = a := by
  unfold liftWritePreserveDefaultFiber
  by_cases ha : a = default
  · subst ha
    by_cases hcur : inv current = default
    · simp [hcur]
    · simp [hcur, hemb]
  · simp [ha, hemb]

theorem lift_preserveDefaultFiber_respects
    [DecidableEq Γ₁]
    (M : TM0.Machine Γ₁ Λ)
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a)
    (hinv_default : inv default = default) :
    Respects
      (TM0.step M)
      (TM0.step (liftMachinePreserveDefaultFiber M emb inv))
      (liftInvRel inv hinv_default) := by
  unfold Respects liftInvRel
  unfold TM0.step liftMachinePreserveDefaultFiber
  rintro ⟨q, T⟩ ⟨q', T'⟩ ⟨hq, hT⟩
  have hhead : T.head = inv T'.head := by
    have := congrArg Tape.head hT
    simpa [invPM] using this
  change q = q' at hq
  subst q'
  change T = Tape.map (invPM inv hinv_default) T' at hT
  rcases h : M q (inv T'.head) with (_ | ⟨q'', stmt⟩)
  · have hsrc : M q T.head = none := by
      rw [hhead]
      exact h
    simp +decide [hsrc, h]
  · have hsrc : M q T.head = some (q'', stmt) := by
      rw [hhead]
      exact h
    simp +decide [Reaches₁, hsrc]
    refine ⟨⟨q'', match stmt with
      | TM0.Stmt.move d => Tape.move d T'
      | TM0.Stmt.write a =>
          Tape.write (liftWritePreserveDefaultFiber emb inv T'.head a) T'⟩, ?_, ?_⟩
    · constructor
      · rfl
      · cases stmt with
        | move d =>
            simp [hT, Tape.map_move]
        | write a =>
            have hw :
                (invPM inv hinv_default).f
                  (liftWritePreserveDefaultFiber emb inv T'.head a) = a := by
              simpa [invPM] using
                inv_liftWritePreserveDefaultFiber emb inv hemb T'.head a
            simp [hT, Tape.map_write, hw]
    · refine Relation.TransGen.single ?_
      cases stmt with
      | move d =>
          refine ⟨q'', TM0.Stmt.move d, ?_, rfl⟩
          simp [hhead, h]
      | write a =>
          refine ⟨q'', TM0.Stmt.write
            (liftWritePreserveDefaultFiber emb inv T'.head a), ?_, rfl⟩
          simp [hhead, h]

theorem liftInv_init_rel
    (inv : Γ₂ → Γ₁) (hinv_default : inv default = default)
    (l : List Γ₂) :
    liftInvRel inv hinv_default
      (@TM0.init Γ₁ Λ _ _ (l.map inv))
      (@TM0.init Γ₂ Λ _ _ l) := by
  constructor
  · rfl
  · simp [liftInvRel, TM0.init, Tape.map_mk₁, invPM]

/-- Evaluation preserves Dom for the inverse-default-fiber-preserving lift. -/
theorem lift_preserveDefaultFiber_eval_dom
    [DecidableEq Γ₁]
    (M : TM0.Machine Γ₁ Λ)
    (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a)
    (hinv_default : inv default = default)
    (l : List Γ₂) :
    (TM0.eval M (l.map inv)).Dom ↔
    (TM0.eval (liftMachinePreserveDefaultFiber M emb inv) l).Dom := by
  simp only [TM0.eval]
  exact tr_eval_dom
    (lift_preserveDefaultFiber_respects M emb inv hemb hinv_default)
    (liftInv_init_rel inv hinv_default l) |>.symm

end TM0AlphabetSim
