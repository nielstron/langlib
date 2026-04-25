import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.EmptyTM
import Langlib.Automata.Turing.DSL.TM0Restrict

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

end TM0AlphabetSim