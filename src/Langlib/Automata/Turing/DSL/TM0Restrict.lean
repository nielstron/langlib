import Mathlib

/-! # TM0 Restriction to Finite Support

Given a TM0 machine supported by a finite set of states, we construct an
equivalent TM0 machine whose state type is a subtype, hence `Fintype`.

## Main results

- `Turing.TM0.restrict` — restrict a TM0 machine to a finite support set
- `Turing.TM0.restrict_eval_dom_iff` — the restricted machine halts iff the original does
-/

open Turing

namespace Turing.TM0

variable {Γ : Type} {Λ : Type} [Inhabited Λ] [Inhabited Γ]

/-- Restrict a TM0 machine to states in a finite support set `S`.
Since the machine is supported by `S`, all transitions stay within `S`,
so the restriction doesn't change behavior. -/
noncomputable def restrict (M : Machine Γ Λ) (S : Finset Λ)
    (hS : Supports M ↑S) :
    @Machine Γ { q : Λ // q ∈ S } ⟨⟨default, hS.1⟩⟩ :=
  fun ⟨q, hq⟩ a =>
    match hm : M q a with
    | some (q', s) =>
      have hq' : q' ∈ S := hS.2 (show (q', s) ∈ M q a from hm ▸ rfl) hq
      some (⟨q', hq'⟩, s)
    | none => none

/-- The bisimulation relation: configs are related when the restricted config's
state projects to the original config's state, and tapes are equal. -/
def restrictRel (S : Finset Λ) :
    @Cfg Γ { q : Λ // q ∈ S } _ → @Cfg Γ Λ _ → Prop :=
  fun c₂ c₁ => c₁.q = c₂.q.val ∧ c₁.Tape = c₂.Tape

/-
The step functions respect the bisimulation relation.
-/
theorem restrict_respects (M : Machine Γ Λ) (S : Finset Λ)
    (hS : Supports M ↑S) :
    Turing.Respects
      (@step Γ Λ _ _ M)
      (@step Γ _ ⟨⟨default, hS.1⟩⟩ _ (restrict M S hS))
      (fun c₁ c₂ => restrictRel S c₂ c₁) := by
  intro c₁ c₂ h; rcases c₁ with ⟨ q₁, T₁ ⟩ ; rcases c₂ with ⟨ ⟨ q₂, hq₂ ⟩, T₂ ⟩ ; simp_all +decide [ Respects ] ;
  unfold step; rcases h with ⟨ rfl, rfl ⟩ ;
  rcases h : M q₁ T₁.head with ( _ | ⟨ q', a ⟩ ) <;> simp +decide [ *, Reaches₁ ] at *;
  · unfold restrict; aesop;
  · refine' ⟨ _, _, Relation.TransGen.single _ ⟩;
    rotate_left;
    exact ⟨ ⟨ q', hS.2 ( show ( q', a ) ∈ M q₁ T₁.head from h.symm ▸ by simp +decide ) hq₂ ⟩, match a with | Stmt.move d => Tape.move d T₁ | Stmt.write a => Tape.write a T₁ ⟩;
    · use q';
      use hS.2 ( show ( q', a ) ∈ M q₁ T₁.head from h.symm ▸ by simp +decide ) hq₂;
      use a;
      cases a <;> simp +decide [ * ];
      · unfold restrict; aesop;
      · unfold restrict; aesop;
    · cases a <;> tauto

/-
Initial configs are related.
-/
theorem restrict_init_rel (M : Machine Γ Λ) (S : Finset Λ)
    (hS : Supports M ↑S) (l : List Γ) :
    restrictRel S (@init Γ _ ⟨⟨default, hS.1⟩⟩ _ l) (@init Γ Λ _ _ l) := by
  exact ⟨ rfl, rfl ⟩

/-- The restricted TM0 halts if and only if the original does.

Uses `Turing.tr_eval_dom` with the bisimulation relation `restrictRel`. -/
theorem restrict_eval_dom_iff (M : Machine Γ Λ) (S : Finset Λ)
    (hS : Supports M ↑S) (l : List Γ) :
    (@eval Γ Λ _ _ M l).Dom ↔
    (@eval Γ _ ⟨⟨default, hS.1⟩⟩ _ (restrict M S hS) l).Dom := by
  simp only [eval, Eq.to_iff rfl]
  exact (Turing.tr_eval_dom (restrict_respects M S hS) (restrict_init_rel M S hS l)).symm

end Turing.TM0