module

public import Langlib.Classes.Recursive.Definition

/-!
# Elementary Recursive Languages

This file records the immediate recursive languages, witnessed by TM0 machines
that halt without taking a step.
-/

open Turing

variable {T : Type}

/-- The universal language is recursive. -/
public theorem is_Recursive_univ : is_Recursive (Set.univ : Language T) := by
  let M : TM0.Machine (Option (T ⊕ Empty)) Unit := fun _ _ => none
  refine ⟨Empty, inferInstance, Unit, inferInstance, inferInstance, M, (fun _ => true), ?_, ?_⟩
  · intro w
    rw [Part.dom_iff_mem]
    refine ⟨TM0.init (w.map fun t => some (Sum.inl t)), ?_⟩
    rw [Turing.mem_eval]
    exact ⟨Relation.ReflTransGen.refl, by simp [M, TM0.step]⟩
  · intro w h
    exact ⟨fun _ => rfl, fun _ => Set.mem_univ w⟩

/-- The empty language is recursive. -/
public theorem is_Recursive_empty : is_Recursive (∅ : Set (List T)) := by
  let M : TM0.Machine (Option (T ⊕ Empty)) Unit := fun _ _ => none
  refine ⟨Empty, inferInstance, Unit, inferInstance, inferInstance, M, (fun _ => false), ?_, ?_⟩
  · intro w
    rw [Part.dom_iff_mem]
    refine ⟨TM0.init (w.map fun t => some (Sum.inl t)), ?_⟩
    rw [Turing.mem_eval]
    exact ⟨Relation.ReflTransGen.refl, by simp [M, TM0.step]⟩
  · intro w h
    exact ⟨False.elim, fun hfalse => by cases hfalse⟩
