module

public import Langlib.Classes.Recursive.Definition
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Mathlib.Computability.DFA

/-!
# Regular Languages Are Recursive

This file converts a finite-state DFA into a TM0 decider by scanning right across
the input while carrying the DFA state in the TM0 state.
-/

open Turing

namespace RecursiveRegular

variable {α σ : Type}

noncomputable def dfaMachine (M : DFA α σ) [Inhabited σ] :
    TM0.Machine (Option (α ⊕ Empty)) σ :=
  fun q a =>
    match a with
    | some (Sum.inl x) => some (M.step q x, TM0.Stmt.move Dir.right)
    | _ => none

lemma dfaMachine_scan (M : DFA α σ) [Inhabited σ] (q : σ) :
    ∀ (w : List α) (left : List (Option (α ⊕ Empty))),
      Reaches (TM0.step (dfaMachine M))
        ⟨q, Tape.mk₂ left (w.map fun x => some (Sum.inl x))⟩
        ⟨M.evalFrom q w, Tape.mk₂ ((w.map fun x => some (Sum.inl x)).reverse ++ left) []⟩
  | [], left => by
      exact Relation.ReflTransGen.refl
  | x :: xs, left => by
      have hstep :
          TM0.step (dfaMachine M)
            ⟨q, Tape.mk₂ left ((x :: xs).map fun x => some (Sum.inl x))⟩ =
          some ⟨M.step q x, Tape.mk₂ (some (Sum.inl x) :: left)
            (xs.map fun x => some (Sum.inl x))⟩ := by
        simp [dfaMachine, TM0.step, Tape.mk₂, Tape.mk', Tape.move, ListBlank.tail_mk]
      refine Relation.ReflTransGen.head hstep ?_
      convert dfaMachine_scan M (M.step q x) xs (some (Sum.inl x) :: left) using 1
      simp [DFA.evalFrom, List.map, List.reverse_cons, List.append_assoc]

public theorem is_Recursive_of_dfa [Fintype σ] (M : DFA α σ) :
    is_Recursive M.accepts := by
  classical
  letI : Inhabited σ := ⟨M.start⟩
  let accept : σ → Bool := fun q => if q ∈ M.accept then true else false
  let TM : TM0.Machine (Option (α ⊕ Empty)) σ := dfaMachine M
  refine ⟨Empty, inferInstance, σ, inferInstance, inferInstance, TM, accept, ?_, ?_⟩
  · intro w
    let cfg : TM0.Cfg (Option (α ⊕ Empty)) σ :=
      ⟨M.eval w, Tape.mk₂ ((w.map fun x => some (Sum.inl x)).reverse) []⟩
    have hmem : cfg ∈ eval (TM0.step TM)
        (TM0.init (w.map fun x => some (Sum.inl x))) := by
      rw [Turing.mem_eval]
      refine ⟨?_, ?_⟩
      · simpa [TM, TM0.init, Tape.mk₁] using dfaMachine_scan M M.start w []
      · change TM0.step TM cfg = none
        simp [cfg, TM, dfaMachine, TM0.step, Tape.mk₂, Tape.mk']
    exact Part.dom_iff_mem.mpr ⟨cfg, hmem⟩
  · intro w h
    let cfg : TM0.Cfg (Option (α ⊕ Empty)) σ :=
      ⟨M.eval w, Tape.mk₂ ((w.map fun x => some (Sum.inl x)).reverse) []⟩
    have hmem : cfg ∈ eval (TM0.step TM)
        (TM0.init (w.map fun x => some (Sum.inl x))) := by
      rw [Turing.mem_eval]
      refine ⟨?_, ?_⟩
      · simpa [TM, TM0.init, Tape.mk₁] using dfaMachine_scan M M.start w []
      · change TM0.step TM cfg = none
        simp [cfg, TM, dfaMachine, TM0.step, Tape.mk₂, Tape.mk']
    have hcfg :
        (eval (TM0.step TM) (TM0.init (w.map fun x => some (Sum.inl x)))).get h = cfg :=
      Part.mem_unique (Part.get_mem h) hmem
    have hq :
        ((eval (TM0.step TM)
          (TM0.init (w.map fun x => some (Sum.inl x)))).get h).q = M.eval w := by
      exact congrArg TM0.Cfg.q hcfg
    by_cases hacc : M.eval w ∈ M.accept <;> simp [DFA.mem_accepts, accept, hq, hacc]

end RecursiveRegular

public theorem is_Recursive_of_isRegular {L : Language α}
    (hL : L.IsRegular) : is_Recursive L := by
  obtain ⟨σ, _hσ, M, rfl⟩ := hL
  exact RecursiveRegular.is_Recursive_of_dfa M

/-- Every singleton word language is recursive. -/
public theorem is_Recursive_singleton_word (w : List α) :
    is_Recursive ({w} : Language α) :=
  is_Recursive_of_isRegular (Language.isRegular_singleton_word w)
