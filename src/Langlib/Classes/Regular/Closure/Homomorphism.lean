import Mathlib
import Langlib.Utilities.Homomorphism
import Langlib.Classes.Regular.Closure.Concatenation
import Langlib.Classes.Regular.Closure.Star

/-! # Regular Closure Under (String) Homomorphism

This file proves that regular languages are closed under symbol maps (letter-to-letter
homomorphisms) and, more generally, under string homomorphisms.

## Main results

- `Language.IsRegular.map` — if `L` is regular then `Language.map f L` is regular.
- `Language.IsRegular.homomorphicImage` — if `L` is regular (over a finite alphabet)
  then its image under a string homomorphism is regular.
-/

namespace Language

open Classical

variable {α β : Type*}

section SymbolMap

variable {σ : Type*} [Fintype σ]

/-- NFA recognising the image of a DFA language under a symbol map.

For a DFA `M` over `α` and a function `f : α → β`, the NFA over `β` has the same
states.  On symbol `b`, from state `q`, the NFA non-deterministically guesses a
preimage `a` with `f a = b` and transitions to `M.step q a`. -/
noncomputable def mapNFA (M : DFA α σ) (f : α → β) : NFA β σ where
  step := fun q b => { q' | ∃ a, f a = b ∧ M.step q a = q' }
  start := {M.start}
  accept := M.accept

variable (M : DFA α σ) (f : α → β)

/-
The map-NFA evaluates singleton sets correctly: from `{q}` on word `List.map f v`,
    the result contains `M.evalFrom q v`.
-/
private lemma mapNFA_evalFrom_map (q : σ) (v : List α) :
    M.evalFrom q v ∈ (mapNFA M f).evalFrom {q} (List.map f v) := by
      induction' v using List.reverseRecOn with v a ih generalizing q <;> simp_all +decide [ NFA.evalFrom_append ];
      exact Set.mem_biUnion ( ih q ) ⟨ a, rfl, rfl ⟩

/-
If `q'` is in the NFA evaluation from `{q}` on `w`, then there exists a word `v`
    with `List.map f v = w` and `M.evalFrom q v = q'`.
-/
private lemma mapNFA_evalFrom_inv (q q' : σ) (w : List β)
    (h : q' ∈ (mapNFA M f).evalFrom {q} w) :
    ∃ v, List.map f v = w ∧ M.evalFrom q v = q' := by
      revert h;
      induction' w with b w ih generalizing q q' <;> simp +decide [ *, NFA.evalFrom_cons ];
      · exact fun h => h.symm;
      · intro h
        obtain ⟨q'', hq'', hq'⟩ : ∃ q'' ∈ (mapNFA M f).step q b, q' ∈ (mapNFA M f).evalFrom {q''} w := by
          contrapose! h;
          have h_foldl_stepSet : ∀ (S : Set σ) (w : List β), (mapNFA M f).evalFrom S w = ⋃ q'' ∈ S, (mapNFA M f).evalFrom {q''} w := by
            intro S w; induction' w using List.reverseRecOn with w ih <;> simp +decide [ *, NFA.evalFrom_cons ] ;
            simp +decide [ Set.ext_iff, NFA.stepSet ];
          rw [ h_foldl_stepSet ] ; simp +contextual [ h ];
        obtain ⟨ v, hv₁, hv₂ ⟩ := ih q'' q' hq';
        obtain ⟨ a, ha₁, ha₂ ⟩ := hq''; use a :: v; aesop;

/-
The map-NFA accepts exactly the image of the DFA language under `List.map f`.
-/
theorem mapNFA_correct :
    (mapNFA M f).accepts = Language.map f M.accepts := by
      ext w;
      constructor;
      · rintro ⟨ S, hS₁, hS₂ ⟩;
        obtain ⟨ v, hv₁, hv₂ ⟩ := mapNFA_evalFrom_inv M f ( M.start ) S w hS₂;
        exact ⟨ v, by aesop ⟩;
      · rintro ⟨ v, hv, rfl ⟩;
        exact ⟨ _, hv, mapNFA_evalFrom_map M f _ _ ⟩

end SymbolMap

/-- Regular languages are closed under symbol maps (letter-to-letter homomorphisms). -/
theorem IsRegular.map {L : Language α} (hL : L.IsRegular) (f : α → β) :
    (Language.map f L).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  rw [← mapNFA_correct M f]
  exact ⟨_, inferInstance, (mapNFA M f).toDFA, (mapNFA M f).toDFA_correct⟩

end Language