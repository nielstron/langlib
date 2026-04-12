import Mathlib
import Langlib.Utilities.Homomorphism
import Langlib.Classes.Regular.Closure.Concatenation
import Langlib.Classes.Regular.Closure.Star
import Langlib.Classes.Regular.Closure.Substitution

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

section StringHomomorphism

variable {γ : Type}

/-! ### Singleton word languages are regular -/

/-
The language `{[]}` (containing only the empty word) is regular.
-/
theorem isRegular_epsilon : ({[]} : Language γ).IsRegular := by
  -- The DFA has two states: state 0 (start and accepting) and state 1 (sink). All transitions from state 0 go to state 1, and all transitions from state 1 go to state 1.
  use Fin 2;
  use inferInstance;
  fconstructor;
  exact ⟨ fun _ _ => 1, 0, { 0 } ⟩;
  ext ( _ | w ) <;> simp +decide [ DFA.accepts ];
  · exact (iff_true_right rfl).mpr rfl;
  · simp +decide [ DFA.acceptsFrom ];
    induction ‹List γ› <;> simp_all +decide [ DFA.evalFrom ];
    · grind +revert;
    · grind

/-
The language `{[a]}` (containing only the single-letter word) is regular.
-/
theorem isRegular_singleton_letter (a : γ) : ({[a]} : Language γ).IsRegular := by
  constructor;
  refine' ⟨ _, _, _ ⟩;
  case w => exact Fin 3;
  exact inferInstance;
  refine' { start := 0, step := fun q x => if q = 0 ∧ x = a then 1 else 2, accept := { 1 } };
  ext w; simp [DFA.accepts];
  rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ DFA.acceptsFrom ];
  · simp +decide [ DFA.evalFrom ];
    grind +extAll;
  · grind +suggestions;
  · induction w <;> simp_all +decide [ DFA.evalFrom ];
    · grind;
    · grind

/-
The singleton set `{a :: w}` equals the concatenation `{[a]} * {w}`.
-/
private lemma singleton_cons_eq_mul (a : γ) (w : List γ) :
    ({a :: w} : Language γ) = {[a]} * {w} := by
      ext x;
      constructor;
      · rintro rfl;
        exact ⟨ [a], by aesop ⟩;
      · rintro ⟨ u, v, hu, hv, rfl ⟩;
        cases v ; cases hv ; aesop

/-- Any singleton word language is regular. -/
theorem isRegular_singleton_word : ∀ (w : List γ), ({w} : Language γ).IsRegular
  | [] => isRegular_epsilon
  | a :: w => by
      rw [singleton_cons_eq_mul a w]
      exact (isRegular_singleton_letter a).mul' (isRegular_singleton_word w)

/-- Regular languages are closed under string homomorphism.

Given a regular language `L` over a finite alphabet and a string homomorphism
`h : α' → List γ`, the image `{h(w) | w ∈ L}` is regular. -/
theorem IsRegular.homomorphicImage {α' : Type} [Fintype α'] {L : Language α'}
    (hL : L.IsRegular) (h : α' → List γ) :
    (L.homomorphicImage h).IsRegular := by
  unfold Language.homomorphicImage
  exact hL.subst' (fun a => isRegular_singleton_word (h a))

end StringHomomorphism

end Language