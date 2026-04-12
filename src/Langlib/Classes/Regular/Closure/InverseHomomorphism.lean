import Mathlib
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Utilities.Homomorphism
import Langlib.Utilities.ClosurePredicates

/-! # Regular Closure Under Inverse String Homomorphism

This file proves that regular languages are closed under inverse string
homomorphism. Given a DFA `M` recognising `L` and a string homomorphism
`h : β → List α`, we construct a DFA for `h⁻¹(L) = {w ∈ β* | h*(w) ∈ L}` by
composing `h` into the transition function.

## Main results

- `inverseHomDFA` — the DFA for the preimage under a string homomorphism.
- `inverseHomDFA_correct` — correctness of the construction.
- `Language.IsRegular.inverseStringHomomorphism` — if `L` is regular then
  `{w | w.flatMap h ∈ L}` is regular.
-/

open Classical

variable {α β : Type*}

section InverseHomomorphism

variable {σ : Type*} [Fintype σ]

/-- DFA for the inverse homomorphism `h⁻¹(L)`.

Given a DFA `M` over `α` and a string homomorphism `h : β → List α`, the
new DFA has the same state set but transitions via `M.evalFrom q (h b)` — it
processes the entire image `h(b)` in one step. -/
noncomputable def inverseHomDFA (M : DFA α σ) (h : β → List α) : DFA β σ where
  step := fun q b => M.evalFrom q (h b)
  start := M.start
  accept := M.accept

variable (M : DFA α σ) (h : β → List α)

/-
The eval of the inverse-homomorphism DFA equals the original DFA's eval on the
    homomorphic image.
-/
omit [Fintype σ] in
lemma inverseHomDFA_eval (w : List β) :
    (inverseHomDFA M h).eval w = M.eval (w.flatMap h) := by
      unfold inverseHomDFA;
      induction' w using List.reverseRecOn with w x ih;
      · rfl;
      · simp_all +decide [ DFA.eval, DFA.evalFrom ]

omit [Fintype σ] in
@[simp] lemma inverseHomDFA_accept :
    (inverseHomDFA M h).accept = M.accept := rfl

/-
The inverse-homomorphism DFA accepts exactly the preimage of `M.accepts` under
    the string homomorphism.
-/
theorem inverseHomDFA_correct :
    (inverseHomDFA M h).accepts = { w : List β | w.flatMap h ∈ M.accepts } := by
      convert Set.ext _;
      intro w;
      convert ( DFA.mem_accepts _ );
      rw [ inverseHomDFA_eval ];
      rfl

end InverseHomomorphism

namespace Language

/-- Regular languages are closed under inverse string homomorphism. -/
theorem IsRegular.inverseStringHomomorphism {L : Language α}
    (hL : L.IsRegular) (h : β → List α) :
    Language.IsRegular { w : List β | w.flatMap h ∈ L } := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, inferInstance, inverseHomDFA M h, inverseHomDFA_correct M h⟩

end Language

/-- The class of regular languages is closed under inverse string homomorphism. -/
theorem RG_closedUnderInverseHomomorphism :
    ClosedUnderInverseHomomorphism is_RG := by
  intro α β L h hL
  exact is_RG_of_isRegular ((isRegular_of_is_RG hL).inverseStringHomomorphism h)
