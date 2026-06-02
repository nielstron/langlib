module

public import Langlib.Automata.LinearBounded.Equivalence.CSGToLBA.Soundness
import Mathlib.Tactic
@[expose]
public section

/-!
# Context-Sensitive Grammar → LBA (Kuroda's Construction)

This is the capstone of the CS → LBA direction. It assembles the two-way correctness of the
backward-simulating LBA `kMachine g₀` (built in `CSGToLBA/Construction.lean`, proven complete in
`CSGToLBA/Completeness.lean` and sound in `CSGToLBA/Soundness.lean`) into the core statement
`noncontracting_finite_to_LBA`: a non-contracting grammar with finitely many nonterminals is
recognised by a nondeterministic LBA on a tape of exactly `|w|` cells.

The empty-word bookkeeping and the reduction from an arbitrary context-sensitive grammar are
done in `Equivalence/ContextSensitive.lean`.

## References

* Kuroda, S.-Y. (1964), "Classes of languages and linear-bounded automata".
* Hopcroft, Motwani, Ullman, *Introduction to Automata Theory, Languages, and Computation*,
  Chapter 9.
-/

namespace KurodaConstruction

open List Relation Classical

noncomputable section

variable {T : Type}
theorem noncontracting_finite_to_LBA [Fintype T] [DecidableEq T]
    (g₀ : grammar T) (hfin : Finite g₀.nt) (hnc : grammar_noncontracting g₀) :
    ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
      (_ : DecidableEq Γ) (_ : DecidableEq Λ)
      (M : LBA.Machine (Option (T ⊕ Γ)) Λ),
      LBA.LanguageViaEmbed M (fun t => some (Sum.inl t)) = grammar_language g₀ := by
  haveI : Fintype g₀.nt := Fintype.ofFinite _
  haveI : DecidableEq g₀.nt := Classical.decEq _
  refine ⟨KGamma g₀, KState g₀, inferInstance, inferInstance, inferInstance, inferInstance,
    kMachine g₀, ?_⟩
  funext w
  apply propext
  constructor
  · -- soundness: an accepting run on `w` exhibits a derivation `[S] ⇒* w`
    exact kMachine_sound g₀ hnc w
  · -- completeness: a derivation `[S] ⇒* w` is replayed by an accepting run
    exact kMachine_complete g₀ hnc w
end

end KurodaConstruction
