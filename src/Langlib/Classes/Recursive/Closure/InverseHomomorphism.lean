module

public import Langlib.Classes.Recursive.Decidability.Membership
import Langlib.Utilities.PrimrecHelpers

/-!
# Recursive Closure Under Inverse Homomorphism

This file proves that recursive languages over finite alphabets are closed under inverse
string homomorphism.

Membership in the inverse image `{w | w.flatMap h ∈ L}` is decided by computing
`w.flatMap h` and running the decider for `L`.
-/

/-- Recursive languages over finite alphabets are closed under inverse string homomorphism. -/
public theorem is_Recursive_inverseHomomorphism {α β : Type}
    [Fintype α] [Fintype β] (L : Language β) (h : α → List β) :
    is_Recursive L → is_Recursive ({w : List α | w.flatMap h ∈ L} : Language α) := by
  intro hL
  classical
  haveI : DecidableEq α := Classical.decEq _
  haveI : DecidableEq β := Classical.decEq _
  haveI : Primcodable α :=
    Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.truncEquivFin α).out
  haveI : Primcodable β :=
    Primcodable.ofEquiv (Fin (Fintype.card β)) (Fintype.truncEquivFin β).out
  obtain ⟨f, hf, hs⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable hL)
  refine is_Recursive_of_computable_decide
    ({w : List α | w.flatMap h ∈ L} : Language α)
    (fun w => f (w.flatMap h))
    (hf.comp (primrec_flatMap_finite h).to_comp) ?_
  intro w
  simpa using (iff_of_eq (congrFun hs (w.flatMap h)))

/-- The class of recursive languages is closed under inverse string homomorphism. -/
public theorem Recursive_closedUnderInverseHomomorphism :
    ClosedUnderInverseHomomorphism is_Recursive := by
  intro α β _ _ L h hL
  exact is_Recursive_inverseHomomorphism L h hL
