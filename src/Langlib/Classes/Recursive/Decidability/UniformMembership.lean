module

public import Langlib.Classes.Recursive.Basics.Post
public import Langlib.Utilities.ComputabilityPredicates

@[expose]
public section

/-!
# No uniform membership algorithm for all recursive languages

Every individual recursive language has decidable membership, but there is no
adequate computable numbering of *all* recursive languages whose membership
relation is uniformly decidable.  This distinction matters for
`ComputableMembership`, which deliberately asks for a uniform algorithm taking a
language code as an input.

The proof is the usual diagonal argument.  Given a proposed presentation
`languageOf`, encode a code `c` by the unary word of length `encode c` and define a
language which disagrees with `languageOf c` on that word.  Uniform decidability
makes the diagonal language recursive, while adequacy says that it itself has a
code, yielding a contradiction.
-/

open Encodable

/-- The diagonal language associated to a proposed coded presentation. -/
private def recursiveDiagonal {T Code : Type} [Primcodable Code]
    (languageOf : Code → Language T) : Language T :=
  fun w =>
    match decode (α := Code) w.length with
    | none => False
    | some c => w ∉ languageOf c

/-- Uniformly decidable membership would make the diagonal language recursive. -/
private theorem recursiveDiagonal_isRecursive
    {T Code : Type} [DecidableEq T] [Fintype T] [Primcodable T] [Primcodable Code]
    (languageOf : Code → Language T)
    (hmem : ComputablePred (fun p : Code × List T => p.2 ∈ languageOf p.1)) :
    is_Recursive (recursiveDiagonal languageOf) := by
  obtain ⟨f, hf, hspec⟩ := ComputablePred.computable_iff.mp hmem
  let diagonalDecider : List T → Bool := fun w =>
    match decode (α := Code) w.length with
    | none => false
    | some c => !f (c, w)
  have hdecode : Computable (fun w : List T => decode (α := Code) w.length) :=
    Computable.decode.comp Computable.list_length
  have hbranch : Computable₂ (fun (w : List T) (c : Code) => !f (c, w)) := by
    exact (Primrec.not.to_comp.comp
      (hf.comp (Computable.pair Computable.snd Computable.fst))).to₂
  have hdecider : Computable diagonalDecider := by
    exact (Computable.option_casesOn hdecode (Computable.const false) hbranch).of_eq
      fun w => by
        simp only [diagonalDecider]
        cases decode (α := Code) w.length <;> rfl
  apply is_Recursive_of_computable_decide (recursiveDiagonal languageOf)
      diagonalDecider hdecider
  intro w
  change
    (match decode (α := Code) w.length with
      | none => False
      | some c => w ∉ languageOf c) ↔
    (match decode (α := Code) w.length with
      | none => false
      | some c => !f (c, w)) = true
  cases hcode : decode (α := Code) w.length with
  | none => simp only [Bool.false_eq_true]
  | some c =>
      have hfc : (w ∈ languageOf c) ↔ f (c, w) = true := by
        have := congrFun hspec (c, w)
        simpa using iff_of_eq this
      cases hfval : f (c, w) <;> simp_all

/-- Over any nonempty finite computably encoded alphabet, there is no adequate
presentation of all recursive languages with uniformly computable membership. -/
public theorem Recursive_notComputableMembership
    {T Code : Type} [DecidableEq T] [Fintype T] [Primcodable T] [Nonempty T]
    [Primcodable Code] (languageOf : Code → Language T) :
    ¬ ComputableMembership Recursive languageOf := by
  intro h
  have hdiag : is_Recursive (recursiveDiagonal languageOf) :=
    recursiveDiagonal_isRecursive languageOf h.2.2
  obtain ⟨c, hc⟩ := (h.1 (recursiveDiagonal languageOf)).mp hdiag
  let w : List T := List.replicate (encode c) (Classical.arbitrary T)
  have hdecode : decode (α := Code) w.length = some c := by
    simp [w]
  have hiff : w ∈ recursiveDiagonal languageOf ↔
      w ∉ recursiveDiagonal languageOf := by
    change (match decode (α := Code) w.length with
      | none => False
      | some c' => w ∉ languageOf c') ↔ _
    simp only [hdecode]
    rw [hc]
  tauto
