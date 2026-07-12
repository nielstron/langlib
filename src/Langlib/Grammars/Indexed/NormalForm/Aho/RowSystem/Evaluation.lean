module

public import Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.Trace
public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.PaddedReach

set_option maxHeartbeats 800000

@[expose]
public section

/-!
# Evaluation lemmas for Aho's packed row checker

Physical input cells contain blocks of twenty-one logical work slots. This module bridges the
certified row system's cell-by-cell evaluator to the flattened input and work-track evaluators
used by the completeness and soundness proofs.
-/

set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

public noncomputable def evalRowTriples (g : IndexedGrammar T) [Fintype g.nt] :
    RowState g → List (RowCell g × RowCell g × RowCert g) → RowState g
  | state, [] => state
  | state, (old, new, cert) :: rows =>
      evalRowTriples g (rowStepCell g state old new cert) rows

public theorem evalStep_rowTriples (g : IndexedGrammar T) [Fintype g.nt]
    (state : RowState g) (rows : List (RowCell g × RowCell g × RowCert g)) :
    (ahoRowSystem g).evalStep state (rows.map fun r => r.1)
        (rows.map fun r => r.2.1) (rows.map fun r => r.2.2) =
      some (evalRowTriples g state rows) := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨old, new, cert⟩
      simp only [List.map_cons, CertifiedRowSystem.evalStep, ahoRowSystem_stepCell,
        evalRowTriples]
      exact ih _

/-- Flattening the consecutive physical work blocks recovers the fixed-width padded slot row. -/
public theorem packedBlockList_flatten (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (n : ℕ) :
    (packedBlockList g work 0 n).flatMap List.ofFn = paddedWork n work := by
  unfold packedBlockList paddedWork List.flatMap
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, packedCell, Nat.zero_add] using
    (List.ofFn_mul (fun i : Fin (n * workWidth) => work[i.val]?)).symm

private theorem foldThree_flatten
    {S X Y Z O N P : Type}
    (big : S → List X → List Y → List Z → S)
    (small : S → List O → List N → List P → S)
    (step : S → X → Y → Z → S)
    (flattenX : X → List O) (flattenY : Y → List N)
    (flattenZ : Z → List P)
    (hbigNil : ∀ state, big state [] [] [] = state)
    (hsmallNil : ∀ state, small state [] [] [] = state)
    (hbigCons : ∀ state x xs y ys z zs,
      big state (x :: xs) (y :: ys) (z :: zs) =
        big (step state x y z) xs ys zs)
    (hcombine : ∀ state x y z xs ys zs,
      small state (flattenX x ++ xs) (flattenY y ++ ys) (flattenZ z ++ zs) =
        small (step state x y z) xs ys zs)
    (state : S)
    (xs : List X) (ys : List Y) (zs : List Z)
    (hys : ys.length = xs.length) (hzs : zs.length = xs.length) :
    big state xs ys zs = small state
      (xs.flatMap flattenX) (ys.flatMap flattenY) (zs.flatMap flattenZ) := by
  induction xs generalizing state ys zs with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp (by simpa using hys)
      have hz : zs = [] := List.length_eq_zero_iff.mp (by simpa using hzs)
      subst ys
      subst zs
      simp only [List.flatMap_nil, hbigNil, hsmallNil]
  | cons x xs ih =>
      cases ys with
      | nil => simp at hys
      | cons y ys =>
          cases zs with
          | nil => simp at hzs
          | cons z zs =>
              simp only [List.length_cons, Nat.succ.injEq] at hys hzs
              rw [hbigCons, ih (step state x y z) ys zs hys hzs]
              simp only [List.flatMap_cons]
              exact (hcombine state x y z (xs.flatMap flattenX)
                (ys.flatMap flattenY) (zs.flatMap flattenZ)).symm

/-- Folding physical blocks is the same computation as folding their flattened slot streams. -/
public theorem evalWorkBlocks_eq_evalWorkSlots (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old new : List (WorkBlock g)) (choices : List (Fin workWidth → WorkPhase))
    (hnew : new.length = old.length) (hchoices : choices.length = old.length) :
    evalWorkBlocks g cert state old new choices =
      evalWorkSlots g cert state (old.flatMap List.ofFn) (new.flatMap List.ofFn)
        (choices.flatMap List.ofFn) := by
  apply foldThree_flatten (evalWorkBlocks g cert) (evalWorkSlots g cert)
    (evalWorkBlock g cert) List.ofFn List.ofFn List.ofFn
  · intro state
    rfl
  · intro state
    rfl
  · intro state x xs y ys z zs
    rfl
  · intro state x y z xs ys zs
    rw [evalWorkSlots_append g cert state (List.ofFn x) xs
      (List.ofFn y) ys (List.ofFn z) zs (by simp) (by simp)]
    rfl
  · exact hnew
  · exact hchoices

end Aho
end IndexedGrammar
